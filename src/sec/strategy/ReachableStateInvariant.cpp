// Copyright 2024-2026 keplertech.io
// SPDX-License-Identifier: GPL-3.0-only

#include "strategy/ReachableStateInvariant.h"

#include <algorithm>
#include <cctype>
#include <cstdint>
#include <cstdio>
#include <limits>
#include <memory_resource>
#include <optional>
#include <set>
#include <stdexcept>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/BoolExprUtils.h"
#include "strategy/StructuralStateInvariant.h"

namespace KEPLER_FORMAL::SEC {

// Overall reachable-state strengthening algorithm:
// 1. Discover any reset inputs and explicit initial-state information.
// 2. Filter structural state pairs down to ones compatible with startup.
// 3. If reset/bootstrap is available, specialize next-state logic under reset.
// 4. Symbolically push known reset-state values forward for a few cycles.
// 5. Keep only the state equalities that survive each bootstrap step.
// 6. Return both the startup correspondence and the anchored equalities/value
//    facts that later proof engines can rely on.

namespace {

constexpr size_t kBootstrapSatRecoverySupportBudget = 4096;
constexpr size_t kBootstrapSatRecoveryNodeBudget = 2048;
// SAT recovery is already filtered by support size. Keep the candidate budget
// at the same scale so cheap reset/bootstrap cones are not discarded before the
// KI/IMC engines get a useful invariant, while wide ASIC cones still fall back
// to the engine-level COI proof instead of launching unbounded per-bit SAT.
constexpr size_t kBootstrapSatRecoveryCandidateBudget =
    kBootstrapSatRecoverySupportBudget;
constexpr size_t kSelectiveBootstrapValueCandidateBudget = 10000;
constexpr size_t kUnpairedStateDependency = std::numeric_limits<size_t>::max();

using ConstantEvalMemo =
    std::pmr::unordered_map<BoolExpr*, std::optional<bool>>;
using SpecializedNextMap =
    std::unordered_map<SignalKey, BoolExpr*, SignalKeyHash>;

struct ResetStepEvalSummary {
  bool valid = true;
  std::optional<bool> constant;
  bool proven = false;
};

bool isConstBoolExpr(BoolExpr* expr, bool value) {
  return expr != nullptr && expr->getOp() == Op::VAR &&
         expr->getId() == static_cast<size_t>(value ? 1 : 0);
}

bool areSatEquivalentUnderAbstractMaps(
    BoolExpr* expr0,
    BoolExpr* expr1,
    const LocalToAbstractVarMap& abstractMap0,
    const LocalToAbstractVarMap& abstractMap1,
    KEPLER_FORMAL::Config::SolverType solverType) {
  try {
    std::unordered_map<BoolExpr*, BoolExpr*> memo0;
    std::unordered_map<BoolExpr*, BoolExpr*> memo1;
    BoolExpr* remapped0 = remapBoolExprVariables(expr0, abstractMap0, memo0);
    BoolExpr* remapped1 = remapBoolExprVariables(expr1, abstractMap1, memo1);
    return boolFormulaImplies(
        BoolExpr::createTrue(),
        makeEqualityExpr(remapped0, remapped1),
        solverType);
  } catch (const std::runtime_error&) {
    return false;
  }
}

bool addBoundedSupportVar(
    size_t varID,
    std::pmr::unordered_set<size_t>& support,
    size_t budget) {
  if (varID >= 2) {
    support.insert(varID);
  }
  return support.size() <= budget;
}

bool collectBoundedSupportVars(
    BoolExpr* root,
    std::pmr::unordered_set<const BoolExpr*>& visited,
    std::pmr::unordered_set<size_t>& support,
    size_t supportBudget,
    size_t nodeBudget,
    size_t& visitedNodes,
    std::vector<BoolExpr*>& stack) {
  if (root == nullptr) {
    return true;  // LCOV_EXCL_LINE
  }

  stack.clear();
  stack.push_back(root);
  while (!stack.empty()) {
    BoolExpr* node = stack.back();
    stack.pop_back();
    if (node == nullptr || !visited.insert(node).second) {
      continue;  // LCOV_EXCL_LINE
    }
    if (++visitedNodes > nodeBudget) {
      return false;
    }

    if (node->getOp() == Op::VAR) {
      if (!addBoundedSupportVar(node->getId(), support, supportBudget)) {
        return false;
      }
      continue;
    }
    if (node->getRight() != nullptr) {
      stack.push_back(node->getRight());
    }
    if (node->getLeft() != nullptr) {
      stack.push_back(node->getLeft());
    }
  }
  return true;
}

std::optional<size_t> bootstrapSatRecoverySupportSize(BoolExpr* expr0,
                                                      BoolExpr* expr1) {
  std::pmr::monotonic_buffer_resource supportResource;
  std::pmr::unordered_set<const BoolExpr*> visited{&supportResource};
  std::pmr::unordered_set<size_t> support{&supportResource};
  std::vector<BoolExpr*> stack;
  visited.reserve(kBootstrapSatRecoveryNodeBudget + 1);
  support.reserve(kBootstrapSatRecoverySupportBudget + 1);
  size_t visitedNodes = 0;
  // This only decides whether an ambiguous bootstrap cone is cheap enough for
  // SAT recovery.  Do not allocate full support or visited-node sets on ASIC
  // cones: stop as soon as either the support or expression-DAG budget is
  // exceeded and let the proof engine handle that cone in its normal COI query.
  if (!collectBoundedSupportVars(
          expr0,
          visited,
          support,
          kBootstrapSatRecoverySupportBudget,
          kBootstrapSatRecoveryNodeBudget,
          visitedNodes,
          stack)) {
    return std::nullopt;
  }
  if (!collectBoundedSupportVars(
          expr1,
          visited,
          support,
          kBootstrapSatRecoverySupportBudget,
          kBootstrapSatRecoveryNodeBudget,
          visitedNodes,
          stack)) {
    return std::nullopt;
  }
  return support.size();
}

std::string normalizeSignalBaseName(const std::string& name) {
  std::string base = name;
  const auto bracket = base.find('[');
  if (bracket != std::string::npos) {
    base = base.substr(0, bracket);
  }
  std::transform(base.begin(), base.end(), base.begin(), [](unsigned char ch) {
    return static_cast<char>(std::toupper(ch));
  });
  return base;
}

bool hasSuffix(const std::string& value, const std::string& suffix) {
  return value.size() >= suffix.size() &&
         value.compare(value.size() - suffix.size(), suffix.size(), suffix) == 0;
}

bool isResetNameToken(const std::string& candidate, const std::string& token) {
  // Domain-prefixed top resets, for example `wb_rst_i`, normalize to `WB_RST`
  // after input-suffix stripping.  Match only a final underscore-separated
  // reset token so prefixes do not block reachable-state reset bootstrap.
  return candidate == token || hasSuffix(candidate, "_" + token);
}

std::vector<std::string> resetNameCandidates(const std::string& displayName) {
  // Reset ports frequently carry RTL direction suffixes (`reset_i`, `rst_ni`).
  // Strip only those common input suffixes before classification so a real
  // reset is bootstrapped, without broadening the matcher to arbitrary names.
  const std::string normalized = normalizeSignalBaseName(displayName);
  std::vector<std::string> candidates = {normalized};
  if (hasSuffix(normalized, "_IN")) {
    candidates.push_back(normalized.substr(0, normalized.size() - 3));
  }
  if (hasSuffix(normalized, "_I")) {
    candidates.push_back(normalized.substr(0, normalized.size() - 2));
  }
  if (hasSuffix(normalized, "_NI")) {
    candidates.push_back(normalized.substr(0, normalized.size() - 1));
  }
  return candidates;
}

std::optional<bool> getResetAssertionValue(const std::string& displayName) {
  for (const auto& candidate : resetNameCandidates(displayName)) {
    if (isResetNameToken(candidate, "RESET") ||
        isResetNameToken(candidate, "RST")) {
      return true;
    }
    if (isResetNameToken(candidate, "RESET_N") ||
        isResetNameToken(candidate, "RESETN") ||
        isResetNameToken(candidate, "RESET_L") ||
        isResetNameToken(candidate, "RST_N") ||
        isResetNameToken(candidate, "RSTN") ||
        isResetNameToken(candidate, "RST_L")) {
      return false;
    }
  }
  return std::nullopt;
}

std::unordered_map<size_t, bool> collectResetAssignments(
    const SequentialDesignModel& model) {
  // Reset controls are identified from the aligned user-visible signal names
  // and then converted into the local BoolExpr variable IDs used by the model.
  std::unordered_map<size_t, bool> assignments;
  for (const auto& key : model.environmentInputs) {
    const auto displayIt = model.displayNameByKey.find(key);
    const auto varIt = model.inputVarByKey.find(key);
    if (displayIt == model.displayNameByKey.end() ||
        varIt == model.inputVarByKey.end()) {
      continue;
    }
    const auto assertedValue = getResetAssertionValue(displayIt->second);
    if (!assertedValue.has_value()) {
      continue;
    }
    assignments.emplace(varIt->second, *assertedValue);
  }
  return assignments;
}

bool haveConflictingInitialValues(
    const SequentialDesignModel& model0,
    const SignalKey& key0,
    const SequentialDesignModel& model1,
    const SignalKey& key1) {
  const auto initial0 = model0.initialStateValueByKey.find(key0);
  const auto initial1 = model1.initialStateValueByKey.find(key1);
  return initial0 != model0.initialStateValueByKey.end() &&
         initial1 != model1.initialStateValueByKey.end() &&
         initial0->second != initial1->second;
}

void appendStatePairIfUnused(
    AlignedSignals& states,
    const std::string& name,
    const SignalKey& key0,
    const SignalKey& key1,
    std::unordered_set<SignalKey, SignalKeyHash>& usedKeys0,
    std::unordered_set<SignalKey, SignalKeyHash>& usedKeys1) {
  if (usedKeys0.find(key0) != usedKeys0.end() ||
      usedKeys1.find(key1) != usedKeys1.end()) {
    return;
  }

  states.names.push_back(name);
  states.keys0.push_back(key0);
  states.keys1.push_back(key1);
  usedKeys0.insert(key0);
  usedKeys1.insert(key1);
}

AlignedSignals mergeStartupCorrespondence(
    const AlignedSignals& structuralStates,
    const AlignedSignals& additionalStates) {
  AlignedSignals mergedStates;
  std::unordered_set<SignalKey, SignalKeyHash> usedKeys0;
  std::unordered_set<SignalKey, SignalKeyHash> usedKeys1;
  usedKeys0.reserve(structuralStates.keys0.size() + additionalStates.keys0.size());
  usedKeys1.reserve(structuralStates.keys1.size() + additionalStates.keys1.size());
  mergedStates.names.reserve(structuralStates.names.size() + additionalStates.names.size());
  mergedStates.keys0.reserve(structuralStates.keys0.size() + additionalStates.keys0.size());
  mergedStates.keys1.reserve(structuralStates.keys1.size() + additionalStates.keys1.size());
  for (size_t i = 0; i < structuralStates.names.size(); ++i) {
    appendStatePairIfUnused(
        mergedStates,
        structuralStates.names[i],
        structuralStates.keys0[i],
        structuralStates.keys1[i],
        usedKeys0,
        usedKeys1);
  }
  for (size_t i = 0; i < additionalStates.names.size(); ++i) {
    appendStatePairIfUnused(
        mergedStates,
        additionalStates.names[i],
        additionalStates.keys0[i],
        additionalStates.keys1[i],
        usedKeys0,
        usedKeys1);
  }
  return mergedStates;
}

AlignedSignals keepEqualitiesWithStateVariables(
    const SequentialDesignModel& model0,
    const SequentialDesignModel& model1,
    const AlignedSignals& states) {
  AlignedSignals filteredStates;
  for (size_t i = 0; i < states.names.size(); ++i) {
    if (model0.inputVarByKey.find(states.keys0[i]) == model0.inputVarByKey.end() ||
        model1.inputVarByKey.find(states.keys1[i]) == model1.inputVarByKey.end()) {
      continue;
    }
    filteredStates.names.push_back(states.names[i]);
    filteredStates.keys0.push_back(states.keys0[i]);
    filteredStates.keys1.push_back(states.keys1[i]);
  }
  return filteredStates;
}

std::vector<SignalKey> collectResetBootstrapRelevantStateKeys(
    const SequentialDesignModel& model,
    const std::vector<SignalKey>& rootKeys,
    size_t cycles) {
  std::unordered_map<size_t, SignalKey> stateKeyByVar;
  stateKeyByVar.reserve(model.stateBits.size());
  for (const auto& key : model.stateBits) {
    if (const auto varIt = model.inputVarByKey.find(key);
        varIt != model.inputVarByKey.end()) {
      stateKeyByVar.emplace(varIt->second, key);
    }
  }

  std::unordered_set<SignalKey, SignalKeyHash> selected;
  selected.reserve(rootKeys.size());
  std::vector<SignalKey> ordered;
  ordered.reserve(rootKeys.size());
  std::vector<SignalKey> frontier;
  frontier.reserve(rootKeys.size());
  auto addKey = [&](const SignalKey& key, std::vector<SignalKey>& target) {
    if (selected.insert(key).second) {
      ordered.push_back(key);
      target.push_back(key);
    }
  };
  for (const auto& key : rootKeys) {
    addKey(key, frontier);
  }

  std::pmr::monotonic_buffer_resource traversalResource;
  std::pmr::unordered_set<BoolExpr*> visitedExprs{&traversalResource};
  std::vector<BoolExpr*> stack;
  auto appendSupportedStateKeys = [&](BoolExpr* expr,
                                      std::vector<SignalKey>& target) {
    if (expr == nullptr) {
      return;  // LCOV_EXCL_LINE
    }

    stack.push_back(expr);
    while (!stack.empty()) {
      BoolExpr* node = stack.back();
      stack.pop_back();
      if (node == nullptr || !visitedExprs.insert(node).second) {
        continue;
      }
      if (node->getOp() == Op::VAR) {
        if (const auto stateIt = stateKeyByVar.find(node->getId());
            stateIt != stateKeyByVar.end()) {
          addKey(stateIt->second, target);
        }
        continue;
      }
      if (node->getRight() != nullptr) {
        stack.push_back(node->getRight());
      }
      if (node->getLeft() != nullptr) {
        stack.push_back(node->getLeft());
      }
    }
  };

  for (size_t depth = 0; depth < cycles && !frontier.empty(); ++depth) {
    std::vector<SignalKey> nextFrontier;
    for (const auto& key : frontier) {
      const auto nextIt = model.nextStateExprByStateKey.find(key);
      if (nextIt == model.nextStateExprByStateKey.end() ||
          nextIt->second == nullptr) {
        continue;  // LCOV_EXCL_LINE
      }
      appendSupportedStateKeys(nextIt->second, nextFrontier);
    }
    frontier = std::move(nextFrontier);
  }
  return ordered;
}

std::unordered_map<size_t, size_t> buildStatePairIndexByVar(
    const SequentialDesignModel& model,
    const std::vector<SignalKey>& candidateKeys) {
  std::unordered_map<size_t, size_t> pairIndexByVar;
  pairIndexByVar.reserve(model.stateBits.size());
  for (const auto& key : model.stateBits) {
    if (const auto varIt = model.inputVarByKey.find(key);
        varIt != model.inputVarByKey.end()) {
      pairIndexByVar.emplace(varIt->second, kUnpairedStateDependency);
    }
  }
  for (size_t i = 0; i < candidateKeys.size(); ++i) {
    if (const auto varIt = model.inputVarByKey.find(candidateKeys[i]);
        varIt != model.inputVarByKey.end()) {
      pairIndexByVar[varIt->second] = i;
    }
  }
  return pairIndexByVar;
}

bool isProvenResetStepOperand(const ResetStepEvalSummary& summary) {
  return summary.constant.has_value() || summary.proven;
}

ResetStepEvalSummary evaluateResetStepExpr(
    BoolExpr* expr,
    const std::unordered_map<size_t, bool>& resetAssignments,
    const std::unordered_map<size_t, size_t>& statePairIndexByVar,
    const std::vector<char>& previousProvenPairs,
    const std::vector<std::optional<bool>>& previousPairConstants,
    std::pmr::unordered_map<BoolExpr*, ResetStepEvalSummary>& memo) {
  if (expr == nullptr) {
    return {.valid = false};
  }
  if (const auto memoIt = memo.find(expr); memoIt != memo.end()) {
    return memoIt->second;
  }

  ResetStepEvalSummary summary;
  switch (expr->getOp()) {
    case Op::VAR: {
      const size_t id = expr->getId();
      if (id < 2) {
        summary.constant = id == 1;
        summary.proven = true;
      } else if (const auto resetIt = resetAssignments.find(id);
                 resetIt != resetAssignments.end()) {
        summary.constant = resetIt->second;
        summary.proven = true;
      } else if (const auto pairIt = statePairIndexByVar.find(id);
                 pairIt != statePairIndexByVar.end()) {
        if (pairIt->second == kUnpairedStateDependency) {
          summary.proven = false;
        } else if (previousPairConstants[pairIt->second].has_value()) {
          summary.constant = *previousPairConstants[pairIt->second];
          summary.proven = true;
        } else {
          summary.proven = previousProvenPairs[pairIt->second];
        }
      } else {
        // Non-state variables are top/environment inputs in the SEC model.
        // The structural COI validation already proved both sides use the same
        // aligned input classes, so no internal name equality is introduced here.
        summary.proven = true;
      }
      break;
    }
    case Op::NOT: {
      auto child = evaluateResetStepExpr(
          expr->getLeft(),
          resetAssignments,
          statePairIndexByVar,
          previousProvenPairs,
          previousPairConstants,
          memo);
      if (!child.valid) {
        summary.valid = false;
        break;
      }
      if (child.constant.has_value()) {
        summary.constant = !*child.constant;
      }
      summary.proven = isProvenResetStepOperand(child);
      break;
    }
    case Op::AND: {
      auto lhs = evaluateResetStepExpr(
          expr->getLeft(),
          resetAssignments,
          statePairIndexByVar,
          previousProvenPairs,
          previousPairConstants,
          memo);
      if (!lhs.valid) {
        summary.valid = false;
        break;
      }
      if (lhs.constant.has_value() && !*lhs.constant) {
        summary.constant = false;
        summary.proven = true;
        break;
      }
      auto rhs = evaluateResetStepExpr(
          expr->getRight(),
          resetAssignments,
          statePairIndexByVar,
          previousProvenPairs,
          previousPairConstants,
          memo);
      if (!rhs.valid) {
        summary.valid = false;
        break;
      }
      if (rhs.constant.has_value() && !*rhs.constant) {
        summary.constant = false;
        summary.proven = true;
        break;
      }
      if (lhs.constant.has_value() && rhs.constant.has_value()) {
        summary.constant = *lhs.constant && *rhs.constant;
        summary.proven = true;
        break;
      }
      summary.proven =
          isProvenResetStepOperand(lhs) && isProvenResetStepOperand(rhs);
      break;
    }
    case Op::OR: {
      auto lhs = evaluateResetStepExpr(
          expr->getLeft(),
          resetAssignments,
          statePairIndexByVar,
          previousProvenPairs,
          previousPairConstants,
          memo);
      if (!lhs.valid) {
        summary.valid = false;
        break;
      }
      if (lhs.constant.has_value() && *lhs.constant) {
        summary.constant = true;
        summary.proven = true;
        break;
      }
      auto rhs = evaluateResetStepExpr(
          expr->getRight(),
          resetAssignments,
          statePairIndexByVar,
          previousProvenPairs,
          previousPairConstants,
          memo);
      if (!rhs.valid) {
        summary.valid = false;
        break;
      }
      if (rhs.constant.has_value() && *rhs.constant) {
        summary.constant = true;
        summary.proven = true;
        break;
      }
      if (lhs.constant.has_value() && rhs.constant.has_value()) {
        summary.constant = *lhs.constant || *rhs.constant;
        summary.proven = true;
        break;
      }
      summary.proven =
          isProvenResetStepOperand(lhs) && isProvenResetStepOperand(rhs);
      break;
    }
    case Op::XOR: {
      auto lhs = evaluateResetStepExpr(
          expr->getLeft(),
          resetAssignments,
          statePairIndexByVar,
          previousProvenPairs,
          previousPairConstants,
          memo);
      auto rhs = evaluateResetStepExpr(
          expr->getRight(),
          resetAssignments,
          statePairIndexByVar,
          previousProvenPairs,
          previousPairConstants,
          memo);
      if (!lhs.valid || !rhs.valid) {
        summary.valid = false;
        break;
      }
      if (lhs.constant.has_value() && rhs.constant.has_value()) {
        summary.constant = *lhs.constant != *rhs.constant;
        summary.proven = true;
        break;
      }
      summary.proven =
          isProvenResetStepOperand(lhs) && isProvenResetStepOperand(rhs);
      break;
    }
    case Op::NONE:
    default:
      summary.valid = false;
      break;
  }

  auto [it, _] = memo.emplace(expr, std::move(summary));
  return it->second;
}

AlignedSignals deriveResetBootstrapStateEqualitiesByDependency(
    const SequentialDesignModel& model0,
    const SequentialDesignModel& model1,
    const AlignedSignals& candidateStates,
    const AlignedSignals& startupEqualities,
    size_t cycles,
    bool secDiagEnabled,
    std::unordered_map<SignalKey, bool, SignalKeyHash>* bootstrapValues0,
    std::unordered_map<SignalKey, bool, SignalKeyHash>* bootstrapValues1) {
  if (cycles == 0 || candidateStates.names.empty()) {
    return {};
  }
  const auto resetAssignments0 = collectResetAssignments(model0);
  const auto resetAssignments1 = collectResetAssignments(model1);
  if (resetAssignments0.empty() || resetAssignments1.empty()) {
    return {};  // LCOV_EXCL_LINE
  }

  const auto statePairIndexByVar0 =
      buildStatePairIndexByVar(model0, candidateStates.keys0);
  const auto statePairIndexByVar1 =
      buildStatePairIndexByVar(model1, candidateStates.keys1);

  std::vector<char> proven(candidateStates.names.size(), false);
  std::vector<std::optional<bool>> provenConstants(candidateStates.names.size());
  std::unordered_map<SignalKey, size_t, SignalKeyHash> candidatePairByKey0;
  candidatePairByKey0.reserve(candidateStates.names.size());
  for (size_t i = 0; i < candidateStates.names.size(); ++i) {
    candidatePairByKey0.emplace(candidateStates.keys0[i], i);
  }
  size_t seededStartupEqualities = 0;
  for (size_t i = 0; i < startupEqualities.names.size(); ++i) {
    const auto candidateIt = candidatePairByKey0.find(startupEqualities.keys0[i]);
    if (candidateIt == candidatePairByKey0.end() ||
        candidateStates.keys1[candidateIt->second] != startupEqualities.keys1[i]) {
      continue;
    }
    if (!proven[candidateIt->second]) {
      proven[candidateIt->second] = true;
      ++seededStartupEqualities;
    }
  }
  if (secDiagEnabled && seededStartupEqualities != 0) {
    std::fprintf(
        stderr,
        "SEC diag: bootstrap dependency seeded_startup_equalities=%zu\n",
        seededStartupEqualities);
    std::fflush(stderr);
  }
  for (size_t step = 0; step < cycles; ++step) {
    std::vector<char> nextProven(candidateStates.names.size(), false);
    std::vector<std::optional<bool>> nextProvenConstants(
        candidateStates.names.size());
    std::pmr::monotonic_buffer_resource memoResource0;
    std::pmr::monotonic_buffer_resource memoResource1;
    std::pmr::unordered_map<BoolExpr*, ResetStepEvalSummary> memo0{&memoResource0};
    std::pmr::unordered_map<BoolExpr*, ResetStepEvalSummary> memo1{&memoResource1};
    memo0.reserve(candidateStates.names.size() * 2);
    memo1.reserve(candidateStates.names.size() * 2);
    for (size_t i = 0; i < candidateStates.names.size(); ++i) {
      const auto nextIt0 =
          model0.nextStateExprByStateKey.find(candidateStates.keys0[i]);
      const auto nextIt1 =
          model1.nextStateExprByStateKey.find(candidateStates.keys1[i]);
      if (nextIt0 == model0.nextStateExprByStateKey.end() ||
          nextIt1 == model1.nextStateExprByStateKey.end()) {
        continue;
      }
      const auto eval0 = evaluateResetStepExpr(
          nextIt0->second,
          resetAssignments0,
          statePairIndexByVar0,
          proven,
          provenConstants,
          memo0);
      const auto eval1 = evaluateResetStepExpr(
          nextIt1->second,
          resetAssignments1,
          statePairIndexByVar1,
          proven,
          provenConstants,
          memo1);
      if (!eval0.valid || !eval1.valid) {
        continue;
      }
      if (eval0.constant.has_value() || eval1.constant.has_value()) {
        nextProven[i] =
            eval0.constant.has_value() && eval1.constant.has_value() &&
            *eval0.constant == *eval1.constant;
        if (nextProven[i]) {
          nextProvenConstants[i] = *eval0.constant;
        }
        continue;
      }
      nextProven[i] = eval0.proven && eval1.proven;
    }
    proven = std::move(nextProven);
    provenConstants = std::move(nextProvenConstants);
    if (secDiagEnabled) {
      std::fprintf(
          stderr,
          "SEC diag: bootstrap dependency step %zu equalities=%zu constants=%zu\n",
          step + 1,
          static_cast<size_t>(std::count(proven.begin(), proven.end(), true)),
          static_cast<size_t>(std::count_if(
              provenConstants.begin(),
              provenConstants.end(),
              [](const std::optional<bool>& value) {
                return value.has_value();
              })));
      std::fflush(stderr);
    }
  }

  AlignedSignals result;
  for (size_t i = 0; i < candidateStates.names.size(); ++i) {
    if (provenConstants[i].has_value()) {
      if (bootstrapValues0 != nullptr) {
        (*bootstrapValues0)[candidateStates.keys0[i]] = *provenConstants[i];
      }
      if (bootstrapValues1 != nullptr) {
        (*bootstrapValues1)[candidateStates.keys1[i]] = *provenConstants[i];
      }
    }
    if (!proven[i]) {
      continue;
    }
    result.names.push_back(candidateStates.names[i]);
    result.keys0.push_back(candidateStates.keys0[i]);
    result.keys1.push_back(candidateStates.keys1[i]);
  }
  return result;
}

AlignedSignals filterStateEqualitiesByInitialValue(
    const SequentialDesignModel& model0,
    const SequentialDesignModel& model1,
    const AlignedSignals& candidateStates) {
  AlignedSignals anchoredStates;
  for (size_t i = 0; i < candidateStates.names.size(); ++i) {
    const auto initial0 = model0.initialStateValueByKey.find(candidateStates.keys0[i]);
    const auto initial1 = model1.initialStateValueByKey.find(candidateStates.keys1[i]);
    if (initial0 == model0.initialStateValueByKey.end() ||
        initial1 == model1.initialStateValueByKey.end() ||
        initial0->second != initial1->second) {
      continue;
    }

    anchoredStates.names.push_back(candidateStates.names[i]);
    anchoredStates.keys0.push_back(candidateStates.keys0[i]);
    anchoredStates.keys1.push_back(candidateStates.keys1[i]);
  }
  return anchoredStates;
}

AlignedSignals filterStateEqualitiesByInitialCompatibility(
    const SequentialDesignModel& model0,
    const SequentialDesignModel& model1,
    const AlignedSignals& candidateStates) {
  AlignedSignals compatibleStates;
  for (size_t i = 0; i < candidateStates.names.size(); ++i) {
    if (haveConflictingInitialValues(
            model0, candidateStates.keys0[i], model1, candidateStates.keys1[i])) {
      continue;
    }

    compatibleStates.names.push_back(candidateStates.names[i]);
    compatibleStates.keys0.push_back(candidateStates.keys0[i]);
    compatibleStates.keys1.push_back(candidateStates.keys1[i]);
  }
  return compatibleStates;
}

size_t defaultResetBootstrapCycles(bool hasResetBootstrap, bool hasCompleteInitialState) {
  return (hasResetBootstrap && !hasCompleteInitialState) ? 3u : 0u;
}

std::optional<bool> evaluateConstantUnderAssignments(
    BoolExpr* expr,
    const std::unordered_map<size_t, bool>& assignments,
    ConstantEvalMemo& memo) {
  if (expr == nullptr) {
    return std::nullopt;
  }
  if (const auto it = memo.find(expr); it != memo.end()) {
    return it->second;
  }

  struct EvalFrame {
    BoolExpr* node = nullptr;
    uint8_t stage = 0;
  };

  auto childValue = [&](BoolExpr* child) -> std::optional<bool> {
    // LCOV_EXCL_START
    if (child == nullptr) {
      return std::nullopt;
    }
    // LCOV_EXCL_STOP
    if (const auto it = memo.find(child); it != memo.end()) {
      return it->second;
    }
    return std::nullopt;  // LCOV_EXCL_LINE
  };

  // Reset bootstrap evaluates hundreds of thousands of hash-consed next-state
  // DAG roots on large ASICs.  Keep the recursive short-circuit semantics, but
  // use an explicit stack so shared cones are visited once without deep call
  // stacks before the real proof engine starts.
  std::vector<EvalFrame> stack{{expr, 0}};
  while (!stack.empty()) {
    EvalFrame& frame = stack.back();
    BoolExpr* node = frame.node;
    // LCOV_EXCL_START
    if (node == nullptr || memo.find(node) != memo.end()) {
      stack.pop_back();
      continue;
    }
    // LCOV_EXCL_STOP

    switch (node->getOp()) {
      case Op::VAR: {
        std::optional<bool> value;
        if (node->getId() < 2) {
          value = node->getId() == 1;
        } else if (const auto it = assignments.find(node->getId());
                   it != assignments.end()) {
          value = it->second;
        }
        memo.emplace(node, value);
        stack.pop_back();
        break;
      }
      case Op::NOT:
        if (frame.stage == 0) {
          frame.stage = 1;
          if (node->getLeft() != nullptr &&
              memo.find(node->getLeft()) == memo.end()) {
            stack.push_back({node->getLeft(), 0});
          }
          break;
        }
        if (const auto operand = childValue(node->getLeft());
            operand.has_value()) {
          memo.emplace(node, !*operand);
        } else {
          memo.emplace(node, std::nullopt);
        }
        stack.pop_back();
        break;
      case Op::AND:
        if (frame.stage == 0) {
          frame.stage = 1;
          if (node->getLeft() != nullptr &&
              memo.find(node->getLeft()) == memo.end()) {
            stack.push_back({node->getLeft(), 0});
          }
          break;
        }
        if (frame.stage == 1) {
          const auto lhs = childValue(node->getLeft());
          if (lhs.has_value() && !*lhs) {
            memo.emplace(node, false);
            stack.pop_back();
            break;
          }
          frame.stage = 2;
          if (node->getRight() != nullptr &&
              memo.find(node->getRight()) == memo.end()) {
            stack.push_back({node->getRight(), 0});
          }
          break;
        }
        {
          const auto lhs = childValue(node->getLeft());
          const auto rhs = childValue(node->getRight());
          if (rhs.has_value() && !*rhs) {
            memo.emplace(node, false);
          } else if (lhs.has_value() && rhs.has_value()) {
            memo.emplace(node, *lhs && *rhs);
          } else {
            memo.emplace(node, std::nullopt);
          }
          stack.pop_back();
        }
        break;
      case Op::OR:
        if (frame.stage == 0) {
          frame.stage = 1;
          if (node->getLeft() != nullptr &&
              memo.find(node->getLeft()) == memo.end()) {
            stack.push_back({node->getLeft(), 0});
          }
          break;
        }
        if (frame.stage == 1) {
          const auto lhs = childValue(node->getLeft());
          if (lhs.has_value() && *lhs) {
            memo.emplace(node, true);
            stack.pop_back();
            break;
          }
          frame.stage = 2;
          if (node->getRight() != nullptr &&
              memo.find(node->getRight()) == memo.end()) {
            stack.push_back({node->getRight(), 0});
          }
          break;
        }
        {
          const auto lhs = childValue(node->getLeft());
          const auto rhs = childValue(node->getRight());
          if (rhs.has_value() && *rhs) {
            memo.emplace(node, true);
          } else if (lhs.has_value() && rhs.has_value()) {
            memo.emplace(node, *lhs || *rhs);
          } else {
            memo.emplace(node, std::nullopt);
          }
          stack.pop_back();
        }
        break;
      case Op::XOR:
        if (frame.stage == 0) {
          frame.stage = 1;
          if (node->getLeft() != nullptr &&
              memo.find(node->getLeft()) == memo.end()) {
            stack.push_back({node->getLeft(), 0});
          }
          break;
        }
        if (frame.stage == 1) {
          frame.stage = 2;
          if (node->getRight() != nullptr &&
              memo.find(node->getRight()) == memo.end()) {
            stack.push_back({node->getRight(), 0});
          }
          break;
        }
        {
          const auto lhs = childValue(node->getLeft());
          const auto rhs = childValue(node->getRight());
          if (lhs.has_value() && rhs.has_value()) {
            memo.emplace(node, *lhs != *rhs);
          } else {
            memo.emplace(node, std::nullopt);
          }
          stack.pop_back();
        }
        break;
      case Op::NONE:
      default:
        memo.emplace(node, std::nullopt);
        stack.pop_back();
        break;
    }
  }

  return memo.at(expr);
}

std::unordered_map<SignalKey, bool, SignalKeyHash> deriveResetBootstrapStateValues(
    const SequentialDesignModel& model,
    size_t cycles) {
  // This is a small symbolic reset simulation. We keep only states whose value
  // becomes constant under the asserted-reset environment.
  const auto resetAssignments = collectResetAssignments(model);
  if (resetAssignments.empty() || cycles == 0) {
    return {};
  }

  std::unordered_map<SignalKey, bool, SignalKeyHash> knownStates =
      model.initialStateValueByKey;
  for (size_t step = 0; step < cycles; ++step) {
    std::unordered_map<size_t, bool> assignments = resetAssignments;
    for (const auto& [key, value] : knownStates) {
      const auto varIt = model.inputVarByKey.find(key);
      if (varIt != model.inputVarByKey.end()) {
        assignments.emplace(varIt->second, value);
      }
    }

    std::unordered_map<SignalKey, bool, SignalKeyHash> nextKnownStates;
    // The reset-value sweep touches large shared transition DAGs and then
    // discards the memo at the end of the bootstrap step.  A monotonic arena
    // avoids per-node malloc/free churn in this pre-proof pass.
    std::pmr::monotonic_buffer_resource memoResource;
    ConstantEvalMemo memo{&memoResource};
    memo.reserve(std::min<size_t>(model.stateBits.size() * 4, 1'000'000));
    for (const auto& key : model.stateBits) {
      const auto value = evaluateConstantUnderAssignments(
          model.nextStateExprByStateKey.at(key), assignments, memo);
      if (value.has_value()) {
        nextKnownStates.emplace(key, *value);
      }
    }
    knownStates = std::move(nextKnownStates);
  }

  return knownStates;
}

std::unordered_map<SignalKey, bool, SignalKeyHash>
deriveResetBootstrapStateValuesForKeys(
    const SequentialDesignModel& model,
    const std::vector<SignalKey>& rootKeys,
    size_t cycles) {
  const auto resetAssignments = collectResetAssignments(model);
  if (resetAssignments.empty() || cycles == 0 || rootKeys.empty()) {
    return {};
  }

  const auto relevantKeys =
      collectResetBootstrapRelevantStateKeys(model, rootKeys, cycles);
  std::unordered_map<SignalKey, bool, SignalKeyHash> knownStates =
      model.initialStateValueByKey;
  for (size_t step = 0; step < cycles; ++step) {
    std::unordered_map<size_t, bool> assignments = resetAssignments;
    for (const auto& [key, value] : knownStates) {
      const auto varIt = model.inputVarByKey.find(key);
      if (varIt != model.inputVarByKey.end()) {
        assignments.emplace(varIt->second, value);
      }
    }

    std::unordered_map<SignalKey, bool, SignalKeyHash> nextKnownStates;
    nextKnownStates.reserve(relevantKeys.size());
    std::pmr::monotonic_buffer_resource memoResource;
    ConstantEvalMemo memo{&memoResource};
    memo.reserve(std::min<size_t>(relevantKeys.size() * 16, 1'000'000));
    for (const auto& key : relevantKeys) {
      const auto nextIt = model.nextStateExprByStateKey.find(key);
      if (nextIt == model.nextStateExprByStateKey.end()) {
        continue;  // LCOV_EXCL_LINE
      }
      const auto value =
          evaluateConstantUnderAssignments(nextIt->second, assignments, memo);
      if (value.has_value()) {
        nextKnownStates.emplace(key, *value);
      }
    }
    knownStates = std::move(nextKnownStates);
  }

  return knownStates;
}

SpecializedNextMap specializeNextStatesForReset(
    const SequentialDesignModel& model,
    const std::unordered_map<size_t, bool>& resetAssignments,
    const std::vector<SignalKey>& relevantKeys) {
  SpecializedNextMap specialized;
  specialized.reserve(relevantKeys.size());
  std::unordered_map<BoolExpr*, BoolExpr*> memo;
  for (const auto& key : relevantKeys) {
    const auto nextIt = model.nextStateExprByStateKey.find(key);
    if (nextIt == model.nextStateExprByStateKey.end()) {
      specialized.emplace(key, nullptr);
      continue;
    }
    // Always mine reset-specialized structure here.  The bounded SAT-recovery
    // pass below is the expensive part and already has support/node guards;
    // pre-skipping this structural substitution loses cheap reset equalities on
    // wide ASIC cones and regresses KI/IMC/PDR into deep bounded searches.
    try {
      specialized.emplace(
          key,
          substituteBoolExprVariables(nextIt->second, resetAssignments, memo));
    } catch (const std::runtime_error&) {
      specialized.emplace(key, nullptr);
    }
  }
  return specialized;
}

AlignedSignals deriveResetBootstrapStateEqualities(
    const SequentialDesignModel& model0,
    const SequentialDesignModel& model1,
    const AlignedSignals& alignedInputs,
    const AlignedSignals& candidateStates,
    const AlignedSignals& startupEqualities,
    size_t cycles,
    KEPLER_FORMAL::Config::SolverType solverType,
    bool secDiagEnabled,
    bool seedCandidateEqualitiesAtInitialState = true) {
  // Push candidate state equalities through the reset-specialized next-state
  // logic. A pair survives only if both sides either collapse to the same
  // constant or stay structurally equivalent after each bootstrap step.
  if (cycles == 0 || candidateStates.names.empty()) {
    return filterStateEqualitiesByInitialValue(model0, model1, candidateStates);
  }

  const auto resetAssignments0 = collectResetAssignments(model0);
  const auto resetAssignments1 = collectResetAssignments(model1);
  if (resetAssignments0.empty() || resetAssignments1.empty()) {
    return filterStateEqualitiesByInitialValue(model0, model1, candidateStates);  // LCOV_EXCL_LINE
  }

  const auto relevantKeys0 =
      collectResetBootstrapRelevantStateKeys(model0, candidateStates.keys0, cycles);
  const auto relevantKeys1 =
      collectResetBootstrapRelevantStateKeys(model1, candidateStates.keys1, cycles);
  if (secDiagEnabled) {
    std::fprintf(
        stderr,
        "SEC diag: bootstrap candidate states=%zu relevant0=%zu relevant1=%zu "
        "cycles=%zu\n",
        candidateStates.names.size(),
        relevantKeys0.size(),
        relevantKeys1.size(),
        cycles);
    std::fflush(stderr);
  }

  const auto resetSpecializedNext0 =
      specializeNextStatesForReset(model0, resetAssignments0, relevantKeys0);
  const auto resetSpecializedNext1 =
      specializeNextStatesForReset(model1, resetAssignments1, relevantKeys1);
  const SpecializedNextMap& resetNext0 = resetSpecializedNext0;
  const SpecializedNextMap& resetNext1 = resetSpecializedNext1;

  AlignedSignals currentEqualities =
      seedCandidateEqualitiesAtInitialState
          ? mergeStartupCorrespondence(
                filterStateEqualitiesByInitialValue(model0, model1, candidateStates),
                startupEqualities)
          : startupEqualities;
  std::unordered_map<SignalKey, bool, SignalKeyHash> currentKnownValues0 =
      model0.initialStateValueByKey;
  std::unordered_map<SignalKey, bool, SignalKeyHash> currentKnownValues1 =
      model1.initialStateValueByKey;

  for (size_t step = 0; step < cycles; ++step) {
    std::unordered_map<size_t, bool> stateAssignments0;
    std::unordered_map<size_t, bool> stateAssignments1;
    stateAssignments0.reserve(currentKnownValues0.size());
    stateAssignments1.reserve(currentKnownValues1.size());
    for (const auto& [key, value] : currentKnownValues0) {
      if (const auto it = model0.inputVarByKey.find(key); it != model0.inputVarByKey.end()) {
        stateAssignments0.emplace(it->second, value);
      }
    }
    for (const auto& [key, value] : currentKnownValues1) {
      if (const auto it = model1.inputVarByKey.find(key); it != model1.inputVarByKey.end()) {
        stateAssignments1.emplace(it->second, value);
      }
    }

    std::unordered_map<SignalKey, BoolExpr*, SignalKeyHash> specializedNext0;
    std::unordered_map<SignalKey, BoolExpr*, SignalKeyHash> specializedNext1;
    specializedNext0.reserve(relevantKeys0.size());
    specializedNext1.reserve(relevantKeys1.size());
    std::unordered_map<BoolExpr*, BoolExpr*> stateSubMemo0;
    std::unordered_map<BoolExpr*, BoolExpr*> stateSubMemo1;
    for (const auto& key : relevantKeys0) {
      try {
        specializedNext0.emplace(
            key,
            substituteBoolExprVariables(
                resetNext0.at(key), stateAssignments0, stateSubMemo0));
      } catch (const std::runtime_error&) {  // LCOV_EXCL_LINE
        specializedNext0.emplace(key, nullptr);  // LCOV_EXCL_LINE
      }  // LCOV_EXCL_LINE
    }
    for (const auto& key : relevantKeys1) {
      try {
        specializedNext1.emplace(
            key,
            substituteBoolExprVariables(
                resetNext1.at(key), stateAssignments1, stateSubMemo1));
      } catch (const std::runtime_error&) {  // LCOV_EXCL_LINE
        specializedNext1.emplace(key, nullptr);  // LCOV_EXCL_LINE
      }  // LCOV_EXCL_LINE
    }

    std::unordered_map<SignalKey, bool, SignalKeyHash> nextKnownValues0;
    std::unordered_map<SignalKey, bool, SignalKeyHash> nextKnownValues1;
    nextKnownValues0.reserve(relevantKeys0.size());
    nextKnownValues1.reserve(relevantKeys1.size());
    for (const auto& key : relevantKeys0) {
      if (isConstBoolExpr(specializedNext0.at(key), false)) {
        nextKnownValues0.emplace(key, false);
      } else if (isConstBoolExpr(specializedNext0.at(key), true)) {
        nextKnownValues0.emplace(key, true);
      }
    }
    for (const auto& key : relevantKeys1) {
      if (isConstBoolExpr(specializedNext1.at(key), false)) {
        nextKnownValues1.emplace(key, false);
      } else if (isConstBoolExpr(specializedNext1.at(key), true)) {
        nextKnownValues1.emplace(key, true);
      }
    }

    bool abstractMapsBuilt = false;
    bool abstractMapsAvailable = true;
    LocalToAbstractVarMap abstractMap0;
    LocalToAbstractVarMap abstractMap1;
    std::pmr::monotonic_buffer_resource abstractEquivalenceResource;
    AbstractExprPairMemo abstractEquivalenceMemo{&abstractEquivalenceResource};
    size_t satRecoveredEqualities = 0;
    auto ensureAbstractMaps = [&]() {
      if (abstractMapsBuilt) {
        return abstractMapsAvailable;
      }
      abstractMapsBuilt = true;
      const auto mappedCurrentEqualities =
          keepEqualitiesWithStateVariables(model0, model1, currentEqualities);
      try {
        auto maps = buildAbstractTransitionMaps(
            model0, model1, alignedInputs, mappedCurrentEqualities);
        abstractMap0 = std::move(maps.first);
        abstractMap1 = std::move(maps.second);
      } catch (const std::out_of_range&) {
        abstractMapsAvailable = false;
      }
      return abstractMapsAvailable;
    };

    struct PendingSatRecovery {
      size_t candidateIndex = 0;
      BoolExpr* expr0 = nullptr;
      BoolExpr* expr1 = nullptr;
      size_t supportSize = 0;
    };

    // SAT recovery is a useful precision boost for small reset/bootstrap
    // frontiers, but on memory-heavy ASICs it can otherwise become thousands of
    // independent SAT calls before the real proof starts. Mark cheap/structural
    // equalities immediately, then spend the SAT budget only on small ambiguous
    // cases and let the top-level SEC engine handle the large cones in one COI.
    std::vector<char> equalAfterStep(candidateStates.names.size(), false);
    std::vector<PendingSatRecovery> pendingSatRecovery;
    pendingSatRecovery.reserve(
        std::min(candidateStates.names.size(), kBootstrapSatRecoveryCandidateBudget));
    size_t satSkippedEqualities = 0;
    for (size_t i = 0; i < candidateStates.names.size(); ++i) {
      const auto& key0 = candidateStates.keys0[i];
      const auto& key1 = candidateStates.keys1[i];

      const auto known0 = nextKnownValues0.find(key0);
      const auto known1 = nextKnownValues1.find(key1);
      if (known0 != nextKnownValues0.end() && known1 != nextKnownValues1.end() &&
          known0->second == known1->second) {
        equalAfterStep[i] = true;
      } else if (specializedNext0.at(key0) == nullptr ||
                 specializedNext1.at(key1) == nullptr) {
        equalAfterStep[i] = false;
      } else if (!ensureAbstractMaps()) {
        equalAfterStep[i] = false;
      } else {
        // The abstract maps are fixed for this bootstrap step.  Keep one
        // structural-equivalence memo across all candidate states so shared
        // sub-DAGs in memory-heavy designs are compared once instead of once
        // per state bit.
        equalAfterStep[i] = areEquivalentUnderAbstractMaps(
            specializedNext0.at(key0),
            specializedNext1.at(key1),
            abstractMap0,
            abstractMap1,
            abstractEquivalenceMemo);
        if (!equalAfterStep[i]) {
          // Gate SAT recovery by the number of ambiguous cheap cones, not by
          // total state count.  ASIC cases can have thousands of state bits but
          // only a handful that need SAT to prove a reordered equivalent cone;
          // dropping those weakens KI/IMC enough to reintroduce deep searches.
          if (const auto supportSize = bootstrapSatRecoverySupportSize(
                  specializedNext0.at(key0), specializedNext1.at(key1));
              supportSize.has_value()) {
            pendingSatRecovery.push_back(
                {i, specializedNext0.at(key0), specializedNext1.at(key1),
                 *supportSize});
          } else {
            ++satSkippedEqualities;
          }
        }
      }
    }

    if (pendingSatRecovery.size() > kBootstrapSatRecoveryCandidateBudget) {
      std::sort(
          pendingSatRecovery.begin(),
          pendingSatRecovery.end(),
          [](const PendingSatRecovery& lhs, const PendingSatRecovery& rhs) {
            if (lhs.supportSize != rhs.supportSize) {
              return lhs.supportSize < rhs.supportSize;
            }
            return lhs.candidateIndex < rhs.candidateIndex;
          });
      satSkippedEqualities =
          pendingSatRecovery.size() - kBootstrapSatRecoveryCandidateBudget;
      pendingSatRecovery.resize(kBootstrapSatRecoveryCandidateBudget);
    }
    for (const auto& pending : pendingSatRecovery) {
      if (areSatEquivalentUnderAbstractMaps(
              pending.expr0,
              pending.expr1,
              abstractMap0,
              abstractMap1,
              solverType)) {
        equalAfterStep[pending.candidateIndex] = true;
        ++satRecoveredEqualities;
      }
    }

    AlignedSignals nextEqualities;
    for (size_t i = 0; i < candidateStates.names.size(); ++i) {
      if (!equalAfterStep[i]) {
        continue;
      }

      nextEqualities.names.push_back(candidateStates.names[i]);
      nextEqualities.keys0.push_back(candidateStates.keys0[i]);
      nextEqualities.keys1.push_back(candidateStates.keys1[i]);
    }

    currentEqualities = std::move(nextEqualities);
    currentKnownValues0 = std::move(nextKnownValues0);
    currentKnownValues1 = std::move(nextKnownValues1);
    if (secDiagEnabled) {
      fprintf(
          stderr,
          "SEC diag: bootstrap step %zu equalities=%zu known0=%zu known1=%zu\n",
          step + 1,
          currentEqualities.names.size(),
          currentKnownValues0.size(),
          currentKnownValues1.size());
      if (satRecoveredEqualities != 0) {
        fprintf(
            stderr,
            "SEC diag: bootstrap step %zu sat_recovered_equalities=%zu\n",
            step + 1,
            satRecoveredEqualities);
      }
      if (satSkippedEqualities != 0) {
        fprintf(
            stderr,
            "SEC diag: bootstrap step %zu sat_recovery_skipped=%zu\n",
            step + 1,
            satSkippedEqualities);
      }
      fflush(stderr);
    }
  }

  return currentEqualities;
}

bool hasCompleteInitialState(const SequentialDesignModel& model0,
                             const SequentialDesignModel& model1) {
  return model0.initialStateValueByKey.size() == model0.stateBits.size() &&
         model1.initialStateValueByKey.size() == model1.stateBits.size();
}

bool hasExplicitInitialState(const SequentialDesignModel& model0,
                             const SequentialDesignModel& model1) {
  return !model0.initialStateValueByKey.empty() ||
         !model1.initialStateValueByKey.empty();
}

}  // namespace

ReachableStateInvariant buildReachableStateInvariant(
    const SequentialDesignModel& model0,
    const SequentialDesignModel& model1,
    const AlignedSignals& alignedInputs,
    const AlignedSignals& inductiveStateEqualities,
    bool deriveResetBootstrapStrengthening,
    bool secDiagEnabled,
    KEPLER_FORMAL::Config::SolverType solverType,
    bool deriveResetBootstrapEqualities,
    const AlignedSignals& resetBootstrapCandidateEqualities) {
  ReachableStateInvariant invariant;
  // First decide which startup model we have: explicit init, reset bootstrap,
  // both, or neither. That determines how strong the frame-0 correspondence
  // may safely be.
  const bool hasResetBootstrap = !collectResetAssignments(model0).empty() &&
      !collectResetAssignments(model1).empty();

  invariant.bootstrapCycles = defaultResetBootstrapCycles(
      hasResetBootstrap, hasCompleteInitialState(model0, model1));
  const auto structuralStartupCorrespondence = filterStateEqualitiesByInitialCompatibility(
      model0, model1, inductiveStateEqualities);
  invariant.initialStateCorrespondence = structuralStartupCorrespondence;

  if (hasResetBootstrap) {
    const bool hasResetBootstrapCandidates =
        !resetBootstrapCandidateEqualities.names.empty() &&
        invariant.bootstrapCycles != 0;
    if (!resetBootstrapCandidateEqualities.names.empty()) {
      // Reset bootstrap starts from an arbitrary pre-reset state.  Additional
      // startup correspondence may only come from structurally checked COI
      // candidates rooted at aligned top outputs, never from internal names.
      // Base-case COI indexes this relation before encoding it, so large ASIC
      // cases still pull in only the startup pairs needed by the checked top
      // output cone.
      invariant.initialStateCorrespondence = mergeStartupCorrespondence(
          invariant.initialStateCorrespondence,
          resetBootstrapCandidateEqualities);
    }
    auto deriveCandidateBootstrapFacts = [&]() {
      if (!hasResetBootstrapCandidates) {
        return;
      }
      if (resetBootstrapCandidateEqualities.names.size() <=
          kSelectiveBootstrapValueCandidateBudget) {
        invariant.bootstrapValues0 = deriveResetBootstrapStateValuesForKeys(
            model0,
            resetBootstrapCandidateEqualities.keys0,
            invariant.bootstrapCycles);
        invariant.bootstrapValues1 = deriveResetBootstrapStateValuesForKeys(
            model1,
            resetBootstrapCandidateEqualities.keys1,
            invariant.bootstrapCycles);
      }
      invariant.bootstrapOnlyStateEqualities =
          deriveResetBootstrapStateEqualitiesByDependency(
              model0,
              model1,
              resetBootstrapCandidateEqualities,
              invariant.initialStateCorrespondence,
              invariant.bootstrapCycles,
              secDiagEnabled,
              &invariant.bootstrapValues0,
              &invariant.bootstrapValues1);
    };

    // Walk the reset window to find which candidate equalities are true at the
    // first checked frame. The seed includes startup equalities, but a pair is
    // promoted only if reset-specialized transition logic proves it survives.
    if (!deriveResetBootstrapEqualities) {
      // PDR validates the concrete reset frontier separately, so it does not
      // need the expensive reset-specialized sweep that mines additional
      // post-reset equality lemmas. It still receives the concrete bootstrap
      // state values below, which are what prevent artificial resetless
      // startup traces; PDR can then learn only the local equalities it needs.
      invariant.anchoredStateEqualities = structuralStartupCorrespondence;
      // The reset unroll can include state that is intentionally not reset.
      // For PDR we may relate that pre-reset state only through a checked
      // structural COI relation rooted at top outputs, never by internal names.
      deriveCandidateBootstrapFacts();
    } else if (invariant.bootstrapCycles == 0) {
      invariant.anchoredStateEqualities = structuralStartupCorrespondence;
    } else {
      const auto bootstrapCandidateStates = mergeStartupCorrespondence(
          inductiveStateEqualities,
          resetBootstrapCandidateEqualities);
      invariant.anchoredStateEqualities = deriveResetBootstrapStateEqualities(
          model0,
          model1,
          alignedInputs,
          bootstrapCandidateStates,
          invariant.initialStateCorrespondence,
          invariant.bootstrapCycles,
          solverType,
          secDiagEnabled);
      deriveCandidateBootstrapFacts();
    }

    if (deriveResetBootstrapStrengthening) {
      invariant.bootstrapValues0 =
          deriveResetBootstrapStateValues(model0, invariant.bootstrapCycles);
      invariant.bootstrapValues1 =
          deriveResetBootstrapStateValues(model1, invariant.bootstrapCycles);
    }
  } else if (hasExplicitInitialState(model0, model1)) {
    // Without reset, we can only anchor the state pairs whose explicit init
    // values agree on both sides.
    invariant.anchoredStateEqualities = filterStateEqualitiesByInitialValue(
        model0, model1, inductiveStateEqualities);
  } else {
    // Resetless, init-less SEC may only start from state correspondences that
    // were inferred structurally. Same-named flops are intentionally not used
    // here: without reset or explicit init, a name is not a proof that the two
    // state variables start equal.
    invariant.anchoredStateEqualities = structuralStartupCorrespondence;
  }

  return invariant;
}

}  // namespace KEPLER_FORMAL::SEC
