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
#include <string_view>
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

constexpr size_t kBootstrapSatRecoveryCandidateBudget = 1024;
constexpr size_t kBootstrapSatRecoverySupportBudget = 4096;

using ConstantEvalMemo =
    std::pmr::unordered_map<BoolExpr*, std::optional<bool>>;

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

bool isWithinBootstrapSatRecoverySupportBudget(BoolExpr* expr0, BoolExpr* expr1) {
  std::set<size_t> support = expr0->getSupportVars();
  const auto support1 = expr1->getSupportVars();
  support.insert(support1.begin(), support1.end());
  return support.size() <= kBootstrapSatRecoverySupportBudget;
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

std::vector<std::string> resetNameCandidates(const std::string& displayName) {
  // Reset ports frequently carry RTL direction suffixes (`reset_i`, `rst_ni`).
  // Strip only those common input suffixes before classification so a real
  // reset is bootstrapped, without broadening the matcher to arbitrary names.
  const std::string normalized = normalizeSignalBaseName(displayName);
  std::vector<std::string> candidates = {normalized};
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
    if (candidate == "RESET" || candidate == "RST") {
      return true;
    }
    if (candidate == "RESET_N" || candidate == "RESETN" ||
        candidate == "RST_N" || candidate == "RSTN") {
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

struct StateNameGroup {
  size_t firstIndex = std::numeric_limits<size_t>::max();
  size_t count = 0;
};

using StateNameGroups = std::unordered_map<std::string_view, StateNameGroup>;

StateNameGroups groupStatesByDisplayName(const SequentialDesignModel& model) {
  StateNameGroups statesByName;
  statesByName.reserve(model.stateBits.size());
  for (const auto& key : model.stateBits) {
    const auto displayIt = model.displayNameByKey.find(key);
    if (displayIt == model.displayNameByKey.end()) {
      continue;
    }
    // Keep string_views into the immutable model display-name table. This
    // preserves content-based matching while avoiding per-state string and
    // vector allocations on large reset/bootstrap candidate sets.
    auto [groupIt, inserted] =
        statesByName.try_emplace(std::string_view(displayIt->second));
    if (inserted) {
      groupIt->second.firstIndex = &key - model.stateBits.data();
    }
    ++groupIt->second.count;
  }
  return statesByName;
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

AlignedSignals alignSameNamedStatesByDisplayName(
    const SequentialDesignModel& model0,
    const SequentialDesignModel& model1,
    const StateNameGroups& statesByName0,
    const StateNameGroups& statesByName1,
    bool requireInitialCompatibility) {
  // Exact state display-name matches are useful SEC candidates after
  // optimization keeps register names but changes surrounding logic. Startup
  // assumptions must respect explicit init values; bootstrap candidates may be
  // reset-derived later even if explicit init values differ.
  AlignedSignals sameNamedStates;
  const size_t maxPairs = std::min(model0.stateBits.size(), model1.stateBits.size());
  sameNamedStates.names.reserve(maxPairs);
  sameNamedStates.keys0.reserve(maxPairs);
  sameNamedStates.keys1.reserve(maxPairs);
  for (const auto& key0 : model0.stateBits) {
    const auto displayIt = model0.displayNameByKey.find(key0);
    if (displayIt == model0.displayNameByKey.end()) {
      continue;
    }

    const auto displayName = std::string_view(displayIt->second);
    const auto countIt0 = statesByName0.find(displayName);
    const auto countIt1 = statesByName1.find(displayName);
    if (countIt0 == statesByName0.end() || countIt0->second.count != 1 ||
        countIt1 == statesByName1.end() || countIt1->second.count != 1) {
      continue;
    }

    if (countIt1->second.firstIndex >= model1.stateBits.size()) {
      continue;  // LCOV_EXCL_LINE
    }

    const auto& key1 = model1.stateBits[countIt1->second.firstIndex];
    if (requireInitialCompatibility &&
        haveConflictingInitialValues(model0, key0, model1, key1)) {
      continue;
    }

    sameNamedStates.names.push_back(displayIt->second);
    sameNamedStates.keys0.push_back(key0);
    sameNamedStates.keys1.push_back(key1);
  }
  return sameNamedStates;
}

AlignedSignals alignSameNamedStatesForStartup(
    const SequentialDesignModel& model0,
    const SequentialDesignModel& model1,
    const StateNameGroups& statesByName0,
    const StateNameGroups& statesByName1) {
  // Startup equalities are frame-0 assumptions, so they are allowed only when
  // explicit init information does not contradict the name-based pairing.
  return alignSameNamedStatesByDisplayName(
      model0,
      model1,
      statesByName0,
      statesByName1,
      /*requireInitialCompatibility=*/true);
}

AlignedSignals alignSameNamedStatesForBootstrapCandidates(
    const SequentialDesignModel& model0,
    const SequentialDesignModel& model1,
    const StateNameGroups& statesByName0,
    const StateNameGroups& statesByName1) {
  // Reset/bootstrap can later prove a pair equal even if frame-0 explicit init
  // values disagree, so candidate collection itself does not reject those pairs.
  return alignSameNamedStatesByDisplayName(
      model0,
      model1,
      statesByName0,
      statesByName1,
      /*requireInitialCompatibility=*/false);
}

AlignedSignals mergeStartupCorrespondence(
    const AlignedSignals& structuralStates,
    const AlignedSignals& sameNamedStates) {
  AlignedSignals mergedStates;
  std::unordered_set<SignalKey, SignalKeyHash> usedKeys0;
  std::unordered_set<SignalKey, SignalKeyHash> usedKeys1;
  usedKeys0.reserve(structuralStates.keys0.size() + sameNamedStates.keys0.size());
  usedKeys1.reserve(structuralStates.keys1.size() + sameNamedStates.keys1.size());
  mergedStates.names.reserve(structuralStates.names.size() + sameNamedStates.names.size());
  mergedStates.keys0.reserve(structuralStates.keys0.size() + sameNamedStates.keys0.size());
  mergedStates.keys1.reserve(structuralStates.keys1.size() + sameNamedStates.keys1.size());
  for (size_t i = 0; i < structuralStates.names.size(); ++i) {
    appendStatePairIfUnused(
        mergedStates,
        structuralStates.names[i],
        structuralStates.keys0[i],
        structuralStates.keys1[i],
        usedKeys0,
        usedKeys1);
  }
  for (size_t i = 0; i < sameNamedStates.names.size(); ++i) {
    appendStatePairIfUnused(
        mergedStates,
        sameNamedStates.names[i],
        sameNamedStates.keys0[i],
        sameNamedStates.keys1[i],
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

AlignedSignals deriveResetBootstrapStateEqualities(
    const SequentialDesignModel& model0,
    const SequentialDesignModel& model1,
    const AlignedSignals& alignedInputs,
    const AlignedSignals& candidateStates,
    const AlignedSignals& startupEqualities,
    size_t cycles,
    KEPLER_FORMAL::Config::SolverType solverType,
    bool secDiagEnabled) {
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

  auto specializeForReset = [](const SequentialDesignModel& model,
                               const std::unordered_map<size_t, bool>& resetAssignments) {
    std::unordered_map<SignalKey, BoolExpr*, SignalKeyHash> specialized;
    specialized.reserve(model.stateBits.size());
    std::unordered_map<BoolExpr*, BoolExpr*> memo;
    for (const auto& key : model.stateBits) {
      const auto nextIt = model.nextStateExprByStateKey.find(key);
      if (nextIt == model.nextStateExprByStateKey.end()) {
        specialized.emplace(key, nullptr);
        continue;
      }
      try {
        specialized.emplace(
            key,
            substituteBoolExprVariables(nextIt->second, resetAssignments, memo));
      } catch (const std::runtime_error&) {
        specialized.emplace(key, nullptr);
      }
    }
    return specialized;
  };

  const auto resetSpecializedNext0 = specializeForReset(model0, resetAssignments0);
  const auto resetSpecializedNext1 = specializeForReset(model1, resetAssignments1);

  AlignedSignals currentEqualities = mergeStartupCorrespondence(
      filterStateEqualitiesByInitialValue(model0, model1, candidateStates),
      startupEqualities);
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
    specializedNext0.reserve(model0.stateBits.size());
    specializedNext1.reserve(model1.stateBits.size());
    std::unordered_map<BoolExpr*, BoolExpr*> stateSubMemo0;
    std::unordered_map<BoolExpr*, BoolExpr*> stateSubMemo1;
    for (const auto& key : model0.stateBits) {
      try {
        specializedNext0.emplace(
            key,
            substituteBoolExprVariables(
                resetSpecializedNext0.at(key), stateAssignments0, stateSubMemo0));
      } catch (const std::runtime_error&) {  // LCOV_EXCL_LINE
        specializedNext0.emplace(key, nullptr);  // LCOV_EXCL_LINE
      }  // LCOV_EXCL_LINE
    }
    for (const auto& key : model1.stateBits) {
      try {
        specializedNext1.emplace(
            key,
            substituteBoolExprVariables(
                resetSpecializedNext1.at(key), stateAssignments1, stateSubMemo1));
      } catch (const std::runtime_error&) {  // LCOV_EXCL_LINE
        specializedNext1.emplace(key, nullptr);  // LCOV_EXCL_LINE
      }  // LCOV_EXCL_LINE
    }

    std::unordered_map<SignalKey, bool, SignalKeyHash> nextKnownValues0;
    std::unordered_map<SignalKey, bool, SignalKeyHash> nextKnownValues1;
    nextKnownValues0.reserve(model0.stateBits.size());
    nextKnownValues1.reserve(model1.stateBits.size());
    for (const auto& key : model0.stateBits) {
      if (isConstBoolExpr(specializedNext0.at(key), false)) {
        nextKnownValues0.emplace(key, false);
      } else if (isConstBoolExpr(specializedNext0.at(key), true)) {
        nextKnownValues0.emplace(key, true);
      }
    }
    for (const auto& key : model1.stateBits) {
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
          pendingSatRecovery.push_back(
              {i, specializedNext0.at(key0), specializedNext1.at(key1)});
        }
      }
    }

    size_t satSkippedEqualities = 0;
    if (pendingSatRecovery.size() <= kBootstrapSatRecoveryCandidateBudget) {
      for (const auto& pending : pendingSatRecovery) {
        if (!isWithinBootstrapSatRecoverySupportBudget(
                pending.expr0, pending.expr1)) {
          ++satSkippedEqualities;
          continue;
        }
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
    } else {
      satSkippedEqualities = pendingSatRecovery.size();
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
    bool deriveResetBootstrapEqualities) {
  ReachableStateInvariant invariant;
  // First decide which startup model we have: explicit init, reset bootstrap,
  // both, or neither. That determines how strong the frame-0 correspondence
  // may safely be.
  const bool hasResetBootstrap = !collectResetAssignments(model0).empty() &&
      !collectResetAssignments(model1).empty();

  invariant.bootstrapCycles = defaultResetBootstrapCycles(
      hasResetBootstrap, hasCompleteInitialState(model0, model1));
  const auto statesByName0 = groupStatesByDisplayName(model0);
  const auto statesByName1 = groupStatesByDisplayName(model1);
  const auto structuralStartupCorrespondence = filterStateEqualitiesByInitialCompatibility(
      model0, model1, inductiveStateEqualities);
  invariant.initialStateCorrespondence = mergeStartupCorrespondence(
      structuralStartupCorrespondence,
      alignSameNamedStatesForStartup(model0, model1, statesByName0, statesByName1));

  if (hasResetBootstrap) {
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
    } else if (invariant.bootstrapCycles == 0) {
      invariant.anchoredStateEqualities = structuralStartupCorrespondence;
    } else {
      const auto bootstrapCandidateStates = mergeStartupCorrespondence(
          inductiveStateEqualities,
          alignSameNamedStatesForBootstrapCandidates(
              model0, model1, statesByName0, statesByName1));
      invariant.anchoredStateEqualities = deriveResetBootstrapStateEqualities(
          model0,
          model1,
          alignedInputs,
          bootstrapCandidateStates,
          invariant.initialStateCorrespondence,
          invariant.bootstrapCycles,
          solverType,
          secDiagEnabled);
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
    // Resetless, init-less SEC still starts from a relational frame-0
    // correspondence: structurally matched state pairs are assumed equal in the
    // miter's initial state. Those pairs were selected by the transition
    // structural invariant, not by name alone, so they are legitimate
    // strengthening facts for the induction step even when no concrete reset
    // value exists. Promoting them here lets k-induction prove the real
    // transition relation instead of rediscovering thousands of state
    // correspondences through deep output cones.
    invariant.anchoredStateEqualities = structuralStartupCorrespondence;
  }

  return invariant;
}

}  // namespace KEPLER_FORMAL::SEC
