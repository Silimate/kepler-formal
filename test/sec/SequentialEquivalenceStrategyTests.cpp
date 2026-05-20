// Copyright 2024-2026 keplertech.io
// SPDX-License-Identifier: GPL-3.0-only

#include <gtest/gtest.h>

#include <algorithm>
#include <array>
#include <cctype>
#include <cstdlib>
#include <deque>
#include <filesystem>
#include <fstream>
#include <limits>
#include <map>
#include <optional>
#include <set>
#include <sstream>
#include <stdexcept>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "BoolExprCache.h"
#include "DNL.h"
#include "NLDB0.h"
#include "NLName.h"
#include "NLUniverse.h"
#include "SNLDesign.h"
#include "SNLDesignModeling.h"
#include "SNLLibertyConstructor.h"
#include "SNLSVConstructor.h"
#include "SNLPath.h"
#include "SNLBusNet.h"
#include "SNLBusNetBit.h"
#include "SNLBusTerm.h"
#include "SNLBusTermBit.h"
#include "SNLInstance.h"
#include "SNLScalarNet.h"
#include "SNLScalarTerm.h"
#include "common/BoolExprUtils.h"
#include "common/ProofProblemDebug.h"
#include "imc/ExactInterpolantSynthesizer.h"
#include "imc/IMCEngine.h"
#include "kinduction/KInductionEngine.h"
#include "kinduction/OutputBatching.h"
#include "pdr/PDREngine.h"
#include "kinduction/BaseCaseSolver.h"
#include "kinduction/SatEncoding.h"
#include "kinduction/InductionStepSolver.h"
#include "model/SequentialDesignModel.h"
#include "proof/TransitionExprResolver.h"
#include "BuildPrimaryOutputClauses.h"
#include "strategy/ReachableStateInvariant.h"
#include "strategy/SequentialEquivalenceStrategy.h"
#include "strategy/StructuralStateInvariant.h"

using namespace naja::NL;
using namespace KEPLER_FORMAL::SEC;
using KEPLER_FORMAL::BoolExpr;

namespace KEPLER_FORMAL::SEC::detail {

namespace {

struct PendingPinTermForTest {
  naja::DNL::DNLID termID = naja::DNL::DNLID_MAX;
  naja::NL::NLID::Bit bit = 0;
};

struct PendingTransitionForTest {
  naja::DNL::DNLID stateTermID = naja::DNL::DNLID_MAX;
  naja::NL::NLID::Bit stateBit = 0;
  size_t independentStateOutputCount = 0;
  std::unordered_map<std::string, std::vector<PendingPinTermForTest>> pinTermIDs;
};

struct ConeTraceForTest {
  std::vector<std::vector<std::string>> levels;
  std::set<std::string> allTerms;
};

struct ConeDiffReportForTest {
  ConeTraceForTest trace;
  std::string error;
};

struct ScopedDnlContextForTest {
  explicit ScopedDnlContextForTest(naja::NL::SNLDesign* top)
      : universe_(naja::NL::NLUniverse::get()),
        previousTop_(universe_ ? universe_->getTopDesign() : nullptr) {
    if (universe_ == nullptr) {
      throw std::runtime_error("NLUniverse not created for SEC cone tracing");
    }

    naja::DNL::destroy();
    universe_->setTopDesign(top);
    dnl_ = naja::DNL::get();
  }

  ~ScopedDnlContextForTest() {
    naja::DNL::destroy();
    if (universe_ != nullptr && previousTop_ != nullptr) {
      universe_->setTopDesign(previousTop_);
    }
  }

  naja::DNL::DNLFull* dnl() const {
    return dnl_;
  }

 private:
  naja::NL::NLUniverse* universe_ = nullptr;
  naja::NL::SNLDesign* previousTop_ = nullptr;
  naja::DNL::DNLFull* dnl_ = nullptr;
};

std::string formatBoolValueForTest(bool value) {
  return value ? "1" : "0";
}

std::string normalizePinNameForTest(const std::string& name) {
  std::string normalized = name;
  for (char& ch : normalized) {
    ch = static_cast<char>(std::toupper(static_cast<unsigned char>(ch)));
  }
  return normalized;
}

std::string normalizeSignalBaseNameForTest(const std::string& name) {
  std::string base = name;
  const auto bracket = base.find('[');
  if (bracket != std::string::npos) {
    base = base.substr(0, bracket);
  }
  return normalizePinNameForTest(base);
}

std::optional<bool> getResetAssertionValueFromDisplayNameForTest(
    const std::string& displayName);

std::optional<naja::DNL::DNLID> resolvePendingPinTermIDForTest(
    const PendingTransitionForTest& pending,
    const char* pinName) {
  const auto pinIt = pending.pinTermIDs.find(pinName);
  if (pinIt == pending.pinTermIDs.end()) {
    return std::nullopt;
  }

  const auto& candidates = pinIt->second;
  if (candidates.empty()) {
    return std::nullopt;
  }

  if (candidates.size() > 1) {
    for (const auto& candidate : candidates) {
      if (candidate.bit == pending.stateBit) {
        return candidate.termID;
      }
    }
    throw std::runtime_error(
        "Missing bit-matched sequential pin `" + std::string(pinName) + "`");
  }

  const bool isDataPin = std::string(pinName) == "D";
  if (isDataPin && pending.independentStateOutputCount > 1) {
    throw std::runtime_error(
        "Shared scalar D input cannot define multiple independent state outputs");
  }

  return candidates.front().termID;
}

BoolExpr* getRequiredOutputExprForTest(
    const PendingTransitionForTest& pending,
    const char* pinName,
    const std::unordered_map<naja::DNL::DNLID, BoolExpr*>& outputExprByTerm) {
  const auto resolvedTermID = resolvePendingPinTermIDForTest(pending, pinName);
  if (!resolvedTermID.has_value()) {
    return nullptr;
  }
  const auto exprIt = outputExprByTerm.find(*resolvedTermID);
  if (exprIt == outputExprByTerm.end()) {
    throw std::runtime_error(
        "Missing combinational expression for sequential pin `" +
        std::string(pinName) + "`");
  }
  return exprIt->second;
}

std::optional<bool> evaluateConstantUnderAssignmentsImplForTest(
    BoolExpr* expr,
    const std::unordered_map<size_t, bool>& assignments,
    std::unordered_map<BoolExpr*, std::optional<bool>>& memo) {
  if (expr == nullptr) {
    return std::nullopt;
  }
  if (const auto it = memo.find(expr); it != memo.end()) {
    return it->second;
  }

  std::optional<bool> value;
  switch (expr->getOp()) {
    case Op::VAR:
      if (expr->getId() < 2) {
        value = expr->getId() == 1;
      } else if (const auto it = assignments.find(expr->getId());
                 it != assignments.end()) {
        value = it->second;
      }
      break;
    case Op::NOT: {
      const auto operand = evaluateConstantUnderAssignmentsImplForTest(
          expr->getLeft(), assignments, memo);
      if (operand.has_value()) {
        value = !*operand;
      }
      break;
    }
    case Op::AND: {
      const auto lhs = evaluateConstantUnderAssignmentsImplForTest(
          expr->getLeft(), assignments, memo);
      if (lhs.has_value() && !*lhs) {
        value = false;
        break;
      }
      const auto rhs = evaluateConstantUnderAssignmentsImplForTest(
          expr->getRight(), assignments, memo);
      if (rhs.has_value() && !*rhs) {
        value = false;
      } else if (lhs.has_value() && rhs.has_value()) {
        value = *lhs && *rhs;
      }
      break;
    }
    case Op::OR: {
      const auto lhs = evaluateConstantUnderAssignmentsImplForTest(
          expr->getLeft(), assignments, memo);
      if (lhs.has_value() && *lhs) {
        value = true;
        break;
      }
      const auto rhs = evaluateConstantUnderAssignmentsImplForTest(
          expr->getRight(), assignments, memo);
      if (rhs.has_value() && *rhs) {
        value = true;
      } else if (lhs.has_value() && rhs.has_value()) {
        value = *lhs || *rhs;
      }
      break;
    }
    case Op::XOR: {
      const auto lhs = evaluateConstantUnderAssignmentsImplForTest(
          expr->getLeft(), assignments, memo);
      const auto rhs = evaluateConstantUnderAssignmentsImplForTest(
          expr->getRight(), assignments, memo);
      if (lhs.has_value() && rhs.has_value()) {
        value = *lhs != *rhs;
      }
      break;
    }
    case Op::NONE:
    default:
      break;
  }

  memo.emplace(expr, value);
  return value;
}

std::unordered_map<size_t, bool> collectResetAssignmentsForTest(
    const SequentialDesignModel& model) {
  std::unordered_map<size_t, bool> assignments;
  for (const auto& key : model.environmentInputs) {
    const auto displayIt = model.displayNameByKey.find(key);
    const auto varIt = model.inputVarByKey.find(key);
    if (displayIt == model.displayNameByKey.end() ||
        varIt == model.inputVarByKey.end()) {
      continue;
    }
    const auto assertedValue =
        getResetAssertionValueFromDisplayNameForTest(displayIt->second);
    if (!assertedValue.has_value()) {
      continue;
    }
    assignments.emplace(varIt->second, *assertedValue);
  }
  return assignments;
}

std::vector<std::string> setDifferenceForTest(const std::set<std::string>& lhs,
                                              const std::set<std::string>& rhs) {
  std::vector<std::string> diff;
  std::set_difference(
      lhs.begin(), lhs.end(), rhs.begin(), rhs.end(), std::back_inserter(diff));
  return diff;
}

std::string describeMismatchedNamesForTest(const std::vector<std::string>& lhs,
                                           const std::vector<std::string>& rhs,
                                           const char* label) {
  std::ostringstream oss;
  oss << "Mismatched " << label << " sets";
  if (!lhs.empty()) {
    oss << " lhs=[";
    for (size_t i = 0; i < lhs.size(); ++i) {
      if (i) {
        oss << ", ";
      }
      oss << lhs[i];
    }
    oss << "]";
  }
  if (!rhs.empty()) {
    oss << " rhs=[";
    for (size_t i = 0; i < rhs.size(); ++i) {
      if (i) {
        oss << ", ";
      }
      oss << rhs[i];
    }
    oss << "]";
  }
  return oss.str();
}

std::map<SignalKey, std::string, SignalKeyLess> buildKeyToNameMapForTest(
    const std::vector<SignalKey>& keys,
    const std::unordered_map<SignalKey, std::string, SignalKeyHash>& displayNames,
    const char* label) {
  std::map<SignalKey, std::string, SignalKeyLess> byKey;
  for (const auto& key : keys) {
    const auto nameIt = displayNames.find(key);
    if (nameIt == displayNames.end()) {
      throw std::runtime_error(
          std::string("Missing display name for SEC ") + label);
    }
    const auto [_, inserted] = byKey.emplace(key, nameIt->second);
    if (!inserted) {
      throw std::runtime_error(
          std::string("Duplicate SEC ") + label + " key `" +
          signalKeyToString(key) + "`");
    }
  }
  return byKey;
}

std::vector<std::string> sortedNamesForTest(
    const std::map<SignalKey, std::string, SignalKeyLess>& byKey) {
  std::vector<std::string> names;
  names.reserve(byKey.size());
  for (const auto& [_, name] : byKey) {
    names.push_back(name);
  }
  return names;
}

std::optional<naja::DNL::DNLID> findTermByDisplayNameForTest(
    naja::DNL::DNLFull* dnl,
    const std::string& signalName);

std::string getTerminalDisplayNameForTest(
    const naja::DNL::DNLTerminalFull& terminal);

std::vector<naja::DNL::DNLID> resolveTermsByKeyForTest(
    naja::DNL::DNLFull* dnl,
    const std::vector<SignalKey>& keys);

std::string formatConeTermForTest(naja::DNL::DNLFull* dnl,
                                  naja::DNL::DNLID termID);

ConeTraceForTest buildConeTraceForTest(
    naja::DNL::DNLFull* dnl,
    naja::DNL::DNLID seedTermID,
    const std::vector<naja::DNL::DNLID>& environmentInputs);

std::string formatConeTracebackForTest(
    const KInductionResult::CounterexampleWitness& witness,
    const SequentialDesignModel& model0,
    const SequentialDesignModel& model1,
    naja::NL::SNLDesign* top0,
    naja::NL::SNLDesign* top1);

}  // namespace

BoolExpr* buildNextStateExprForTest(
    size_t stateTermID,
    const std::unordered_map<std::string, naja::DNL::DNLID>& pinTermIDs,
    const std::vector<size_t>& termDNLID2varID,
    const std::unordered_map<naja::DNL::DNLID, BoolExpr*>& outputExprByTerm) {
  PendingTransitionForTest pending;
  pending.stateTermID = stateTermID;
  pending.independentStateOutputCount = 1;
  for (const auto& [pinName, termID] : pinTermIDs) {
    pending.pinTermIDs[pinName].push_back({termID, 0});
  }

  if (pending.stateTermID >= termDNLID2varID.size()) {
    throw std::runtime_error("Sequential state term is out of range");
  }

  const size_t stateVarID = termDNLID2varID[pending.stateTermID];
  if (stateVarID < 2) {
    throw std::runtime_error("Sequential state bit was mapped to a constant");
  }

  BoolExpr* data = getRequiredOutputExprForTest(pending, "D", outputExprByTerm);
  if (data == nullptr) {
    throw std::runtime_error("Unsupported sequential primitive without D input");
  }

  BoolExpr* current = BoolExpr::Var(stateVarID);
  BoolExpr* next = data;

  if (BoolExpr* enable = getRequiredOutputExprForTest(pending, "E", outputExprByTerm)) {
    next = BoolExpr::Or(
        BoolExpr::And(enable, data),
        BoolExpr::And(BoolExpr::Not(enable), current));
  }

  const BoolExpr* resetHigh =
      getRequiredOutputExprForTest(pending, "R", outputExprByTerm);
  const BoolExpr* resetLow =
      getRequiredOutputExprForTest(pending, "RN", outputExprByTerm);
  const BoolExpr* setHigh =
      getRequiredOutputExprForTest(pending, "S", outputExprByTerm);

  int controlKinds = 0;
  controlKinds += resetHigh != nullptr ? 1 : 0;
  controlKinds += resetLow != nullptr ? 1 : 0;
  controlKinds += setHigh != nullptr ? 1 : 0;
  if (controlKinds > 1) {
    throw std::runtime_error(
        "Unsupported sequential primitive with multiple control styles");
  }

  if (resetHigh) {
    next = BoolExpr::And(BoolExpr::Not(const_cast<BoolExpr*>(resetHigh)), next);
  } else if (resetLow) {
    next = BoolExpr::And(const_cast<BoolExpr*>(resetLow), next);
  } else if (setHigh) {
    next = BoolExpr::Or(
        const_cast<BoolExpr*>(setHigh),
        BoolExpr::And(BoolExpr::Not(const_cast<BoolExpr*>(setHigh)), next));
  }

  return next;
}

std::optional<bool> detectInitialStateValueForTest(
    const std::unordered_map<std::string, naja::DNL::DNLID>& pinTermIDs) {
  PendingTransitionForTest pending;
  pending.independentStateOutputCount = 1;
  for (const auto& [pinName, termID] : pinTermIDs) {
    pending.pinTermIDs[pinName].push_back({termID, 0});
  }

  const bool hasResetHigh = resolvePendingPinTermIDForTest(pending, "R").has_value();
  const bool hasResetLow = resolvePendingPinTermIDForTest(pending, "RN").has_value();
  const bool hasSetHigh = resolvePendingPinTermIDForTest(pending, "S").has_value();

  int controlKinds = 0;
  controlKinds += hasResetHigh ? 1 : 0;
  controlKinds += hasResetLow ? 1 : 0;
  controlKinds += hasSetHigh ? 1 : 0;
  if (controlKinds > 1) {
    throw std::runtime_error(
        "Unsupported sequential primitive with multiple control styles");
  }

  if (hasResetHigh || hasResetLow) {
    return false;
  }
  if (hasSetHigh) {
    return true;
  }
  return std::nullopt;
}

std::optional<bool> evaluateConstantUnderAssignmentsForTest(
    BoolExpr* expr,
    const std::unordered_map<size_t, bool>& assignments) {
  std::unordered_map<BoolExpr*, std::optional<bool>> memo;
  return evaluateConstantUnderAssignmentsImplForTest(expr, assignments, memo);
}

void inferSynthesizedResetInitialStateValuesForTest(SequentialDesignModel& model) {
  const auto resetAssignments = collectResetAssignmentsForTest(model);
  if (resetAssignments.empty()) {
    return;
  }

  auto countUniqueExprNodes =
      [](const std::unordered_map<SignalKey, BoolExpr*, SignalKeyHash>& exprByKey) {
        std::unordered_set<BoolExpr*> visited;
        std::vector<BoolExpr*> stack;
        for (const auto& [_, root] : exprByKey) {
          if (root != nullptr) {
            stack.push_back(root);
          }
        }

        while (!stack.empty()) {
          BoolExpr* current = stack.back();
          stack.pop_back();
          if (current == nullptr || !visited.insert(current).second) {
            continue;
          }
          if (current->getLeft() != nullptr) {
            stack.push_back(current->getLeft());
          }
          if (current->getRight() != nullptr) {
            stack.push_back(current->getRight());
          }
        }
        return visited.size();
      };

  std::unordered_map<SignalKey, BoolExpr*, SignalKeyHash> resetSpecializedNextStateByKey;
  resetSpecializedNextStateByKey.reserve(model.stateBits.size());
  std::unordered_map<BoolExpr*, BoolExpr*> resetSubstitutionMemo;
  for (const auto& key : model.stateBits) {
    const auto nextStateIt = model.nextStateExprByStateKey.find(key);
    if (nextStateIt == model.nextStateExprByStateKey.end()) {
      continue;
    }
    resetSpecializedNextStateByKey.emplace(
        key,
        substituteBoolExprVariables(
            nextStateIt->second, resetAssignments, resetSubstitutionMemo));
  }

  constexpr size_t kMaxResetSpecializedExprNodesForInitInference = 50000;
  if (countUniqueExprNodes(resetSpecializedNextStateByKey) >
      kMaxResetSpecializedExprNodesForInitInference) {
    return;
  }

  auto collectReferencedStateVars = [](BoolExpr* expr) {
    std::unordered_set<size_t> referencedVars;
    if (expr == nullptr) {
      return referencedVars;
    }

    std::vector<BoolExpr*> stack = {expr};
    std::unordered_set<BoolExpr*> visited;
    while (!stack.empty()) {
      BoolExpr* current = stack.back();
      stack.pop_back();
      if (current == nullptr || !visited.insert(current).second) {
        continue;
      }
      if (current->getOp() == Op::VAR) {
        if (current->getId() >= 2) {
          referencedVars.insert(current->getId());
        }
        continue;
      }
      if (current->getLeft() != nullptr) {
        stack.push_back(current->getLeft());
      }
      if (current->getRight() != nullptr) {
        stack.push_back(current->getRight());
      }
    }
    return referencedVars;
  };

  std::unordered_map<size_t, SignalKey> stateKeyByVar;
  std::unordered_map<size_t, std::vector<SignalKey>> dependentStatesByVar;
  stateKeyByVar.reserve(model.stateBits.size());
  dependentStatesByVar.reserve(model.stateBits.size());
  for (const auto& key : model.stateBits) {
    const auto varIt = model.inputVarByKey.find(key);
    if (varIt != model.inputVarByKey.end()) {
      stateKeyByVar.emplace(varIt->second, key);
    }
  }
  for (const auto& key : model.stateBits) {
    const auto nextStateIt = resetSpecializedNextStateByKey.find(key);
    if (nextStateIt == resetSpecializedNextStateByKey.end()) {
      continue;
    }
    const auto referencedVars = collectReferencedStateVars(nextStateIt->second);
    for (const auto referencedVar : referencedVars) {
      if (stateKeyByVar.find(referencedVar) == stateKeyByVar.end()) {
        continue;
      }
      dependentStatesByVar[referencedVar].push_back(key);
    }
  }

  std::unordered_map<SignalKey, SignalKey, SignalKeyHash> complementedPartnerByKey;
  complementedPartnerByKey.reserve(model.complementedStateRelations.size() * 2);
  for (const auto& relation : model.complementedStateRelations) {
    complementedPartnerByKey.emplace(relation.primaryKey, relation.complementedKey);
    complementedPartnerByKey.emplace(relation.complementedKey, relation.primaryKey);
  }

  std::unordered_map<size_t, bool> assignments = resetAssignments;
  for (const auto& [key, value] : model.initialStateValueByKey) {
    const auto varIt = model.inputVarByKey.find(key);
    if (varIt != model.inputVarByKey.end()) {
      assignments.emplace(varIt->second, value);
    }
  }

  std::deque<SignalKey> workQueue(model.stateBits.begin(), model.stateBits.end());
  auto recordKnownState = [&](const SignalKey& key, bool value) {
    const auto [it, inserted] = model.initialStateValueByKey.emplace(key, value);
    if (!inserted) {
      return;
    }

    const auto varIt = model.inputVarByKey.find(key);
    if (varIt != model.inputVarByKey.end()) {
      assignments[varIt->second] = value;
      const auto dependentIt = dependentStatesByVar.find(varIt->second);
      if (dependentIt != dependentStatesByVar.end()) {
        workQueue.insert(
            workQueue.end(),
            dependentIt->second.begin(),
            dependentIt->second.end());
      }
    }

    const auto partnerIt = complementedPartnerByKey.find(key);
    if (partnerIt != complementedPartnerByKey.end() &&
        model.initialStateValueByKey.find(partnerIt->second) ==
            model.initialStateValueByKey.end()) {
      workQueue.push_back(partnerIt->second);
    }
  };

  while (!workQueue.empty()) {
    const SignalKey key = workQueue.front();
    workQueue.pop_front();

    if (model.initialStateValueByKey.find(key) != model.initialStateValueByKey.end()) {
      const auto partnerIt = complementedPartnerByKey.find(key);
      if (partnerIt != complementedPartnerByKey.end() &&
          model.initialStateValueByKey.find(partnerIt->second) ==
              model.initialStateValueByKey.end()) {
        recordKnownState(partnerIt->second, !model.initialStateValueByKey.at(key));
      }
      continue;
    }

    const auto nextStateIt = resetSpecializedNextStateByKey.find(key);
    if (nextStateIt == resetSpecializedNextStateByKey.end()) {
      continue;
    }

    std::unordered_map<BoolExpr*, std::optional<bool>> memo;
    const auto resetValue = evaluateConstantUnderAssignmentsImplForTest(
        nextStateIt->second, assignments, memo);
    if (resetValue.has_value()) {
      recordKnownState(key, *resetValue);
    }
  }
}

std::optional<bool> getResetAssertionValueForTest(const std::string& displayName) {
  return getResetAssertionValueFromDisplayNameForTest(displayName);
}

namespace {

std::optional<bool> getResetAssertionValueFromDisplayNameForTest(
    const std::string& displayName) {
  const auto hasSuffix = [](const std::string& value, const std::string& suffix) {
    return value.size() >= suffix.size() &&
           value.compare(value.size() - suffix.size(), suffix.size(), suffix) == 0;
  };
  const std::string normalized = normalizeSignalBaseNameForTest(displayName);
  std::vector<std::string> candidates = {normalized};
  if (hasSuffix(normalized, "_I")) {
    candidates.push_back(normalized.substr(0, normalized.size() - 2));
  }
  if (hasSuffix(normalized, "_NI")) {
    candidates.push_back(normalized.substr(0, normalized.size() - 1));
  }
  for (const auto& candidate : candidates) {
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
 
}  // namespace

std::unordered_map<SignalKey, bool, SignalKeyHash>
deriveResetBootstrapStateValuesForTest(
    const SequentialDesignModel& model,
    size_t cycles) {
  const auto resetAssignments = collectResetAssignmentsForTest(model);
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
    std::unordered_map<BoolExpr*, std::optional<bool>> memo;
    for (const auto& key : model.stateBits) {
      const auto value = evaluateConstantUnderAssignmentsImplForTest(
          model.nextStateExprByStateKey.at(key), assignments, memo);
      if (value.has_value()) {
        nextKnownStates.emplace(key, *value);
      }
    }
    knownStates = std::move(nextKnownStates);
  }

  return knownStates;
}

AlignedSignals filterStateEqualitiesByInitialValueForTest(
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

std::string formatStringListForTest(const std::vector<std::string>& values,
                                    size_t limit) {
  if (values.empty()) {
    return "<none>";
  }

  std::ostringstream oss;
  const size_t printed = std::min(values.size(), limit);
  for (size_t i = 0; i < printed; ++i) {
    if (i) {
      oss << ", ";
    }
    oss << values[i];
  }
  if (values.size() > printed) {
    oss << ", ... +" << (values.size() - printed) << " more";
  }
  return oss.str();
}

std::string formatConeLevelsForTest(
    const std::vector<std::vector<std::string>>& levels) {
  constexpr size_t kMaxLevels = 12;
  constexpr size_t kMaxTermsPerLevel = 12;

  if (levels.empty()) {
    return "    <no traced cone terms>\n";
  }

  std::ostringstream oss;
  const size_t printedLevels = std::min(levels.size(), kMaxLevels);
  for (size_t level = 0; level < printedLevels; ++level) {
    oss << "    step " << level << ": "
        << formatStringListForTest(levels[level], kMaxTermsPerLevel) << "\n";
  }
  if (levels.size() > printedLevels) {
    oss << "    ... +" << (levels.size() - printedLevels)
        << " more trace steps\n";
  }
  return oss.str();
}

std::string formatCounterexampleWitnessForTest(
    const KInductionResult& result,
    const SequentialDesignModel& model0,
    const SequentialDesignModel& model1,
    naja::NL::SNLDesign* top0,
    naja::NL::SNLDesign* top1) {
  if (!result.witness.has_value()) {
    return "";
  }

  const auto& witness = *result.witness;
  std::ostringstream oss;
  oss << "Counterexample reaches the first bad frame at cycle "
      << witness.badFrame << ".\n";

  if (witness.inputTrace.empty()) {
    oss << "Input trace: <none>\n";
  } else {
    oss << "Input trace:\n";
    for (const auto& frame : witness.inputTrace) {
      oss << "  cycle " << frame.frame << ": ";
      if (frame.assignments.empty()) {
        oss << "<no environment inputs>";
      } else {
        for (size_t i = 0; i < frame.assignments.size(); ++i) {
          if (i) {
            oss << ", ";
          }
          oss << frame.assignments[i].signal << "="
              << formatBoolValueForTest(frame.assignments[i].value);
        }
      }
      oss << "\n";
    }
  }

  if (!witness.outputMismatches.empty()) {
    oss << "Observed output mismatches at cycle " << witness.badFrame << ":\n";
    for (const auto& mismatch : witness.outputMismatches) {
      oss << "  " << mismatch.signal << ": design0="
          << formatBoolValueForTest(mismatch.design0Value)
          << ", design1=" << formatBoolValueForTest(mismatch.design1Value) << "\n";
    }
  }

  oss << formatConeTracebackForTest(witness, model0, model1, top0, top1);
  return oss.str();
}

AlignedSignals alignSignalsByNameForTest(
    const std::vector<SignalKey>& keys0,
    const std::unordered_map<SignalKey, std::string, SignalKeyHash>& displayNames0,
    const std::vector<SignalKey>& keys1,
    const std::unordered_map<SignalKey, std::string, SignalKeyHash>& displayNames1,
    const char* label) {
  const auto byKey0 = buildKeyToNameMapForTest(keys0, displayNames0, label);
  const auto byKey1 = buildKeyToNameMapForTest(keys1, displayNames1, label);
  if (byKey0.size() != byKey1.size()) {
    throw std::runtime_error(describeMismatchedNamesForTest(
        sortedNamesForTest(byKey0), sortedNamesForTest(byKey1), label));
  }

  auto it0 = byKey0.begin();
  auto it1 = byKey1.begin();
  for (; it0 != byKey0.end() && it1 != byKey1.end(); ++it0, ++it1) {
    if (it0->first != it1->first) {
      throw std::runtime_error(describeMismatchedNamesForTest(
          sortedNamesForTest(byKey0), sortedNamesForTest(byKey1), label));
    }
  }

  AlignedSignals aligned;
  aligned.names.reserve(byKey0.size());
  aligned.keys0.reserve(byKey0.size());
  aligned.keys1.reserve(byKey0.size());
  for (const auto& [key, displayName] : byKey0) {
    aligned.names.push_back(displayName);
    aligned.keys0.push_back(key);
    aligned.keys1.push_back(key);
  }
  return aligned;
}

SignalKey getTerminalPathKeyForTest(
    const naja::DNL::DNLTerminalFull& terminal) {
  SignalKey key;
  const auto pathNames = terminal.getDNLInstance().getPath().getPathNames();
  key.first.reserve(pathNames.size() + 1);
  for (const auto& name : pathNames) {
    key.first.push_back(name.getID());
  }
  key.first.push_back(terminal.getSnlBitTerm()->getName().getID());
  key.second.push_back(
      static_cast<naja::NL::NLID::DesignObjectID>(terminal.getSnlBitTerm()->getBit()));
  return key;
}

std::optional<naja::DNL::DNLID> findTermByKeyForTest(
    naja::DNL::DNLFull* dnl,
    const SignalKey& key) {
  for (naja::DNL::DNLID termID = 0; termID < dnl->getDNLTerms().size(); ++termID) {
    const auto& term = dnl->getDNLTerminalFromID(termID);
    if (term.isNull()) {
      continue;
    }
    if (getTerminalPathKeyForTest(term) == key) {
      return termID;
    }
  }
  return std::nullopt;
}

std::vector<naja::DNL::DNLID> selectRequiredBuilderOutputsForTest(
    const std::vector<naja::DNL::DNLID>& collectedOutputs,
    const std::unordered_set<naja::DNL::DNLID>& topOutputTerms,
    const std::vector<naja::DNL::DNLID>& sequentialDependencyTerms,
    const std::unordered_set<naja::DNL::DNLID>& prunedBuilderOutputTerms) {
  const std::unordered_set<naja::DNL::DNLID> sequentialDependencySet(
      sequentialDependencyTerms.begin(), sequentialDependencyTerms.end());
  std::vector<naja::DNL::DNLID> filteredOutputs;
  filteredOutputs.reserve(collectedOutputs.size());

  for (const auto outputTermID : collectedOutputs) {
    if (prunedBuilderOutputTerms.find(outputTermID) !=
        prunedBuilderOutputTerms.end()) {
      continue;
    }
    if (topOutputTerms.find(outputTermID) != topOutputTerms.end() ||
        sequentialDependencySet.find(outputTermID) != sequentialDependencySet.end()) {
      filteredOutputs.push_back(outputTermID);
    }
  }

  return filteredOutputs;
}

namespace {

std::string getTerminalDisplayNameForTest(
    const naja::DNL::DNLTerminalFull& terminal) {
  std::ostringstream oss;
  const auto pathNames = terminal.getDNLInstance().getPath().getPathNames();
  for (const auto& name : pathNames) {
    oss << name.getString() << ".";
  }
  oss << terminal.getSnlBitTerm()->getName().getString() << "["
      << terminal.getSnlBitTerm()->getBit() << "]";
  return oss.str();
}

std::optional<naja::DNL::DNLID> findTermByDisplayNameForTest(
    naja::DNL::DNLFull* dnl,
    const std::string& signalName) {
  for (naja::DNL::DNLID termID = 0; termID < dnl->getDNLTerms().size(); ++termID) {
    const auto& term = dnl->getDNLTerminalFromID(termID);
    if (term.isNull()) {
      continue;
    }
    if (getTerminalDisplayNameForTest(term) == signalName) {
      return termID;
    }
  }
  return std::nullopt;
}

std::optional<naja::DNL::DNLID> findFirstTermByDisplayPrefixForTest(
    naja::DNL::DNLFull* dnl,
    const std::string& signalPrefix) {
  for (naja::DNL::DNLID termID = 0; termID < dnl->getDNLTerms().size(); ++termID) {
    const auto& term = dnl->getDNLTerminalFromID(termID);
    if (term.isNull()) {
      continue;
    }
    if (getTerminalDisplayNameForTest(term).rfind(signalPrefix, 0) == 0) {
      return termID;
    }
  }
  return std::nullopt;
}

std::optional<naja::DNL::DNLID> findBuildableOutputRootForTest(
    naja::DNL::DNLFull* dnl,
    naja::DNL::DNLID requestedTermID,
    std::vector<std::string>* chain = nullptr) {
  std::unordered_set<naja::DNL::DNLID> visitedTerms;
  naja::DNL::DNLID currentTermID = requestedTermID;
  while (currentTermID != naja::DNL::DNLID_MAX &&
         visitedTerms.insert(currentTermID).second) {
    const auto& currentTerm = dnl->getDNLTerminalFromID(currentTermID);
    if (currentTerm.isNull()) {
      return std::nullopt;
    }
    if (chain != nullptr) {
      chain->push_back(getTerminalDisplayNameForTest(currentTerm));
    }
    if (currentTerm.isTopPort() &&
        currentTerm.getSnlBitTerm()->getDirection() !=
            naja::NL::SNLBitTerm::Direction::Output) {
      return currentTermID;
    }
    if (currentTerm.getSnlBitTerm()->getDirection() ==
        naja::NL::SNLBitTerm::Direction::Output) {
      const auto& inst = currentTerm.getDNLInstance();
      auto* model = inst.getSNLModel();
      if (model != nullptr && naja::NL::NLDB0::isAssign(model)) {
        std::optional<naja::DNL::DNLID> passthroughDriver;
        for (auto* inputBitTerm :
             naja::NL::SNLDesignModeling::getCombinatorialInputs(
                 const_cast<naja::NL::SNLBitTerm*>(currentTerm.getSnlBitTerm()))) {
          if (inputBitTerm == nullptr ||
              inputBitTerm->getDirection() ==
                  naja::NL::SNLBitTerm::Direction::Output) {
            continue;
          }
          const auto& inputTerm = inst.getTerminalFromBitTerm(inputBitTerm);
          if (inputTerm.isNull() || inputTerm.getIsoID() == naja::DNL::DNLID_MAX) {
            passthroughDriver.reset();
            break;
          }
          const auto& iso =
              dnl->getDNLIsoDB().getIsoFromIsoIDconst(inputTerm.getIsoID());
          if (iso.isConstant() || iso.getDrivers().size() != 1) {
            passthroughDriver.reset();
            break;
          }
          if (passthroughDriver.has_value()) {
            passthroughDriver.reset();
            break;
          }
          passthroughDriver = iso.getDrivers().front();
        }
        if (passthroughDriver.has_value()) {
          currentTermID = *passthroughDriver;
          continue;
        }
      }
      return currentTermID;
    }

    const auto isoID = currentTerm.getIsoID();
    if (isoID == naja::DNL::DNLID_MAX) {
      return std::nullopt;
    }
    const auto& iso = dnl->getDNLIsoDB().getIsoFromIsoIDconst(isoID);
    if (iso.isConstant() || iso.getDrivers().size() != 1) {
      return std::nullopt;
    }
    currentTermID = iso.getDrivers().front();
  }
  return std::nullopt;
}

struct BuilderOutputProbeForTest {
  std::optional<naja::DNL::DNLID> normalizedRoot;
  std::string normalizedRootName;
  std::string normalizedRootModelName;
  bool hasBuiltExpr = false;
  bool hasSkip = false;
  std::string skipDetail;
  std::vector<std::string> normalizationChain;
  std::vector<std::string> rootSupportTerms;
  std::vector<std::string> rootCombinationalInputs;
  std::vector<std::string> driverSpine;
};

BuilderOutputProbeForTest probeRequestedBuilderOutputForTest(
    naja::DNL::DNLFull* dnl,
    naja::DNL::DNLID requestedTermID) {
  BuilderOutputProbeForTest probe;
  probe.normalizedRoot =
      findBuildableOutputRootForTest(dnl, requestedTermID, &probe.normalizationChain);
  if (!probe.normalizedRoot.has_value()) {
    return probe;
  }
  probe.normalizedRootName =
      getTerminalDisplayNameForTest(dnl->getDNLTerminalFromID(*probe.normalizedRoot));
  const auto& rootTerm = dnl->getDNLTerminalFromID(*probe.normalizedRoot);
  const auto& rootInst = rootTerm.getDNLInstance();
  probe.normalizedRootModelName = rootInst.getSNLModel()->getName().getString();
  for (naja::DNL::DNLID termID = rootInst.getTermIndexes().first;
       termID <= rootInst.getTermIndexes().second; ++termID) {
    const auto& term = dnl->getDNLTerminalFromID(termID);
    if (term.isNull() || term.getSnlBitTerm()->getDirection() ==
                             naja::NL::SNLBitTerm::Direction::Output) {
      continue;
    }
    std::ostringstream support;
    support << getTerminalDisplayNameForTest(term);
    if (term.getIsoID() == naja::DNL::DNLID_MAX) {
      support << " iso=<invalid>";
    } else {
      const auto& iso = dnl->getDNLIsoDB().getIsoFromIsoIDconst(term.getIsoID());
      support << " iso=" << iso.getIsoID()
              << " drivers=" << iso.getDrivers().size()
              << " readers=" << iso.getReaders().size()
              << " const0=" << (iso.isConstant0() ? "true" : "false")
              << " const1=" << (iso.isConstant1() ? "true" : "false")
              << " driver_terms=[";
      for (size_t index = 0; index < iso.getDrivers().size(); ++index) {
        if (index != 0) {
          support << ", ";
        }
        const auto& driverTerm = dnl->getDNLTerminalFromID(iso.getDrivers()[index]);
        support << getTerminalDisplayNameForTest(driverTerm)
                << "{dir="
                << static_cast<int>(driverTerm.getSnlBitTerm()->getDirection())
                << ",model="
                << driverTerm.getDNLInstance().getSNLModel()->getName().getString()
                << "}";
      }
      support << "]";
    }
    probe.rootSupportTerms.push_back(support.str());
  }
  for (auto* bitTerm :
       naja::NL::SNLDesignModeling::getCombinatorialInputs(rootTerm.getSnlBitTerm())) {
    if (bitTerm == nullptr) {
      continue;
    }
    const auto& inputTerm = rootInst.getTerminalFromBitTerm(bitTerm);
    if (inputTerm.isNull()) {
      continue;
    }
    std::ostringstream support;
    support << getTerminalDisplayNameForTest(inputTerm);
    if (inputTerm.getIsoID() == naja::DNL::DNLID_MAX) {
      support << " iso=<invalid>";
    } else {
      const auto& iso = dnl->getDNLIsoDB().getIsoFromIsoIDconst(inputTerm.getIsoID());
      support << " iso=" << iso.getIsoID()
              << " drivers=" << iso.getDrivers().size()
              << " readers=" << iso.getReaders().size()
              << " const0=" << (iso.isConstant0() ? "true" : "false")
              << " const1=" << (iso.isConstant1() ? "true" : "false")
              << " driver_terms=[";
      for (size_t index = 0; index < iso.getDrivers().size(); ++index) {
        if (index != 0) {
          support << ", ";
        }
        const auto& driverTerm = dnl->getDNLTerminalFromID(iso.getDrivers()[index]);
        support << getTerminalDisplayNameForTest(driverTerm)
                << "{dir="
                << static_cast<int>(driverTerm.getSnlBitTerm()->getDirection())
                << ",model="
                << driverTerm.getDNLInstance().getSNLModel()->getName().getString()
                << "}";
      }
      support << "]";
    }
    probe.rootCombinationalInputs.push_back(support.str());
  }
  {
    std::unordered_set<naja::DNL::DNLID> visited;
    naja::DNL::DNLID currentTermID = *probe.normalizedRoot;
    while (visited.insert(currentTermID).second) {
      const auto& currentTerm = dnl->getDNLTerminalFromID(currentTermID);
      std::ostringstream step;
      step << getTerminalDisplayNameForTest(currentTerm)
           << "{model="
           << currentTerm.getDNLInstance().getSNLModel()->getName().getString()
           << "}";
      probe.driverSpine.push_back(step.str());

      std::optional<naja::DNL::DNLID> nextDriver;
      bool ambiguousNext = false;
      const auto& currentInst = currentTerm.getDNLInstance();
      for (auto* bitTerm : naja::NL::SNLDesignModeling::getCombinatorialInputs(
               const_cast<naja::NL::SNLBitTerm*>(currentTerm.getSnlBitTerm()))) {
        if (bitTerm == nullptr ||
            bitTerm->getDirection() ==
                naja::NL::SNLBitTerm::Direction::Output) {
          continue;
        }
        const auto& inputTerm = currentInst.getTerminalFromBitTerm(bitTerm);
        if (inputTerm.isNull() || inputTerm.getIsoID() == naja::DNL::DNLID_MAX) {
          ambiguousNext = true;
          nextDriver.reset();
          break;
        }
        const auto& iso =
            dnl->getDNLIsoDB().getIsoFromIsoIDconst(inputTerm.getIsoID());
        if (iso.isConstant()) {
          continue;
        }
        if (iso.getDrivers().size() != 1) {
          ambiguousNext = true;
          nextDriver.reset();
          break;
        }
        if (nextDriver.has_value()) {
          ambiguousNext = true;
          nextDriver.reset();
          break;
        }
        nextDriver = iso.getDrivers().front();
      }
      if (ambiguousNext || !nextDriver.has_value()) {
        break;
      }
      currentTermID = *nextDriver;
    }
  }

  KEPLER_FORMAL::BuildPrimaryOutputClauses builder;
  builder.collect();
  builder.setOutputs({*probe.normalizedRoot});
  builder.build();

  const auto& outputs = builder.getOutputs();
  const auto& exprs = builder.getPOs();
  for (size_t index = 0; index < outputs.size(); ++index) {
    if (outputs[index] != *probe.normalizedRoot) {
      continue;
    }
    probe.hasBuiltExpr =
        exprs[index] != nullptr && exprs[index]->isValid();
    break;
  }
  if (const auto skippedIt = builder.getSkippedOutputs().find(*probe.normalizedRoot);
      skippedIt != builder.getSkippedOutputs().end()) {
    probe.hasSkip = true;
    probe.skipDetail = skippedIt->second.detail;
  }
  return probe;
}

std::vector<naja::DNL::DNLID> resolveTermsByKeyForTest(
    naja::DNL::DNLFull* dnl,
    const std::vector<SignalKey>& keys) {
  std::vector<naja::DNL::DNLID> resolved;
  resolved.reserve(keys.size());
  for (const auto& key : keys) {
    if (auto termID = findTermByKeyForTest(dnl, key); termID.has_value()) {
      resolved.push_back(*termID);
    }
  }
  return resolved;
}

std::string formatConeTermForTest(naja::DNL::DNLFull* dnl,
                                  naja::DNL::DNLID termID) {
  const auto& term = dnl->getDNLTerminalFromID(termID);
  if (term.isNull()) {
    return "<null>";
  }
  if (term.getIsoID() == naja::DNL::DNLID_MAX) {
    return getTerminalDisplayNameForTest(term);
  }

  const auto& iso = dnl->getDNLIsoDB().getIsoFromIsoIDconst(term.getIsoID());
  if (iso.isConstant0()) {
    return "Constant 0";
  }
  if (iso.isConstant1()) {
    return "Constant 1";
  }
  return getTerminalDisplayNameForTest(term);
}

ConeTraceForTest buildConeTraceForTest(
    naja::DNL::DNLFull* dnl,
    naja::DNL::DNLID seedTermID,
    const std::vector<naja::DNL::DNLID>& environmentInputs) {
  ConeTraceForTest trace;
  std::vector<bool> isEnvironmentInput(dnl->getDNLTerms().size(), false);
  for (const auto termID : environmentInputs) {
    if (termID < isEnvironmentInput.size()) {
      isEnvironmentInput[termID] = true;
    }
  }

  const auto seedIsoID = dnl->getDNLTerminalFromID(seedTermID).getIsoID();
  if (seedIsoID == naja::DNL::DNLID_MAX) {
    return trace;
  }

  std::vector<naja::DNL::DNLID> currentIsos = {seedIsoID};
  std::unordered_set<naja::DNL::DNLID> visitedIsos;
  while (!currentIsos.empty()) {
    std::set<std::string> levelTerms;
    std::vector<naja::DNL::DNLID> nextIsos;

    for (const auto isoID : currentIsos) {
      if (isoID == naja::DNL::DNLID_MAX || !visitedIsos.insert(isoID).second) {
        continue;
      }

      const auto& iso = dnl->getDNLIsoDB().getIsoFromIsoIDconst(isoID);
      if (iso.isConstant0()) {
        levelTerms.insert("Constant 0");
        continue;
      }
      if (iso.isConstant1()) {
        levelTerms.insert("Constant 1");
        continue;
      }

      for (const auto driver : iso.getDrivers()) {
        if (driver == naja::DNL::DNLID_MAX) {
          continue;
        }

        const auto& driverTerm = dnl->getDNLTerminalFromID(driver);
        if (driverTerm.isNull()) {
          continue;
        }

        levelTerms.insert(formatConeTermForTest(dnl, driver));
        if (driver < isEnvironmentInput.size() && isEnvironmentInput[driver]) {
          continue;
        }

        const auto& inst = driverTerm.getDNLInstance();
        for (naja::DNL::DNLID termID = inst.getTermIndexes().first;
             termID != naja::DNL::DNLID_MAX && termID <= inst.getTermIndexes().second;
             ++termID) {
          const auto& term = dnl->getDNLTerminalFromID(termID);
          if (term.isNull()) {
            continue;
          }
          if (term.getSnlBitTerm()->getDirection() ==
              naja::NL::SNLBitTerm::Direction::Output) {
            continue;
          }
          if (term.getIsoID() != naja::DNL::DNLID_MAX) {
            nextIsos.push_back(term.getIsoID());
          }
        }
      }
    }

    if (!levelTerms.empty()) {
      std::vector<std::string> orderedTerms(levelTerms.begin(), levelTerms.end());
      trace.allTerms.insert(orderedTerms.begin(), orderedTerms.end());
      trace.levels.push_back(std::move(orderedTerms));
    }

    std::sort(nextIsos.begin(), nextIsos.end());
    nextIsos.erase(std::unique(nextIsos.begin(), nextIsos.end()), nextIsos.end());
    currentIsos = std::move(nextIsos);
  }

  return trace;
}

ConeDiffReportForTest buildConeDiffReportForTest(
    naja::NL::SNLDesign* top,
    const std::string& differenceSignal,
    const std::vector<SignalKey>& environmentInputs) {
  ConeDiffReportForTest report;
  ScopedDnlContextForTest dnlContext(top);
  auto* dnl = dnlContext.dnl();

  const auto seedTermID = findTermByDisplayNameForTest(dnl, differenceSignal);
  if (!seedTermID.has_value()) {
    report.error =
        "could not resolve the differing SEC signal back into the DNL";
    return report;
  }

  report.trace = buildConeTraceForTest(
      dnl, *seedTermID, resolveTermsByKeyForTest(dnl, environmentInputs));
  return report;
}

std::string formatConeTracebackForTest(
    const KInductionResult::CounterexampleWitness& witness,
    const SequentialDesignModel& model0,
    const SequentialDesignModel& model1,
    naja::NL::SNLDesign* top0,
    naja::NL::SNLDesign* top1) {
  if (witness.outputMismatches.empty()) {
    return "";
  }
  const auto& differencePoint = witness.outputMismatches.front();

  std::ostringstream oss;
  oss << "Traceback for first differing point `" << differencePoint.signal
      << "` at cycle " << witness.badFrame << ":\n";

  try {
    const auto report0 = buildConeDiffReportForTest(
        top0, differencePoint.signal, model0.environmentInputs);
    const auto report1 = buildConeDiffReportForTest(
        top1, differencePoint.signal, model1.environmentInputs);

    if (!report0.error.empty() || !report1.error.empty()) {
      oss << "  Cone traceback unavailable: ";
      if (!report0.error.empty()) {
        oss << "design0 " << report0.error;
      }
      if (!report0.error.empty() && !report1.error.empty()) {
        oss << "; ";
      }
      if (!report1.error.empty()) {
        oss << "design1 " << report1.error;
      }
      oss << "\n";
      return oss.str();
    }

    oss << "  design0 cone to environment inputs:\n"
        << formatConeLevelsForTest(report0.trace.levels);
    oss << "  design1 cone to environment inputs:\n"
        << formatConeLevelsForTest(report1.trace.levels);

    constexpr size_t kMaxDiffTerms = 20;
    const auto onlyInDesign0 =
        setDifferenceForTest(report0.trace.allTerms, report1.trace.allTerms);
    const auto onlyInDesign1 =
        setDifferenceForTest(report1.trace.allTerms, report0.trace.allTerms);
    oss << "  cone terms only in design0: "
        << formatStringListForTest(onlyInDesign0, kMaxDiffTerms) << "\n";
    oss << "  cone terms only in design1: "
        << formatStringListForTest(onlyInDesign1, kMaxDiffTerms) << "\n";
  } catch (const std::exception& e) {
    oss << "  Cone traceback unavailable: " << e.what() << "\n";
  }

  return oss.str();
}

}  // namespace

}  // namespace KEPLER_FORMAL::SEC::detail

namespace {

class SequentialEquivalenceStrategyTests : public ::testing::Test {
 protected:
  void TearDown() override {
    naja::DNL::destroy();
    if (auto* universe = NLUniverse::get()) {
      universe->destroy();
    }
    KEPLER_FORMAL::BoolExprCache::destroy();
  }
};

class ScopedEnvVar {
 public:
  ScopedEnvVar(const char* name, const char* value)
      : name_(name) {
    if (const char* current = std::getenv(name_); current != nullptr) {
      previousValue_ = current;
    }
    setenv(name_, value, 1);
  }

  ~ScopedEnvVar() {
    if (previousValue_.has_value()) {
      setenv(name_, previousValue_->c_str(), 1);
    } else {
      unsetenv(name_);
    }
  }

 private:
  const char* name_;
  std::optional<std::string> previousValue_;
};

class ScopedSecBoundaryAbstraction {
 public:
  explicit ScopedSecBoundaryAbstraction(bool enabled)
      : previousValue_(
            KEPLER_FORMAL::Config::getSecTreatUncomputableSeqAsBoundary()) {
    KEPLER_FORMAL::Config::setSecTreatUncomputableSeqAsBoundary(enabled);
  }

  ~ScopedSecBoundaryAbstraction() {
    KEPLER_FORMAL::Config::setSecTreatUncomputableSeqAsBoundary(previousValue_);
  }

 private:
  bool previousValue_;
};

// Synthetic tests below do not always build a Naja universe. Production SEC
// keys come from NLName::getID() on real terminals; this local allocator only
// gives those unit-only artificial keys stable, collision-free identities.
naja::NL::NLID::DesignObjectID makeSyntheticSignalNameID(
    const std::string& name) {
  static std::unordered_map<std::string, naja::NL::NLID::DesignObjectID> ids;
  const auto nextID =
      static_cast<naja::NL::NLID::DesignObjectID>(ids.size() + 1);
  return ids.emplace(name, nextID).first->second;
}

SignalKey makeSignalKey(const std::string& name) {
  SignalKey key;
  const auto nameID = makeSyntheticSignalNameID(name);
  key.first.push_back(nameID);
  key.second.push_back(nameID);
  return key;
}

SequentialDesignModel makeCombinationalExtractedModel(BoolExpr* outputExpr) {
  SequentialDesignModel model;
  const SignalKey inputKey = makeSignalKey("in");
  const SignalKey outputKey = makeSignalKey("out");
  model.environmentInputs = {inputKey};
  model.topInputKeys = {inputKey};
  model.topOutputKeys = {outputKey};
  model.allObservedOutputs = {outputKey};
  model.observedOutputs = {outputKey};
  model.inputVarByKey.emplace(inputKey, 2);
  model.displayNameByKey.emplace(inputKey, "in[0]");
  model.displayNameByKey.emplace(outputKey, "out[0]");
  model.observedOutputExprByKey.emplace(outputKey, outputExpr);
  return model;
}

KInductionProblem buildLinearChainSecProblem(size_t logicalStateCount) {
  const auto bitCount = [logicalStateCount]() {
    size_t bits = 0;
    size_t encodedStates = 1;
    while (encodedStates < logicalStateCount) {
      encodedStates <<= 1;
      ++bits;
    }
    return std::max<size_t>(bits, 1);
  }();

  const auto buildStateExpr = [](const std::vector<size_t>& symbols, size_t value) {
    BoolExpr* expr = BoolExpr::createTrue();
    for (size_t bit = 0; bit < symbols.size(); ++bit) {
      expr = BoolExpr::And(
          expr,
          (value & (size_t{1} << bit)) != 0 ? BoolExpr::Var(symbols[bit])
                                            : BoolExpr::Not(BoolExpr::Var(symbols[bit])));
    }
    return BoolExpr::simplify(expr);
  };

  const auto buildNextBitExpr =
      [&](const std::vector<size_t>& symbols, size_t bitIndex) {
        BoolExpr* expr = BoolExpr::createFalse();
        for (size_t logicalState = 0; logicalState < logicalStateCount; ++logicalState) {
          const size_t nextLogicalState =
              logicalState + 1 < logicalStateCount ? logicalState + 1 : logicalState;
          if ((nextLogicalState & (size_t{1} << bitIndex)) == 0) {
            continue;
          }
          expr = BoolExpr::Or(expr, buildStateExpr(symbols, logicalState));
        }
        return BoolExpr::simplify(expr);
      };

  KInductionProblem problem;
  problem.state0Symbols.reserve(bitCount);
  problem.state1Symbols.reserve(bitCount);
  problem.allSymbols.reserve(bitCount * 2);

  size_t nextSymbol = 2;
  for (size_t bit = 0; bit < bitCount; ++bit) {
    problem.state0Symbols.push_back(nextSymbol++);
  }
  for (size_t bit = 0; bit < bitCount; ++bit) {
    problem.state1Symbols.push_back(nextSymbol++);
  }
  problem.allSymbols.insert(
      problem.allSymbols.end(), problem.state0Symbols.begin(), problem.state0Symbols.end());
  problem.allSymbols.insert(
      problem.allSymbols.end(), problem.state1Symbols.begin(), problem.state1Symbols.end());

  for (size_t bit = 0; bit < bitCount; ++bit) {
    problem.transitions0.emplace_back(
        problem.state0Symbols[bit], buildNextBitExpr(problem.state0Symbols, bit));
    problem.transitions1.emplace_back(
        problem.state1Symbols[bit], buildNextBitExpr(problem.state1Symbols, bit));
  }

  problem.initialCondition = BoolExpr::And(
      buildStateExpr(problem.state0Symbols, 0), buildStateExpr(problem.state1Symbols, 0));
  problem.initializedStateCount = problem.allSymbols.size();
  problem.totalStateCount = problem.allSymbols.size();
  problem.observedOutputExprs0 = {
      buildStateExpr(problem.state0Symbols, logicalStateCount - 1)};
  problem.observedOutputExprs1 = {
      buildStateExpr(problem.state1Symbols, logicalStateCount - 1)};
  problem.property = makeEqualityExpr(
      problem.observedOutputExprs0.front(), problem.observedOutputExprs1.front());
  problem.bad = BoolExpr::Not(problem.property);
  problem.inductionProperty = problem.property;
  problem.inductionBad = problem.bad;
  return problem;
}

KInductionProblem buildDocumentedBooleanPdrCounterexampleProblem() {
  KInductionProblem problem;
  problem.description = "documented Boolean PDR counterexample miter";
  problem.environmentInputNames = {"in"};
  problem.observedOutputNames = {"q_miter"};
  problem.inputSymbols = {4};
  problem.state0Symbols = {2};
  problem.state1Symbols = {3};
  problem.allSymbols = {2, 3, 4};
  problem.initialCondition =
      BoolExpr::And(BoolExpr::Not(BoolExpr::Var(2)), BoolExpr::Not(BoolExpr::Var(3)));
  problem.initializedStateCount = 2;
  problem.totalStateCount = 2;
  problem.observedOutputExprs0 = {BoolExpr::Var(2)};
  problem.observedOutputExprs1 = {BoolExpr::Var(3)};
  problem.transitions0.emplace_back(2, BoolExpr::Not(BoolExpr::Var(2)));
  problem.transitions1.emplace_back(3, BoolExpr::And(BoolExpr::Var(3), BoolExpr::Var(4)));
  problem.property = makeEqualityExpr(BoolExpr::Var(2), BoolExpr::Var(3));
  problem.bad = BoolExpr::Xor(BoolExpr::Var(2), BoolExpr::Var(3));
  problem.inductionProperty = problem.property;
  problem.inductionBad = problem.bad;
  return problem;
}

SNLDesignModeling::BitTerms collectBitTerms(SNLBusTerm* bus) {
  SNLDesignModeling::BitTerms bits;
  for (auto* bit : bus->getBits()) {
    bits.push_back(bit);
  }
  return bits;
}

SNLDesign* createInvModel(NLLibrary* library) {
  auto* model =
      SNLDesign::create(library, SNLDesign::Type::Primitive, NLName("INV"));
  auto* input =
      SNLScalarTerm::create(model, SNLTerm::Direction::Input, NLName("A"));
  auto* output =
      SNLScalarTerm::create(model, SNLTerm::Direction::Output, NLName("Y"));
  SNLDesignModeling::addCombinatorialArcs({input}, {output});
  SNLDesignModeling::setTruthTable(model, SNLTruthTable::Inv());
  return model;
}

SNLDesign* createAnd2Model(NLLibrary* library) {
  auto* model =
      SNLDesign::create(library, SNLDesign::Type::Primitive, NLName("AND2"));
  auto* input0 =
      SNLScalarTerm::create(model, SNLTerm::Direction::Input, NLName("A"));
  auto* input1 =
      SNLScalarTerm::create(model, SNLTerm::Direction::Input, NLName("B"));
  auto* output =
      SNLScalarTerm::create(model, SNLTerm::Direction::Output, NLName("Y"));
  SNLDesignModeling::addCombinatorialArcs({input0, input1}, {output});
  SNLDesignModeling::setTruthTable(
      model,
      SNLTruthTable(
          2,
          SNLTruthTable::GenericType::AND,
          SNLTruthTable::fullDependencies(2)));
  return model;
}

SNLDesign* createOr2Model(NLLibrary* library) {
  auto* model =
      SNLDesign::create(library, SNLDesign::Type::Primitive, NLName("OR2"));
  auto* input0 =
      SNLScalarTerm::create(model, SNLTerm::Direction::Input, NLName("A"));
  auto* input1 =
      SNLScalarTerm::create(model, SNLTerm::Direction::Input, NLName("B"));
  auto* output =
      SNLScalarTerm::create(model, SNLTerm::Direction::Output, NLName("Y"));
  SNLDesignModeling::addCombinatorialArcs({input0, input1}, {output});
  SNLDesignModeling::setTruthTable(
      model,
      SNLTruthTable(
          2,
          SNLTruthTable::GenericType::OR,
          SNLTruthTable::fullDependencies(2)));
  return model;
}

SNLDesign* createOpaqueLeafModel(NLLibrary* library) {
  auto* model =
      SNLDesign::create(library, SNLDesign::Type::Primitive, NLName("OPAQUE"));
  SNLScalarTerm::create(model, SNLTerm::Direction::Input, NLName("A"));
  SNLScalarTerm::create(model, SNLTerm::Direction::Output, NLName("Y"));
  return model;
}

SNLDesign* createSinglePortMemoryModel(
    NLLibrary* library,
    const std::string& name,
    bool withReset = false) {
  auto* model =
      SNLDesign::create(library, SNLDesign::Type::Primitive, NLName(name));
  auto* clock =
      SNLScalarTerm::create(model, SNLTerm::Direction::Input, NLName("CLK"));
  auto* reset = withReset
      ? SNLScalarTerm::create(model, SNLTerm::Direction::Input, NLName("RST"))
      : nullptr;
  auto* chipEnable =
      SNLScalarTerm::create(model, SNLTerm::Direction::Input, NLName("CE"));
  auto* writeEnable =
      SNLScalarTerm::create(model, SNLTerm::Direction::Input, NLName("WE"));
  auto* address =
      SNLBusTerm::create(model, SNLTerm::Direction::Input, 1, 0, NLName("ADDR"));
  auto* writeData =
      SNLBusTerm::create(model, SNLTerm::Direction::Input, 3, 0, NLName("WDATA"));
  auto* writeMask =
      SNLBusTerm::create(model, SNLTerm::Direction::Input, 3, 0, NLName("WMASK"));
  auto* readData =
      SNLBusTerm::create(model, SNLTerm::Direction::Output, 3, 0, NLName("RDATA"));

  SNLDesignModeling::BitTerms readDataBits;
  SNLDesignModeling::BitTerms readAddressBits;
  SNLDesignModeling::BitTerms writeDataBits;
  SNLDesignModeling::BitTerms writeMaskBits;
  for (int bit = 0; bit <= 3; ++bit) {
    readDataBits.push_back(readData->getBit(bit));
    writeDataBits.push_back(writeData->getBit(bit));
    writeMaskBits.push_back(writeMask->getBit(bit));
    if (bit <= 1) {
      readAddressBits.push_back(address->getBit(bit));
    }
  }
  SNLDesignModeling::addClockToOutputsArcs(clock, readDataBits);
  SNLDesignModeling::BitTerms clockInputs = {
      address->getBit(0),
      address->getBit(1),
      writeData->getBit(0),
      writeData->getBit(1),
      writeData->getBit(2),
      writeData->getBit(3),
      writeMask->getBit(0),
      writeMask->getBit(1),
      writeMask->getBit(2),
      writeMask->getBit(3),
      chipEnable,
      writeEnable};
  if (reset != nullptr) {
    clockInputs.push_back(reset);
  }
  SNLDesignModeling::addInputsToClockArcs(clockInputs, clock);
  SNLDesignModeling::addCombinatorialArcs(readAddressBits, readDataBits);

  SNLDesignModeling::MemoryInterface interface;
  interface.width = 4;
  interface.depth = 4;
  interface.abits = 2;
  interface.clock = clock;
  if (reset != nullptr) {
    interface.resetMode = SNLDesignModeling::MemoryResetMode::AsyncHigh;
    interface.reset = reset;
  }
  interface.readPorts.push_back(
      {.address = {address->getBit(0), address->getBit(1)},
       .data = {readData->getBit(0),
                readData->getBit(1),
                readData->getBit(2),
                readData->getBit(3)}});
  interface.writePorts.push_back(
      {.address = {address->getBit(0), address->getBit(1)},
       .data = {writeData->getBit(0),
                writeData->getBit(1),
                writeData->getBit(2),
                writeData->getBit(3)},
       .mask = {writeMask->getBit(0),
                writeMask->getBit(1),
                writeMask->getBit(2),
                writeMask->getBit(3)},
       .enables = {chipEnable, writeEnable}});
  SNLDesignModeling::setMemoryInterface(model, interface);
  return model;
}

SNLDesign* createSinglePortMemoryTop(
    NLLibrary* library,
    const std::string& name,
    SNLDesign* memoryModel,
    std::optional<int> floatingWriteDataBit = std::nullopt,
    bool floatingReset = false) {
  auto* top =
      SNLDesign::create(library, SNLDesign::Type::Standard, NLName(name));
  auto* topClock =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("clk"));
  auto* topChipEnable =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("ce"));
  auto* topWriteEnable =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("we"));
  auto* modelReset = memoryModel->getScalarTerm(NLName("RST"));
  auto* topReset = modelReset == nullptr || floatingReset
      ? nullptr
      : SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("rst"));
  auto* topAddress =
      SNLBusTerm::create(top, SNLTerm::Direction::Input, 1, 0, NLName("addr"));
  auto* topWriteData =
      SNLBusTerm::create(top, SNLTerm::Direction::Input, 3, 0, NLName("wdata"));
  auto* topWriteMask =
      SNLBusTerm::create(top, SNLTerm::Direction::Input, 3, 0, NLName("wmask"));
  auto* topOut =
      SNLBusTerm::create(top, SNLTerm::Direction::Output, 3, 0, NLName("out"));

  auto* memory = SNLInstance::create(top, memoryModel, NLName("mem0"));
  auto* clockNet = SNLScalarNet::create(top, NLName("clk_net"));
  auto* chipEnableNet = SNLScalarNet::create(top, NLName("ce_net"));
  auto* writeEnableNet = SNLScalarNet::create(top, NLName("we_net"));
  auto* resetNet = modelReset == nullptr
      ? nullptr
      : SNLScalarNet::create(top, NLName("rst_net"));
  auto* addressNet = SNLBusNet::create(top, 1, 0, NLName("addr_net"));
  auto* writeDataNet = SNLBusNet::create(top, 3, 0, NLName("wdata_net"));
  auto* writeMaskNet = SNLBusNet::create(top, 3, 0, NLName("wmask_net"));
  auto* outNet = SNLBusNet::create(top, 3, 0, NLName("out_net"));

  topClock->setNet(clockNet);
  topChipEnable->setNet(chipEnableNet);
  topWriteEnable->setNet(writeEnableNet);
  if (topReset != nullptr) {
    topReset->setNet(resetNet);
  }
  memory->getInstTerm(memoryModel->getScalarTerm(NLName("CLK")))->setNet(clockNet);
  memory->getInstTerm(memoryModel->getScalarTerm(NLName("CE")))->setNet(chipEnableNet);
  memory->getInstTerm(memoryModel->getScalarTerm(NLName("WE")))->setNet(writeEnableNet);
  if (modelReset != nullptr) {
    memory->getInstTerm(modelReset)->setNet(resetNet);
  }

  auto* modelAddress = memoryModel->getBusTerm(NLName("ADDR"));
  auto* modelWriteData = memoryModel->getBusTerm(NLName("WDATA"));
  auto* modelWriteMask = memoryModel->getBusTerm(NLName("WMASK"));
  auto* modelReadData = memoryModel->getBusTerm(NLName("RDATA"));
  for (int bit = 0; bit <= 1; ++bit) {
    topAddress->getBit(bit)->setNet(addressNet->getBit(bit));
    memory->getInstTerm(modelAddress->getBit(bit))->setNet(addressNet->getBit(bit));
  }
  for (int bit = 0; bit <= 3; ++bit) {
    if (floatingWriteDataBit.has_value() && bit == *floatingWriteDataBit) {
      auto* floatingWriteDataNet = SNLScalarNet::create(
          top, NLName("floating_wdata" + std::to_string(bit) + "_net"));
      memory->getInstTerm(modelWriteData->getBit(bit))->setNet(floatingWriteDataNet);
    } else {
      topWriteData->getBit(bit)->setNet(writeDataNet->getBit(bit));
      memory->getInstTerm(modelWriteData->getBit(bit))->setNet(writeDataNet->getBit(bit));
    }
    topWriteMask->getBit(bit)->setNet(writeMaskNet->getBit(bit));
    topOut->getBit(bit)->setNet(outNet->getBit(bit));
    memory->getInstTerm(modelWriteMask->getBit(bit))->setNet(writeMaskNet->getBit(bit));
    memory->getInstTerm(modelReadData->getBit(bit))->setNet(outNet->getBit(bit));
  }

  return top;
}

std::filesystem::path repoRootForSecTests() {
  if (const char* prefix = std::getenv("TEST_DATA_PREFIX");
      prefix != nullptr) {
    return std::filesystem::path(prefix);
  }
  return std::filesystem::path(__FILE__).parent_path().parent_path().parent_path();
}

struct Cva6SourceContextForSecTests {
  std::filesystem::path cva6RepoDir;
  std::filesystem::path hpdcacheDir;
  std::string targetCfg;
};

std::optional<Cva6SourceContextForSecTests> resolveCva6SourceContextForSecTests() {
  const char* cva6RepoDirEnv = std::getenv("CVA6_REPO_DIR");
  const char* hpdcacheDirEnv = std::getenv("HPDCACHE_DIR");
  const char* targetCfgEnv = std::getenv("TARGET_CFG");

  std::filesystem::path cva6RepoDir;
  if (cva6RepoDirEnv != nullptr && *cva6RepoDirEnv != '\0') {
    cva6RepoDir = cva6RepoDirEnv;
  } else {
    const auto fallbackRepoDir = std::filesystem::path("/Users/noamcohen/dev/CVA6/cva6");
    if (std::filesystem::exists(fallbackRepoDir)) {
      cva6RepoDir = fallbackRepoDir;
    }
  }
  if (cva6RepoDir.empty() || !std::filesystem::exists(cva6RepoDir)) {
    return std::nullopt;
  }

  std::filesystem::path hpdcacheDir;
  if (hpdcacheDirEnv != nullptr && *hpdcacheDirEnv != '\0') {
    hpdcacheDir = hpdcacheDirEnv;
  } else {
    const auto fallbackHpdcacheDir =
        cva6RepoDir / "core" / "cache_subsystem" / "hpdcache";
    if (std::filesystem::exists(fallbackHpdcacheDir)) {
      hpdcacheDir = fallbackHpdcacheDir;
    }
  }
  if (hpdcacheDir.empty() || !std::filesystem::exists(hpdcacheDir)) {
    return std::nullopt;
  }

  std::string targetCfg = "cv64a6_imafdc_sv39";
  if (targetCfgEnv != nullptr && *targetCfgEnv != '\0') {
    targetCfg = targetCfgEnv;
  }

  return Cva6SourceContextForSecTests{
      std::move(cva6RepoDir), std::move(hpdcacheDir), std::move(targetCfg)};
}

std::string substituteCva6FlistVariablesForSecTests(
    std::string text,
    const Cva6SourceContextForSecTests& context) {
  const std::array<std::pair<std::string_view, std::string>, 3> substitutions{{
      {"${CVA6_REPO_DIR}", context.cva6RepoDir.string()},
      {"${HPDCACHE_DIR}", context.hpdcacheDir.string()},
      {"${TARGET_CFG}", context.targetCfg},
  }};

  for (const auto& [needle, replacement] : substitutions) {
    size_t pos = 0;
    while ((pos = text.find(needle, pos)) != std::string::npos) {
      text.replace(pos, needle.size(), replacement);
      pos += replacement.size();
    }
  }
  return text;
}

void collectExpandedSlangArgsFromCommandFileForSecTests(
    const std::filesystem::path& commandFile,
    const Cva6SourceContextForSecTests& context,
    std::unordered_set<std::string>& visitedFiles,
    std::vector<std::string>& args) {
  const auto normalizedPath = std::filesystem::weakly_canonical(commandFile);
  if (!visitedFiles.insert(normalizedPath.string()).second) {
    return;
  }

  std::ifstream input(normalizedPath);
  ASSERT_TRUE(input.good()) << "Failed to read command file: " << normalizedPath.string();

  std::string line;
  while (std::getline(input, line)) {
    line = substituteCva6FlistVariablesForSecTests(line, context);
    const auto commentPos = line.find("//");
    if (commentPos != std::string::npos) {
      line.erase(commentPos);
    }
    const auto first = line.find_first_not_of(" \t\r\n");
    if (first == std::string::npos) {
      continue;
    }
    const auto last = line.find_last_not_of(" \t\r\n");
    line = line.substr(first, last - first + 1);
    if (line.empty()) {
      continue;
    }

    if (line.rfind("-F ", 0) == 0 || line.rfind("-f ", 0) == 0) {
      const auto nestedPath = normalizedPath.parent_path() / line.substr(3);
      collectExpandedSlangArgsFromCommandFileForSecTests(
          nestedPath, context, visitedFiles, args);
      continue;
    }
    args.push_back(std::move(line));
  }
}

SNLSVConstructor::Paths buildExpandedCva6SlangArgsForSecTests(
    const Cva6SourceContextForSecTests& context,
    const std::string& topName,
    const std::vector<std::filesystem::path>& extraSources = {}) {
  const auto flistPath = context.cva6RepoDir / "core" / "Flist.cva6";
  std::unordered_set<std::string> visitedFiles;
  std::vector<std::string> args;
  collectExpandedSlangArgsFromCommandFileForSecTests(
      flistPath, context, visitedFiles, args);
  for (const auto& extraSource : extraSources) {
    args.push_back(extraSource.string());
  }
  args.push_back("--top");
  args.push_back(topName);

  SNLSVConstructor::Paths paths;
  paths.reserve(args.size());
  for (const auto& arg : args) {
    paths.emplace_back(arg);
  }
  return paths;
}

SNLDesign* loadLibertyMemoryModel(
    NLLibrary* primitivesLibrary,
    const std::string& libertyFileName,
    const std::string& cellName) {
  SNLLibertyConstructor constructor(primitivesLibrary);
  constructor.construct(repoRootForSecTests() / "example" / libertyFileName);
  auto* model = primitivesLibrary->getSNLDesign(NLName(cellName));
  if (model == nullptr) {
    throw std::runtime_error("Failed to load Liberty memory model `" + cellName + "`");
  }
  return model;
}

SNLDesign* loadSystemVerilogTopFromSource(
    NLLibrary* designLibrary,
    const std::string& moduleName,
    const std::string& sourceText) {
  const auto svDir =
      std::filesystem::temp_directory_path() / ("sec_sv_" + moduleName);
  std::filesystem::remove_all(svDir);
  std::filesystem::create_directories(svDir);

  const auto svPath = svDir / (moduleName + ".sv");
  std::ofstream svFile(svPath);
  if (!svFile.good()) {
    throw std::runtime_error(
        "Failed to create temporary SystemVerilog source `" +
        svPath.string() + "`");
  }
  svFile << sourceText;
  svFile.close();

  SNLSVConstructor constructor(designLibrary);
  constructor.construct(svPath);
  auto* top = designLibrary->getSNLDesign(NLName(moduleName));
  if (top == nullptr) {
    throw std::runtime_error(
        "Failed to construct SystemVerilog top `" + moduleName + "`");
  }
  return top;
}

SNLDesign* loadSystemVerilogTopFromPaths(
    NLLibrary* designLibrary,
    const std::string& moduleName,
    const SNLSVConstructor::Paths& paths) {
  SNLSVConstructor constructor(designLibrary);
  constructor.construct(paths);
  auto* top = designLibrary->getSNLDesign(NLName(moduleName));
  if (top == nullptr) {
    throw std::runtime_error(
        "Failed to construct SystemVerilog top `" + moduleName + "`");
  }
  return top;
}

SNLDesign* loadRealCva6PerfCountersTargetConfigTopForSecTests(
    NLLibrary* designLibrary,
    const Cva6SourceContextForSecTests& context,
    const std::string& moduleName) {
  const auto svDir = std::filesystem::temp_directory_path() / moduleName;
  std::filesystem::remove_all(svDir);
  std::filesystem::create_directories(svDir);
  const auto wrapperPath = svDir / (moduleName + ".sv");
  std::ofstream wrapperFile(wrapperPath);
  if (!wrapperFile.good()) {
    throw std::runtime_error(
        "Failed to create SEC CVA6 wrapper `" + wrapperPath.string() + "`");
  }
  wrapperFile
      << R"(module )"
      << moduleName
      << R"(
  import ariane_pkg::*;
  import cva6_config_pkg::*;
#(
  parameter config_pkg::cva6_cfg_t CVA6Cfg =
      build_config_pkg::build_config(cva6_cfg)
) ();
  localparam type branchpredict_sbe_t = struct packed {
    cf_t                     cf;
    logic [CVA6Cfg.VLEN-1:0] predict_address;
  };

  localparam type exception_t = struct packed {
    logic [CVA6Cfg.XLEN-1:0]  cause;
    logic [CVA6Cfg.XLEN-1:0]  tval;
    logic [CVA6Cfg.GPLEN-1:0] tval2;
    logic [31:0]              tinst;
    logic                     gva;
    logic                     valid;
  };

  localparam type bp_resolve_t = struct packed {
    logic                    valid;
    logic [CVA6Cfg.VLEN-1:0] pc;
    logic [CVA6Cfg.VLEN-1:0] target_address;
    logic                    is_mispredict;
    logic                    is_taken;
    cf_t                     cf_type;
  };

  localparam type icache_dreq_t = struct packed {
    logic                    req;
    logic                    kill_s1;
    logic                    kill_s2;
    logic                    spec;
    logic [CVA6Cfg.VLEN-1:0] vaddr;
  };

  localparam type cbo_t = logic [7:0];

  localparam type dcache_req_i_t = struct packed {
    logic [CVA6Cfg.DCACHE_INDEX_WIDTH-1:0] address_index;
    logic [CVA6Cfg.DCACHE_TAG_WIDTH-1:0]   address_tag;
    logic [CVA6Cfg.XLEN-1:0]               data_wdata;
    logic [CVA6Cfg.DCACHE_USER_WIDTH-1:0]  data_wuser;
    logic                                  data_req;
    logic                                  data_we;
    logic [(CVA6Cfg.XLEN/8)-1:0]           data_be;
    logic [1:0]                            data_size;
    logic [CVA6Cfg.DcacheIdWidth-1:0]      data_id;
    logic                                  kill_req;
    logic                                  tag_valid;
    cbo_t                                  cbo_op;
  };

  localparam type scoreboard_entry_t = struct packed {
    logic [CVA6Cfg.VLEN-1:0]              pc;
    logic [CVA6Cfg.TRANS_ID_BITS-1:0]     trans_id;
    fu_t                                  fu;
    fu_op                                 op;
    logic [REG_ADDR_SIZE-1:0]             rs1;
    logic [REG_ADDR_SIZE-1:0]             rs2;
    logic [REG_ADDR_SIZE-1:0]             rd;
    logic [CVA6Cfg.XLEN-1:0]              result;
    logic                                 valid;
    logic                                 use_imm;
    logic                                 use_zimm;
    logic                                 use_pc;
    exception_t                           ex;
    branchpredict_sbe_t                   bp;
    logic                                 is_compressed;
    logic                                 is_macro_instr;
    logic                                 is_last_macro_instr;
    logic                                 is_double_rd_macro_instr;
    logic                                 vfp;
    logic                                 is_zcmt;
  };

  logic clk_i;
  logic rst_ni;
  logic debug_mode_i;
  logic [11:0] addr_i;
  logic we_i;
  logic [CVA6Cfg.XLEN-1:0] data_i;
  logic [CVA6Cfg.XLEN-1:0] data_o;
  scoreboard_entry_t [CVA6Cfg.NrCommitPorts-1:0] commit_instr_i;
  logic [CVA6Cfg.NrCommitPorts-1:0] commit_ack_i;
  logic l1_icache_miss_i;
  logic l1_dcache_miss_i;
  logic itlb_miss_i;
  logic dtlb_miss_i;
  logic sb_full_i;
  logic if_empty_i;
  exception_t ex_i;
  logic eret_i;
  bp_resolve_t resolved_branch_i;
  exception_t branch_exceptions_i;
  icache_dreq_t l1_icache_access_i;
  dcache_req_i_t [2:0] l1_dcache_access_i;
  logic [2:0][CVA6Cfg.DCACHE_SET_ASSOC-1:0] miss_vld_bits_i;
  logic i_tlb_flush_i;
  logic stall_issue_i;
  logic [31:0] mcountinhibit_i;

  assign clk_i = 1'b0;
  assign rst_ni = 1'b1;
  assign debug_mode_i = 1'b0;
  assign addr_i = '0;
  assign we_i = 1'b0;
  assign data_i = '0;
  assign commit_instr_i = '0;
  assign commit_ack_i = '0;
  assign l1_icache_miss_i = 1'b0;
  assign l1_dcache_miss_i = 1'b0;
  assign itlb_miss_i = 1'b0;
  assign dtlb_miss_i = 1'b0;
  assign sb_full_i = 1'b0;
  assign if_empty_i = 1'b0;
  assign ex_i = '0;
  assign eret_i = 1'b0;
  assign resolved_branch_i = '0;
  assign branch_exceptions_i = '0;
  assign l1_icache_access_i = '0;
  assign l1_dcache_access_i = '0;
  assign miss_vld_bits_i = '0;
  assign i_tlb_flush_i = 1'b0;
  assign stall_issue_i = 1'b0;
  assign mcountinhibit_i = '0;

  perf_counters #(
    .CVA6Cfg(CVA6Cfg),
    .bp_resolve_t(bp_resolve_t),
    .dcache_req_i_t(dcache_req_i_t),
    .dcache_req_o_t(dcache_req_i_t),
    .exception_t(exception_t),
    .icache_dreq_t(icache_dreq_t),
    .scoreboard_entry_t(scoreboard_entry_t)
  ) dut (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .debug_mode_i(debug_mode_i),
    .addr_i(addr_i),
    .we_i(we_i),
    .data_i(data_i),
    .data_o(data_o),
    .commit_instr_i(commit_instr_i),
    .commit_ack_i(commit_ack_i),
    .l1_icache_miss_i(l1_icache_miss_i),
    .l1_dcache_miss_i(l1_dcache_miss_i),
    .itlb_miss_i(itlb_miss_i),
    .dtlb_miss_i(dtlb_miss_i),
    .sb_full_i(sb_full_i),
    .if_empty_i(if_empty_i),
    .ex_i(ex_i),
    .eret_i(eret_i),
    .resolved_branch_i(resolved_branch_i),
    .branch_exceptions_i(branch_exceptions_i),
    .l1_icache_access_i(l1_icache_access_i),
    .l1_dcache_access_i(l1_dcache_access_i),
    .miss_vld_bits_i(miss_vld_bits_i),
    .i_tlb_flush_i(i_tlb_flush_i),
    .stall_issue_i(stall_issue_i),
    .mcountinhibit_i(mcountinhibit_i)
  );
endmodule
)";
  wrapperFile.close();

  const auto args = buildExpandedCva6SlangArgsForSecTests(
      context, moduleName, {wrapperPath});
  return loadSystemVerilogTopFromPaths(designLibrary, moduleName, args);
}

SNLDesign* createMirroredInstanceTop(
    NLLibrary* library,
    const std::string& name,
    SNLDesign* model) {
  auto* top =
      SNLDesign::create(library, SNLDesign::Type::Standard, NLName(name));
  auto* instance = SNLInstance::create(top, model, NLName("mem0"));

  for (auto* scalarTerm : model->getScalarTerms()) {
    auto* topTerm = SNLScalarTerm::create(
        top, scalarTerm->getDirection(), scalarTerm->getName());
    auto* net = SNLScalarNet::create(
        top, NLName(scalarTerm->getName().getString() + "_net"));
    topTerm->setNet(net);
    instance->getInstTerm(scalarTerm)->setNet(net);
  }

  for (auto* busTerm : model->getBusTerms()) {
    auto* topTerm = SNLBusTerm::create(
        top,
        busTerm->getDirection(),
        busTerm->getMSB(),
        busTerm->getLSB(),
        busTerm->getName());
    auto* net = SNLBusNet::create(
        top,
        busTerm->getMSB(),
        busTerm->getLSB(),
        NLName(busTerm->getName().getString() + "_net"));
    for (int bit = busTerm->getLSB(); bit <= busTerm->getMSB(); ++bit) {
      topTerm->getBit(bit)->setNet(net->getBit(bit));
      instance->getInstTerm(busTerm->getBit(bit))->setNet(net->getBit(bit));
    }
  }

  return top;
}

SNLDesign* createDffTop(
    NLLibrary* library,
    const std::string& name,
    SNLDesign* invModel,
    bool invertData,
    bool invertOutput,
    const std::string& inputName,
    const std::string& outputName,
    const std::string& ffName) {
  auto* top =
      SNLDesign::create(library, SNLDesign::Type::Standard, NLName(name));
  auto* topIn =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName(inputName));
  auto* topClock =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("clk"));
  auto* topOut =
      SNLScalarTerm::create(top, SNLTerm::Direction::Output, NLName(outputName));

  auto* ff = SNLInstance::create(top, NLDB0::getDFF(), NLName(ffName));
  SNLInstance* dataInv = nullptr;
  SNLInstance* outputInv = nullptr;
  if (invertData) {
    dataInv = SNLInstance::create(top, invModel, NLName("inv_data"));
  }
  if (invertOutput) {
    outputInv = SNLInstance::create(top, invModel, NLName("inv_out"));
  }

  auto* netIn = SNLScalarNet::create(top, NLName("net_in"));
  auto* netClock = SNLScalarNet::create(top, NLName("net_clk"));
  auto* netData = SNLScalarNet::create(top, NLName("net_data"));
  auto* netQ = SNLScalarNet::create(top, NLName("net_q"));
  auto* netOut = SNLScalarNet::create(top, NLName("net_out"));

  topIn->setNet(netIn);
  topClock->setNet(netClock);

  if (invertData) {
    dataInv->getInstTerm(invModel->getScalarTerm(NLName("A")))->setNet(netIn);
    dataInv->getInstTerm(invModel->getScalarTerm(NLName("Y")))->setNet(netData);
  }

  ff->getInstTerm(NLDB0::getDFFClock())->setNet(netClock);
  ff->getInstTerm(NLDB0::getDFFData())->setNet(invertData ? netData : netIn);
  ff->getInstTerm(NLDB0::getDFFOutput())->setNet(netQ);

  if (invertOutput) {
    topOut->setNet(netOut);
    outputInv->getInstTerm(invModel->getScalarTerm(NLName("A")))->setNet(netQ);
    outputInv->getInstTerm(invModel->getScalarTerm(NLName("Y")))->setNet(netOut);
  } else {
    topOut->setNet(netQ);
  }

  return top;
}

SNLDesign* createOpaqueBoundaryTop(
    NLLibrary* library,
    const std::string& name,
    SNLDesign* opaqueModel) {
  auto* top =
      SNLDesign::create(library, SNLDesign::Type::Standard, NLName(name));
  auto* topIn =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("in"));
  auto* topOut =
      SNLScalarTerm::create(top, SNLTerm::Direction::Output, NLName("out"));

  auto* opaque = SNLInstance::create(top, opaqueModel, NLName("opaque0"));
  auto* netIn = SNLScalarNet::create(top, NLName("net_in"));
  auto* netOut = SNLScalarNet::create(top, NLName("net_out"));

  topIn->setNet(netIn);
  topOut->setNet(netOut);
  opaque->getInstTerm(opaqueModel->getScalarTerm(NLName("A")))->setNet(netIn);
  opaque->getInstTerm(opaqueModel->getScalarTerm(NLName("Y")))->setNet(netOut);

  return top;
}

SNLDesign* createDffTop(
    NLLibrary* library,
    const std::string& name,
    SNLDesign* invModel,
    bool invertData,
    bool invertOutput,
    const std::string& ffName = "ff0") {
  return createDffTop(
      library, name, invModel, invertData, invertOutput, "in", "out", ffName);
}

SNLDesign* createNamedOutputDffTop(
    NLLibrary* library,
    const std::string& name,
    SNLDesign* invModel,
    const std::string& outputName) {
  return createDffTop(
      library, name, invModel, false, false, "in", outputName, "ff0");
}

SNLDesign* createNamedInputDffTop(
    NLLibrary* library,
    const std::string& name,
    SNLDesign* invModel,
    const std::string& inputName) {
  return createDffTop(
      library, name, invModel, false, false, inputName, "out", "ff0");
}

SNLDesign* createExtraOutputDffTop(
    NLLibrary* library,
    const std::string& name,
    SNLDesign* invModel) {
  auto* top =
      SNLDesign::create(library, SNLDesign::Type::Standard, NLName(name));
  auto* topIn =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("in"));
  auto* topClock =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("clk"));
  auto* topOut =
      SNLScalarTerm::create(top, SNLTerm::Direction::Output, NLName("out"));
  auto* topExtra =
      SNLScalarTerm::create(top, SNLTerm::Direction::Output, NLName("out_extra"));

  auto* ff = SNLInstance::create(top, NLDB0::getDFF(), NLName("ff0"));
  auto* extraInv = SNLInstance::create(top, invModel, NLName("inv_extra"));
  auto* netIn = SNLScalarNet::create(top, NLName("net_in"));
  auto* netClock = SNLScalarNet::create(top, NLName("net_clk"));
  auto* netQ = SNLScalarNet::create(top, NLName("net_q"));
  auto* netExtra = SNLScalarNet::create(top, NLName("net_extra"));

  topIn->setNet(netIn);
  topClock->setNet(netClock);
  topOut->setNet(netQ);
  topExtra->setNet(netExtra);
  ff->getInstTerm(NLDB0::getDFFClock())->setNet(netClock);
  ff->getInstTerm(NLDB0::getDFFData())->setNet(netIn);
  ff->getInstTerm(NLDB0::getDFFOutput())->setNet(netQ);
  extraInv->getInstTerm(invModel->getScalarTerm(NLName("A")))->setNet(netQ);
  extraInv->getInstTerm(invModel->getScalarTerm(NLName("Y")))->setNet(netExtra);

  return top;
}

SNLDesign* createExtraInputDffTop(
    NLLibrary* library,
    const std::string& name) {
  auto* top =
      SNLDesign::create(library, SNLDesign::Type::Standard, NLName(name));
  auto* topIn =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("in"));
  auto* topExtra =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("in_extra"));
  auto* topClock =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("clk"));
  auto* topOut =
      SNLScalarTerm::create(top, SNLTerm::Direction::Output, NLName("out"));

  auto* ff = SNLInstance::create(top, NLDB0::getDFF(), NLName("ff0"));
  auto* netIn = SNLScalarNet::create(top, NLName("net_in"));
  auto* netExtra = SNLScalarNet::create(top, NLName("net_extra"));
  auto* netClock = SNLScalarNet::create(top, NLName("net_clk"));
  auto* netQ = SNLScalarNet::create(top, NLName("net_q"));

  topIn->setNet(netIn);
  topExtra->setNet(netExtra);
  topClock->setNet(netClock);
  topOut->setNet(netQ);
  ff->getInstTerm(NLDB0::getDFFClock())->setNet(netClock);
  ff->getInstTerm(NLDB0::getDFFData())->setNet(netIn);
  ff->getInstTerm(NLDB0::getDFFOutput())->setNet(netQ);

  return top;
}

SNLDesign* createDffeTop(
    NLLibrary* library,
    const std::string& name) {
  auto* top =
      SNLDesign::create(library, SNLDesign::Type::Standard, NLName(name));
  auto* topIn =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("in"));
  auto* topEnable =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("en"));
  auto* topClock =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("clk"));
  auto* topOut =
      SNLScalarTerm::create(top, SNLTerm::Direction::Output, NLName("out"));

  auto* ff = SNLInstance::create(top, NLDB0::getDFFE(), NLName("ff0"));
  auto* netIn = SNLScalarNet::create(top, NLName("net_in"));
  auto* netEnable = SNLScalarNet::create(top, NLName("net_en"));
  auto* netClock = SNLScalarNet::create(top, NLName("net_clk"));
  auto* netQ = SNLScalarNet::create(top, NLName("net_q"));

  topIn->setNet(netIn);
  topEnable->setNet(netEnable);
  topClock->setNet(netClock);
  topOut->setNet(netQ);

  ff->getInstTerm(NLDB0::getDFFEClock())->setNet(netClock);
  ff->getInstTerm(NLDB0::getDFFEData())->setNet(netIn);
  ff->getInstTerm(NLDB0::getDFFEEnable())->setNet(netEnable);
  ff->getInstTerm(NLDB0::getDFFEOutput())->setNet(netQ);

  return top;
}

SNLDesign* createResetInitializedPipelineTop(
    NLLibrary* library,
    const std::string& name,
    bool driveLastStageFromReset,
    const std::vector<std::string>& ffNames);

SNLDesign* createResetInitializedShiftPipelineTopWithStages(
    NLLibrary* library,
    const std::string& name,
    size_t stages);

SNLDesign* createResetInitializedPipelineTop(
    NLLibrary* library,
    const std::string& name,
    bool driveLastStageFromReset) {
  return createResetInitializedPipelineTop(
      library,
      name,
      driveLastStageFromReset,
      {"ff0", "ff1", "ff2"});
}

SNLDesign* createResetInitializedPipelineTop(
    NLLibrary* library,
    const std::string& name,
    bool driveLastStageFromReset,
    const std::vector<std::string>& ffNames) {
  if (ffNames.size() != 3) {
    throw std::invalid_argument(
        "createResetInitializedPipelineTop expects exactly three flop names");
  }

  auto* top =
      SNLDesign::create(library, SNLDesign::Type::Standard, NLName(name));
  auto* topIn =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("in"));
  auto* topResetN =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("rst_n"));
  auto* topClock =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("clk"));
  auto* topOut =
      SNLScalarTerm::create(top, SNLTerm::Direction::Output, NLName("out"));

  auto* ff0 = SNLInstance::create(top, NLDB0::getDFFRN(), NLName(ffNames[0]));
  auto* ff1 = SNLInstance::create(top, NLDB0::getDFFRN(), NLName(ffNames[1]));
  auto* ff2 = SNLInstance::create(top, NLDB0::getDFFRN(), NLName(ffNames[2]));

  auto* netIn = SNLScalarNet::create(top, NLName("net_in"));
  auto* netResetN = SNLScalarNet::create(top, NLName("net_rst_n"));
  auto* netClock = SNLScalarNet::create(top, NLName("net_clk"));
  auto* netQ0 = SNLScalarNet::create(top, NLName("net_q0"));
  auto* netQ1 = SNLScalarNet::create(top, NLName("net_q1"));
  auto* netQ2 = SNLScalarNet::create(top, NLName("net_q2"));

  topIn->setNet(netIn);
  topResetN->setNet(netResetN);
  topClock->setNet(netClock);
  topOut->setNet(netQ0);

  for (auto* ff : {ff0, ff1, ff2}) {
    ff->getInstTerm(NLDB0::getDFFRNClock())->setNet(netClock);
    ff->getInstTerm(NLDB0::getDFFRNResetN())->setNet(netResetN);
  }

  ff0->getInstTerm(NLDB0::getDFFRNData())->setNet(netQ1);
  ff0->getInstTerm(NLDB0::getDFFRNOutput())->setNet(netQ0);
  ff1->getInstTerm(NLDB0::getDFFRNData())->setNet(netQ2);
  ff1->getInstTerm(NLDB0::getDFFRNOutput())->setNet(netQ1);
  ff2->getInstTerm(NLDB0::getDFFRNData())->setNet(
      driveLastStageFromReset ? netResetN : netIn);
  ff2->getInstTerm(NLDB0::getDFFRNOutput())->setNet(netQ2);

  return top;
}

SNLDesign* createResetInitializedShiftPipelineTopWithStages(
    NLLibrary* library,
    const std::string& name,
    size_t stages) {
  if (stages == 0) {
    throw std::invalid_argument(
        "createResetInitializedShiftPipelineTopWithStages expects at least one stage");
  }

  auto* top =
      SNLDesign::create(library, SNLDesign::Type::Standard, NLName(name));
  auto* topIn =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("in"));
  auto* topResetN =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("rst_n"));
  auto* topClock =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("clk"));
  auto* topOut =
      SNLScalarTerm::create(top, SNLTerm::Direction::Output, NLName("out"));

  auto* netIn = SNLScalarNet::create(top, NLName("net_in"));
  auto* netResetN = SNLScalarNet::create(top, NLName("net_rst_n"));
  auto* netClock = SNLScalarNet::create(top, NLName("net_clk"));
  std::vector<SNLScalarNet*> stageNets;
  stageNets.reserve(stages);
  for (size_t i = 0; i < stages; ++i) {
    stageNets.push_back(
        SNLScalarNet::create(top, NLName("net_q" + std::to_string(i))));
  }

  topIn->setNet(netIn);
  topResetN->setNet(netResetN);
  topClock->setNet(netClock);
  topOut->setNet(stageNets.front());

  for (size_t i = 0; i < stages; ++i) {
    auto* ff = SNLInstance::create(
        top, NLDB0::getDFFRN(), NLName("ff" + std::to_string(i)));
    ff->getInstTerm(NLDB0::getDFFRNClock())->setNet(netClock);
    ff->getInstTerm(NLDB0::getDFFRNResetN())->setNet(netResetN);
    ff->getInstTerm(NLDB0::getDFFRNData())->setNet(
        i + 1 == stages ? netIn : stageNets[i + 1]);
    ff->getInstTerm(NLDB0::getDFFRNOutput())->setNet(stageNets[i]);
  }

  return top;
}

SNLDesign* createBootstrapPipelineTopWithStages(
    NLLibrary* library,
    const std::string& name,
    SNLDesign* invModel,
    SNLDesign* andModel,
    size_t stages) {
  auto* top =
      SNLDesign::create(library, SNLDesign::Type::Standard, NLName(name));
  auto* topIn =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("in"));
  auto* topReset =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("rst"));
  auto* topClock =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("clk"));
  auto* topOut =
      SNLScalarTerm::create(top, SNLTerm::Direction::Output, NLName("out"));

  auto* resetInv = SNLInstance::create(top, invModel, NLName("reset_inv"));
  std::vector<SNLInstance*> gates;
  std::vector<SNLInstance*> flops;
  gates.reserve(stages);
  flops.reserve(stages);
  for (size_t i = 0; i < stages; ++i) {
    gates.push_back(
        SNLInstance::create(top, andModel, NLName("gate" + std::to_string(i))));
    flops.push_back(
        SNLInstance::create(top, NLDB0::getDFF(), NLName("ff" + std::to_string(i))));
  }

  auto* netIn = SNLScalarNet::create(top, NLName("net_in"));
  auto* netReset = SNLScalarNet::create(top, NLName("net_rst"));
  auto* netResetN = SNLScalarNet::create(top, NLName("net_rst_n"));
  auto* netClock = SNLScalarNet::create(top, NLName("net_clk"));
  std::vector<SNLScalarNet*> dataNets;
  std::vector<SNLScalarNet*> stateNets;
  dataNets.reserve(stages);
  stateNets.reserve(stages);
  for (size_t i = 0; i < stages; ++i) {
    dataNets.push_back(
        SNLScalarNet::create(top, NLName("net_d" + std::to_string(i))));
    stateNets.push_back(
        SNLScalarNet::create(top, NLName("net_q" + std::to_string(i))));
  }

  topIn->setNet(netIn);
  topReset->setNet(netReset);
  topClock->setNet(netClock);
  topOut->setNet(stateNets.front());

  resetInv->getInstTerm(invModel->getScalarTerm(NLName("A")))->setNet(netReset);
  resetInv->getInstTerm(invModel->getScalarTerm(NLName("Y")))->setNet(netResetN);

  for (size_t i = 0; i < stages; ++i) {
    gates[i]->getInstTerm(andModel->getScalarTerm(NLName("A")))->setNet(
        i + 1 == stages ? netIn : stateNets[i + 1]);
    gates[i]->getInstTerm(andModel->getScalarTerm(NLName("B")))->setNet(netResetN);
    gates[i]->getInstTerm(andModel->getScalarTerm(NLName("Y")))->setNet(dataNets[i]);
  }

  for (auto* ff : flops) {
    ff->getInstTerm(NLDB0::getDFFClock())->setNet(netClock);
  }
  for (size_t i = 0; i < stages; ++i) {
    flops[i]->getInstTerm(NLDB0::getDFFData())->setNet(dataNets[i]);
    flops[i]->getInstTerm(NLDB0::getDFFOutput())->setNet(stateNets[i]);
  }

  return top;
}

SNLDesign* createBootstrapPipelineTop(
    NLLibrary* library,
    const std::string& name,
    SNLDesign* invModel,
    SNLDesign* andModel) {
  return createBootstrapPipelineTopWithStages(library, name, invModel, andModel, 3);
}

SNLDesign* createResetLoadsInputTop(
    NLLibrary* library,
    const std::string& name,
    SNLDesign* invModel,
    SNLDesign* andModel,
    SNLDesign* orModel) {
  auto* top =
      SNLDesign::create(library, SNLDesign::Type::Standard, NLName(name));
  auto* topIn =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("in"));
  auto* topReset =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("rst"));
  auto* topClock =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("clk"));
  auto* topOut =
      SNLScalarTerm::create(top, SNLTerm::Direction::Output, NLName("out"));

  auto* resetInv = SNLInstance::create(top, invModel, NLName("reset_inv"));
  auto* loadData = SNLInstance::create(top, andModel, NLName("load_data"));
  auto* holdData = SNLInstance::create(top, andModel, NLName("hold_data"));
  auto* muxOut = SNLInstance::create(top, orModel, NLName("mux_out"));
  auto* ff = SNLInstance::create(top, NLDB0::getDFF(), NLName("ff0"));

  auto* netIn = SNLScalarNet::create(top, NLName("net_in"));
  auto* netReset = SNLScalarNet::create(top, NLName("net_rst"));
  auto* netResetN = SNLScalarNet::create(top, NLName("net_rst_n"));
  auto* netClock = SNLScalarNet::create(top, NLName("net_clk"));
  auto* netLoad = SNLScalarNet::create(top, NLName("net_load"));
  auto* netHold = SNLScalarNet::create(top, NLName("net_hold"));
  auto* netD = SNLScalarNet::create(top, NLName("net_d"));
  auto* netQ = SNLScalarNet::create(top, NLName("net_q"));

  topIn->setNet(netIn);
  topReset->setNet(netReset);
  topClock->setNet(netClock);
  topOut->setNet(netQ);

  resetInv->getInstTerm(invModel->getScalarTerm(NLName("A")))->setNet(netReset);
  resetInv->getInstTerm(invModel->getScalarTerm(NLName("Y")))->setNet(netResetN);

  loadData->getInstTerm(andModel->getScalarTerm(NLName("A")))->setNet(netReset);
  loadData->getInstTerm(andModel->getScalarTerm(NLName("B")))->setNet(netIn);
  loadData->getInstTerm(andModel->getScalarTerm(NLName("Y")))->setNet(netLoad);

  holdData->getInstTerm(andModel->getScalarTerm(NLName("A")))->setNet(netResetN);
  holdData->getInstTerm(andModel->getScalarTerm(NLName("B")))->setNet(netQ);
  holdData->getInstTerm(andModel->getScalarTerm(NLName("Y")))->setNet(netHold);

  muxOut->getInstTerm(orModel->getScalarTerm(NLName("A")))->setNet(netLoad);
  muxOut->getInstTerm(orModel->getScalarTerm(NLName("B")))->setNet(netHold);
  muxOut->getInstTerm(orModel->getScalarTerm(NLName("Y")))->setNet(netD);

  ff->getInstTerm(NLDB0::getDFFClock())->setNet(netClock);
  ff->getInstTerm(NLDB0::getDFFData())->setNet(netD);
  ff->getInstTerm(NLDB0::getDFFOutput())->setNet(netQ);

  return top;
}

SNLDesign* createResetLoadsInputTwoStageTop(
    NLLibrary* library,
    const std::string& name,
    SNLDesign* invModel,
    SNLDesign* andModel,
    SNLDesign* orModel) {
  auto* top =
      SNLDesign::create(library, SNLDesign::Type::Standard, NLName(name));
  auto* topIn =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("in"));
  auto* topReset =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("rst"));
  auto* topClock =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("clk"));
  auto* topOut =
      SNLScalarTerm::create(top, SNLTerm::Direction::Output, NLName("out"));

  auto* resetInv = SNLInstance::create(top, invModel, NLName("reset_inv"));
  auto* loadData = SNLInstance::create(top, andModel, NLName("load_data"));
  auto* holdData = SNLInstance::create(top, andModel, NLName("hold_data"));
  auto* muxOut = SNLInstance::create(top, orModel, NLName("mux_out"));
  auto* ffHidden = SNLInstance::create(top, NLDB0::getDFF(), NLName("ff_hidden"));
  auto* ffOut = SNLInstance::create(top, NLDB0::getDFF(), NLName("ff_out"));

  auto* netIn = SNLScalarNet::create(top, NLName("net_in"));
  auto* netReset = SNLScalarNet::create(top, NLName("net_rst"));
  auto* netResetN = SNLScalarNet::create(top, NLName("net_rst_n"));
  auto* netClock = SNLScalarNet::create(top, NLName("net_clk"));
  auto* netLoad = SNLScalarNet::create(top, NLName("net_load"));
  auto* netHold = SNLScalarNet::create(top, NLName("net_hold"));
  auto* netHiddenD = SNLScalarNet::create(top, NLName("net_hidden_d"));
  auto* netHiddenQ = SNLScalarNet::create(top, NLName("net_hidden_q"));
  auto* netOutQ = SNLScalarNet::create(top, NLName("net_out_q"));

  topIn->setNet(netIn);
  topReset->setNet(netReset);
  topClock->setNet(netClock);
  topOut->setNet(netOutQ);

  resetInv->getInstTerm(invModel->getScalarTerm(NLName("A")))->setNet(netReset);
  resetInv->getInstTerm(invModel->getScalarTerm(NLName("Y")))->setNet(netResetN);

  loadData->getInstTerm(andModel->getScalarTerm(NLName("A")))->setNet(netReset);
  loadData->getInstTerm(andModel->getScalarTerm(NLName("B")))->setNet(netIn);
  loadData->getInstTerm(andModel->getScalarTerm(NLName("Y")))->setNet(netLoad);

  holdData->getInstTerm(andModel->getScalarTerm(NLName("A")))->setNet(netResetN);
  holdData->getInstTerm(andModel->getScalarTerm(NLName("B")))->setNet(netHiddenQ);
  holdData->getInstTerm(andModel->getScalarTerm(NLName("Y")))->setNet(netHold);

  muxOut->getInstTerm(orModel->getScalarTerm(NLName("A")))->setNet(netLoad);
  muxOut->getInstTerm(orModel->getScalarTerm(NLName("B")))->setNet(netHold);
  muxOut->getInstTerm(orModel->getScalarTerm(NLName("Y")))->setNet(netHiddenD);

  for (auto* ff : {ffHidden, ffOut}) {
    ff->getInstTerm(NLDB0::getDFFClock())->setNet(netClock);
  }
  ffHidden->getInstTerm(NLDB0::getDFFData())->setNet(netHiddenD);
  ffHidden->getInstTerm(NLDB0::getDFFOutput())->setNet(netHiddenQ);
  ffOut->getInstTerm(NLDB0::getDFFData())->setNet(netHiddenQ);
  ffOut->getInstTerm(NLDB0::getDFFOutput())->setNet(netOutQ);

  return top;
}

SNLDesign* createResetLoadsInputShiftPipelineTopWithStages(
    NLLibrary* library,
    const std::string& name,
    SNLDesign* invModel,
    SNLDesign* andModel,
    SNLDesign* orModel,
    size_t stages) {
  auto* top =
      SNLDesign::create(library, SNLDesign::Type::Standard, NLName(name));
  auto* topIn =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("in"));
  auto* topReset =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("rst"));
  auto* topClock =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("clk"));
  auto* topOut =
      SNLScalarTerm::create(top, SNLTerm::Direction::Output, NLName("out"));

  auto* resetInv = SNLInstance::create(top, invModel, NLName("reset_inv"));
  auto* loadData = SNLInstance::create(top, andModel, NLName("load_data"));
  auto* holdData = SNLInstance::create(top, andModel, NLName("hold_data"));
  auto* muxOut = SNLInstance::create(top, orModel, NLName("mux_out"));

  std::vector<SNLInstance*> flops;
  flops.reserve(stages);
  for (size_t i = 0; i < stages; ++i) {
    flops.push_back(
        SNLInstance::create(top, NLDB0::getDFF(), NLName("ff" + std::to_string(i))));
  }

  auto* netIn = SNLScalarNet::create(top, NLName("net_in"));
  auto* netReset = SNLScalarNet::create(top, NLName("net_rst"));
  auto* netResetN = SNLScalarNet::create(top, NLName("net_rst_n"));
  auto* netClock = SNLScalarNet::create(top, NLName("net_clk"));
  auto* netLoad = SNLScalarNet::create(top, NLName("net_load"));
  auto* netHold = SNLScalarNet::create(top, NLName("net_hold"));
  auto* netLastD = SNLScalarNet::create(top, NLName("net_last_d"));
  std::vector<SNLScalarNet*> stateNets;
  stateNets.reserve(stages);
  for (size_t i = 0; i < stages; ++i) {
    stateNets.push_back(
        SNLScalarNet::create(top, NLName("net_q" + std::to_string(i))));
  }

  topIn->setNet(netIn);
  topReset->setNet(netReset);
  topClock->setNet(netClock);
  topOut->setNet(stateNets.front());

  resetInv->getInstTerm(invModel->getScalarTerm(NLName("A")))->setNet(netReset);
  resetInv->getInstTerm(invModel->getScalarTerm(NLName("Y")))->setNet(netResetN);

  loadData->getInstTerm(andModel->getScalarTerm(NLName("A")))->setNet(netReset);
  loadData->getInstTerm(andModel->getScalarTerm(NLName("B")))->setNet(netIn);
  loadData->getInstTerm(andModel->getScalarTerm(NLName("Y")))->setNet(netLoad);

  holdData->getInstTerm(andModel->getScalarTerm(NLName("A")))->setNet(netResetN);
  holdData->getInstTerm(andModel->getScalarTerm(NLName("B")))->setNet(stateNets.back());
  holdData->getInstTerm(andModel->getScalarTerm(NLName("Y")))->setNet(netHold);

  muxOut->getInstTerm(orModel->getScalarTerm(NLName("A")))->setNet(netLoad);
  muxOut->getInstTerm(orModel->getScalarTerm(NLName("B")))->setNet(netHold);
  muxOut->getInstTerm(orModel->getScalarTerm(NLName("Y")))->setNet(netLastD);

  for (auto* ff : flops) {
    ff->getInstTerm(NLDB0::getDFFClock())->setNet(netClock);
  }
  for (size_t i = 0; i + 1 < stages; ++i) {
    flops[i]->getInstTerm(NLDB0::getDFFData())->setNet(stateNets[i + 1]);
    flops[i]->getInstTerm(NLDB0::getDFFOutput())->setNet(stateNets[i]);
  }
  flops.back()->getInstTerm(NLDB0::getDFFData())->setNet(netLastD);
  flops.back()->getInstTerm(NLDB0::getDFFOutput())->setNet(stateNets.back());

  return top;
}

SNLDesign* createDffQnModel(NLLibrary* library) {
  auto* model =
      SNLDesign::create(library, SNLDesign::Type::Primitive, NLName("DFF_Q_QN"));
  auto* data =
      SNLScalarTerm::create(model, SNLTerm::Direction::Input, NLName("D"));
  auto* clock =
      SNLScalarTerm::create(model, SNLTerm::Direction::Input, NLName("CK"));
  auto* q =
      SNLScalarTerm::create(model, SNLTerm::Direction::Output, NLName("Q"));
  auto* qn =
      SNLScalarTerm::create(model, SNLTerm::Direction::Output, NLName("QN"));
  SNLDesignModeling::addInputsToClockArcs({data}, clock);
  SNLDesignModeling::addClockToOutputsArcs(clock, {q, qn});
  return model;
}

SNLDesign* createNamedComplementSequentialModel(
    NLLibrary* library,
    const std::string& name,
    const std::string& primaryPinName,
    const std::string& complementPinName) {
  auto* model =
      SNLDesign::create(library, SNLDesign::Type::Primitive, NLName(name));
  auto* data =
      SNLScalarTerm::create(model, SNLTerm::Direction::Input, NLName("D"));
  auto* clock =
      SNLScalarTerm::create(model, SNLTerm::Direction::Input, NLName("CK"));
  auto* primary = SNLScalarTerm::create(
      model, SNLTerm::Direction::Output, NLName(primaryPinName));
  auto* complement = SNLScalarTerm::create(
      model, SNLTerm::Direction::Output, NLName(complementPinName));
  SNLDesignModeling::addInputsToClockArcs({data}, clock);
  SNLDesignModeling::addClockToOutputsArcs(clock, {primary, complement});
  return model;
}

SNLDesign* createComplementFirstSequentialModel(
    NLLibrary* library,
    const std::string& name,
    const std::string& primaryPinName,
    const std::string& complementPinName) {
  auto* model =
      SNLDesign::create(library, SNLDesign::Type::Primitive, NLName(name));
  auto* data =
      SNLScalarTerm::create(model, SNLTerm::Direction::Input, NLName("D"));
  auto* clock =
      SNLScalarTerm::create(model, SNLTerm::Direction::Input, NLName("CK"));
  auto* complement = SNLScalarTerm::create(
      model, SNLTerm::Direction::Output, NLName(complementPinName));
  auto* primary = SNLScalarTerm::create(
      model, SNLTerm::Direction::Output, NLName(primaryPinName));
  SNLDesignModeling::addInputsToClockArcs({data}, clock);
  SNLDesignModeling::addClockToOutputsArcs(clock, {primary, complement});
  return model;
}

SNLDesign* createSetOnlySequentialModel(NLLibrary* library,
                                        const std::string& name) {
  auto* model =
      SNLDesign::create(library, SNLDesign::Type::Primitive, NLName(name));
  auto* data =
      SNLScalarTerm::create(model, SNLTerm::Direction::Input, NLName("D"));
  auto* set =
      SNLScalarTerm::create(model, SNLTerm::Direction::Input, NLName("S"));
  auto* clock =
      SNLScalarTerm::create(model, SNLTerm::Direction::Input, NLName("CK"));
  auto* output =
      SNLScalarTerm::create(model, SNLTerm::Direction::Output, NLName("Q"));
  SNLDesignModeling::addInputsToClockArcs({data, set}, clock);
  SNLDesignModeling::addClockToOutputsArcs(clock, {output});
  return model;
}

SNLDesign* createBusSequentialModel(NLLibrary* library,
                                    const std::string& name) {
  auto* model =
      SNLDesign::create(library, SNLDesign::Type::Primitive, NLName(name));
  auto* data = SNLBusTerm::create(
      model, SNLTerm::Direction::Input, 1, 0, NLName("D"));
  auto* clock =
      SNLScalarTerm::create(model, SNLTerm::Direction::Input, NLName("CK"));
  auto* output = SNLBusTerm::create(
      model, SNLTerm::Direction::Output, 1, 0, NLName("Q"));
  SNLDesignModeling::addInputsToClockArcs(collectBitTerms(data), clock);
  SNLDesignModeling::addClockToOutputsArcs(clock, collectBitTerms(output));
  return model;
}

SNLDesign* createNoDataSequentialModel(NLLibrary* library,
                                       const std::string& name) {
  auto* model =
      SNLDesign::create(library, SNLDesign::Type::Primitive, NLName(name));
  auto* clock =
      SNLScalarTerm::create(model, SNLTerm::Direction::Input, NLName("CK"));
  auto* output =
      SNLScalarTerm::create(model, SNLTerm::Direction::Output, NLName("Q"));
  SNLDesignModeling::addClockToOutputsArcs(clock, {output});
  return model;
}

SNLDesign* createExtraUpdatePinSequentialModel(NLLibrary* library,
                                               const std::string& name) {
  auto* model =
      SNLDesign::create(library, SNLDesign::Type::Primitive, NLName(name));
  auto* data =
      SNLScalarTerm::create(model, SNLTerm::Direction::Input, NLName("D"));
  auto* address =
      SNLScalarTerm::create(model, SNLTerm::Direction::Input, NLName("A"));
  auto* clock =
      SNLScalarTerm::create(model, SNLTerm::Direction::Input, NLName("CK"));
  auto* output =
      SNLScalarTerm::create(model, SNLTerm::Direction::Output, NLName("Q"));
  SNLDesignModeling::addInputsToClockArcs({data, address}, clock);
  SNLDesignModeling::addClockToOutputsArcs(clock, {output});
  return model;
}

SNLDesign* createResetSetSequentialModel(NLLibrary* library,
                                         const std::string& name) {
  auto* model =
      SNLDesign::create(library, SNLDesign::Type::Primitive, NLName(name));
  auto* data =
      SNLScalarTerm::create(model, SNLTerm::Direction::Input, NLName("D"));
  auto* reset =
      SNLScalarTerm::create(model, SNLTerm::Direction::Input, NLName("R"));
  auto* set =
      SNLScalarTerm::create(model, SNLTerm::Direction::Input, NLName("S"));
  auto* clock =
      SNLScalarTerm::create(model, SNLTerm::Direction::Input, NLName("CK"));
  auto* output =
      SNLScalarTerm::create(model, SNLTerm::Direction::Output, NLName("Q"));
  SNLDesignModeling::addInputsToClockArcs({data, reset, set}, clock);
  SNLDesignModeling::addClockToOutputsArcs(clock, {output});
  return model;
}

SNLDesign* createNamedComplementSetSequentialModel(
    NLLibrary* library,
    const std::string& name,
    const std::string& primaryPinName,
    const std::string& complementPinName) {
  auto* model =
      SNLDesign::create(library, SNLDesign::Type::Primitive, NLName(name));
  auto* data =
      SNLScalarTerm::create(model, SNLTerm::Direction::Input, NLName("D"));
  auto* set =
      SNLScalarTerm::create(model, SNLTerm::Direction::Input, NLName("S"));
  auto* clock =
      SNLScalarTerm::create(model, SNLTerm::Direction::Input, NLName("CK"));
  auto* primary = SNLScalarTerm::create(
      model, SNLTerm::Direction::Output, NLName(primaryPinName));
  auto* complement = SNLScalarTerm::create(
      model, SNLTerm::Direction::Output, NLName(complementPinName));
  SNLDesignModeling::addInputsToClockArcs({data, set}, clock);
  SNLDesignModeling::addClockToOutputsArcs(clock, {primary, complement});
  return model;
}

SNLDesign* createSequentialOutputPairTop(
    NLLibrary* library,
    const std::string& name,
    SNLDesign* sequentialModel,
    const std::string& primaryPinName,
    const std::string& secondaryPinName) {
  auto* top =
      SNLDesign::create(library, SNLDesign::Type::Standard, NLName(name));
  auto* topIn =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("in"));
  auto* topClock =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("clk"));
  auto* topPrimary =
      SNLScalarTerm::create(top, SNLTerm::Direction::Output, NLName("out_primary"));
  auto* topSecondary = SNLScalarTerm::create(
      top, SNLTerm::Direction::Output, NLName("out_secondary"));

  auto* seq = SNLInstance::create(top, sequentialModel, NLName("ff0"));
  auto* netIn = SNLScalarNet::create(top, NLName("net_in"));
  auto* netClock = SNLScalarNet::create(top, NLName("net_clk"));
  auto* netPrimary = SNLScalarNet::create(top, NLName("net_primary"));
  auto* netSecondary = SNLScalarNet::create(top, NLName("net_secondary"));

  topIn->setNet(netIn);
  topClock->setNet(netClock);
  topPrimary->setNet(netPrimary);
  topSecondary->setNet(netSecondary);

  seq->getInstTerm(sequentialModel->getScalarTerm(NLName("D")))->setNet(netIn);
  seq->getInstTerm(sequentialModel->getScalarTerm(NLName("CK")))->setNet(netClock);
  seq->getInstTerm(sequentialModel->getScalarTerm(NLName(primaryPinName)))->setNet(
      netPrimary);
  seq->getInstTerm(sequentialModel->getScalarTerm(NLName(secondaryPinName)))->setNet(
      netSecondary);

  return top;
}

SNLDesign* createSetOnlySequentialTop(
    NLLibrary* library,
    const std::string& name,
    SNLDesign* sequentialModel) {
  auto* top =
      SNLDesign::create(library, SNLDesign::Type::Standard, NLName(name));
  auto* topIn =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("in"));
  auto* topSet =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("set"));
  auto* topClock =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("clk"));
  auto* topOut =
      SNLScalarTerm::create(top, SNLTerm::Direction::Output, NLName("out"));

  auto* seq = SNLInstance::create(top, sequentialModel, NLName("ff0"));
  auto* netIn = SNLScalarNet::create(top, NLName("net_in"));
  auto* netSet = SNLScalarNet::create(top, NLName("net_set"));
  auto* netClock = SNLScalarNet::create(top, NLName("net_clk"));
  auto* netOut = SNLScalarNet::create(top, NLName("net_out"));

  topIn->setNet(netIn);
  topSet->setNet(netSet);
  topClock->setNet(netClock);
  topOut->setNet(netOut);

  seq->getInstTerm(sequentialModel->getScalarTerm(NLName("D")))->setNet(netIn);
  seq->getInstTerm(sequentialModel->getScalarTerm(NLName("S")))->setNet(netSet);
  seq->getInstTerm(sequentialModel->getScalarTerm(NLName("CK")))->setNet(netClock);
  seq->getInstTerm(sequentialModel->getScalarTerm(NLName("Q")))->setNet(netOut);

  return top;
}

SNLDesign* createBusSequentialTop(
    NLLibrary* library,
    const std::string& name,
    SNLDesign* sequentialModel) {
  auto* top =
      SNLDesign::create(library, SNLDesign::Type::Standard, NLName(name));
  auto* topIn = SNLBusTerm::create(
      top, SNLTerm::Direction::Input, 1, 0, NLName("in"));
  auto* topClock =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("clk"));
  auto* topOut = SNLBusTerm::create(
      top, SNLTerm::Direction::Output, 1, 0, NLName("out"));

  auto* seq = SNLInstance::create(top, sequentialModel, NLName("ff0"));
  auto* netIn = SNLBusNet::create(top, 1, 0, NLName("net_in"));
  auto* netClock = SNLScalarNet::create(top, NLName("net_clk"));
  auto* netOut = SNLBusNet::create(top, 1, 0, NLName("net_out"));

  topClock->setNet(netClock);
  seq->getInstTerm(sequentialModel->getScalarTerm(NLName("CK")))->setNet(netClock);

  auto* modelData = sequentialModel->getBusTerm(NLName("D"));
  auto* modelOutput = sequentialModel->getBusTerm(NLName("Q"));
  for (int bit = 0; bit <= 1; ++bit) {
    topIn->getBit(bit)->setNet(netIn->getBit(bit));
    topOut->getBit(bit)->setNet(netOut->getBit(bit));
    seq->getInstTerm(modelData->getBit(bit))->setNet(netIn->getBit(bit));
    seq->getInstTerm(modelOutput->getBit(bit))->setNet(netOut->getBit(bit));
  }

  return top;
}

SNLDesign* createComplementedSetSequentialTop(
    NLLibrary* library,
    const std::string& name,
    SNLDesign* sequentialModel,
    const std::string& primaryPinName,
    const std::string& complementPinName) {
  auto* top =
      SNLDesign::create(library, SNLDesign::Type::Standard, NLName(name));
  auto* topIn =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("in"));
  auto* topSet =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("set"));
  auto* topClock =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("clk"));
  auto* topPrimary =
      SNLScalarTerm::create(top, SNLTerm::Direction::Output, NLName("out_primary"));
  auto* topSecondary = SNLScalarTerm::create(
      top, SNLTerm::Direction::Output, NLName("out_secondary"));

  auto* seq = SNLInstance::create(top, sequentialModel, NLName("ff0"));
  auto* netIn = SNLScalarNet::create(top, NLName("net_in"));
  auto* netSet = SNLScalarNet::create(top, NLName("net_set"));
  auto* netClock = SNLScalarNet::create(top, NLName("net_clk"));
  auto* netPrimary = SNLScalarNet::create(top, NLName("net_primary"));
  auto* netSecondary = SNLScalarNet::create(top, NLName("net_secondary"));

  topIn->setNet(netIn);
  topSet->setNet(netSet);
  topClock->setNet(netClock);
  topPrimary->setNet(netPrimary);
  topSecondary->setNet(netSecondary);

  seq->getInstTerm(sequentialModel->getScalarTerm(NLName("D")))->setNet(netIn);
  seq->getInstTerm(sequentialModel->getScalarTerm(NLName("S")))->setNet(netSet);
  seq->getInstTerm(sequentialModel->getScalarTerm(NLName("CK")))->setNet(netClock);
  seq->getInstTerm(sequentialModel->getScalarTerm(NLName(primaryPinName)))->setNet(
      netPrimary);
  seq->getInstTerm(sequentialModel->getScalarTerm(NLName(complementPinName)))->setNet(
      netSecondary);

  return top;
}

SNLDesign* createNoDataSequentialTop(
    NLLibrary* library,
    const std::string& name,
    SNLDesign* sequentialModel) {
  auto* top =
      SNLDesign::create(library, SNLDesign::Type::Standard, NLName(name));
  auto* topClock =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("clk"));
  auto* topOut =
      SNLScalarTerm::create(top, SNLTerm::Direction::Output, NLName("out"));

  auto* seq = SNLInstance::create(top, sequentialModel, NLName("ff0"));
  auto* netClock = SNLScalarNet::create(top, NLName("net_clk"));
  auto* netOut = SNLScalarNet::create(top, NLName("net_out"));

  topClock->setNet(netClock);
  topOut->setNet(netOut);

  seq->getInstTerm(sequentialModel->getScalarTerm(NLName("CK")))->setNet(netClock);
  seq->getInstTerm(sequentialModel->getScalarTerm(NLName("Q")))->setNet(netOut);

  return top;
}

SNLDesign* createExtraUpdatePinSequentialTop(
    NLLibrary* library,
    const std::string& name,
    SNLDesign* sequentialModel) {
  auto* top =
      SNLDesign::create(library, SNLDesign::Type::Standard, NLName(name));
  auto* topIn =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("in"));
  auto* topAddr =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("addr"));
  auto* topClock =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("clk"));
  auto* topOut =
      SNLScalarTerm::create(top, SNLTerm::Direction::Output, NLName("out"));

  auto* seq = SNLInstance::create(top, sequentialModel, NLName("ff0"));
  auto* netIn = SNLScalarNet::create(top, NLName("net_in"));
  auto* netAddr = SNLScalarNet::create(top, NLName("net_addr"));
  auto* netClock = SNLScalarNet::create(top, NLName("net_clk"));
  auto* netOut = SNLScalarNet::create(top, NLName("net_out"));

  topIn->setNet(netIn);
  topAddr->setNet(netAddr);
  topClock->setNet(netClock);
  topOut->setNet(netOut);

  seq->getInstTerm(sequentialModel->getScalarTerm(NLName("D")))->setNet(netIn);
  seq->getInstTerm(sequentialModel->getScalarTerm(NLName("A")))->setNet(netAddr);
  seq->getInstTerm(sequentialModel->getScalarTerm(NLName("CK")))->setNet(netClock);
  seq->getInstTerm(sequentialModel->getScalarTerm(NLName("Q")))->setNet(netOut);

  return top;
}

SNLDesign* createPartialCoverageNoDriverTop(
    NLLibrary* library,
    const std::string& name) {
  auto* top =
      SNLDesign::create(library, SNLDesign::Type::Standard, NLName(name));
  auto* topIn =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("in"));
  auto* topClock =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("clk"));
  auto* topGood =
      SNLScalarTerm::create(top, SNLTerm::Direction::Output, NLName("good"));
  auto* topBad =
      SNLScalarTerm::create(top, SNLTerm::Direction::Output, NLName("bad"));

  auto* ff = SNLInstance::create(top, NLDB0::getDFF(), NLName("ff0"));
  auto* netIn = SNLScalarNet::create(top, NLName("net_in"));
  auto* netClock = SNLScalarNet::create(top, NLName("net_clk"));
  auto* netData = SNLScalarNet::create(top, NLName("net_data"));
  auto* netQ = SNLScalarNet::create(top, NLName("net_q"));

  topIn->setNet(netIn);
  topClock->setNet(netClock);
  topGood->setNet(netIn);
  topBad->setNet(netQ);

  ff->getInstTerm(NLDB0::getDFFClock())->setNet(netClock);
  ff->getInstTerm(NLDB0::getDFFData())->setNet(netData);
  ff->getInstTerm(NLDB0::getDFFOutput())->setNet(netQ);

  return top;
}

SNLDesign* createPartialCoverageMultiDriverTop(
    NLLibrary* library,
    const std::string& name,
    SNLDesign* invModel) {
  auto* top =
      SNLDesign::create(library, SNLDesign::Type::Standard, NLName(name));
  auto* topInA =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("in_a"));
  auto* topInB =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("in_b"));
  auto* topClock =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("clk"));
  auto* topGood =
      SNLScalarTerm::create(top, SNLTerm::Direction::Output, NLName("good"));
  auto* topBad =
      SNLScalarTerm::create(top, SNLTerm::Direction::Output, NLName("bad"));

  auto* inv0 = SNLInstance::create(top, invModel, NLName("inv0"));
  auto* inv1 = SNLInstance::create(top, invModel, NLName("inv1"));
  auto* ff = SNLInstance::create(top, NLDB0::getDFF(), NLName("ff0"));
  auto* netInA = SNLScalarNet::create(top, NLName("net_in_a"));
  auto* netInB = SNLScalarNet::create(top, NLName("net_in_b"));
  auto* netClock = SNLScalarNet::create(top, NLName("net_clk"));
  auto* netMulti = SNLScalarNet::create(top, NLName("net_multi"));
  auto* netQ = SNLScalarNet::create(top, NLName("net_q"));

  topInA->setNet(netInA);
  topInB->setNet(netInB);
  topClock->setNet(netClock);
  topGood->setNet(netInA);
  topBad->setNet(netQ);

  inv0->getInstTerm(invModel->getScalarTerm(NLName("A")))->setNet(netInA);
  inv0->getInstTerm(invModel->getScalarTerm(NLName("Y")))->setNet(netMulti);
  inv1->getInstTerm(invModel->getScalarTerm(NLName("A")))->setNet(netInB);
  inv1->getInstTerm(invModel->getScalarTerm(NLName("Y")))->setNet(netMulti);

  ff->getInstTerm(NLDB0::getDFFClock())->setNet(netClock);
  ff->getInstTerm(NLDB0::getDFFData())->setNet(netMulti);
  ff->getInstTerm(NLDB0::getDFFOutput())->setNet(netQ);

  return top;
}

SNLDesign* createPartialCoverageLogicalLoopTop(
    NLLibrary* library,
    const std::string& name) {
  auto* top =
      SNLDesign::create(library, SNLDesign::Type::Standard, NLName(name));
  auto* topIn =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("in"));
  auto* topSel =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("sel"));
  auto* topClock =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("clk"));
  auto* topGood =
      SNLScalarTerm::create(top, SNLTerm::Direction::Output, NLName("good"));
  auto* topBad =
      SNLScalarTerm::create(top, SNLTerm::Direction::Output, NLName("bad"));

  auto* assign = SNLInstance::create(top, NLDB0::getAssign(), NLName("assign0"));
  auto* mux = SNLInstance::create(top, NLDB0::getMux2(), NLName("mux0"));
  auto* ff = SNLInstance::create(top, NLDB0::getDFF(), NLName("ff0"));
  auto* netIn = SNLScalarNet::create(top, NLName("net_in"));
  auto* netSel = SNLScalarNet::create(top, NLName("net_sel"));
  auto* netClock = SNLScalarNet::create(top, NLName("net_clk"));
  auto* netLoopSeed = SNLScalarNet::create(top, NLName("net_loop_seed"));
  auto* netLoopIn = SNLScalarNet::create(top, NLName("net_loop_in"));
  auto* netQ = SNLScalarNet::create(top, NLName("net_q"));

  topIn->setNet(netIn);
  topSel->setNet(netSel);
  topClock->setNet(netClock);
  topGood->setNet(netIn);
  topBad->setNet(netQ);

  assign->getInstTerm(NLDB0::getAssignInput())->setNet(netLoopIn);
  assign->getInstTerm(NLDB0::getAssignOutput())->setNet(netLoopSeed);

  mux->getInstTerm(NLDB0::getMux2InputA()->getBit(0))->setNet(netLoopSeed);
  mux->getInstTerm(NLDB0::getMux2InputB()->getBit(0))->setNet(netIn);
  mux->getInstTerm(NLDB0::getMux2Select())->setNet(netSel);
  mux->getInstTerm(NLDB0::getMux2Output()->getBit(0))->setNet(netLoopIn);

  ff->getInstTerm(NLDB0::getDFFClock())->setNet(netClock);
  ff->getInstTerm(NLDB0::getDFFData())->setNet(netLoopSeed);
  ff->getInstTerm(NLDB0::getDFFOutput())->setNet(netQ);

  return top;
}

SNLDesign* createUnsupportedPrimitiveCoverageTop(
    NLLibrary* library,
    const std::string& name,
    SNLDesign* sequentialModel) {
  auto* top =
      SNLDesign::create(library, SNLDesign::Type::Standard, NLName(name));
  auto* topIn =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("in"));
  auto* topClock =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("clk"));
  auto* topGood =
      SNLScalarTerm::create(top, SNLTerm::Direction::Output, NLName("good"));
  auto* topBad =
      SNLScalarTerm::create(top, SNLTerm::Direction::Output, NLName("bad"));

  auto* seq = SNLInstance::create(top, sequentialModel, NLName("ff0"));
  auto* netIn = SNLScalarNet::create(top, NLName("net_in"));
  auto* netClock = SNLScalarNet::create(top, NLName("net_clk"));
  auto* netOut = SNLScalarNet::create(top, NLName("net_out"));

  topIn->setNet(netIn);
  topClock->setNet(netClock);
  topGood->setNet(netIn);
  topBad->setNet(netOut);

  seq->getInstTerm(sequentialModel->getScalarTerm(NLName("CK")))->setNet(netClock);
  seq->getInstTerm(sequentialModel->getScalarTerm(NLName("Q")))->setNet(netOut);

  return top;
}

SNLDesign* createCombinationalInvTop(NLLibrary* library,
                                     const std::string& name,
                                     SNLDesign* invModel) {
  auto* top =
      SNLDesign::create(library, SNLDesign::Type::Standard, NLName(name));
  auto* topIn =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("in"));
  auto* topOut =
      SNLScalarTerm::create(top, SNLTerm::Direction::Output, NLName("out"));

  auto* inv = SNLInstance::create(top, invModel, NLName("inv0"));
  auto* netIn = SNLScalarNet::create(top, NLName("net_in"));
  auto* netOut = SNLScalarNet::create(top, NLName("net_out"));

  topIn->setNet(netIn);
  topOut->setNet(netOut);
  inv->getInstTerm(invModel->getScalarTerm(NLName("A")))->setNet(netIn);
  inv->getInstTerm(invModel->getScalarTerm(NLName("Y")))->setNet(netOut);

  return top;
}

SNLDesign* createResetSetSequentialTop(
    NLLibrary* library,
    const std::string& name,
    SNLDesign* sequentialModel) {
  auto* top =
      SNLDesign::create(library, SNLDesign::Type::Standard, NLName(name));
  auto* topIn =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("in"));
  auto* topReset =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("rst"));
  auto* topSet =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("set"));
  auto* topClock =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("clk"));
  auto* topOut =
      SNLScalarTerm::create(top, SNLTerm::Direction::Output, NLName("out"));

  auto* seq = SNLInstance::create(top, sequentialModel, NLName("ff0"));
  auto* netIn = SNLScalarNet::create(top, NLName("net_in"));
  auto* netReset = SNLScalarNet::create(top, NLName("net_rst"));
  auto* netSet = SNLScalarNet::create(top, NLName("net_set"));
  auto* netClock = SNLScalarNet::create(top, NLName("net_clk"));
  auto* netOut = SNLScalarNet::create(top, NLName("net_out"));

  topIn->setNet(netIn);
  topReset->setNet(netReset);
  topSet->setNet(netSet);
  topClock->setNet(netClock);
  topOut->setNet(netOut);

  seq->getInstTerm(sequentialModel->getScalarTerm(NLName("D")))->setNet(netIn);
  seq->getInstTerm(sequentialModel->getScalarTerm(NLName("R")))->setNet(netReset);
  seq->getInstTerm(sequentialModel->getScalarTerm(NLName("S")))->setNet(netSet);
  seq->getInstTerm(sequentialModel->getScalarTerm(NLName("CK")))->setNet(netClock);
  seq->getInstTerm(sequentialModel->getScalarTerm(NLName("Q")))->setNet(netOut);

  return top;
}

SNLDesign* createDffreTop(
    NLLibrary* library,
    const std::string& name) {
  auto* top =
      SNLDesign::create(library, SNLDesign::Type::Standard, NLName(name));
  auto* topIn =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("in"));
  auto* topEnable =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("en"));
  auto* topReset =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("rst"));
  auto* topClock =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("clk"));
  auto* topOut =
      SNLScalarTerm::create(top, SNLTerm::Direction::Output, NLName("out"));

  auto* ff = SNLInstance::create(top, NLDB0::getDFFRE(), NLName("ff0"));
  auto* netIn = SNLScalarNet::create(top, NLName("net_in"));
  auto* netEnable = SNLScalarNet::create(top, NLName("net_en"));
  auto* netReset = SNLScalarNet::create(top, NLName("net_rst"));
  auto* netClock = SNLScalarNet::create(top, NLName("net_clk"));
  auto* netOut = SNLScalarNet::create(top, NLName("net_out"));

  topIn->setNet(netIn);
  topEnable->setNet(netEnable);
  topReset->setNet(netReset);
  topClock->setNet(netClock);
  topOut->setNet(netOut);

  ff->getInstTerm(NLDB0::getDFFREData())->setNet(netIn);
  ff->getInstTerm(NLDB0::getDFFREEnable())->setNet(netEnable);
  ff->getInstTerm(NLDB0::getDFFREReset())->setNet(netReset);
  ff->getInstTerm(NLDB0::getDFFREClock())->setNet(netClock);
  ff->getInstTerm(NLDB0::getDFFREOutput())->setNet(netOut);

  return top;
}

SNLDesign* createComplementedOutputTop(
    NLLibrary* library,
    const std::string& name,
    SNLDesign* ffModel,
    SNLDesign* invModel,
    bool rebuildOutputsFromComplements) {
  auto* top =
      SNLDesign::create(library, SNLDesign::Type::Standard, NLName(name));
  auto* topIn =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("in"));
  auto* topClock =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("clk"));
  auto* topOutQ =
      SNLScalarTerm::create(top, SNLTerm::Direction::Output, NLName("out_q"));
  auto* topOutQn =
      SNLScalarTerm::create(top, SNLTerm::Direction::Output, NLName("out_qn"));

  auto* ff = SNLInstance::create(top, ffModel, NLName("ff0"));
  SNLInstance* qnToQInv = nullptr;
  SNLInstance* qToQnInv = nullptr;
  if (rebuildOutputsFromComplements) {
    qnToQInv = SNLInstance::create(top, invModel, NLName("inv_qn_to_q"));
    qToQnInv = SNLInstance::create(top, invModel, NLName("inv_q_to_qn"));
  }

  auto* netIn = SNLScalarNet::create(top, NLName("net_in"));
  auto* netClock = SNLScalarNet::create(top, NLName("net_clk"));
  auto* netQ = SNLScalarNet::create(top, NLName("net_q"));
  auto* netQn = SNLScalarNet::create(top, NLName("net_qn"));
  auto* netOutQ = SNLScalarNet::create(top, NLName("net_out_q"));
  auto* netOutQn = SNLScalarNet::create(top, NLName("net_out_qn"));

  topIn->setNet(netIn);
  topClock->setNet(netClock);

  ff->getInstTerm(ffModel->getScalarTerm(NLName("CK")))->setNet(netClock);
  ff->getInstTerm(ffModel->getScalarTerm(NLName("D")))->setNet(netIn);
  ff->getInstTerm(ffModel->getScalarTerm(NLName("Q")))->setNet(netQ);
  ff->getInstTerm(ffModel->getScalarTerm(NLName("QN")))->setNet(netQn);

  if (rebuildOutputsFromComplements) {
    topOutQ->setNet(netOutQ);
    topOutQn->setNet(netOutQn);
    qnToQInv->getInstTerm(invModel->getScalarTerm(NLName("A")))->setNet(netQn);
    qnToQInv->getInstTerm(invModel->getScalarTerm(NLName("Y")))->setNet(netOutQ);
    qToQnInv->getInstTerm(invModel->getScalarTerm(NLName("A")))->setNet(netQ);
    qToQnInv->getInstTerm(invModel->getScalarTerm(NLName("Y")))->setNet(netOutQn);
  } else {
    topOutQ->setNet(netQ);
    topOutQn->setNet(netQn);
  }

  return top;
}

SignalKey findKeyByDisplayName(const SequentialDesignModel& model,
                               const std::string& displayName) {
  for (const auto& [key, currentName] : model.displayNameByKey) {
    if (currentName == displayName) {
      return key;
    }
  }
  throw std::runtime_error("Missing display name in extracted model: " + displayName);
}

}  // namespace

TEST_F(SequentialEquivalenceStrategyTests, IdenticalDffDesignsAreEquivalent) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* primitives =
      NLLibrary::create(db, NLLibrary::Type::Primitives, NLName("prims"));
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* invModel = createInvModel(primitives);
  auto* top0 = createDffTop(library, "top0", invModel, false, false);
  auto* top1 = createDffTop(library, "top1", invModel, false, false);

  SequentialEquivalenceStrategy strategy(top0, top1);
  const auto result = strategy.run(3);

  EXPECT_EQ(result.status, SequentialEquivalenceStatus::Equivalent);
  EXPECT_EQ(result.bound, 1u);
}

TEST_F(SequentialEquivalenceStrategyTests, IdenticalDffDesignsAreEquivalentWithPdrEngine) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* library = NLLibrary::create(db, NLName("LIB"));
  auto* primitives = NLLibrary::create(db, NLLibrary::Type::Primitives, NLName("PRIMS"));
  auto* invModel = createInvModel(primitives);

  auto* top0 =
      createDffTop(library, "top0", invModel, false, false, "in", "out", "ff0");
  auto* top1 =
      createDffTop(library, "top1", invModel, false, false, "in", "out", "ff1");

  SequentialEquivalenceStrategy strategy(
      top0,
      top1,
      KEPLER_FORMAL::Config::SolverType::KISSAT,
      SecEngine::Pdr);
  const auto result = strategy.run(2);

  EXPECT_EQ(result.status, SequentialEquivalenceStatus::Equivalent);
  EXPECT_LE(result.bound, 1u);
}

TEST_F(SequentialEquivalenceStrategyTests,
       IdenticalDffDesignsAreEquivalentWithKInductionEngine) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* library = NLLibrary::create(db, NLName("LIB"));
  auto* primitives = NLLibrary::create(db, NLLibrary::Type::Primitives, NLName("PRIMS"));
  auto* invModel = createInvModel(primitives);

  auto* top0 =
      createDffTop(library, "top0", invModel, false, false, "in", "out", "ff0");
  auto* top1 =
      createDffTop(library, "top1", invModel, false, false, "in", "out", "ff1");

  SequentialEquivalenceStrategy strategy(
      top0,
      top1,
      KEPLER_FORMAL::Config::SolverType::KISSAT,
      SecEngine::KInduction);
  const auto result = strategy.run(2);

  EXPECT_EQ(result.status, SequentialEquivalenceStatus::Equivalent);
  EXPECT_LE(result.bound, 1u);
}

TEST_F(SequentialEquivalenceStrategyTests, IdenticalDffDesignsAreEquivalentWithImcEngine) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* library = NLLibrary::create(db, NLName("LIB"));
  auto* primitives = NLLibrary::create(db, NLLibrary::Type::Primitives, NLName("PRIMS"));
  auto* invModel = createInvModel(primitives);

  auto* top0 =
      createDffTop(library, "top0", invModel, false, false, "in", "out", "ff0");
  auto* top1 =
      createDffTop(library, "top1", invModel, false, false, "in", "out", "ff1");

  SequentialEquivalenceStrategy strategy(
      top0,
      top1,
      KEPLER_FORMAL::Config::SolverType::KISSAT,
      SecEngine::Imc);
  const auto result = strategy.run(2);

  EXPECT_EQ(result.status, SequentialEquivalenceStatus::Equivalent);
  EXPECT_LE(result.bound, 1u);
}

TEST_F(SequentialEquivalenceStrategyTests, OutputMismatchFailsAfterInitialObservation) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* primitives =
      NLLibrary::create(db, NLLibrary::Type::Primitives, NLName("prims"));
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* invModel = createInvModel(primitives);
  auto* top0 = createDffTop(library, "top0", invModel, false, false);
  auto* top1 = createDffTop(library, "top1", invModel, false, true);

  SequentialEquivalenceStrategy strategy(top0, top1);
  const auto result = strategy.run(3);

  EXPECT_EQ(result.status, SequentialEquivalenceStatus::Different);
  EXPECT_EQ(result.bound, 0u);
}

TEST_F(SequentialEquivalenceStrategyTests, NextStateMismatchFailsAtOneStep) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* primitives =
      NLLibrary::create(db, NLLibrary::Type::Primitives, NLName("prims"));
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* invModel = createInvModel(primitives);
  auto* top0 = createDffTop(library, "top0", invModel, false, false);
  auto* top1 = createDffTop(library, "top1", invModel, true, false);

  SequentialEquivalenceStrategy strategy(top0, top1);
  const auto result = strategy.run(3);

  EXPECT_EQ(result.status, SequentialEquivalenceStatus::Different);
  EXPECT_EQ(result.bound, 1u);
}

TEST_F(SequentialEquivalenceStrategyTests, DffeHoldSemanticsAreProved) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* top0 = createDffeTop(library, "top0");
  auto* top1 = createDffeTop(library, "top1");

  SequentialEquivalenceStrategy strategy(top0, top1);
  const auto result = strategy.run(3);

  EXPECT_EQ(result.status, SequentialEquivalenceStatus::Equivalent);
  EXPECT_EQ(result.bound, 1u);
}

TEST_F(SequentialEquivalenceStrategyTests, ComplementedStateOutputsRemainConsistent) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* primitives =
      NLLibrary::create(db, NLLibrary::Type::Primitives, NLName("prims"));
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* invModel = createInvModel(primitives);
  auto* dffQnModel = createDffQnModel(primitives);
  auto* top0 =
      createComplementedOutputTop(library, "top0", dffQnModel, invModel, false);
  auto* top1 =
      createComplementedOutputTop(library, "top1", dffQnModel, invModel, true);

  SequentialEquivalenceStrategy strategy(top0, top1);
  const auto result = strategy.run(3);

  EXPECT_EQ(result.status, SequentialEquivalenceStatus::Equivalent);
  EXPECT_EQ(result.bound, 1u);
}

TEST_F(SequentialEquivalenceStrategyTests, EquivalentDesignsWithRenamedStateAreAccepted) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* primitives =
      NLLibrary::create(db, NLLibrary::Type::Primitives, NLName("prims"));
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* invModel = createInvModel(primitives);
  auto* top0 = createDffTop(library, "top0", invModel, false, false, "state_a");
  auto* top1 = createDffTop(library, "top1", invModel, false, false, "state_b");

  SequentialEquivalenceStrategy strategy(top0, top1);
  const auto result = strategy.run(3);

  EXPECT_EQ(result.status, SequentialEquivalenceStatus::Equivalent);
  EXPECT_EQ(result.bound, 1u);
}

TEST_F(SequentialEquivalenceStrategyTests,
       RenamedStatePipelineIsProvedWithoutNameBasedStateMatching) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* top0 = createResetInitializedPipelineTop(
      library, "top0", false, {"left0", "left1", "left2"});
  auto* top1 = createResetInitializedPipelineTop(
      library, "top1", false, {"right0", "right1", "right2"});

  SequentialEquivalenceStrategy strategy(top0, top1);
  const auto result = strategy.run(3);

  EXPECT_EQ(result.status, SequentialEquivalenceStatus::Equivalent);
  EXPECT_LE(result.bound, 3u);
}

TEST_F(SequentialEquivalenceStrategyTests,
       ResetInitializedThreeStagePipelineFailsAtThreeSteps) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* top0 = createResetInitializedPipelineTop(library, "top0", false);
  auto* top1 = createResetInitializedPipelineTop(library, "top1", true);

  SequentialEquivalenceStrategy strategy(top0, top1);
  const auto result = strategy.run(4);

  EXPECT_EQ(result.status, SequentialEquivalenceStatus::Different);
  EXPECT_EQ(result.bound, 3u);
}

TEST_F(SequentialEquivalenceStrategyTests,
       ResetInitializedEquivalentPipelineIsProved) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* top0 = createResetInitializedPipelineTop(library, "top0", false);
  auto* top1 = createResetInitializedPipelineTop(library, "top1", false);

  SequentialEquivalenceStrategy strategy(top0, top1);
  const auto result = strategy.run(3);

  EXPECT_EQ(result.status, SequentialEquivalenceStatus::Equivalent);
  EXPECT_EQ(result.bound, 1u);
}

TEST_F(SequentialEquivalenceStrategyTests,
       ResetInitializedRenamedPipelineClosesWithinThreeStepSecProof) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* top0 = createResetInitializedPipelineTop(
      library, "top0", false, {"ff0", "ff1", "ff2"});
  auto* top1 = createResetInitializedPipelineTop(
      library, "top1", false, {"state_a", "state_b", "state_c"});

  SequentialEquivalenceStrategy strategy(top0, top1);
  const auto result = strategy.run(4);

  EXPECT_EQ(result.status, SequentialEquivalenceStatus::Equivalent);
  EXPECT_LE(result.bound, 3u);
}

TEST_F(SequentialEquivalenceStrategyTests,
       ResetBootstrapEquivalentPipelineIsProved) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* primitives =
      NLLibrary::create(db, NLLibrary::Type::Primitives, NLName("prims"));
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* invModel = createInvModel(primitives);
  auto* andModel = createAnd2Model(primitives);
  auto* top0 =
      createBootstrapPipelineTop(library, "top0", invModel, andModel);
  auto* top1 =
      createBootstrapPipelineTop(library, "top1", invModel, andModel);

  SequentialEquivalenceStrategy strategy(top0, top1);
  const auto result = strategy.run(3);

  EXPECT_EQ(result.status, SequentialEquivalenceStatus::Equivalent);
  EXPECT_LE(result.bound, 3u);
}

TEST_F(SequentialEquivalenceStrategyTests,
       ResetBootstrapCanAnchorEqualStatesWithoutConstantValues) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* primitives =
      NLLibrary::create(db, NLLibrary::Type::Primitives, NLName("prims"));
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* invModel = createInvModel(primitives);
  auto* andModel = createAnd2Model(primitives);
  auto* orModel = createOr2Model(primitives);
  auto* top0 =
      createResetLoadsInputTop(library, "top0", invModel, andModel, orModel);
  auto* top1 =
      createResetLoadsInputTop(library, "top1", invModel, andModel, orModel);

  SequentialEquivalenceStrategy strategy(top0, top1);
  const auto result = strategy.run(3);

  EXPECT_EQ(result.status, SequentialEquivalenceStatus::Equivalent);
  EXPECT_LE(result.bound, 3u);
}

TEST_F(SequentialEquivalenceStrategyTests,
       ResetBootstrapCanAnchorHiddenEqualStatesWithoutConstantValues) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* primitives =
      NLLibrary::create(db, NLLibrary::Type::Primitives, NLName("prims"));
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* invModel = createInvModel(primitives);
  auto* andModel = createAnd2Model(primitives);
  auto* orModel = createOr2Model(primitives);
  auto* top0 = createResetLoadsInputTwoStageTop(
      library, "top0", invModel, andModel, orModel);
  auto* top1 = createResetLoadsInputTwoStageTop(
      library, "top1", invModel, andModel, orModel);

  SequentialEquivalenceStrategy strategy(top0, top1);
  const auto result = strategy.run(3);

  EXPECT_EQ(result.status, SequentialEquivalenceStatus::Equivalent);
  EXPECT_LE(result.bound, 3u);
}

TEST_F(SequentialEquivalenceStrategyTests,
       BoolFormulaImplicationProvesCommutedConeUnderStateEquality) {
  BoolExpr* stateEquality = makeEqualityExpr(BoolExpr::Var(2), BoolExpr::Var(4));
  BoolExpr* outputEquality = makeEqualityExpr(
      BoolExpr::And(BoolExpr::Var(2), BoolExpr::Var(3)),
      BoolExpr::And(BoolExpr::Var(3), BoolExpr::Var(4)));
  BoolExpr* unrelatedEquality =
      makeEqualityExpr(BoolExpr::Var(2), BoolExpr::Var(3));

  EXPECT_TRUE(boolFormulaImplies(
      stateEquality,
      outputEquality,
      KEPLER_FORMAL::Config::getSolverType()));
  EXPECT_FALSE(boolFormulaImplies(
      stateEquality,
      unrelatedEquality,
      KEPLER_FORMAL::Config::getSolverType()));
}

TEST_F(SequentialEquivalenceStrategyTests,
       ResetBootstrapAutomaticallyExtendsForHiddenShiftPipelines) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* primitives =
      NLLibrary::create(db, NLLibrary::Type::Primitives, NLName("prims"));
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* invModel = createInvModel(primitives);
  auto* andModel = createAnd2Model(primitives);
  auto* orModel = createOr2Model(primitives);
  auto* top0 = createResetLoadsInputShiftPipelineTopWithStages(
      library, "top0", invModel, andModel, orModel, 20);
  auto* top1 = createResetLoadsInputShiftPipelineTopWithStages(
      library, "top1", invModel, andModel, orModel, 20);

  SequentialEquivalenceStrategy strategy(top0, top1);
  const auto result = strategy.run(1);

  EXPECT_EQ(result.status, SequentialEquivalenceStatus::Equivalent);
  EXPECT_EQ(result.bound, 1u);
}

TEST_F(SequentialEquivalenceStrategyTests,
       ResetBootstrapLongEquivalentPipelineStillClosesAtSmallK) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* primitives =
      NLLibrary::create(db, NLLibrary::Type::Primitives, NLName("prims"));
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* invModel = createInvModel(primitives);
  auto* andModel = createAnd2Model(primitives);
  auto* top0 =
      createBootstrapPipelineTopWithStages(library, "top0", invModel, andModel, 12);
  auto* top1 =
      createBootstrapPipelineTopWithStages(library, "top1", invModel, andModel, 12);

  SequentialEquivalenceStrategy strategy(top0, top1);
  const auto result = strategy.run(3);

  EXPECT_EQ(result.status, SequentialEquivalenceStatus::Equivalent);
  EXPECT_LE(result.bound, 3u);
}

TEST_F(SequentialEquivalenceStrategyTests,
       StructuralInvariantHandlesMismatchedStateCountsWithoutOscillation) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* top0 = createResetInitializedShiftPipelineTopWithStages(
      library, "top0", 5);
  auto* top1 = createResetInitializedShiftPipelineTopWithStages(
      library, "top1", 1);

  SequentialEquivalenceStrategy strategy(top0, top1);
  const auto result = strategy.run(6);

  EXPECT_EQ(result.status, SequentialEquivalenceStatus::Different);
  EXPECT_EQ(result.bound, 1u);
  EXPECT_LE(result.bound, 6u);
}

TEST_F(SequentialEquivalenceStrategyTests,
       ReachableStateInvariantUsesExplicitInitialCompatibilityWithoutReset) {
  const SignalKey state0A = makeSignalKey("state0A");
  const SignalKey state0B = makeSignalKey("state0B");
  const SignalKey state1A = makeSignalKey("state1A");
  const SignalKey state1B = makeSignalKey("state1B");

  SequentialDesignModel model0;
  model0.stateBits = {state0A, state0B};
  model0.initialStateValueByKey.emplace(state0A, false);
  model0.initialStateValueByKey.emplace(state0B, true);

  SequentialDesignModel model1;
  model1.stateBits = {state1A, state1B};
  model1.initialStateValueByKey.emplace(state1A, false);
  model1.initialStateValueByKey.emplace(state1B, false);

  AlignedSignals candidateStates;
  candidateStates.names = {"state_a", "state_b"};
  candidateStates.keys0 = {state0A, state0B};
  candidateStates.keys1 = {state1A, state1B};

  const auto invariant =
      buildReachableStateInvariant(model0, model1, AlignedSignals{}, candidateStates);

  EXPECT_EQ(invariant.bootstrapCycles, 0u);
  ASSERT_EQ(invariant.initialStateCorrespondence.names.size(), 1u);
  EXPECT_EQ(invariant.initialStateCorrespondence.names[0], "state_a");
  ASSERT_EQ(invariant.anchoredStateEqualities.names.size(), 1u);
  EXPECT_EQ(invariant.anchoredStateEqualities.names[0], "state_a");
  EXPECT_TRUE(invariant.bootstrapValues0.empty());
  EXPECT_TRUE(invariant.bootstrapValues1.empty());
}

TEST_F(SequentialEquivalenceStrategyTests,
       ReachableStateInvariantSkipsSameNamedStartupPairWithConflictingInit) {
  const SignalKey state0 = makeSignalKey("state0");
  const SignalKey state1 = makeSignalKey("state1");

  SequentialDesignModel model0;
  model0.stateBits = {state0};
  model0.displayNameByKey.emplace(state0, "same_name_state[0]");
  model0.initialStateValueByKey.emplace(state0, false);

  SequentialDesignModel model1;
  model1.stateBits = {state1};
  model1.displayNameByKey.emplace(state1, "same_name_state[0]");
  model1.initialStateValueByKey.emplace(state1, true);

  const auto invariant =
      buildReachableStateInvariant(model0, model1, AlignedSignals{}, AlignedSignals{});

  EXPECT_EQ(invariant.bootstrapCycles, 0u);
  EXPECT_TRUE(invariant.initialStateCorrespondence.names.empty());
  EXPECT_TRUE(invariant.anchoredStateEqualities.names.empty());
}

TEST_F(SequentialEquivalenceStrategyTests,
       ReachableStateInvariantSkipsBootstrapWhenResetAndInitialStateAreComplete) {
  const SignalKey rst0 = makeSignalKey("rst0");
  const SignalKey rst1 = makeSignalKey("rst1");
  const SignalKey state0 = makeSignalKey("state0");
  const SignalKey state1 = makeSignalKey("state1");

  SequentialDesignModel model0;
  model0.environmentInputs = {rst0};
  model0.stateBits = {state0};
  model0.inputVarByKey.emplace(rst0, 2);
  model0.displayNameByKey.emplace(rst0, "rst");
  model0.initialStateValueByKey.emplace(state0, false);

  SequentialDesignModel model1;
  model1.environmentInputs = {rst1};
  model1.stateBits = {state1};
  model1.inputVarByKey.emplace(rst1, 3);
  model1.displayNameByKey.emplace(rst1, "rst");
  model1.initialStateValueByKey.emplace(state1, false);

  AlignedSignals alignedInputs;
  alignedInputs.names = {"rst"};
  alignedInputs.keys0 = {rst0};
  alignedInputs.keys1 = {rst1};

  AlignedSignals candidateStates;
  candidateStates.names = {"state"};
  candidateStates.keys0 = {state0};
  candidateStates.keys1 = {state1};

  const auto invariant =
      buildReachableStateInvariant(model0, model1, alignedInputs, candidateStates);

  EXPECT_EQ(invariant.bootstrapCycles, 0u);
  ASSERT_EQ(invariant.initialStateCorrespondence.names.size(), 1u);
  EXPECT_EQ(invariant.initialStateCorrespondence.names[0], "state");
  ASSERT_EQ(invariant.anchoredStateEqualities.names.size(), 1u);
  EXPECT_EQ(invariant.anchoredStateEqualities.names[0], "state");
  EXPECT_TRUE(invariant.bootstrapValues0.empty());
  EXPECT_TRUE(invariant.bootstrapValues1.empty());
}

TEST_F(SequentialEquivalenceStrategyTests,
       ReachableStateInvariantDerivesBootstrapValuesAndAnchorsFromReset) {
  const SignalKey rst0 = makeSignalKey("rst0");
  const SignalKey rst1 = makeSignalKey("rst1");
  const SignalKey state0 = makeSignalKey("state0");
  const SignalKey state1 = makeSignalKey("state1");

  SequentialDesignModel model0;
  model0.environmentInputs = {rst0};
  model0.stateBits = {state0};
  model0.inputVarByKey.emplace(rst0, 2);
  model0.displayNameByKey.emplace(rst0, "rst");
  model0.nextStateExprByStateKey.emplace(state0, BoolExpr::Not(BoolExpr::Var(2)));

  SequentialDesignModel model1;
  model1.environmentInputs = {rst1};
  model1.stateBits = {state1};
  model1.inputVarByKey.emplace(rst1, 3);
  model1.displayNameByKey.emplace(rst1, "rst");
  model1.nextStateExprByStateKey.emplace(state1, BoolExpr::Not(BoolExpr::Var(3)));

  AlignedSignals alignedInputs;
  alignedInputs.names = {"rst"};
  alignedInputs.keys0 = {rst0};
  alignedInputs.keys1 = {rst1};

  AlignedSignals candidateStates;
  candidateStates.names = {"state"};
  candidateStates.keys0 = {state0};
  candidateStates.keys1 = {state1};

  const auto invariant =
      buildReachableStateInvariant(model0, model1, alignedInputs, candidateStates);

  EXPECT_EQ(invariant.bootstrapCycles, 3u);
  ASSERT_EQ(invariant.initialStateCorrespondence.names.size(), 1u);
  EXPECT_EQ(invariant.initialStateCorrespondence.names[0], "state");
  ASSERT_EQ(invariant.anchoredStateEqualities.names.size(), 1u);
  EXPECT_EQ(invariant.anchoredStateEqualities.names[0], "state");
  ASSERT_EQ(invariant.bootstrapValues0.size(), 1u);
  EXPECT_FALSE(invariant.bootstrapValues0.at(state0));
  ASSERT_EQ(invariant.bootstrapValues1.size(), 1u);
  EXPECT_FALSE(invariant.bootstrapValues1.at(state1));
}

TEST_F(SequentialEquivalenceStrategyTests,
       ReachableStateInvariantCanSkipBootstrapValueSweepForPdr) {
  const SignalKey rst0 = makeSignalKey("rst0");
  const SignalKey rst1 = makeSignalKey("rst1");
  const SignalKey state0 = makeSignalKey("state0");
  const SignalKey state1 = makeSignalKey("state1");

  SequentialDesignModel model0;
  model0.environmentInputs = {rst0};
  model0.stateBits = {state0};
  model0.inputVarByKey.emplace(rst0, 2);
  model0.displayNameByKey.emplace(rst0, "rst");
  model0.nextStateExprByStateKey.emplace(state0, BoolExpr::Not(BoolExpr::Var(2)));

  SequentialDesignModel model1;
  model1.environmentInputs = {rst1};
  model1.stateBits = {state1};
  model1.inputVarByKey.emplace(rst1, 3);
  model1.displayNameByKey.emplace(rst1, "rst");
  model1.nextStateExprByStateKey.emplace(state1, BoolExpr::Not(BoolExpr::Var(3)));

  AlignedSignals alignedInputs;
  alignedInputs.names = {"rst"};
  alignedInputs.keys0 = {rst0};
  alignedInputs.keys1 = {rst1};

  AlignedSignals candidateStates;
  candidateStates.names = {"state"};
  candidateStates.keys0 = {state0};
  candidateStates.keys1 = {state1};

  const auto invariant = buildReachableStateInvariant(
      model0,
      model1,
      alignedInputs,
      candidateStates,
      /*deriveResetBootstrapStrengthening=*/false,
      /*secDiagEnabled=*/false,
      KEPLER_FORMAL::Config::SolverType::KISSAT,
      /*deriveResetBootstrapEqualities=*/false);

  // PDR keeps the concrete reset window but lets BMC/reset-frontier checks
  // validate startup candidates instead of precomputing every state value.
  EXPECT_EQ(invariant.bootstrapCycles, 3u);
  ASSERT_EQ(invariant.anchoredStateEqualities.names.size(), 1u);
  EXPECT_EQ(invariant.anchoredStateEqualities.names[0], "state");
  EXPECT_TRUE(invariant.bootstrapValues0.empty());
  EXPECT_TRUE(invariant.bootstrapValues1.empty());
}

TEST_F(SequentialEquivalenceStrategyTests,
       ReachableStateInvariantRecognizesInputSuffixedResetNames) {
  const SignalKey reset0 = makeSignalKey("reset0");
  const SignalKey reset1 = makeSignalKey("reset1");
  const SignalKey activeLowReset0 = makeSignalKey("activeLowReset0");
  const SignalKey activeLowReset1 = makeSignalKey("activeLowReset1");
  const SignalKey state0 = makeSignalKey("state0");
  const SignalKey state1 = makeSignalKey("state1");
  const SignalKey lowState0 = makeSignalKey("lowState0");
  const SignalKey lowState1 = makeSignalKey("lowState1");

  SequentialDesignModel model0;
  model0.environmentInputs = {reset0, activeLowReset0};
  model0.stateBits = {state0, lowState0};
  model0.inputVarByKey.emplace(reset0, 2);
  model0.inputVarByKey.emplace(activeLowReset0, 4);
  model0.inputVarByKey.emplace(state0, 6);
  model0.inputVarByKey.emplace(lowState0, 8);
  model0.displayNameByKey.emplace(reset0, "reset_i");
  model0.displayNameByKey.emplace(activeLowReset0, "rst_ni");
  model0.nextStateExprByStateKey.emplace(state0, BoolExpr::Not(BoolExpr::Var(2)));
  model0.nextStateExprByStateKey.emplace(lowState0, BoolExpr::Var(4));

  SequentialDesignModel model1;
  model1.environmentInputs = {reset1, activeLowReset1};
  model1.stateBits = {state1, lowState1};
  model1.inputVarByKey.emplace(reset1, 3);
  model1.inputVarByKey.emplace(activeLowReset1, 5);
  model1.inputVarByKey.emplace(state1, 7);
  model1.inputVarByKey.emplace(lowState1, 9);
  model1.displayNameByKey.emplace(reset1, "reset_i");
  model1.displayNameByKey.emplace(activeLowReset1, "rst_ni");
  model1.nextStateExprByStateKey.emplace(state1, BoolExpr::Not(BoolExpr::Var(3)));
  model1.nextStateExprByStateKey.emplace(lowState1, BoolExpr::Var(5));

  AlignedSignals alignedInputs;
  alignedInputs.names = {"reset_i", "rst_ni"};
  alignedInputs.keys0 = {reset0, activeLowReset0};
  alignedInputs.keys1 = {reset1, activeLowReset1};

  AlignedSignals candidateStates;
  candidateStates.names = {"state", "low_state"};
  candidateStates.keys0 = {state0, lowState0};
  candidateStates.keys1 = {state1, lowState1};

  const auto invariant =
      buildReachableStateInvariant(model0, model1, alignedInputs, candidateStates);

  EXPECT_EQ(invariant.bootstrapCycles, 3u);
  ASSERT_EQ(invariant.bootstrapValues0.size(), 2u);
  EXPECT_FALSE(invariant.bootstrapValues0.at(state0));
  EXPECT_FALSE(invariant.bootstrapValues0.at(lowState0));
  ASSERT_EQ(invariant.bootstrapValues1.size(), 2u);
  EXPECT_FALSE(invariant.bootstrapValues1.at(state1));
  EXPECT_FALSE(invariant.bootstrapValues1.at(lowState1));
}

TEST_F(SequentialEquivalenceStrategyTests,
       ReachableStateInvariantCoversSatRemapFailureForUnalignedBootstrapInput) {
  const SignalKey rst0 = makeSignalKey("rst0");
  const SignalKey rst1 = makeSignalKey("rst1");
  const SignalKey privateInput0 = makeSignalKey("privateInput0");
  const SignalKey privateInput1 = makeSignalKey("privateInput1");
  const SignalKey state0 = makeSignalKey("state0");
  const SignalKey state1 = makeSignalKey("state1");

  SequentialDesignModel model0;
  model0.environmentInputs = {rst0, privateInput0};
  model0.stateBits = {state0};
  model0.inputVarByKey.emplace(rst0, 2);
  model0.inputVarByKey.emplace(privateInput0, 4);
  model0.inputVarByKey.emplace(state0, 6);
  model0.displayNameByKey.emplace(rst0, "rst");
  model0.displayNameByKey.emplace(privateInput0, "private");
  model0.displayNameByKey.emplace(state0, "state_q[0]");
  model0.nextStateExprByStateKey.emplace(state0, BoolExpr::Var(4));

  SequentialDesignModel model1;
  model1.environmentInputs = {rst1, privateInput1};
  model1.stateBits = {state1};
  model1.inputVarByKey.emplace(rst1, 3);
  model1.inputVarByKey.emplace(privateInput1, 5);
  model1.inputVarByKey.emplace(state1, 7);
  model1.displayNameByKey.emplace(rst1, "rst");
  model1.displayNameByKey.emplace(privateInput1, "private");
  model1.displayNameByKey.emplace(state1, "state_q[0]");
  model1.nextStateExprByStateKey.emplace(state1, BoolExpr::Var(5));

  AlignedSignals alignedInputs;
  alignedInputs.names = {"rst"};
  alignedInputs.keys0 = {rst0};
  alignedInputs.keys1 = {rst1};

  AlignedSignals candidateStates;
  candidateStates.names = {"state_q[0]"};
  candidateStates.keys0 = {state0};
  candidateStates.keys1 = {state1};

  const auto invariant =
      buildReachableStateInvariant(model0, model1, alignedInputs, candidateStates);

  EXPECT_EQ(invariant.bootstrapCycles, 3u);
  ASSERT_EQ(invariant.initialStateCorrespondence.names.size(), 1u);
  EXPECT_EQ(invariant.initialStateCorrespondence.names[0], "state_q[0]");
  EXPECT_TRUE(invariant.anchoredStateEqualities.names.empty());
}

TEST_F(SequentialEquivalenceStrategyTests,
       ReachableStateInvariantCoversMissingMapBootstrapFallback) {
  const SignalKey rst0 = makeSignalKey("rst0");
  const SignalKey rst1 = makeSignalKey("rst1");
  const SignalKey missingInput0 = makeSignalKey("missingInput0");
  const SignalKey missingInput1 = makeSignalKey("missingInput1");
  const SignalKey mappedState0 = makeSignalKey("mappedState0");
  const SignalKey mappedState1 = makeSignalKey("mappedState1");
  const SignalKey missingState0 = makeSignalKey("missingState0");
  const SignalKey missingState1 = makeSignalKey("missingState1");

  SequentialDesignModel model0;
  model0.environmentInputs = {rst0};
  model0.stateBits = {mappedState0, missingState0};
  model0.inputVarByKey.emplace(rst0, 2);
  model0.inputVarByKey.emplace(mappedState0, 4);
  model0.displayNameByKey.emplace(rst0, "rst");
  model0.initialStateValueByKey.emplace(missingState0, false);
  model0.nextStateExprByStateKey.emplace(mappedState0, BoolExpr::Var(4));
  model0.nextStateExprByStateKey.emplace(missingState0, BoolExpr::createFalse());

  SequentialDesignModel model1;
  model1.environmentInputs = {rst1};
  model1.stateBits = {mappedState1, missingState1};
  model1.inputVarByKey.emplace(rst1, 3);
  model1.inputVarByKey.emplace(mappedState1, 5);
  model1.displayNameByKey.emplace(rst1, "rst");
  model1.initialStateValueByKey.emplace(missingState1, false);
  model1.nextStateExprByStateKey.emplace(mappedState1, BoolExpr::Var(5));
  model1.nextStateExprByStateKey.emplace(missingState1, BoolExpr::createFalse());

  AlignedSignals alignedInputs;
  alignedInputs.names = {"rst", "missing"};
  alignedInputs.keys0 = {rst0, missingInput0};
  alignedInputs.keys1 = {rst1, missingInput1};

  AlignedSignals candidateStates;
  candidateStates.names = {"mapped", "missing"};
  candidateStates.keys0 = {mappedState0, missingState0};
  candidateStates.keys1 = {mappedState1, missingState1};

  const auto invariant =
      buildReachableStateInvariant(model0, model1, alignedInputs, candidateStates);

  EXPECT_EQ(invariant.bootstrapCycles, 3u);
  ASSERT_EQ(invariant.anchoredStateEqualities.names.size(), 1u);
  EXPECT_EQ(invariant.anchoredStateEqualities.names[0], "missing");
}

TEST_F(SequentialEquivalenceStrategyTests,
       ReachableStateInvariantThrowsAfterMissingBootstrapNextStateExpr) {
  const SignalKey rst0 = makeSignalKey("rst0");
  const SignalKey rst1 = makeSignalKey("rst1");
  const SignalKey state0 = makeSignalKey("state0");
  const SignalKey state1 = makeSignalKey("state1");

  SequentialDesignModel model0;
  model0.environmentInputs = {rst0};
  model0.stateBits = {state0};
  model0.inputVarByKey.emplace(rst0, 2);
  model0.inputVarByKey.emplace(state0, 4);
  model0.displayNameByKey.emplace(rst0, "rst");

  SequentialDesignModel model1;
  model1.environmentInputs = {rst1};
  model1.stateBits = {state1};
  model1.inputVarByKey.emplace(rst1, 3);
  model1.inputVarByKey.emplace(state1, 5);
  model1.displayNameByKey.emplace(rst1, "rst");

  AlignedSignals alignedInputs;
  alignedInputs.names = {"rst"};
  alignedInputs.keys0 = {rst0};
  alignedInputs.keys1 = {rst1};

  AlignedSignals candidateStates;
  candidateStates.names = {"state"};
  candidateStates.keys0 = {state0};
  candidateStates.keys1 = {state1};

  EXPECT_THROW(
      static_cast<void>(
          buildReachableStateInvariant(model0, model1, alignedInputs, candidateStates)),
      std::out_of_range);
}

TEST_F(SequentialEquivalenceStrategyTests,
       ReachableStateInvariantReportsSatRecoveredBootstrapEquality) {
  const SignalKey rst0 = makeSignalKey("rst0");
  const SignalKey rst1 = makeSignalKey("rst1");
  const SignalKey data0 = makeSignalKey("data0");
  const SignalKey data1 = makeSignalKey("data1");
  const SignalKey state0 = makeSignalKey("state0");
  const SignalKey state1 = makeSignalKey("state1");

  SequentialDesignModel model0;
  model0.environmentInputs = {rst0, data0};
  model0.stateBits = {state0};
  model0.inputVarByKey.emplace(rst0, 2);
  model0.inputVarByKey.emplace(data0, 4);
  model0.inputVarByKey.emplace(state0, 6);
  model0.displayNameByKey.emplace(rst0, "rst");
  model0.displayNameByKey.emplace(data0, "data");
  model0.displayNameByKey.emplace(state0, "state_q[0]");
  model0.nextStateExprByStateKey.emplace(
      state0,
      BoolExpr::And(BoolExpr::Var(6), BoolExpr::Var(4)));

  SequentialDesignModel model1;
  model1.environmentInputs = {rst1, data1};
  model1.stateBits = {state1};
  model1.inputVarByKey.emplace(rst1, 3);
  model1.inputVarByKey.emplace(data1, 5);
  model1.inputVarByKey.emplace(state1, 7);
  model1.displayNameByKey.emplace(rst1, "rst");
  model1.displayNameByKey.emplace(data1, "data");
  model1.displayNameByKey.emplace(state1, "state_q[0]");
  model1.nextStateExprByStateKey.emplace(
      state1,
      BoolExpr::Not(BoolExpr::Or(
          BoolExpr::Not(BoolExpr::Var(7)),
          BoolExpr::Not(BoolExpr::Var(5)))));

  AlignedSignals alignedInputs;
  alignedInputs.names = {"rst", "data"};
  alignedInputs.keys0 = {rst0, data0};
  alignedInputs.keys1 = {rst1, data1};

  AlignedSignals candidateStates;
  candidateStates.names = {"state_q[0]"};
  candidateStates.keys0 = {state0};
  candidateStates.keys1 = {state1};

  testing::internal::CaptureStderr();
  const auto invariant = buildReachableStateInvariant(
      model0,
      model1,
      alignedInputs,
      candidateStates,
      /*deriveResetBootstrapStrengthening=*/true,
      /*secDiagEnabled=*/true);
  const std::string stderrOutput = testing::internal::GetCapturedStderr();

  EXPECT_EQ(invariant.bootstrapCycles, 3u);
  ASSERT_EQ(invariant.anchoredStateEqualities.names.size(), 1u);
  EXPECT_EQ(invariant.anchoredStateEqualities.names[0], "state_q[0]");
  EXPECT_NE(
      stderrOutput.find("sat_recovered_equalities=1"),
      std::string::npos);
}

TEST_F(SequentialEquivalenceStrategyTests,
       ReachableStateInvariantDerivesBootstrapEqualityFromSameNamedResetlessState) {
  const SignalKey rst0 = makeSignalKey("rst0");
  const SignalKey rst1 = makeSignalKey("rst1");
  const SignalKey structural0 = makeSignalKey("structural0");
  const SignalKey structural1 = makeSignalKey("structural1");
  const SignalKey resetless0 = makeSignalKey("resetless0");
  const SignalKey resetless1 = makeSignalKey("resetless1");

  SequentialDesignModel model0;
  model0.environmentInputs = {rst0};
  model0.stateBits = {structural0, resetless0};
  model0.inputVarByKey.emplace(rst0, 2);
  model0.inputVarByKey.emplace(structural0, 4);
  model0.inputVarByKey.emplace(resetless0, 6);
  model0.displayNameByKey.emplace(rst0, "rst");
  model0.displayNameByKey.emplace(structural0, "u_guard.q[0]");
  model0.displayNameByKey.emplace(resetless0, "text_out[0]$_DFF_P_.QN[0]");
  model0.nextStateExprByStateKey.emplace(structural0, BoolExpr::Not(BoolExpr::Var(2)));
  model0.nextStateExprByStateKey.emplace(resetless0, BoolExpr::Var(6));

  SequentialDesignModel model1;
  model1.environmentInputs = {rst1};
  model1.stateBits = {structural1, resetless1};
  model1.inputVarByKey.emplace(rst1, 3);
  model1.inputVarByKey.emplace(structural1, 5);
  model1.inputVarByKey.emplace(resetless1, 7);
  model1.displayNameByKey.emplace(rst1, "rst");
  model1.displayNameByKey.emplace(structural1, "u_guard.q[0]");
  model1.displayNameByKey.emplace(resetless1, "text_out[0]$_DFF_P_.QN[0]");
  model1.nextStateExprByStateKey.emplace(structural1, BoolExpr::Not(BoolExpr::Var(3)));
  model1.nextStateExprByStateKey.emplace(resetless1, BoolExpr::Var(7));

  AlignedSignals alignedInputs;
  alignedInputs.names = {"rst"};
  alignedInputs.keys0 = {rst0};
  alignedInputs.keys1 = {rst1};

  // This mirrors post-resize AES: only a small structural guard was inferred as
  // inductive, while same-named resetless flops still represent the same
  // startup state. If reset propagation proves the equality survives the
  // bootstrap window, SEC can safely use it at the first checked frame too.
  AlignedSignals inductiveStates;
  inductiveStates.names = {"u_guard.q[0]"};
  inductiveStates.keys0 = {structural0};
  inductiveStates.keys1 = {structural1};

  const auto invariant =
      buildReachableStateInvariant(model0, model1, alignedInputs, inductiveStates);

  EXPECT_EQ(invariant.bootstrapCycles, 3u);
  ASSERT_EQ(invariant.initialStateCorrespondence.names.size(), 2u);
  EXPECT_NE(
      std::find(
          invariant.initialStateCorrespondence.names.begin(),
          invariant.initialStateCorrespondence.names.end(),
          "text_out[0]$_DFF_P_.QN[0]"),
      invariant.initialStateCorrespondence.names.end());
  ASSERT_EQ(invariant.anchoredStateEqualities.names.size(), 2u);
  EXPECT_NE(
      std::find(
          invariant.anchoredStateEqualities.names.begin(),
          invariant.anchoredStateEqualities.names.end(),
          "u_guard.q[0]"),
      invariant.anchoredStateEqualities.names.end());
  EXPECT_NE(
      std::find(
          invariant.anchoredStateEqualities.names.begin(),
          invariant.anchoredStateEqualities.names.end(),
          "text_out[0]$_DFF_P_.QN[0]"),
      invariant.anchoredStateEqualities.names.end());
}

TEST_F(SequentialEquivalenceStrategyTests,
       ReachableStateInvariantUsesSatToAnchorCommutedBootstrapLogic) {
  const SignalKey rst0 = makeSignalKey("rst0");
  const SignalKey rst1 = makeSignalKey("rst1");
  const SignalKey in0 = makeSignalKey("in0");
  const SignalKey in1 = makeSignalKey("in1");
  const SignalKey structural0 = makeSignalKey("structural0");
  const SignalKey structural1 = makeSignalKey("structural1");
  const SignalKey resetless0 = makeSignalKey("resetless0");
  const SignalKey resetless1 = makeSignalKey("resetless1");

  SequentialDesignModel model0;
  model0.environmentInputs = {rst0, in0};
  model0.stateBits = {structural0, resetless0};
  model0.inputVarByKey.emplace(rst0, 2);
  model0.inputVarByKey.emplace(in0, 8);
  model0.inputVarByKey.emplace(structural0, 4);
  model0.inputVarByKey.emplace(resetless0, 6);
  model0.displayNameByKey.emplace(rst0, "rst");
  model0.displayNameByKey.emplace(in0, "in");
  model0.displayNameByKey.emplace(structural0, "u_guard.q[0]");
  model0.displayNameByKey.emplace(resetless0, "state_q[0]");
  model0.nextStateExprByStateKey.emplace(structural0, BoolExpr::Not(BoolExpr::Var(2)));
  model0.nextStateExprByStateKey.emplace(
      resetless0,
      BoolExpr::And(BoolExpr::Var(6), BoolExpr::Var(8)));

  SequentialDesignModel model1;
  model1.environmentInputs = {rst1, in1};
  model1.stateBits = {structural1, resetless1};
  model1.inputVarByKey.emplace(rst1, 3);
  model1.inputVarByKey.emplace(in1, 9);
  model1.inputVarByKey.emplace(structural1, 5);
  model1.inputVarByKey.emplace(resetless1, 7);
  model1.displayNameByKey.emplace(rst1, "rst");
  model1.displayNameByKey.emplace(in1, "in");
  model1.displayNameByKey.emplace(structural1, "u_guard.q[0]");
  model1.displayNameByKey.emplace(resetless1, "state_q[0]");
  model1.nextStateExprByStateKey.emplace(structural1, BoolExpr::Not(BoolExpr::Var(3)));
  model1.nextStateExprByStateKey.emplace(
      resetless1,
      BoolExpr::And(BoolExpr::Var(9), BoolExpr::Var(7)));

  AlignedSignals alignedInputs;
  alignedInputs.names = {"rst", "in"};
  alignedInputs.keys0 = {rst0, in0};
  alignedInputs.keys1 = {rst1, in1};

  AlignedSignals inductiveStates;
  inductiveStates.names = {"u_guard.q[0]"};
  inductiveStates.keys0 = {structural0};
  inductiveStates.keys1 = {structural1};

  const auto invariant =
      buildReachableStateInvariant(model0, model1, alignedInputs, inductiveStates);

  EXPECT_NE(
      std::find(
          invariant.anchoredStateEqualities.names.begin(),
          invariant.anchoredStateEqualities.names.end(),
          "state_q[0]"),
      invariant.anchoredStateEqualities.names.end());
}

TEST_F(SequentialEquivalenceStrategyTests,
       ReachableStateInvariantBootstrapRecoversEqualitiesAfterMismatchedInitialValues) {
  const SignalKey rst0 = makeSignalKey("rst0");
  const SignalKey rst1 = makeSignalKey("rst1");
  const SignalKey state0 = makeSignalKey("state0");
  const SignalKey state1 = makeSignalKey("state1");
  const SignalKey shadow0 = makeSignalKey("shadow0");
  const SignalKey shadow1 = makeSignalKey("shadow1");

  SequentialDesignModel model0;
  model0.environmentInputs = {rst0};
  model0.stateBits = {state0, shadow0};
  model0.inputVarByKey.emplace(rst0, 2);
  model0.inputVarByKey.emplace(state0, 3);
  model0.inputVarByKey.emplace(shadow0, 6);
  model0.displayNameByKey.emplace(rst0, "rst");
  model0.initialStateValueByKey.emplace(state0, false);
  model0.nextStateExprByStateKey.emplace(state0, BoolExpr::Not(BoolExpr::Var(2)));
  model0.nextStateExprByStateKey.emplace(shadow0, BoolExpr::Var(6));

  SequentialDesignModel model1;
  model1.environmentInputs = {rst1};
  model1.stateBits = {state1, shadow1};
  model1.inputVarByKey.emplace(rst1, 4);
  model1.inputVarByKey.emplace(state1, 5);
  model1.inputVarByKey.emplace(shadow1, 7);
  model1.displayNameByKey.emplace(rst1, "rst");
  model1.initialStateValueByKey.emplace(state1, true);
  model1.nextStateExprByStateKey.emplace(state1, BoolExpr::Not(BoolExpr::Var(4)));
  model1.nextStateExprByStateKey.emplace(shadow1, BoolExpr::Var(7));

  AlignedSignals alignedInputs;
  alignedInputs.names = {"rst"};
  alignedInputs.keys0 = {rst0};
  alignedInputs.keys1 = {rst1};

  AlignedSignals candidateStates;
  candidateStates.names = {"state"};
  candidateStates.keys0 = {state0};
  candidateStates.keys1 = {state1};

  ScopedEnvVar secDiag("KEPLER_SEC_DIAG", "1");
  testing::internal::CaptureStderr();
  const auto invariant = buildReachableStateInvariant(
      model0,
      model1,
      alignedInputs,
      candidateStates,
      /*deriveResetBootstrapStrengthening=*/true,
      /*secDiagEnabled=*/true);
  const std::string stderrOutput = testing::internal::GetCapturedStderr();

  EXPECT_EQ(invariant.bootstrapCycles, 3u);
  EXPECT_TRUE(invariant.initialStateCorrespondence.names.empty());
  ASSERT_EQ(invariant.anchoredStateEqualities.names.size(), 1u);
  EXPECT_EQ(invariant.anchoredStateEqualities.names[0], "state");
  ASSERT_EQ(invariant.bootstrapValues0.size(), 1u);
  EXPECT_FALSE(invariant.bootstrapValues0.at(state0));
  ASSERT_EQ(invariant.bootstrapValues1.size(), 1u);
  EXPECT_FALSE(invariant.bootstrapValues1.at(state1));
  EXPECT_NE(stderrOutput.find("SEC diag: bootstrap step 1"), std::string::npos);
}

TEST_F(SequentialEquivalenceStrategyTests,
       ReachableStateInvariantFallsBackWhenBootstrapHasNoCandidates) {
  const SignalKey rst0 = makeSignalKey("rst0");
  const SignalKey rst1 = makeSignalKey("rst1");
  const SignalKey state0 = makeSignalKey("state0");
  const SignalKey state1 = makeSignalKey("state1");

  SequentialDesignModel model0;
  model0.environmentInputs = {rst0};
  model0.stateBits = {state0};
  model0.inputVarByKey.emplace(rst0, 2);
  model0.inputVarByKey.emplace(state0, 4);
  model0.displayNameByKey.emplace(rst0, "rst");
  model0.nextStateExprByStateKey.emplace(state0, BoolExpr::Not(BoolExpr::Var(2)));

  SequentialDesignModel model1;
  model1.environmentInputs = {rst1};
  model1.inputVarByKey.emplace(rst1, 3);
  model1.stateBits = {state1};
  model1.inputVarByKey.emplace(state1, 5);
  model1.displayNameByKey.emplace(rst1, "rst");
  model1.nextStateExprByStateKey.emplace(state1, BoolExpr::Not(BoolExpr::Var(3)));

  const auto invariant = buildReachableStateInvariant(
      model0, model1, AlignedSignals{}, AlignedSignals{});

  EXPECT_EQ(invariant.bootstrapCycles, 3u);
  EXPECT_TRUE(invariant.anchoredStateEqualities.names.empty());
  ASSERT_EQ(invariant.bootstrapValues0.size(), 1u);
  EXPECT_FALSE(invariant.bootstrapValues0.at(state0));
  ASSERT_EQ(invariant.bootstrapValues1.size(), 1u);
  EXPECT_FALSE(invariant.bootstrapValues1.at(state1));
}

TEST_F(SequentialEquivalenceStrategyTests,
       ReachableStateInvariantFallsBackWhenOnlyOneSideHasResetAssignments) {
  const SignalKey rst0 = makeSignalKey("rst0");
  const SignalKey rst1 = makeSignalKey("rst1");
  const SignalKey state0 = makeSignalKey("state0");
  const SignalKey state1 = makeSignalKey("state1");

  SequentialDesignModel model0;
  model0.environmentInputs = {rst0};
  model0.stateBits = {state0};
  model0.inputVarByKey.emplace(rst0, 2);
  model0.inputVarByKey.emplace(state0, 3);
  model0.displayNameByKey.emplace(rst0, "rst");
  model0.initialStateValueByKey.emplace(state0, false);

  SequentialDesignModel model1;
  model1.environmentInputs = {rst1};
  model1.stateBits = {state1};
  model1.inputVarByKey.emplace(state1, 4);
  model1.initialStateValueByKey.emplace(state1, false);

  AlignedSignals candidateStates;
  candidateStates.names = {"state"};
  candidateStates.keys0 = {state0};
  candidateStates.keys1 = {state1};

  const auto invariant = buildReachableStateInvariant(
      model0, model1, AlignedSignals{}, candidateStates);

  EXPECT_EQ(invariant.bootstrapCycles, 0u);
  ASSERT_EQ(invariant.initialStateCorrespondence.names.size(), 1u);
  EXPECT_EQ(invariant.initialStateCorrespondence.names[0], "state");
  ASSERT_EQ(invariant.anchoredStateEqualities.names.size(), 1u);
  EXPECT_EQ(invariant.anchoredStateEqualities.names[0], "state");
}

TEST_F(SequentialEquivalenceStrategyTests,
       ReachableStateInvariantCoversBootstrapValuePropagationEdgeCases) {
  const SignalKey rst0 = makeSignalKey("rst0");
  const SignalKey rst1 = makeSignalKey("rst1");
  const SignalKey truth0 = makeSignalKey("truth0");
  const SignalKey truth1 = makeSignalKey("truth1");
  const SignalKey invalid0 = makeSignalKey("invalid0");
  const SignalKey invalid1 = makeSignalKey("invalid1");
  const SignalKey null0 = makeSignalKey("null0");
  const SignalKey null1 = makeSignalKey("null1");
  const SignalKey diff0 = makeSignalKey("diff0");
  const SignalKey diff1 = makeSignalKey("diff1");
  const SignalKey hidden0 = makeSignalKey("hidden0");
  const SignalKey hidden1 = makeSignalKey("hidden1");

  SequentialDesignModel model0;
  model0.environmentInputs = {rst0};
  model0.stateBits = {truth0, invalid0, null0, diff0, hidden0};
  model0.inputVarByKey.emplace(rst0, 2);
  model0.inputVarByKey.emplace(truth0, 3);
  model0.inputVarByKey.emplace(invalid0, 4);
  model0.inputVarByKey.emplace(null0, 5);
  model0.inputVarByKey.emplace(diff0, 6);
  model0.inputVarByKey.emplace(hidden0, 7);
  model0.displayNameByKey.emplace(rst0, "rst");
  model0.nextStateExprByStateKey.emplace(
      truth0,
      BoolExpr::Xor(BoolExpr::Var(2), BoolExpr::createFalse()));
  model0.nextStateExprByStateKey.emplace(invalid0, BoolExpr::Var(7));
  model0.nextStateExprByStateKey.emplace(null0, nullptr);
  model0.nextStateExprByStateKey.emplace(diff0, BoolExpr::Var(2));
  model0.nextStateExprByStateKey.emplace(hidden0, BoolExpr::Var(7));
  model0.initialStateValueByKey.emplace(truth0, false);
  model0.initialStateValueByKey.emplace(invalid0, false);
  model0.initialStateValueByKey.emplace(null0, false);
  model0.initialStateValueByKey.emplace(diff0, false);

  SequentialDesignModel model1;
  model1.environmentInputs = {rst1};
  model1.stateBits = {truth1, invalid1, null1, diff1, hidden1};
  model1.inputVarByKey.emplace(rst1, 10);
  model1.inputVarByKey.emplace(truth1, 11);
  model1.inputVarByKey.emplace(invalid1, 12);
  model1.inputVarByKey.emplace(null1, 13);
  model1.inputVarByKey.emplace(diff1, 14);
  model1.inputVarByKey.emplace(hidden1, 15);
  model1.displayNameByKey.emplace(rst1, "rst");
  model1.nextStateExprByStateKey.emplace(
      truth1,
      BoolExpr::Xor(BoolExpr::Var(10), BoolExpr::createFalse()));
  model1.nextStateExprByStateKey.emplace(invalid1, BoolExpr::Var(15));
  model1.nextStateExprByStateKey.emplace(null1, nullptr);
  model1.nextStateExprByStateKey.emplace(diff1, BoolExpr::Not(BoolExpr::Var(10)));
  model1.nextStateExprByStateKey.emplace(hidden1, BoolExpr::Var(15));
  model1.initialStateValueByKey.emplace(truth1, true);
  model1.initialStateValueByKey.emplace(invalid1, true);
  model1.initialStateValueByKey.emplace(null1, true);
  model1.initialStateValueByKey.emplace(diff1, true);

  AlignedSignals alignedInputs;
  alignedInputs.names = {"rst"};
  alignedInputs.keys0 = {rst0};
  alignedInputs.keys1 = {rst1};

  AlignedSignals candidateStates;
  candidateStates.names = {"truth", "invalid", "null", "diff"};
  candidateStates.keys0 = {truth0, invalid0, null0, diff0};
  candidateStates.keys1 = {truth1, invalid1, null1, diff1};

  const auto invariant = buildReachableStateInvariant(
      model0, model1, alignedInputs, candidateStates);

  EXPECT_EQ(invariant.bootstrapCycles, 3u);
  EXPECT_TRUE(invariant.initialStateCorrespondence.names.empty());
  EXPECT_TRUE(invariant.bootstrapValues0.at(truth0));
  EXPECT_TRUE(invariant.bootstrapValues1.at(truth1));
  EXPECT_TRUE(invariant.bootstrapValues0.at(diff0));
  EXPECT_FALSE(invariant.bootstrapValues1.at(diff1));
  EXPECT_TRUE(
      std::find(
          invariant.anchoredStateEqualities.names.begin(),
          invariant.anchoredStateEqualities.names.end(),
          "truth") != invariant.anchoredStateEqualities.names.end());
  EXPECT_TRUE(
      std::find(
          invariant.anchoredStateEqualities.names.begin(),
          invariant.anchoredStateEqualities.names.end(),
          "diff") == invariant.anchoredStateEqualities.names.end());
}

TEST_F(SequentialEquivalenceStrategyTests,
       ReachableStateInvariantBootstrapValuesEvaluateConstTrueXorAndInvalidExprStates) {
  const SignalKey rst0 = makeSignalKey("rst0");
  const SignalKey rst1 = makeSignalKey("rst1");
  const SignalKey const0 = makeSignalKey("const0");
  const SignalKey const1 = makeSignalKey("const1");
  const SignalKey xor0 = makeSignalKey("xor0");
  const SignalKey xor1 = makeSignalKey("xor1");
  const SignalKey invalid0 = makeSignalKey("invalid0");
  const SignalKey invalid1 = makeSignalKey("invalid1");
  const SignalKey hidden0 = makeSignalKey("hidden0");
  const SignalKey hidden1 = makeSignalKey("hidden1");
  BoolExpr invalidExpr0;
  BoolExpr invalidExpr1;

  SequentialDesignModel model0;
  model0.environmentInputs = {rst0};
  model0.stateBits = {const0, xor0, invalid0, hidden0};
  model0.inputVarByKey.emplace(rst0, 2);
  model0.inputVarByKey.emplace(const0, 3);
  model0.inputVarByKey.emplace(xor0, 4);
  model0.inputVarByKey.emplace(invalid0, 5);
  model0.inputVarByKey.emplace(hidden0, 6);
  model0.displayNameByKey.emplace(rst0, "rst");
  model0.initialStateValueByKey.emplace(const0, false);
  model0.initialStateValueByKey.emplace(xor0, false);
  model0.initialStateValueByKey.emplace(invalid0, false);
  model0.nextStateExprByStateKey.emplace(const0, BoolExpr::createTrue());
  model0.nextStateExprByStateKey.emplace(
      xor0, BoolExpr::Xor(BoolExpr::Var(2), BoolExpr::createFalse()));
  model0.nextStateExprByStateKey.emplace(invalid0, &invalidExpr0);
  model0.nextStateExprByStateKey.emplace(hidden0, BoolExpr::Var(6));

  SequentialDesignModel model1;
  model1.environmentInputs = {rst1};
  model1.stateBits = {const1, xor1, invalid1, hidden1};
  model1.inputVarByKey.emplace(rst1, 10);
  model1.inputVarByKey.emplace(const1, 11);
  model1.inputVarByKey.emplace(xor1, 12);
  model1.inputVarByKey.emplace(invalid1, 13);
  model1.inputVarByKey.emplace(hidden1, 14);
  model1.displayNameByKey.emplace(rst1, "rst");
  model1.initialStateValueByKey.emplace(const1, false);
  model1.initialStateValueByKey.emplace(xor1, false);
  model1.initialStateValueByKey.emplace(invalid1, false);
  model1.nextStateExprByStateKey.emplace(const1, BoolExpr::createTrue());
  model1.nextStateExprByStateKey.emplace(
      xor1, BoolExpr::Xor(BoolExpr::Var(10), BoolExpr::createFalse()));
  model1.nextStateExprByStateKey.emplace(invalid1, &invalidExpr1);
  model1.nextStateExprByStateKey.emplace(hidden1, BoolExpr::Var(14));

  AlignedSignals candidateStates;
  candidateStates.names = {"const", "xor", "invalid"};
  candidateStates.keys0 = {const0, xor0, invalid0};
  candidateStates.keys1 = {const1, xor1, invalid1};

  const auto invariant = buildReachableStateInvariant(
      model0, model1, AlignedSignals{}, candidateStates);

  EXPECT_EQ(invariant.bootstrapCycles, 3u);
  ASSERT_EQ(invariant.anchoredStateEqualities.names.size(), 2u);
  EXPECT_TRUE(
      std::find(
          invariant.anchoredStateEqualities.names.begin(),
          invariant.anchoredStateEqualities.names.end(),
          "invalid") == invariant.anchoredStateEqualities.names.end());
  EXPECT_TRUE(invariant.bootstrapValues0.at(const0));
  EXPECT_TRUE(invariant.bootstrapValues1.at(const1));
  EXPECT_TRUE(invariant.bootstrapValues0.at(xor0));
  EXPECT_TRUE(invariant.bootstrapValues1.at(xor1));
  EXPECT_EQ(invariant.bootstrapValues0.count(invalid0), 0u);
  EXPECT_EQ(invariant.bootstrapValues1.count(invalid1), 0u);
}

TEST_F(SequentialEquivalenceStrategyTests,
       BoolExprRemapThrowsOnMissingVariableMapping) {
  auto* expr = BoolExpr::And(BoolExpr::Var(2), BoolExpr::Var(3));

  EXPECT_THROW(
      static_cast<void>(remapBoolExprVariables(expr, {{2, 10}})),
      std::runtime_error);
}

TEST_F(SequentialEquivalenceStrategyTests,
       BoolExprHelpersCoverNullXorAndInvalidOperators) {
  EXPECT_EQ(remapBoolExprVariables(nullptr, {}), nullptr);
  EXPECT_EQ(substituteBoolExprVariables(nullptr, {}), nullptr);
  EXPECT_FALSE(isBoolFormulaSatisfiable(
      nullptr, KEPLER_FORMAL::Config::SolverType::KISSAT));
  EXPECT_FALSE(isBoolFormulaSatisfiable(
      BoolExpr::createFalse(), KEPLER_FORMAL::Config::SolverType::KISSAT));
  EXPECT_TRUE(isBoolFormulaSatisfiable(
      BoolExpr::createTrue(), KEPLER_FORMAL::Config::SolverType::KISSAT));
  EXPECT_FALSE(boolFormulaImplies(
      BoolExpr::createTrue(), nullptr, KEPLER_FORMAL::Config::SolverType::KISSAT));
  EXPECT_TRUE(boolFormulaImplies(
      BoolExpr::createFalse(),
      BoolExpr::Var(2),
      KEPLER_FORMAL::Config::SolverType::KISSAT));
  EXPECT_TRUE(boolFormulaImplies(
      BoolExpr::Var(2),
      BoolExpr::createTrue(),
      KEPLER_FORMAL::Config::SolverType::KISSAT));

  BoolExpr invalid;
  EXPECT_THROW(
      static_cast<void>(remapBoolExprVariables(&invalid, {})),
      std::runtime_error);

  auto* xorExpr = BoolExpr::Xor(BoolExpr::Var(2), BoolExpr::Var(3));
  auto* substituted =
      substituteBoolExprVariables(xorExpr, {{2, true}, {3, false}});
  EXPECT_TRUE(substituted->evaluate({}));

  KEPLER_FORMAL::BoolExprCache::Key rawAndWithFalse{
      KEPLER_FORMAL::Op::AND, 0, BoolExpr::createFalse(), BoolExpr::Var(4)};
  EXPECT_FALSE(isBoolFormulaSatisfiable(
      KEPLER_FORMAL::BoolExprCache::getExpression(rawAndWithFalse),
      KEPLER_FORMAL::Config::SolverType::KISSAT));

  EXPECT_THROW(
      static_cast<void>(substituteBoolExprVariables(&invalid, {})),
      std::runtime_error);
}

TEST_F(SequentialEquivalenceStrategyTests,
       BoolExprSubstitutionRewritesAssignedVariablesAndKeepsOthers) {
  auto* expr = BoolExpr::And(BoolExpr::Var(2), BoolExpr::Not(BoolExpr::Var(3)));
  auto* substituted = substituteBoolExprVariables(expr, {{2, true}, {3, false}});

  EXPECT_TRUE(substituted->evaluate({}));
  EXPECT_EQ(substituted->getOp(), KEPLER_FORMAL::Op::VAR);
  EXPECT_EQ(substituted->getId(), 1u);
}

TEST_F(SequentialEquivalenceStrategyTests,
       SatEncodingHelpersCoverConstantCachingAndErrorBranches) {
  SATSolverWrapper solver(KEPLER_FORMAL::Config::SolverType::KISSAT);
  FrameVariableStore variables(solver, {2, 3}, 2);

  EXPECT_THROW(
      static_cast<void>(variables.getLiteral(99, 0)),
      std::runtime_error);
  EXPECT_THROW(
      static_cast<void>(variables.makeLeafLits(3)),
      std::runtime_error);

  FrameFormulaEncoder encoder(solver, variables.makeLeafLits(0));
  EXPECT_THROW(static_cast<void>(encoder.encode(nullptr)), std::invalid_argument);
  EXPECT_THROW(
      static_cast<void>(encoder.encode(BoolExpr::Var(99))),
      std::runtime_error);

  BoolExpr invalid;
  EXPECT_THROW(static_cast<void>(encoder.encode(&invalid)), std::runtime_error);

  const int trueLit = encoder.encode(BoolExpr::createTrue());
  EXPECT_EQ(trueLit, encoder.encode(BoolExpr::createTrue()));

  addSimplePathConstraint(solver, variables, {}, 2);
}

TEST_F(SequentialEquivalenceStrategyTests,
       SatSolverWrapperGetLiteralValueHandlesConstantsUnknownModelsAndErrors) {
  SATSolverWrapper solver(KEPLER_FORMAL::Config::SolverType::GLUCOSE);
  const int symbol = solver.newVar() + 2;
  EXPECT_TRUE(solver.solve());

  EXPECT_FALSE(solver.getLiteralValue(0));
  EXPECT_TRUE(solver.getLiteralValue(1));
  EXPECT_FALSE(solver.getLiteralValue(symbol));
  EXPECT_THROW(static_cast<void>(solver.getLiteralValue(-1)), std::runtime_error);
}

TEST_F(SequentialEquivalenceStrategyTests,
       ResetExpressionProofProfileDisablesSpeculativePreprocessingForModerateProofs) {
  SATSolverWrapper solver(KEPLER_FORMAL::Config::SolverType::KISSAT);
  solver.configureForSecResetExpressionProof(/*coneSymbols=*/1000);

  // Sampling on AES PDR showed moderate reset-expression UNSAT checks spending
  // their wall time in Kissat's probe/sweep/kitten preprocessing. These checks
  // are short-lived local proofs, so the PDR profile should avoid speculative
  // simplification even below the generic large-cone threshold.
  auto* kissatSolver = static_cast<kissat*>(solver.getSolver());
  EXPECT_EQ(kissat_get_option(kissatSolver, "preprocess"), 0);
  EXPECT_EQ(kissat_get_option(kissatSolver, "simplify"), 0);
  EXPECT_EQ(kissat_get_option(kissatSolver, "preprocesscongruence"), 0);
  EXPECT_EQ(kissat_get_option(kissatSolver, "preprocessprobe"), 0);
  EXPECT_EQ(kissat_get_option(kissatSolver, "congruence"), 0);
  EXPECT_EQ(kissat_get_option(kissatSolver, "probe"), 0);
  EXPECT_EQ(kissat_get_option(kissatSolver, "probeinit"), 0);
  EXPECT_EQ(kissat_get_option(kissatSolver, "eliminateinit"), 0);
}

TEST_F(SequentialEquivalenceStrategyTests,
       KissatResourceLimitedSolveReportsUnknownInsteadOfUnsat) {
  SATSolverWrapper limitedSolver(KEPLER_FORMAL::Config::SolverType::KISSAT);
  limitedSolver.configureForSecResetExpressionProof();
  const int x = limitedSolver.newVar() + 2;
  const int y = limitedSolver.newVar() + 2;
  limitedSolver.addClause({x, y});
  limitedSolver.addClause({-x, y});

  // Optional PDR shortcuts may cap Kissat work. A limit hit must be observable
  // as UNKNOWN so callers do not accidentally learn a bogus UNSAT cube.
  EXPECT_EQ(
      limitedSolver.solveWithKissatResourceLimits(
          std::numeric_limits<unsigned>::max(),
          /*decisionLimit=*/0),
      SATSolverWrapper::SolveStatus::Unknown);

  SATSolverWrapper unboundedSolver(KEPLER_FORMAL::Config::SolverType::KISSAT);
  unboundedSolver.configureForSecResetExpressionProof();
  const int ux = unboundedSolver.newVar() + 2;
  const int uy = unboundedSolver.newVar() + 2;
  unboundedSolver.addClause({ux, uy});
  unboundedSolver.addClause({-ux, uy});
  EXPECT_EQ(unboundedSolver.solveStatus(), SATSolverWrapper::SolveStatus::Sat);
}

TEST_F(SequentialEquivalenceStrategyTests,
       BaseCaseSolverFindsCombinationalCounterexampleAtFrameZero) {
  KInductionProblem problem;
  problem.environmentInputNames = {"in"};
  problem.observedOutputNames = {"out"};
  problem.inputSymbols = {2};
  problem.allSymbols = {2};
  problem.observedOutputExprs0 = {BoolExpr::Var(2)};
  problem.observedOutputExprs1 = {BoolExpr::Not(BoolExpr::Var(2))};
  problem.property = makeEqualityExpr(
      problem.observedOutputExprs0[0], problem.observedOutputExprs1[0]);
  problem.bad = BoolExpr::Not(problem.property);

  const auto witness = findBaseCounterexample(
      problem, KEPLER_FORMAL::Config::SolverType::KISSAT, 0);

  ASSERT_TRUE(witness.has_value());
  EXPECT_EQ(witness->badFrame, 0u);
  ASSERT_EQ(witness->inputTrace.size(), 1u);
  EXPECT_EQ(witness->inputTrace[0].frame, 0u);
  ASSERT_EQ(witness->outputMismatches.size(), 1u);
  EXPECT_EQ(witness->outputMismatches[0].signal, "out");
}

TEST_F(SequentialEquivalenceStrategyTests,
       BaseCaseSolverExistenceFrontierKeepsMultiOutputBatchTogether) {
  KInductionProblem problem;
  problem.observedOutputNames = {"out0", "out1"};
  problem.inputSymbols = {2, 3};
  problem.allSymbols = {2, 3};
  problem.observedOutputExprs0 = {BoolExpr::Var(2), BoolExpr::Var(3)};
  problem.observedOutputExprs1 = {BoolExpr::Var(2), BoolExpr::Var(3)};
  problem.property = BoolExpr::And(
      makeEqualityExpr(problem.observedOutputExprs0[0],
                       problem.observedOutputExprs1[0]),
      makeEqualityExpr(problem.observedOutputExprs0[1],
                       problem.observedOutputExprs1[1]));
  problem.bad = BoolExpr::Not(problem.property);

  const ScopedEnvVar kiDiag("KEPLER_SEC_KI_DIAG", "1");
  testing::internal::CaptureStderr();
  EXPECT_FALSE(hasBaseCounterexampleAtFrontier(
      problem, KEPLER_FORMAL::Config::SolverType::KISSAT, 0));
  const std::string stderrOutput = testing::internal::GetCapturedStderr();

  size_t diagCount = 0;
  size_t pos = 0;
  while ((pos = stderrOutput.find("SEC diag: k-induction base coi", pos)) !=
         std::string::npos) {
    ++diagCount;
    ++pos;
  }
  EXPECT_EQ(diagCount, 1u) << stderrOutput;
}

TEST_F(SequentialEquivalenceStrategyTests,
       BaseCaseSolverPdrProofOnlyDoesNotChaseUnrelatedStartupEqualityChain) {
  KInductionProblem problem;
  constexpr size_t x = 2;
  constexpr size_t y = 3;
  problem.state0Symbols = {x, y};
  problem.allSymbols = {x, y};
  problem.initialStateAssignments = {{y, false}};
  problem.initializedStateCount = 1;
  problem.initialCondition = BoolExpr::Not(BoolExpr::Var(y));
  problem.transitions0.emplace_back(x, BoolExpr::Var(y));
  problem.bad = BoolExpr::Var(x);
  problem.property = BoolExpr::Not(problem.bad);
  problem.inductionBad = problem.bad;
  problem.inductionProperty = problem.property;

  size_t previous = y;
  for (size_t i = 0; i < 128; ++i) {
    const size_t symbol = 4 + i;
    problem.state0Symbols.push_back(symbol);
    problem.allSymbols.push_back(symbol);
    problem.initialStateEqualityPairs.emplace_back(previous, symbol);
    previous = symbol;
  }
  problem.totalStateCount = problem.state0Symbols.size();

  const ScopedEnvVar kiDiag("KEPLER_SEC_KI_DIAG", "1");
  testing::internal::CaptureStderr();
  EXPECT_TRUE(provesNoBaseCounterexampleAtFrontier(
      problem, KEPLER_FORMAL::Config::SolverType::KISSAT, 1));
  const std::string stderrOutput = testing::internal::GetCapturedStderr();

  EXPECT_NE(stderrOutput.find("solver_symbols=2"), std::string::npos)
      << stderrOutput;
  EXPECT_NE(stderrOutput.find("transition_targets=1"), std::string::npos)
      << stderrOutput;
}

TEST_F(SequentialEquivalenceStrategyTests,
       BaseCaseSolverObservationOnlyStartsSearchingAtFrameOne) {
  KInductionProblem problem;
  problem.environmentInputNames = {"in"};
  problem.observedOutputNames = {"out"};
  problem.inputSymbols = {2};
  problem.state0Symbols = {3};
  problem.state1Symbols = {4};
  problem.allSymbols = {2, 3, 4};
  problem.observedOutputExprs0 = {BoolExpr::Var(3)};
  problem.observedOutputExprs1 = {BoolExpr::Var(4)};
  problem.transitions0 = {{3, BoolExpr::Var(2)}};
  problem.transitions1 = {{4, BoolExpr::createFalse()}};
  problem.property = makeEqualityExpr(
      problem.observedOutputExprs0[0], problem.observedOutputExprs1[0]);
  problem.bad = BoolExpr::Not(problem.property);

  const auto witness = findBaseCounterexample(
      problem, KEPLER_FORMAL::Config::SolverType::KISSAT, 1);

  ASSERT_TRUE(witness.has_value());
  EXPECT_EQ(witness->badFrame, 1u);
  ASSERT_EQ(witness->inputTrace.size(), 2u);
  EXPECT_EQ(witness->inputTrace.front().frame, 0u);
  EXPECT_EQ(witness->inputTrace.back().frame, 1u);
}

TEST_F(SequentialEquivalenceStrategyTests,
       BaseCaseSolverOffsetsWitnessAfterResetBootstrap) {
  KInductionProblem problem;
  problem.environmentInputNames = {"rst", "in"};
  problem.observedOutputNames = {"out"};
  problem.inputSymbols = {2, 5};
  problem.resetBootstrapCycles = 2;
  problem.resetBootstrapInputs = {{2, true}};
  problem.bootstrapStateAssignments = {{3, false}, {4, false}};
  problem.bootstrapStateEqualityPairs = {{3, 4}};
  problem.state0Symbols = {3};
  problem.state1Symbols = {4};
  problem.allSymbols = {2, 3, 4, 5};
  problem.observedOutputExprs0 = {BoolExpr::Var(3)};
  problem.observedOutputExprs1 = {BoolExpr::Var(4)};
  problem.transitions0 = {{3, BoolExpr::Var(5)}};
  problem.transitions1 = {{4, BoolExpr::createFalse()}};
  problem.property = makeEqualityExpr(
      problem.observedOutputExprs0[0], problem.observedOutputExprs1[0]);
  problem.bad = BoolExpr::Not(problem.property);

  const auto witness = findBaseCounterexample(
      problem, KEPLER_FORMAL::Config::SolverType::KISSAT, 1);

  ASSERT_TRUE(witness.has_value());
  EXPECT_EQ(witness->badFrame, 1u);
  ASSERT_EQ(witness->inputTrace.size(), 2u);
  EXPECT_EQ(witness->inputTrace[0].frame, 0u);
  ASSERT_EQ(witness->inputTrace[0].assignments.size(), 2u);
  EXPECT_EQ(witness->inputTrace[0].assignments[0].signal, "rst");
  EXPECT_FALSE(witness->inputTrace[0].assignments[0].value);
}

TEST_F(SequentialEquivalenceStrategyTests,
       BaseCaseSolverHandlesActiveLowResetBootstrapInputs) {
  KInductionProblem problem;
  problem.environmentInputNames = {"rst_n", "in"};
  problem.observedOutputNames = {"out"};
  problem.inputSymbols = {2, 5};
  problem.resetBootstrapCycles = 1;
  problem.resetBootstrapInputs = {{2, false}};
  problem.bootstrapStateAssignments = {{3, false}, {4, false}};
  problem.state0Symbols = {3};
  problem.state1Symbols = {4};
  problem.allSymbols = {2, 3, 4, 5};
  problem.observedOutputExprs0 = {BoolExpr::Var(3)};
  problem.observedOutputExprs1 = {BoolExpr::Var(4)};
  problem.transitions0 = {{3, BoolExpr::Var(5)}};
  problem.transitions1 = {{4, BoolExpr::createFalse()}};
  problem.property = makeEqualityExpr(
      problem.observedOutputExprs0[0], problem.observedOutputExprs1[0]);
  problem.bad = BoolExpr::Not(problem.property);

  const auto witness = findBaseCounterexample(
      problem, KEPLER_FORMAL::Config::SolverType::KISSAT, 2);

  ASSERT_TRUE(witness.has_value());
  EXPECT_EQ(witness->badFrame, 1u);
  ASSERT_EQ(witness->inputTrace.size(), 2u);
  // The reported witness trace is offset past the hidden bootstrap frame,
  // so an active-low reset is already deasserted in the visible input trace.
  EXPECT_TRUE(witness->inputTrace[0].assignments[0].value);
  EXPECT_TRUE(witness->inputTrace[1].assignments[0].value);
}

TEST_F(SequentialEquivalenceStrategyTests,
       BaseCaseSolverPartialInitWithoutStateRelationUsesObservationFallback) {
  KInductionProblem problem;
  problem.environmentInputNames = {"in"};
  problem.observedOutputNames = {"out"};
  problem.inputSymbols = {2};
  problem.state0Symbols = {3};
  problem.state1Symbols = {4};
  problem.allSymbols = {2, 3, 4};
  problem.observedOutputExprs0 = {BoolExpr::Var(3)};
  problem.observedOutputExprs1 = {BoolExpr::Var(4)};
  problem.transitions0 = {{3, BoolExpr::Var(2)}};
  problem.transitions1 = {{4, BoolExpr::createFalse()}};
  problem.initialCondition = BoolExpr::Not(BoolExpr::Var(3));
  problem.initializedStateCount = 1;
  problem.totalStateCount = 2;
  problem.property = makeEqualityExpr(
      problem.observedOutputExprs0[0], problem.observedOutputExprs1[0]);
  problem.bad = BoolExpr::Not(problem.property);

  const auto witness = findBaseCounterexample(
      problem, KEPLER_FORMAL::Config::SolverType::KISSAT, 1);

  ASSERT_TRUE(witness.has_value());
  EXPECT_EQ(witness->badFrame, 1u);
}

TEST_F(SequentialEquivalenceStrategyTests,
       BaseCaseSolverPartialInitWithStateRelationKeepsFrameZeroAligned) {
  KInductionProblem problem;
  problem.environmentInputNames = {"in"};
  problem.observedOutputNames = {"out"};
  problem.inputSymbols = {2};
  problem.state0Symbols = {3};
  problem.state1Symbols = {4};
  problem.allSymbols = {2, 3, 4};
  problem.observedOutputExprs0 = {BoolExpr::Var(3)};
  problem.observedOutputExprs1 = {BoolExpr::Var(4)};
  problem.transitions0 = {{3, BoolExpr::Var(2)}};
  problem.transitions1 = {{4, BoolExpr::createFalse()}};
  problem.initialCondition = BoolExpr::Not(BoolExpr::Var(3));
  problem.initializedStateCount = 1;
  problem.totalStateCount = 2;
  problem.initialStateEqualityPairs = {{3, 4}};
  problem.property = makeEqualityExpr(
      problem.observedOutputExprs0[0], problem.observedOutputExprs1[0]);
  problem.bad = BoolExpr::Not(problem.property);

  const auto witness = findBaseCounterexample(
      problem, KEPLER_FORMAL::Config::SolverType::KISSAT, 1);

  ASSERT_TRUE(witness.has_value());
  EXPECT_EQ(witness->badFrame, 1u);
}

TEST_F(SequentialEquivalenceStrategyTests,
       ExactInterpolantSynthesizerDerivesOneStepReachableStateInvariant) {
  KInductionProblem problem;
  problem.state0Symbols = {2};
  problem.allSymbols = {2, 3};
  problem.inputSymbols = {3};
  problem.transitions0.emplace_back(2, BoolExpr::createFalse());
  problem.initialCondition = BoolExpr::Not(BoolExpr::Var(2));
  problem.initializedStateCount = 1;
  problem.totalStateCount = 1;
  problem.bad = BoolExpr::Var(2);
  problem.property = BoolExpr::Not(problem.bad);
  problem.inductionProperty = problem.property;
  problem.inductionBad = problem.bad;

  ExactInterpolantSynthesizer engine(
      problem, KEPLER_FORMAL::Config::SolverType::KISSAT);
  const auto interpolant = engine.deriveOneStepReachableStateInvariant(4);

  ASSERT_TRUE(interpolant.has_value());
  EXPECT_TRUE((*interpolant)->evaluate({{2, false}}));
  EXPECT_FALSE((*interpolant)->evaluate({{2, true}}));
}

TEST_F(SequentialEquivalenceStrategyTests,
       ExactInterpolantSynthesizerReturnsNulloptWhenStateBudgetIsExceeded) {
  KInductionProblem problem;
  problem.state0Symbols = {2, 3};
  problem.allSymbols = {2, 3};
  problem.transitions0.emplace_back(2, BoolExpr::Var(2));
  problem.transitions0.emplace_back(3, BoolExpr::Var(3));
  problem.initialCondition =
      BoolExpr::And(BoolExpr::Not(BoolExpr::Var(2)), BoolExpr::Not(BoolExpr::Var(3)));
  problem.initializedStateCount = 2;
  problem.totalStateCount = 2;
  problem.bad = BoolExpr::Var(2);
  problem.property = BoolExpr::Not(problem.bad);
  problem.inductionProperty = problem.property;
  problem.inductionBad = problem.bad;

  ExactInterpolantSynthesizer engine(
      problem, KEPLER_FORMAL::Config::SolverType::KISSAT);
  const auto interpolant = engine.deriveOneStepReachableStateInvariant(1);

  EXPECT_FALSE(interpolant.has_value());
}

TEST_F(SequentialEquivalenceStrategyTests,
       ExactInterpolantSynthesizerReturnsNulloptWhenBadIsReachableInOneStep) {
  KInductionProblem problem;
  problem.state0Symbols = {2};
  problem.allSymbols = {2};
  problem.transitions0.emplace_back(2, BoolExpr::createTrue());
  problem.initialCondition = BoolExpr::Not(BoolExpr::Var(2));
  problem.initializedStateCount = 1;
  problem.totalStateCount = 1;
  problem.bad = BoolExpr::Var(2);
  problem.property = BoolExpr::Not(problem.bad);
  problem.inductionProperty = problem.property;
  problem.inductionBad = problem.bad;

  ExactInterpolantSynthesizer engine(
      problem, KEPLER_FORMAL::Config::SolverType::KISSAT);
  const auto interpolant = engine.deriveOneStepReachableStateInvariant(4);

  EXPECT_FALSE(interpolant.has_value());
}

TEST_F(SequentialEquivalenceStrategyTests,
       ExactInterpolantSynthesizerRejectsNonInductiveInterpolant) {
  KInductionProblem problem;
  problem.state0Symbols = {2, 3};
  problem.allSymbols = {2, 3};
  problem.transitions0.emplace_back(2, BoolExpr::Var(3));
  problem.transitions0.emplace_back(3, BoolExpr::createTrue());
  problem.initialCondition =
      BoolExpr::And(BoolExpr::Not(BoolExpr::Var(2)), BoolExpr::Not(BoolExpr::Var(3)));
  problem.initializedStateCount = 2;
  problem.totalStateCount = 2;
  problem.bad = BoolExpr::Var(2);
  problem.property = BoolExpr::Not(problem.bad);
  problem.inductionProperty = problem.property;
  problem.inductionBad = problem.bad;

  ExactInterpolantSynthesizer engine(
      problem, KEPLER_FORMAL::Config::SolverType::KISSAT);
  const auto interpolant = engine.deriveOneStepReachableStateInvariant(4);

  EXPECT_FALSE(interpolant.has_value());
}

TEST_F(SequentialEquivalenceStrategyTests,
       ExactInterpolantSynthesizerUsesBootstrapAssignmentsAndComplementedStatePairs) {
  KInductionProblem problem;
  problem.state0Symbols = {2, 3};
  problem.allSymbols = {2, 3};
  problem.resetBootstrapCycles = 1;
  problem.bootstrapStateAssignments = {{2, false}, {3, true}};
  problem.bootstrapStateEqualityPairs = {{2, 2}};
  problem.complementedStatePairs0 = {{2, 3}};
  problem.transitions0.emplace_back(2, BoolExpr::createFalse());
  problem.transitions0.emplace_back(3, BoolExpr::createTrue());
  problem.bad = BoolExpr::Var(2);
  problem.property = BoolExpr::Not(problem.bad);
  problem.inductionProperty = problem.property;
  problem.inductionBad = problem.bad;

  ExactInterpolantSynthesizer engine(
      problem, KEPLER_FORMAL::Config::SolverType::KISSAT);
  const auto interpolant = engine.deriveOneStepReachableStateInvariant(4);

  ASSERT_TRUE(interpolant.has_value());
  EXPECT_TRUE((*interpolant)->evaluate({{2, false}, {3, true}}));
  EXPECT_FALSE((*interpolant)->evaluate({{2, true}, {3, false}}));
}

TEST_F(SequentialEquivalenceStrategyTests,
       PDREngineProvesEquivalentSmallTransitionSystem) {
  KInductionProblem problem;
  problem.state0Symbols = {2};
  problem.allSymbols = {2};
  problem.transitions0.emplace_back(2, BoolExpr::createFalse());
  problem.initialCondition = BoolExpr::Not(BoolExpr::Var(2));
  problem.initializedStateCount = 1;
  problem.totalStateCount = 1;
  problem.bad = BoolExpr::Var(2);
  problem.property = BoolExpr::Not(problem.bad);
  problem.inductionProperty = problem.property;
  problem.inductionBad = problem.bad;

  PDREngine engine(problem, KEPLER_FORMAL::Config::SolverType::KISSAT);
  const auto result = engine.run(3);

  EXPECT_EQ(result.status, PDRStatus::Equivalent);
  EXPECT_LE(result.bound, 1u);
}

TEST_F(SequentialEquivalenceStrategyTests,
       PDREngineFullyGeneralizesCheapConstantBlockedWideCubes) {
  KInductionProblem problem;
  constexpr size_t kStateCount = 512;
  const size_t firstStateSymbol = 2;
  const size_t constantFalseSymbol = firstStateSymbol + kStateCount - 1;

  BoolExpr* bad = BoolExpr::createTrue();
  BoolExpr* init = BoolExpr::createTrue();
  problem.state0Symbols.reserve(kStateCount);
  problem.allSymbols.reserve(kStateCount);
  for (size_t index = 0; index < kStateCount; ++index) {
    const size_t symbol = firstStateSymbol + index;
    problem.state0Symbols.push_back(symbol);
    problem.allSymbols.push_back(symbol);
    init = BoolExpr::And(init, BoolExpr::Not(BoolExpr::Var(symbol)));
    bad = BoolExpr::And(bad, BoolExpr::Var(symbol));
    // Only the last target bit is impossible. The other bits are constants that
    // make the first bad cube wide, matching the ASIC case where the actual
    // predecessor surface was tiny but the blocked cube had many literals.
    problem.transitions0.emplace_back(
        symbol,
        symbol == constantFalseSymbol ? BoolExpr::createFalse()
                                      : BoolExpr::createTrue());
  }
  problem.initialCondition = BoolExpr::simplify(init);
  problem.initializedStateCount = kStateCount;
  problem.totalStateCount = kStateCount;
  problem.bad = BoolExpr::simplify(bad);
  problem.property = BoolExpr::Not(problem.bad);
  problem.inductionProperty = problem.property;
  problem.inductionBad = problem.bad;

  const ScopedEnvVar secPdrTrace("KEPLER_SEC_PDR_TRACE", "1");
  testing::internal::CaptureStderr();
  PDREngine engine(
      problem,
      KEPLER_FORMAL::Config::SolverType::KISSAT,
      /*predecessorProjectionLimit=*/kStateCount,
      /*preciseBadCubeStateLimit=*/kStateCount);
  const auto result = engine.run(2);
  const std::string stderrOutput = testing::internal::GetCapturedStderr();

  EXPECT_EQ(result.status, PDRStatus::Equivalent);
  EXPECT_NE(
      stderrOutput.find("(!x" + std::to_string(constantFalseSymbol) + ")\n"),
      std::string::npos);
}

TEST_F(SequentialEquivalenceStrategyTests,
       PDREngineUsesPredecessorCoresForProjectedWideBlockedCubes) {
  KInductionProblem problem;
  constexpr size_t kStateCount = 96;
  constexpr size_t firstStateSymbol = 2;

  BoolExpr* init = BoolExpr::createTrue();
  BoolExpr* bad = BoolExpr::createTrue();
  problem.state0Symbols.reserve(kStateCount);
  problem.allSymbols.reserve(kStateCount);
  for (size_t index = 0; index < kStateCount; ++index) {
    const size_t symbol = firstStateSymbol + index;
    problem.state0Symbols.push_back(symbol);
    problem.allSymbols.push_back(symbol);
    init = BoolExpr::And(init, BoolExpr::Not(BoolExpr::Var(symbol)));
    bad = BoolExpr::And(bad, BoolExpr::Var(symbol));
    problem.initialStateAssignments.push_back({symbol, false});
    // Keep the cheap 8-literal seed reachable, but make the full wide cube
    // unreachable through the remaining identity-held reset-low bits.
    problem.transitions0.emplace_back(
        symbol,
        index < 8 ? BoolExpr::createTrue() : BoolExpr::Var(symbol));
  }
  problem.initialCondition = BoolExpr::simplify(init);
  problem.initializedStateCount = kStateCount;
  problem.totalStateCount = kStateCount;
  problem.bad = BoolExpr::simplify(bad);
  problem.property = BoolExpr::Not(problem.bad);
  problem.inductionProperty = problem.property;
  problem.inductionBad = problem.bad;

  // BlackParrot sampling showed projected-frame stages learning many adjacent
  // wide blockers. The predecessor-core path is still sound in projected mode:
  // if a weaker frame query cannot reach the reduced cube, the complete frame
  // cannot reach it either.
  const ScopedEnvVar pdrStats("KEPLER_SEC_PDR_STATS", "1");
  const ScopedEnvVar pdrStatsInterval("KEPLER_SEC_PDR_STATS_INTERVAL", "1");
  testing::internal::CaptureStderr();
  PDREngine engine(
      problem,
      KEPLER_FORMAL::Config::SolverType::KISSAT,
      /*predecessorProjectionLimit=*/kStateCount,
      /*preciseBadCubeStateLimit=*/kStateCount,
      /*useExactFrameClauses=*/false);
  const auto result = engine.run(2);
  const std::string stderrOutput = testing::internal::GetCapturedStderr();

  EXPECT_EQ(result.status, PDRStatus::Equivalent);
  EXPECT_NE(
      stderrOutput.find("predecessor core target=96->1 source_level=0"),
      std::string::npos)
      << stderrOutput;
}

TEST_F(SequentialEquivalenceStrategyTests,
       PDREngineUsesPredecessorCoresForMediumSupportWideBlockedCubes) {
  KInductionProblem problem;
  constexpr size_t kStateCount = 96;
  constexpr size_t kHeldStateCount = 16;
  constexpr size_t firstStateSymbol = 2;

  BoolExpr* init = BoolExpr::createTrue();
  BoolExpr* bad = BoolExpr::createTrue();
  problem.state0Symbols.reserve(kStateCount);
  problem.allSymbols.reserve(kStateCount);
  for (size_t index = 0; index < kStateCount; ++index) {
    const size_t symbol = firstStateSymbol + index;
    problem.state0Symbols.push_back(symbol);
    problem.allSymbols.push_back(symbol);
    init = BoolExpr::And(init, BoolExpr::Not(BoolExpr::Var(symbol)));
    bad = BoolExpr::And(bad, BoolExpr::Var(symbol));
    problem.initialStateAssignments.push_back({symbol, false});
    const bool heldResetLow =
        index >= 8 && index < 8 + kHeldStateCount;
    problem.transitions0.emplace_back(
        symbol, heldResetLow ? BoolExpr::Var(symbol) : BoolExpr::createTrue());
  }
  problem.initialCondition = BoolExpr::simplify(init);
  problem.initializedStateCount = kStateCount;
  problem.totalStateCount = kStateCount;
  problem.bad = BoolExpr::simplify(bad);
  problem.property = BoolExpr::Not(problem.bad);
  problem.inductionProperty = problem.property;
  problem.inductionBad = problem.bad;

  // The cheap 8-literal seed is reachable, while the full wide cube is blocked
  // by a medium-sized transition surface. BlackParrot produced thousands of
  // such 68/88-literal blockers, so wide cubes should try the predecessor-core
  // oracle before bounded chunk dropping even when their support is not huge.
  const ScopedEnvVar pdrStats("KEPLER_SEC_PDR_STATS", "1");
  const ScopedEnvVar pdrStatsInterval("KEPLER_SEC_PDR_STATS_INTERVAL", "1");
  testing::internal::CaptureStderr();
  PDREngine engine(
      problem,
      KEPLER_FORMAL::Config::SolverType::KISSAT,
      /*predecessorProjectionLimit=*/kStateCount,
      /*preciseBadCubeStateLimit=*/kStateCount,
      /*useExactFrameClauses=*/false);
  const auto result = engine.run(2);
  const std::string stderrOutput = testing::internal::GetCapturedStderr();

  EXPECT_EQ(result.status, PDRStatus::Equivalent);
  EXPECT_NE(
      stderrOutput.find("predecessor core target=96->1 source_level=0"),
      std::string::npos)
      << stderrOutput;
}

TEST_F(SequentialEquivalenceStrategyTests,
       PDREngineUsesPredecessorCoresForMediumHighSupportBlockedCubes) {
  KInductionProblem problem;
  constexpr size_t kTargetStateCount = 12;
  constexpr size_t kSupportStateCount = 40;
  constexpr size_t firstStateSymbol = 2;
  constexpr size_t firstSupportSymbol = firstStateSymbol + kTargetStateCount;

  BoolExpr* init = BoolExpr::createTrue();
  BoolExpr* bad = BoolExpr::createTrue();
  BoolExpr* wideSupport = BoolExpr::createTrue();
  problem.state0Symbols.reserve(kTargetStateCount + kSupportStateCount);
  problem.allSymbols.reserve(kTargetStateCount + kSupportStateCount);
  for (size_t index = 0; index < kSupportStateCount; ++index) {
    const size_t symbol = firstSupportSymbol + index;
    problem.state0Symbols.push_back(symbol);
    problem.allSymbols.push_back(symbol);
    init = BoolExpr::And(init, BoolExpr::Not(BoolExpr::Var(symbol)));
    problem.initialStateAssignments.push_back({symbol, false});
    problem.transitions0.emplace_back(symbol, BoolExpr::Var(symbol));
    wideSupport = BoolExpr::And(wideSupport, BoolExpr::Var(symbol));
  }
  for (size_t index = 0; index < kTargetStateCount; ++index) {
    const size_t symbol = firstStateSymbol + index;
    problem.state0Symbols.push_back(symbol);
    problem.allSymbols.push_back(symbol);
    init = BoolExpr::And(init, BoolExpr::Not(BoolExpr::Var(symbol)));
    bad = BoolExpr::And(bad, BoolExpr::Var(symbol));
    problem.initialStateAssignments.push_back({symbol, false});
    // The first four target bits keep the cheap seed reachable. The remaining
    // target bits depend on a broad support cone that is false in the startup
    // frontier, matching the measured AES 12-literal, 113-support level-zero
    // blockers that were too small for the old medium predecessor-core gate
    // but still expensive to learn one neighboring valuation at a time.
    problem.transitions0.emplace_back(
        symbol,
        index < 4
            ? BoolExpr::createTrue()
            : BoolExpr::And(BoolExpr::Var(symbol), wideSupport));
  }
  problem.initialCondition = BoolExpr::simplify(init);
  problem.initializedStateCount = kTargetStateCount + kSupportStateCount;
  problem.totalStateCount = kTargetStateCount + kSupportStateCount;
  problem.bad = BoolExpr::simplify(bad);
  problem.property = BoolExpr::Not(problem.bad);
  problem.inductionProperty = problem.property;
  problem.inductionBad = problem.bad;

  const ScopedEnvVar pdrStats("KEPLER_SEC_PDR_STATS", "1");
  const ScopedEnvVar pdrStatsInterval("KEPLER_SEC_PDR_STATS_INTERVAL", "1");
  testing::internal::CaptureStderr();
  PDREngine engine(
      problem,
      KEPLER_FORMAL::Config::SolverType::KISSAT,
      /*predecessorProjectionLimit=*/kTargetStateCount + kSupportStateCount,
      /*preciseBadCubeStateLimit=*/kTargetStateCount,
      /*useExactFrameClauses=*/false);
  const auto result = engine.run(2);
  const std::string stderrOutput = testing::internal::GetCapturedStderr();

  EXPECT_EQ(result.status, PDRStatus::Equivalent);
  EXPECT_NE(
      stderrOutput.find("predecessor core target=12->1 source_level=0"),
      std::string::npos)
      << stderrOutput;
}

TEST_F(SequentialEquivalenceStrategyTests,
       PDREngineFindsReachableBadState) {
  KInductionProblem problem;
  problem.state0Symbols = {2};
  problem.allSymbols = {2};
  problem.transitions0.emplace_back(2, BoolExpr::createTrue());
  problem.initialCondition = BoolExpr::Not(BoolExpr::Var(2));
  problem.initializedStateCount = 1;
  problem.totalStateCount = 1;
  problem.bad = BoolExpr::Var(2);
  problem.property = BoolExpr::Not(problem.bad);
  problem.inductionProperty = problem.property;
  problem.inductionBad = problem.bad;

  PDREngine engine(problem, KEPLER_FORMAL::Config::SolverType::KISSAT);
  const auto result = engine.run(3);

  EXPECT_EQ(result.status, PDRStatus::Different);
  EXPECT_EQ(result.bound, 1u);
}

TEST_F(SequentialEquivalenceStrategyTests,
       PDREngineFindsOneStepCounterexampleForDocumentedBooleanMiter) {
  const auto problem = buildDocumentedBooleanPdrCounterexampleProblem();

  PDREngine engine(problem, KEPLER_FORMAL::Config::SolverType::KISSAT);
  const auto result = engine.run(3);

  EXPECT_EQ(result.status, PDRStatus::Different);
  EXPECT_EQ(result.bound, 1u);
}

TEST_F(SequentialEquivalenceStrategyTests,
       PDREngineProjectsBadCubesToRelevantStateSupport) {
  auto problem = buildDocumentedBooleanPdrCounterexampleProblem();
  problem.state0Symbols.push_back(5);
  problem.allSymbols.push_back(5);
  problem.initialCondition = BoolExpr::And(
      problem.initialCondition, BoolExpr::Not(BoolExpr::Var(5)));
  problem.transitions0.emplace_back(
      5, BoolExpr::Xor(BoolExpr::Var(5), BoolExpr::Var(4)));

  const ScopedEnvVar secPdrTrace("KEPLER_SEC_PDR_TRACE", "1");
  testing::internal::CaptureStderr();
  PDREngine engine(problem, KEPLER_FORMAL::Config::SolverType::KISSAT);
  const auto result = engine.run(1);
  const std::string stderrOutput = testing::internal::GetCapturedStderr();

  ASSERT_EQ(result.status, PDRStatus::Different);
  const auto badCubePos = stderrOutput.find("SEC PDR trace: bad_cube@F1");
  ASSERT_NE(badCubePos, std::string::npos);
  const auto nextTracePos = stderrOutput.find("SEC PDR trace:", badCubePos + 1);
  const std::string badCubeTrace = stderrOutput.substr(
      badCubePos,
      nextTracePos == std::string::npos ? std::string::npos
                                        : nextTracePos - badCubePos);
  EXPECT_NE(badCubeTrace.find("x2="), std::string::npos);
  EXPECT_NE(badCubeTrace.find("x3="), std::string::npos);
  EXPECT_EQ(badCubeTrace.find("x5"), std::string::npos);
}

TEST_F(SequentialEquivalenceStrategyTests,
       PDREngineUsesObservationOnlyFrontierWithoutExplicitInit) {
  KInductionProblem problem;
  problem.state0Symbols = {2};
  problem.allSymbols = {2};
  problem.transitions0.emplace_back(2, BoolExpr::createFalse());
  problem.totalStateCount = 1;
  problem.bad = BoolExpr::Var(2);
  problem.property = BoolExpr::Not(problem.bad);
  problem.inductionProperty = problem.property;
  problem.inductionBad = problem.bad;

  PDREngine engine(problem, KEPLER_FORMAL::Config::SolverType::KISSAT);
  const auto result = engine.run(4);

  EXPECT_EQ(result.status, PDRStatus::Equivalent);
  EXPECT_EQ(result.bound, 1u);
}

TEST_F(SequentialEquivalenceStrategyTests,
       PDREngineDoesNotUseImmediateProofWhenFrameBudgetIsZero) {
  KInductionProblem problem;
  problem.state0Symbols = {2};
  problem.allSymbols = {2};
  problem.transitions0.emplace_back(2, BoolExpr::createFalse());
  problem.initialCondition = BoolExpr::Not(BoolExpr::Var(2));
  problem.initializedStateCount = 1;
  problem.totalStateCount = 1;
  problem.bad = BoolExpr::Var(2);
  problem.property = BoolExpr::Not(problem.bad);
  problem.inductionProperty = problem.property;
  problem.inductionBad = problem.bad;

  PDREngine engine(problem, KEPLER_FORMAL::Config::SolverType::KISSAT);
  const auto result = engine.run(0);

  EXPECT_EQ(result.status, PDRStatus::Inconclusive);
  EXPECT_EQ(result.bound, 0u);
}

TEST_F(SequentialEquivalenceStrategyTests,
       PDREngineUsesBootstrapAssignmentsAndComplementedStatePairs) {
  KInductionProblem problem;
  problem.state0Symbols = {2, 3};
  problem.allSymbols = {2, 3};
  problem.resetBootstrapCycles = 1;
  problem.bootstrapStateAssignments = {{2, false}, {3, true}};
  problem.bootstrapStateEqualityPairs = {{2, 2}};
  problem.complementedStatePairs0 = {{2, 3}};
  problem.transitions0.emplace_back(2, BoolExpr::createFalse());
  problem.transitions0.emplace_back(3, BoolExpr::createTrue());
  problem.bad = BoolExpr::Var(2);
  problem.property = BoolExpr::Not(problem.bad);
  problem.inductionProperty = problem.property;
  problem.inductionBad = problem.bad;

  PDREngine engine(problem, KEPLER_FORMAL::Config::SolverType::KISSAT);
  const auto result = engine.run(2);

  EXPECT_EQ(result.status, PDRStatus::Equivalent);
}

TEST_F(SequentialEquivalenceStrategyTests,
       PDREngineDoesNotReuseNonInductiveStrengtheningAsFrameInvariant) {
  KInductionProblem problem;
  problem.state0Symbols = {2, 3};
  problem.allSymbols = {2, 3};
  problem.initialCondition =
      BoolExpr::And(BoolExpr::Not(BoolExpr::Var(2)), BoolExpr::Not(BoolExpr::Var(3)));
  problem.initializedStateCount = 2;
  problem.totalStateCount = 2;
  problem.transitions0.emplace_back(2, BoolExpr::createTrue());
  problem.transitions0.emplace_back(3, BoolExpr::Var(2));
  problem.bad = BoolExpr::Var(3);
  problem.property = BoolExpr::Not(problem.bad);
  // Init implies !x, but it is not inductive: x becomes true in the next step.
  // Reusing it as a frame fact would incorrectly hide the real bad state 11.
  problem.inductionProperty = BoolExpr::Not(BoolExpr::Var(2));
  problem.inductionBad = BoolExpr::Not(problem.inductionProperty);

  PDREngine engine(problem, KEPLER_FORMAL::Config::SolverType::KISSAT);
  const auto result = engine.run(3);

  EXPECT_EQ(result.status, PDRStatus::Different);
  EXPECT_EQ(result.bound, 2u);
}

TEST_F(SequentialEquivalenceStrategyTests,
       PDREngineTriesSharedStrengtheningBeforeWeakStateSubsetFallback) {
  KInductionProblem problem;
  problem.state0Symbols = {2, 3, 4, 5, 6, 7};
  problem.allSymbols = problem.state0Symbols;
  BoolExpr* init = BoolExpr::createTrue();
  for (const auto symbol : problem.state0Symbols) {
    init = BoolExpr::And(init, BoolExpr::Not(BoolExpr::Var(symbol)));
  }
  problem.initialCondition = BoolExpr::simplify(init);
  problem.initializedStateCount = problem.state0Symbols.size();
  problem.totalStateCount = problem.state0Symbols.size();
  problem.transitions0.emplace_back(2, BoolExpr::createFalse());
  problem.transitions0.emplace_back(3, BoolExpr::createFalse());
  problem.transitions0.emplace_back(4, BoolExpr::createFalse());
  problem.transitions0.emplace_back(5, BoolExpr::createFalse());
  problem.transitions0.emplace_back(6, BoolExpr::createTrue());
  problem.transitions0.emplace_back(7, BoolExpr::createFalse());
  // The full equality set fails because 6==7 is not inductive, but pruning can
  // still find the weaker 2==3 subset. PDR should not stop there: the shared
  // strengthening below is also valid and can be strictly stronger for SEC.
  problem.inductiveStateEqualityPairs = {{2, 3}, {6, 7}};
  problem.observedOutputExprs0 = {BoolExpr::Var(6)};
  problem.observedOutputExprs1 = {BoolExpr::Var(7)};
  problem.bad = BoolExpr::Var(5);
  problem.property = BoolExpr::Not(problem.bad);
  problem.inductionProperty = BoolExpr::Not(BoolExpr::Var(4));
  problem.inductionBad = BoolExpr::Not(problem.inductionProperty);

  const ScopedEnvVar pdrStats("KEPLER_SEC_PDR_STATS", "1");
  testing::internal::CaptureStderr();
  PDREngine engine(problem, KEPLER_FORMAL::Config::SolverType::KISSAT);
  const auto result = engine.run(1);
  const std::string stderrOutput = testing::internal::GetCapturedStderr();

  EXPECT_EQ(result.status, PDRStatus::Equivalent);
  EXPECT_NE(
      stderrOutput.find("frame invariant shared_strengthening"),
      std::string::npos);
}

TEST_F(SequentialEquivalenceStrategyTests,
       PDREngineUsesPropertyAsFallbackImmediateProof) {
  KInductionProblem problem;
  problem.state0Symbols = {2};
  problem.allSymbols = {2};
  problem.initialCondition = BoolExpr::Not(BoolExpr::Var(2));
  problem.initializedStateCount = 1;
  problem.totalStateCount = 1;
  problem.transitions0.emplace_back(2, BoolExpr::createFalse());
  problem.bad = BoolExpr::Var(2);
  problem.property = BoolExpr::Not(problem.bad);
  // This strengthening is not implied by Init, so PDR must fall back to the
  // checked SEC property instead of dropping straight into the full clause loop.
  problem.inductionProperty = BoolExpr::Var(2);
  problem.inductionBad = BoolExpr::Not(problem.inductionProperty);

  PDREngine engine(problem, KEPLER_FORMAL::Config::SolverType::KISSAT);
  const auto result = engine.run(3);

  EXPECT_EQ(result.status, PDRStatus::Equivalent);
  EXPECT_EQ(result.bound, 1u);
}

TEST_F(SequentialEquivalenceStrategyTests,
       PDREngineProvesEquivalentExactlyAtThreeFrames) {
  const auto problem = buildLinearChainSecProblem(4);

  PDREngine engine(problem, KEPLER_FORMAL::Config::SolverType::KISSAT);
  const auto result = engine.run(3);

  EXPECT_EQ(result.status, PDRStatus::Equivalent);
  EXPECT_EQ(result.bound, 3u);
}

TEST_F(SequentialEquivalenceStrategyTests,
       PdrDebugFormattingPrintsDocumentedBooleanMiterProblemAndFrames) {
  const auto problem = buildDocumentedBooleanPdrCounterexampleProblem();

  const std::string formattedProblem = formatKInductionProblemForDebug(problem);
  EXPECT_NE(formattedProblem.find("description: documented Boolean PDR counterexample miter"),
            std::string::npos);
  EXPECT_NE(formattedProblem.find("state0_symbols: [x2]"), std::string::npos);
  EXPECT_NE(formattedProblem.find("state1_symbols: [x3]"), std::string::npos);
  EXPECT_NE(formattedProblem.find("input_symbols: [x4]"), std::string::npos);
  EXPECT_NE(formattedProblem.find("transition_formula:"), std::string::npos);
  EXPECT_NE(formattedProblem.find("x2' = ~x2"), std::string::npos);
  EXPECT_NE(formattedProblem.find("x3' = x3 AND x4"), std::string::npos);
  EXPECT_NE(formattedProblem.find("bad: x2 XOR x3"), std::string::npos);

  const ScopedEnvVar secPdrTrace("KEPLER_SEC_PDR_TRACE", "1");
  testing::internal::CaptureStderr();
  PDREngine engine(problem, KEPLER_FORMAL::Config::SolverType::KISSAT);
  const auto result = engine.run(1);
  const std::string stderrOutput = testing::internal::GetCapturedStderr();

  EXPECT_EQ(result.status, PDRStatus::Different);
  EXPECT_EQ(result.bound, 1u);
  EXPECT_NE(stderrOutput.find("SEC PDR trace: problem"), std::string::npos);
  EXPECT_NE(stderrOutput.find("transition_formula:"), std::string::npos);
  EXPECT_NE(stderrOutput.find("SEC PDR trace: seeded_frames"), std::string::npos);
  EXPECT_NE(stderrOutput.find("F[1]"), std::string::npos);
  EXPECT_NE(stderrOutput.find("SEC PDR trace: bad_cube@F1"), std::string::npos);
  EXPECT_NE(stderrOutput.find("{x2=1, x3=0}"), std::string::npos);
}

TEST_F(SequentialEquivalenceStrategyTests,
       ProofProblemDebugFormatsConstantsInvalidExpressionsAndMultiplePairs) {
  BoolExpr invalid;
  KInductionProblem problem;
  problem.description = "debug edge cases";
  problem.allSymbols = {0, 1, 2};
  problem.state0Symbols = {0, 1};
  problem.initialStateEqualityPairs = {{0, 1}, {1, 2}};
  problem.bootstrapStateEqualityPairs = {{0, 1}, {1, 2}};
  problem.inductiveStateEqualityPairs = {{0, 1}, {1, 2}};
  problem.transitions0.emplace_back(0, &invalid);
  problem.property = BoolExpr::Not(BoolExpr::Var(0));
  problem.bad = BoolExpr::Var(1);

  const std::string formattedProblem = formatKInductionProblemForDebug(problem);

  EXPECT_NE(formattedProblem.find("state0_symbols: [FALSE, TRUE]"),
            std::string::npos);
  EXPECT_NE(formattedProblem.find("initial_state_equalities: [FALSE=TRUE, TRUE=x2]"),
            std::string::npos);
  EXPECT_NE(formattedProblem.find("FALSE' = <invalid>"), std::string::npos);
}

TEST_F(SequentialEquivalenceStrategyTests,
       KInductionEngineProvesEquivalentSmallTransitionSystem) {
  KInductionProblem problem;
  problem.state0Symbols = {2};
  problem.allSymbols = {2};
  problem.transitions0.emplace_back(2, BoolExpr::createFalse());
  problem.initialCondition = BoolExpr::Not(BoolExpr::Var(2));
  problem.initializedStateCount = 1;
  problem.totalStateCount = 1;
  problem.bad = BoolExpr::Var(2);
  problem.property = BoolExpr::Not(problem.bad);
  problem.inductionProperty = problem.property;
  problem.inductionBad = problem.bad;

  KInductionEngine engine(problem, KEPLER_FORMAL::Config::SolverType::KISSAT);
  const auto result = engine.run(3);

  EXPECT_EQ(result.status, KInductionStatus::Equivalent);
  EXPECT_LE(result.bound, 1u);
}

TEST_F(SequentialEquivalenceStrategyTests,
       KInductionEngineBatchesSmallOutputProofs) {
  KInductionProblem problem;
  for (size_t i = 0; i < 40; ++i) {
    const size_t symbol = 2 + i;
    problem.allSymbols.push_back(symbol);
    problem.observedOutputNames.push_back("out" + std::to_string(i));
    problem.observedOutputExprs0.push_back(BoolExpr::Var(symbol));
    problem.observedOutputExprs1.push_back(BoolExpr::Var(symbol));
  }

  const ScopedEnvVar kiDiag("KEPLER_SEC_KI_DIAG", "1");
  testing::internal::CaptureStderr();
  KInductionEngine engine(problem, KEPLER_FORMAL::Config::SolverType::KISSAT);
  const auto result = engine.run(1);
  const std::string stderrOutput = testing::internal::GetCapturedStderr();

  size_t baseChecks = 0;
  size_t pos = 0;
  const std::string needle = "SEC diag: k-induction base k=0 begin";
  while ((pos = stderrOutput.find(needle, pos)) != std::string::npos) {
    ++baseChecks;
    pos += needle.size();
  }

  EXPECT_EQ(result.status, KInductionStatus::Equivalent);
  EXPECT_EQ(baseChecks, 2u);
  EXPECT_NE(stderrOutput.find("SEC diag: k-induction problem outputs=40"),
            std::string::npos);
}

TEST_F(SequentialEquivalenceStrategyTests,
       SupportBoundedOutputBatchingKeepsModerateOutputSlicesTogether) {
  KInductionProblem problem;
  for (size_t i = 0; i < 40; ++i) {
    const size_t symbol = 2 + i;
    problem.allSymbols.push_back(symbol);
    problem.observedOutputNames.push_back("out" + std::to_string(i));
    problem.observedOutputExprs0.push_back(BoolExpr::Var(symbol));
    problem.observedOutputExprs1.push_back(BoolExpr::Var(symbol));
  }

  // PDR uses this moderate output-batch shape to avoid hundreds of identical
  // one-output proof attempts while still bounding each SAT cone by output
  // count and support.
  const auto batches =
      buildSupportBoundedOutputBatches(problem, OutputBatchingLimits{16, 512});

  ASSERT_EQ(batches.size(), 3u);
  EXPECT_EQ(batches[0], (std::pair<size_t, size_t>(0, 16)));
  EXPECT_EQ(batches[1], (std::pair<size_t, size_t>(16, 32)));
  EXPECT_EQ(batches[2], (std::pair<size_t, size_t>(32, 40)));
}

TEST_F(SequentialEquivalenceStrategyTests,
       KInductionEngineFindsReachableBadState) {
  KInductionProblem problem;
  problem.state0Symbols = {2};
  problem.allSymbols = {2};
  problem.transitions0.emplace_back(2, BoolExpr::createTrue());
  problem.initialCondition = BoolExpr::Not(BoolExpr::Var(2));
  problem.initializedStateCount = 1;
  problem.totalStateCount = 1;
  problem.bad = BoolExpr::Var(2);
  problem.property = BoolExpr::Not(problem.bad);
  problem.inductionProperty = problem.property;
  problem.inductionBad = problem.bad;

  KInductionEngine engine(problem, KEPLER_FORMAL::Config::SolverType::KISSAT);
  const auto result = engine.run(3);

  EXPECT_EQ(result.status, KInductionStatus::Different);
  ASSERT_TRUE(result.witness.has_value());
  EXPECT_EQ(result.bound, 1u);
  EXPECT_EQ(result.witness->badFrame, 1u);
}

TEST_F(SequentialEquivalenceStrategyTests,
       KInductionEngineDiagnosticsCoverCounterexampleAndInconclusivePaths) {
  {
    KInductionProblem problem;
    problem.allSymbols = {2};
    problem.bad = BoolExpr::createTrue();
    problem.property = BoolExpr::createFalse();
    problem.inductionProperty = problem.property;
    problem.inductionBad = problem.bad;

    const ScopedEnvVar secDiag("KEPLER_SEC_DIAG", "1");
    testing::internal::CaptureStderr();
    KInductionEngine engine(problem, KEPLER_FORMAL::Config::SolverType::KISSAT);
    const auto result = engine.run(3);
    const std::string stderrOutput = testing::internal::GetCapturedStderr();

    EXPECT_EQ(result.status, KInductionStatus::Different);
    EXPECT_EQ(result.bound, 0u);
    EXPECT_NE(
        stderrOutput.find("SEC diag: k-induction base k=0 found cex"),
        std::string::npos);
  }

  {
    KInductionProblem problem;
    problem.state0Symbols = {2};
    problem.allSymbols = {2};
    problem.transitions0.emplace_back(2, BoolExpr::createTrue());
    problem.initialCondition = BoolExpr::Not(BoolExpr::Var(2));
    problem.initializedStateCount = 1;
    problem.totalStateCount = 1;
    problem.bad = BoolExpr::Var(2);
    problem.property = BoolExpr::Not(problem.bad);
    problem.inductionProperty = problem.property;
    problem.inductionBad = problem.bad;

    const ScopedEnvVar secDiag("KEPLER_SEC_DIAG", "1");
    testing::internal::CaptureStderr();
    KInductionEngine engine(problem, KEPLER_FORMAL::Config::SolverType::KISSAT);
    const auto result = engine.run(3);
    const std::string stderrOutput = testing::internal::GetCapturedStderr();

    EXPECT_EQ(result.status, KInductionStatus::Different);
    EXPECT_EQ(result.bound, 1u);
    EXPECT_NE(
        stderrOutput.find("SEC diag: k-induction base k=1 found cex"),
        std::string::npos);
  }

  {
    const auto problem = buildLinearChainSecProblem(6);

    const ScopedEnvVar secDiag("KEPLER_SEC_DIAG", "1");
    testing::internal::CaptureStderr();
    KInductionEngine engine(problem, KEPLER_FORMAL::Config::SolverType::KISSAT);
    const auto result = engine.run(4);
    const std::string stderrOutput = testing::internal::GetCapturedStderr();

    EXPECT_EQ(result.status, KInductionStatus::Inconclusive);
    EXPECT_EQ(result.bound, 4u);
    EXPECT_NE(
        stderrOutput.find("SEC diag: k-induction step k=4 inconclusive"),
        std::string::npos);
  }
}

TEST_F(SequentialEquivalenceStrategyTests,
       IMCEngineProvesEquivalentWithExactInterpolant) {
  KInductionProblem problem;
  problem.state0Symbols = {2, 3};
  problem.allSymbols = {2, 3};
  problem.transitions0.emplace_back(2, BoolExpr::Var(3));
  problem.transitions0.emplace_back(3, BoolExpr::createFalse());
  problem.initialCondition =
      BoolExpr::And(BoolExpr::Not(BoolExpr::Var(2)), BoolExpr::Not(BoolExpr::Var(3)));
  problem.initializedStateCount = 2;
  problem.totalStateCount = 2;
  problem.bad = BoolExpr::Var(2);
  problem.property = BoolExpr::Not(problem.bad);
  problem.inductionProperty = problem.property;
  problem.inductionBad = problem.bad;

  IMCEngine engine(problem, KEPLER_FORMAL::Config::SolverType::KISSAT);
  const auto result = engine.run(3);

  EXPECT_EQ(result.status, IMCStatus::Equivalent);
  EXPECT_EQ(result.bound, 1u);
}

TEST_F(SequentialEquivalenceStrategyTests,
       IMCEngineUsesValidatedSharedStrengtheningInvariant) {
  KInductionProblem problem;
  problem.observedOutputNames = {"out"};
  problem.state0Symbols = {2, 3};
  problem.state1Symbols = {4, 5};
  problem.allSymbols = {2, 3, 4, 5};
  problem.observedOutputExprs0 = {BoolExpr::Var(2)};
  problem.observedOutputExprs1 = {BoolExpr::Var(4)};
  problem.transitions0 = {{2, BoolExpr::Var(3)}, {3, BoolExpr::Var(3)}};
  problem.transitions1 = {{4, BoolExpr::Var(5)}, {5, BoolExpr::Var(5)}};
  problem.initialCondition = BoolExpr::And(
      BoolExpr::And(BoolExpr::Not(BoolExpr::Var(2)), BoolExpr::Not(BoolExpr::Var(3))),
      BoolExpr::And(BoolExpr::Not(BoolExpr::Var(4)), BoolExpr::Not(BoolExpr::Var(5))));
  problem.initializedStateCount = 4;
  problem.totalStateCount = 4;
  problem.property =
      BoolExpr::Not(BoolExpr::Xor(BoolExpr::Var(2), BoolExpr::Var(4)));
  problem.bad = BoolExpr::Xor(BoolExpr::Var(2), BoolExpr::Var(4));
  problem.inductionProperty = BoolExpr::And(
      BoolExpr::Not(BoolExpr::Xor(BoolExpr::Var(2), BoolExpr::Var(4))),
      BoolExpr::Not(BoolExpr::Xor(BoolExpr::Var(3), BoolExpr::Var(5))));
  problem.inductionBad = BoolExpr::Not(problem.inductionProperty);

  IMCEngine engine(problem, KEPLER_FORMAL::Config::SolverType::KISSAT);
  const auto result = engine.run(1);

  EXPECT_EQ(result.status, IMCStatus::Equivalent);
  EXPECT_EQ(result.bound, 1u);
}

TEST_F(SequentialEquivalenceStrategyTests,
       IMCEngineUsesObservationOnlyFrontierWithoutExplicitInit) {
  KInductionProblem problem;
  problem.state0Symbols = {2};
  problem.allSymbols = {2};
  problem.transitions0.emplace_back(2, BoolExpr::Var(2));
  problem.totalStateCount = 1;
  problem.bad = BoolExpr::Var(2);
  problem.property = BoolExpr::Not(problem.bad);
  problem.inductionProperty = problem.property;
  problem.inductionBad = problem.bad;

  IMCEngine engine(problem, KEPLER_FORMAL::Config::SolverType::KISSAT);
  const auto result = engine.run(1);

  EXPECT_EQ(result.status, IMCStatus::Equivalent);
  EXPECT_EQ(result.bound, 1u);
}

TEST_F(SequentialEquivalenceStrategyTests,
       IMCEngineFindsReachableBadState) {
  KInductionProblem problem;
  problem.state0Symbols = {2};
  problem.allSymbols = {2};
  problem.transitions0.emplace_back(2, BoolExpr::createTrue());
  problem.initialCondition = BoolExpr::Not(BoolExpr::Var(2));
  problem.initializedStateCount = 1;
  problem.totalStateCount = 1;
  problem.bad = BoolExpr::Var(2);
  problem.property = BoolExpr::Not(problem.bad);
  problem.inductionProperty = problem.property;
  problem.inductionBad = problem.bad;

  IMCEngine engine(problem, KEPLER_FORMAL::Config::SolverType::KISSAT);
  const auto result = engine.run(3);

  EXPECT_EQ(result.status, IMCStatus::Different);
  ASSERT_TRUE(result.witness.has_value());
  EXPECT_EQ(result.bound, 1u);
  EXPECT_EQ(result.witness->badFrame, 1u);
}

TEST_F(SequentialEquivalenceStrategyTests,
       IMCEngineProvesEquivalentExactlyAtThreeFrames) {
  const auto problem = buildLinearChainSecProblem(4);

  IMCEngine engine(problem, KEPLER_FORMAL::Config::SolverType::KISSAT);
  const auto result = engine.run(3);

  EXPECT_EQ(result.status, IMCStatus::Equivalent);
  EXPECT_EQ(result.bound, 3u);
}

TEST_F(SequentialEquivalenceStrategyTests,
       IMCEngineBatchesFallbackInductionForMultiOutputProblems) {
  auto problem = buildLinearChainSecProblem(4);
  problem.observedOutputNames = {"terminal_state", "low_state_bit"};
  problem.observedOutputExprs0.push_back(BoolExpr::Var(problem.state0Symbols.front()));
  problem.observedOutputExprs1.push_back(BoolExpr::Var(problem.state1Symbols.front()));

  BoolExpr* property = BoolExpr::createTrue();
  for (size_t i = 0; i < problem.observedOutputExprs0.size(); ++i) {
    property = BoolExpr::And(
        property,
        makeEqualityExpr(problem.observedOutputExprs0[i], problem.observedOutputExprs1[i]));
  }
  problem.property = BoolExpr::simplify(property);
  problem.bad = BoolExpr::simplify(BoolExpr::Not(problem.property));
  problem.inductionProperty = problem.property;
  problem.inductionBad = problem.bad;

  IMCEngine engine(problem, KEPLER_FORMAL::Config::SolverType::KISSAT);
  const auto result = engine.run(3);

  EXPECT_EQ(result.status, IMCStatus::Equivalent);
  EXPECT_EQ(result.bound, 2u);
}

TEST_F(SequentialEquivalenceStrategyTests,
       IMCEngineRemainsInconclusiveAtFourFramesWhenFiveAreNeeded) {
  const auto problem = buildLinearChainSecProblem(6);

  IMCEngine engine(problem, KEPLER_FORMAL::Config::SolverType::KISSAT);
  const auto result = engine.run(4);

  EXPECT_EQ(result.status, IMCStatus::Inconclusive);
  EXPECT_EQ(result.bound, 4u);
}

TEST_F(SequentialEquivalenceStrategyTests,
       KInductionEngineProvesEquivalentExactlyAtThreeFrames) {
  const auto problem = buildLinearChainSecProblem(4);

  KInductionEngine engine(problem, KEPLER_FORMAL::Config::SolverType::KISSAT);
  const auto result = engine.run(3);

  EXPECT_EQ(result.status, KInductionStatus::Equivalent);
  EXPECT_EQ(result.bound, 3u);
}

TEST_F(SequentialEquivalenceStrategyTests,
       KInductionEngineRemainsInconclusiveAtFourFramesWhenFiveAreNeeded) {
  const auto problem = buildLinearChainSecProblem(6);

  KInductionEngine engine(problem, KEPLER_FORMAL::Config::SolverType::KISSAT);
  const auto result = engine.run(4);

  EXPECT_EQ(result.status, KInductionStatus::Inconclusive);
  EXPECT_EQ(result.bound, 4u);
}

TEST_F(SequentialEquivalenceStrategyTests,
       InductionStepSolverUsesExplicitInvariantWhenProvided) {
  KInductionProblem problem;
  problem.state0Symbols = {2};
  problem.state1Symbols = {3};
  problem.allSymbols = {2, 3};
  problem.transitions0 = {{2, BoolExpr::Var(2)}};
  problem.transitions1 = {{3, BoolExpr::Var(3)}};
  problem.property = BoolExpr::createTrue();
  problem.bad = BoolExpr::createFalse();
  problem.inductionProperty =
      makeEqualityExpr(BoolExpr::Var(2), BoolExpr::Var(3));
  problem.inductionBad = BoolExpr::Not(problem.inductionProperty);

  EXPECT_TRUE(
      provesByInduction(problem, KEPLER_FORMAL::Config::SolverType::KISSAT, 1));
}

TEST_F(SequentialEquivalenceStrategyTests,
       KInductionEngineCombinationalProblemReturnsImmediately) {
  KInductionProblem problem;
  problem.allSymbols = {2};
  problem.property = BoolExpr::createTrue();
  problem.bad = BoolExpr::createFalse();

  KInductionEngine engine(problem, KEPLER_FORMAL::Config::SolverType::KISSAT);
  const auto result = engine.run(3);

  EXPECT_EQ(result.status, KInductionStatus::Equivalent);
  EXPECT_EQ(result.bound, 0u);
}

TEST_F(SequentialEquivalenceStrategyTests,
       SequentialEquivalenceResultReportsZeroCoverageWhenNoOutputsExist) {
  SequentialEquivalenceResult result;

  EXPECT_EQ(result.outputCoveragePercent(), 0.0);
}

TEST_F(SequentialEquivalenceStrategyTests,
       RunExtractedModelsCountsSatImpliedOutputEquality) {
  const SignalKey out = makeSignalKey("out");
  const SignalKey stateA0 = makeSignalKey("stateA0");
  const SignalKey stateB0 = makeSignalKey("stateB0");
  const SignalKey stateA1 = makeSignalKey("stateA1");
  const SignalKey stateB1 = makeSignalKey("stateB1");

  SequentialDesignModel model0;
  model0.stateBits = {stateA0, stateB0};
  model0.allObservedOutputs = {out};
  model0.observedOutputs = {out};
  model0.inputVarByKey.emplace(stateA0, 2);
  model0.inputVarByKey.emplace(stateB0, 3);
  model0.displayNameByKey.emplace(out, "out[0]");
  model0.displayNameByKey.emplace(stateA0, "state_a[0]");
  model0.displayNameByKey.emplace(stateB0, "state_b[0]");
  model0.initialStateValueByKey.emplace(stateA0, false);
  model0.initialStateValueByKey.emplace(stateB0, false);
  model0.nextStateExprByStateKey.emplace(stateA0, BoolExpr::Var(2));
  model0.nextStateExprByStateKey.emplace(stateB0, BoolExpr::Var(3));
  model0.observedOutputExprByKey.emplace(
      out,
      BoolExpr::And(BoolExpr::Var(2), BoolExpr::Var(3)));

  SequentialDesignModel model1;
  model1.stateBits = {stateA1, stateB1};
  model1.allObservedOutputs = {out};
  model1.observedOutputs = {out};
  model1.inputVarByKey.emplace(stateA1, 4);
  model1.inputVarByKey.emplace(stateB1, 5);
  model1.displayNameByKey.emplace(out, "out[0]");
  model1.displayNameByKey.emplace(stateA1, "state_a[0]");
  model1.displayNameByKey.emplace(stateB1, "state_b[0]");
  model1.initialStateValueByKey.emplace(stateA1, false);
  model1.initialStateValueByKey.emplace(stateB1, false);
  model1.nextStateExprByStateKey.emplace(stateA1, BoolExpr::Var(4));
  model1.nextStateExprByStateKey.emplace(stateB1, BoolExpr::Var(5));
  model1.observedOutputExprByKey.emplace(
      out,
      BoolExpr::Not(BoolExpr::Or(
          BoolExpr::Not(BoolExpr::Var(4)),
          BoolExpr::Not(BoolExpr::Var(5)))));

  const ScopedEnvVar secDiag("KEPLER_SEC_DIAG", "1");
  testing::internal::CaptureStdout();
  SequentialEquivalenceStrategy strategy(
      nullptr,
      nullptr,
      KEPLER_FORMAL::Config::SolverType::KISSAT,
      SecEngine::KInduction);
  const auto result = strategy.runExtractedModels(model0, model1, 1);
  const std::string stdoutOutput = testing::internal::GetCapturedStdout();

  EXPECT_EQ(result.status, SequentialEquivalenceStatus::Equivalent);
  EXPECT_EQ(result.bound, 1u);
  EXPECT_NE(
      stdoutOutput.find("sat_implied_outputs=1"),
      std::string::npos);
}

TEST_F(SequentialEquivalenceStrategyTests,
       RunExtractedModelsStopsOnUnsupportedFirstModelWithBoundaryReports) {
  auto model0 = makeCombinationalExtractedModel(BoolExpr::Var(2));
  auto model1 = makeCombinationalExtractedModel(BoolExpr::Var(2));
  const SignalKey stateKey = makeSignalKey("state");
  const SignalKey internalIn = makeSignalKey("internal_in");
  const SignalKey internalOut = makeSignalKey("internal_out");
  model0.unsupportedReasons = {"unsupported sequential state"};
  model0.abstractedSequentialBoundaries = {"abstracted cell u_ff"};
  model0.internalBoundaryInputKeys = {internalIn};
  model0.internalBoundaryOutputKeys = {internalOut};
  model0.displayNameByKey.emplace(stateKey, "u_ff.STATE[0]");
  model0.displayNameByKey.emplace(internalIn, "u_logic.A[0]");
  model0.displayNameByKey.emplace(internalOut, "u_logic.Y[0]");
  model0.abstractedSequentialBoundaryDetails.push_back(
      {"u_ff", {stateKey}, model0.allObservedOutputs});

  SequentialEquivalenceStrategy strategy(
      nullptr, nullptr, KEPLER_FORMAL::Config::SolverType::KISSAT);
  const auto result = strategy.runExtractedModels(model0, model1, 1);

  EXPECT_EQ(result.status, SequentialEquivalenceStatus::Unsupported);
  EXPECT_NE(result.reason.find("unsupported sequential state"), std::string::npos);
  ASSERT_EQ(result.abstractedSequentialBoundaries.size(), 1u);
  EXPECT_EQ(result.abstractedSequentialBoundaries.front(),
            "design0 abstracted cell u_ff");
  EXPECT_GE(result.extractedBoundaryReports.size(), 4u);
  const auto stateReport = std::find_if(
      result.extractedBoundaryReports.begin(),
      result.extractedBoundaryReports.end(),
      [](const ExtractedBoundaryReportEntry& entry) {
        return entry.signal == "u_ff.STATE[0]";
      });
  ASSERT_NE(stateReport, result.extractedBoundaryReports.end());
  EXPECT_NE(
      std::find(
          stateReport->roles.begin(),
          stateReport->roles.end(),
          "abstracted_sequential_state"),
      stateReport->roles.end());
}

TEST_F(SequentialEquivalenceStrategyTests,
       RunExtractedModelsStopsOnUnsupportedSecondModelAfterFirstReports) {
  auto model0 = makeCombinationalExtractedModel(BoolExpr::Var(2));
  auto model1 = makeCombinationalExtractedModel(BoolExpr::Var(2));
  model0.abstractedSequentialBoundaries = {"kept first-side boundary"};
  model1.unsupportedReasons = {"unsupported second side"};

  SequentialEquivalenceStrategy strategy(
      nullptr, nullptr, KEPLER_FORMAL::Config::SolverType::KISSAT);
  const auto result = strategy.runExtractedModels(model0, model1, 1);

  EXPECT_EQ(result.status, SequentialEquivalenceStatus::Unsupported);
  EXPECT_NE(result.reason.find("unsupported second side"), std::string::npos);
  ASSERT_EQ(result.abstractedSequentialBoundaries.size(), 1u);
  EXPECT_EQ(result.abstractedSequentialBoundaries.front(),
            "design0 kept first-side boundary");
}

TEST_F(SequentialEquivalenceStrategyTests,
       RunExtractedModelsReportsAllConnectivitySkippedOutputs) {
  SequentialDesignModel model0;
  SequentialDesignModel model1;
  std::array<ConnectivitySkipOrigin, 3> origins = {
      ConnectivitySkipOrigin::NoDriver,
      ConnectivitySkipOrigin::MultiDriver,
      ConnectivitySkipOrigin::LogicalLoop};
  for (size_t i = 0; i < origins.size(); ++i) {
    const SignalKey key = makeSignalKey("skipped_out_" + std::to_string(i));
    const std::string name = "out" + std::to_string(i) + "[0]";
    model0.allObservedOutputs.push_back(key);
    model1.allObservedOutputs.push_back(key);
    model0.displayNameByKey.emplace(key, name);
    model1.displayNameByKey.emplace(key, name);
    model0.connectivitySkipInfoByKey.emplace(
        key, ConnectivitySkipInfo{origins[i], "left side"});
    model1.connectivitySkipInfoByKey.emplace(
        key, ConnectivitySkipInfo{origins[i], "right side"});
  }

  SequentialEquivalenceStrategy strategy(
      nullptr, nullptr, KEPLER_FORMAL::Config::SolverType::KISSAT);
  const auto result = strategy.runExtractedModels(model0, model1, 1);

  EXPECT_EQ(result.status, SequentialEquivalenceStatus::Unsupported);
  EXPECT_EQ(result.coveredOutputs, 0u);
  EXPECT_EQ(result.totalOutputs, origins.size());
  ASSERT_EQ(result.skippedObservedOutputs.size(), origins.size());
  const auto hasSkipText = [&](const char* text) {
    return std::any_of(
        result.skippedObservedOutputs.begin(),
        result.skippedObservedOutputs.end(),
        [&](const std::string& skipped) {
          return skipped.find(text) != std::string::npos;
        });
  };
  EXPECT_TRUE(hasSkipText("no-driver connectivity"));
  EXPECT_TRUE(hasSkipText("multi-driver connectivity"));
  EXPECT_TRUE(hasSkipText("logical-loop connectivity"));
}

TEST_F(SequentialEquivalenceStrategyTests,
       RunExtractedModelsReportsMissingOutputExpression) {
  auto model0 = makeCombinationalExtractedModel(BoolExpr::Var(2));
  auto model1 = makeCombinationalExtractedModel(BoolExpr::Var(2));
  model1.observedOutputExprByKey.clear();

  SequentialEquivalenceStrategy strategy(
      nullptr, nullptr, KEPLER_FORMAL::Config::SolverType::KISSAT);
  const auto result = strategy.runExtractedModels(model0, model1, 1);

  EXPECT_EQ(result.status, SequentialEquivalenceStatus::Unsupported);
  EXPECT_NE(
      result.reason.find("Missing observed output expression"),
      std::string::npos);
}

TEST_F(SequentialEquivalenceStrategyTests,
       RunExtractedModelsReportsObservedOutputCoverageMismatch) {
  auto model0 = makeCombinationalExtractedModel(BoolExpr::Var(2));
  auto model1 = makeCombinationalExtractedModel(BoolExpr::Var(2));
  const SignalKey extraKey = makeSignalKey("extra_observed");
  model0.observedOutputs.push_back(extraKey);
  model1.observedOutputs.push_back(extraKey);
  model0.displayNameByKey.emplace(extraKey, "extra[0]");
  model1.displayNameByKey.emplace(extraKey, "extra[0]");

  SequentialEquivalenceStrategy strategy(
      nullptr, nullptr, KEPLER_FORMAL::Config::SolverType::KISSAT);
  const auto result = strategy.runExtractedModels(model0, model1, 1);

  EXPECT_EQ(result.status, SequentialEquivalenceStatus::Unsupported);
  EXPECT_NE(result.reason.find("checked observed outputs"), std::string::npos);
}

TEST_F(SequentialEquivalenceStrategyTests,
       RunExtractedModelsAcceptsSameValueModelWithoutBuildingSatProblem) {
  const auto model = makeCombinationalExtractedModel(BoolExpr::Var(2));

  SequentialEquivalenceStrategy strategy(
      nullptr, nullptr, KEPLER_FORMAL::Config::SolverType::KISSAT);
  const auto result = strategy.runExtractedModels(model, model, 9);

  EXPECT_EQ(result.status, SequentialEquivalenceStatus::Equivalent);
  EXPECT_EQ(result.bound, 0u);
  EXPECT_EQ(result.coveredOutputs, 1u);
  EXPECT_EQ(result.totalOutputs, 1u);
  EXPECT_EQ(result.outputCoveragePercent(), 100.0);
}

TEST_F(SequentialEquivalenceStrategyTests,
       RunExtractedModelsEmitsSelectedEngineDiagnostics) {
  const auto model0 = makeCombinationalExtractedModel(BoolExpr::Var(2));
  const auto model1 = makeCombinationalExtractedModel(BoolExpr::Var(2));
  const ScopedEnvVar secDiag("KEPLER_SEC_DIAG", "1");
  const std::array<std::pair<SecEngine, const char*>, 4> expected = {{
      {SecEngine::Pdr, "pdr engine"},
      {SecEngine::Imc, "imc engine"},
      {SecEngine::KInduction, "classic k-induction engine"},
      {SecEngine::Legacy, "legacy engine"},
  }};

  for (const auto& [engine, label] : expected) {
    testing::internal::CaptureStderr();
    SequentialEquivalenceStrategy strategy(
        nullptr, nullptr, KEPLER_FORMAL::Config::SolverType::KISSAT, engine);
    const auto result = strategy.runExtractedModels(model0, model1, 1);
    const std::string stderrOutput = testing::internal::GetCapturedStderr();

    EXPECT_EQ(result.status, SequentialEquivalenceStatus::Equivalent);
    EXPECT_NE(stderrOutput.find(label), std::string::npos);
  }
}

TEST_F(SequentialEquivalenceStrategyTests,
       RunExtractedModelsFormatsCompactCounterexampleWithoutDnlTraceback) {
  const auto model0 = makeCombinationalExtractedModel(BoolExpr::Var(2));
  const auto model1 = makeCombinationalExtractedModel(BoolExpr::createTrue());

  SequentialEquivalenceStrategy strategy(
      nullptr,
      nullptr,
      KEPLER_FORMAL::Config::SolverType::KISSAT,
      SecEngine::KInduction);
  const auto result = strategy.runExtractedModels(model0, model1, 0);

  EXPECT_EQ(result.status, SequentialEquivalenceStatus::Different);
  EXPECT_EQ(result.bound, 0u);
  EXPECT_NE(result.reason.find("Counterexample reaches"), std::string::npos);
  EXPECT_NE(result.reason.find("compact SEC released"), std::string::npos);
}

TEST_F(SequentialEquivalenceStrategyTests,
       PDREngineFindsInitialBadStateBeforeGrowingFrames) {
  KInductionProblem problem;
  problem.state0Symbols = {2};
  problem.allSymbols = {2};
  problem.transitions0.emplace_back(2, BoolExpr::createFalse());
  problem.initialCondition = BoolExpr::Var(2);
  problem.initializedStateCount = 1;
  problem.totalStateCount = 1;
  problem.bad = BoolExpr::Var(2);
  problem.property = BoolExpr::Not(problem.bad);
  problem.inductionProperty = problem.property;
  problem.inductionBad = problem.bad;

  const ScopedEnvVar secPdrTrace("KEPLER_SEC_PDR_TRACE", "1");
  testing::internal::CaptureStderr();
  PDREngine engine(problem, KEPLER_FORMAL::Config::SolverType::KISSAT);
  const auto result = engine.run(3);
  const std::string stderrOutput = testing::internal::GetCapturedStderr();

  EXPECT_EQ(result.status, PDRStatus::Different);
  EXPECT_EQ(result.bound, 0u);
  EXPECT_NE(stderrOutput.find("bad_cube@F0"), std::string::npos);
}

TEST_F(SequentialEquivalenceStrategyTests,
       PDREngineDoesNotTreatPartialBootstrapSummaryAsExactInitialState) {
  KInductionProblem problem;
  problem.state0Symbols = {2, 3};
  problem.inputSymbols = {4};
  problem.allSymbols = {2, 3, 4};
  problem.resetBootstrapCycles = 1;
  problem.resetBootstrapInputs = {{4, false}};
  // The bootstrap summary can be partial: x is known at the post-reset
  // frontier, while y is only known by actually unrolling the reset transition.
  problem.bootstrapStateAssignments = {{2, false}};
  problem.transitions0.emplace_back(2, BoolExpr::createFalse());
  problem.transitions0.emplace_back(3, BoolExpr::createFalse());
  problem.bad = BoolExpr::Var(3);
  problem.property = BoolExpr::Not(problem.bad);
  problem.inductionProperty = problem.property;
  problem.inductionBad = problem.bad;

  EXPECT_FALSE(
      findBaseCounterexample(
          problem, KEPLER_FORMAL::Config::SolverType::KISSAT, 0)
          .has_value());

  PDREngine engine(problem, KEPLER_FORMAL::Config::SolverType::KISSAT);
  const auto result = engine.run(2);

  EXPECT_EQ(result.status, PDRStatus::Equivalent);
}

TEST_F(SequentialEquivalenceStrategyTests,
       PDREngineRejectsBootstrapPredecessorsOutsideConcreteResetImage) {
  KInductionProblem problem;
  problem.state0Symbols = {2, 3};
  problem.inputSymbols = {4};
  problem.allSymbols = {2, 3, 4};
  problem.resetBootstrapCycles = 1;
  problem.resetBootstrapInputs = {{4, false}};
  // The summary proves x=0 at the post-reset frontier but says nothing about y.
  // The concrete reset unroll also forces y=0.  Without the level-0 refinement,
  // PDR can invent the abstract post-reset state y=1 and use it to reach x'=1.
  problem.bootstrapStateAssignments = {{2, false}};
  problem.transitions0.emplace_back(2, BoolExpr::And(BoolExpr::Var(4), BoolExpr::Var(3)));
  problem.transitions0.emplace_back(3, BoolExpr::createFalse());
  problem.bad = BoolExpr::Var(2);
  problem.property = BoolExpr::Not(problem.bad);
  problem.inductionProperty = problem.property;
  problem.inductionBad = problem.bad;

  EXPECT_FALSE(
      findBaseCounterexample(
          problem, KEPLER_FORMAL::Config::SolverType::KISSAT, 1)
          .has_value());

  PDREngine engine(problem, KEPLER_FORMAL::Config::SolverType::KISSAT);
  const auto result = engine.run(3);

  EXPECT_EQ(result.status, PDRStatus::Equivalent);
}

TEST_F(SequentialEquivalenceStrategyTests,
       PDREngineCanDeferExactResetFrontierChecksToCallerValidation) {
  KInductionProblem problem;
  problem.state0Symbols = {2, 3};
  problem.inputSymbols = {4};
  problem.allSymbols = {2, 3, 4};
  problem.resetBootstrapCycles = 1;
  problem.resetBootstrapInputs = {{4, false}};
  problem.bootstrapStateAssignments = {{2, false}};
  problem.transitions0.emplace_back(2, BoolExpr::And(BoolExpr::Var(4), BoolExpr::Var(3)));
  problem.transitions0.emplace_back(3, BoolExpr::createFalse());
  problem.bad = BoolExpr::Var(2);
  problem.property = BoolExpr::Not(problem.bad);
  problem.inductionProperty = problem.property;
  problem.inductionBad = problem.bad;

  ASSERT_FALSE(
      findBaseCounterexample(
          problem, KEPLER_FORMAL::Config::SolverType::KISSAT, 1)
          .has_value());

  PDREngine engine(
      problem,
      KEPLER_FORMAL::Config::SolverType::KISSAT,
      PDREngine::kDefaultPredecessorProjectionLimit,
      PDREngine::kDefaultPreciseBadCubeStateLimit,
      /*useExactFrameClauses=*/false,
      /*maxPredecessorQueries=*/0,
      /*refineProjectedCounterexamples=*/false,
      PDREngine::kDefaultBoundedRootGeneralizationAttempts,
      /*learnValidatedBadFormulaClauses=*/false,
      /*useExactResetFrontierChecks=*/false);
  const auto result = engine.run(3);

  // Projected SEC stages can return this abstract trace quickly because the
  // top-level SEC strategy immediately validates every PDR difference with the
  // exact bounded base-case query above before accepting it.
  EXPECT_EQ(result.status, PDRStatus::Different);
}

TEST_F(SequentialEquivalenceStrategyTests,
       PDREngineUsesCheapResetConstantFactsWhenExactResetChecksAreDisabled) {
  KInductionProblem problem;
  problem.state0Symbols = {2, 3};
  problem.inputSymbols = {4};
  problem.allSymbols = {2, 3, 4};
  problem.resetBootstrapCycles = 1;
  problem.resetBootstrapInputs = {{4, false}};
  problem.bootstrapStateAssignments = {{2, false}};
  problem.transitions0.emplace_back(2, BoolExpr::And(BoolExpr::Var(4), BoolExpr::Var(3)));
  problem.transitions0.emplace_back(3, BoolExpr::createFalse());
  problem.bad = BoolExpr::Var(2);
  problem.property = BoolExpr::Not(problem.bad);
  problem.inductionProperty = problem.property;
  problem.inductionBad = problem.bad;

  ASSERT_FALSE(
      findBaseCounterexample(
          problem, KEPLER_FORMAL::Config::SolverType::KISSAT, 1)
          .has_value());

  const ScopedEnvVar kiDiag("KEPLER_SEC_KI_DIAG", "1");
  testing::internal::CaptureStderr();
  PDREngine engine(
      problem,
      KEPLER_FORMAL::Config::SolverType::KISSAT,
      PDREngine::kDefaultPredecessorProjectionLimit,
      PDREngine::kDefaultPreciseBadCubeStateLimit,
      /*useExactFrameClauses=*/false,
      /*maxPredecessorQueries=*/0,
      /*refineProjectedCounterexamples=*/true,
      PDREngine::kDefaultBoundedRootGeneralizationAttempts,
      /*learnValidatedBadFormulaClauses=*/false,
      /*useExactResetFrontierChecks=*/false);
  const auto result = engine.run(3);
  const std::string stderrOutput = testing::internal::GetCapturedStderr();

  EXPECT_EQ(result.status, PDRStatus::Equivalent);
  EXPECT_EQ(stderrOutput.find("post_bootstrap_steps=1"), std::string::npos)
      << stderrOutput;
}

TEST_F(SequentialEquivalenceStrategyTests,
       PDREngineUsesResetSpecializedRelationsBeforeExactRootResetFrontier) {
  KInductionProblem problem;
  constexpr size_t x = 2;
  constexpr size_t y = 3;
  constexpr size_t w = 4;
  constexpr size_t reset = 5;
  problem.state0Symbols = {x, y, w};
  problem.inputSymbols = {reset};
  problem.allSymbols = {x, y, w, reset};
  problem.resetBootstrapCycles = 1;
  problem.resetBootstrapInputs = {{reset, true}};
  problem.transitions0.emplace_back(
      x,
      BoolExpr::And(
          BoolExpr::Not(BoolExpr::Var(reset)),
          BoolExpr::And(BoolExpr::Not(BoolExpr::Var(y)), BoolExpr::Var(w))));
  // The reset transition creates y == w at the F[0] frontier, but neither bit
  // is a reset constant.  This guards the sampled ASIC path where exact deeper
  // reset checks are disabled, yet PDR should still learn the abstract F[0]
  // predecessor is outside the concrete post-reset image before doing a wide
  // root-cube validation query.
  problem.transitions0.emplace_back(y, BoolExpr::Var(w));
  problem.transitions0.emplace_back(w, BoolExpr::Var(w));
  problem.bad = BoolExpr::Var(x);
  problem.property = BoolExpr::Not(problem.bad);
  problem.inductionProperty = problem.property;
  problem.inductionBad = problem.bad;

  ASSERT_FALSE(
      findBaseCounterexample(
          problem, KEPLER_FORMAL::Config::SolverType::KISSAT, 2)
          .has_value());

  const ScopedEnvVar pdrStats("KEPLER_SEC_PDR_STATS", "1");
  const ScopedEnvVar pdrStatsInterval("KEPLER_SEC_PDR_STATS_INTERVAL", "1");
  const ScopedEnvVar resetDiag("KEPLER_SEC_PDR_RESET_SHORTCUT_DIAG", "1");
  const ScopedEnvVar kiDiag("KEPLER_SEC_KI_DIAG", "1");
  testing::internal::CaptureStderr();
  PDREngine engine(
      problem,
      KEPLER_FORMAL::Config::SolverType::KISSAT,
      PDREngine::kDefaultPredecessorProjectionLimit,
      PDREngine::kDefaultPreciseBadCubeStateLimit,
      /*useExactFrameClauses=*/false,
      /*maxPredecessorQueries=*/0,
      /*refineProjectedCounterexamples=*/true,
      PDREngine::kDefaultBoundedRootGeneralizationAttempts,
      /*learnValidatedBadFormulaClauses=*/false,
      /*useExactResetFrontierChecks=*/false);
  const auto result = engine.run(3);
  const std::string stderrOutput = testing::internal::GetCapturedStderr();

  EXPECT_EQ(result.status, PDRStatus::Equivalent);
  EXPECT_EQ(stderrOutput.find("reset frontier cube coi"), std::string::npos)
      << stderrOutput;
  EXPECT_EQ(stderrOutput.find("post_bootstrap_steps=1"), std::string::npos)
      << stderrOutput;
}

TEST_F(SequentialEquivalenceStrategyTests,
       PDREngineUsesResetSpecializedExpressionSatBeforeExactRootResetFrontier) {
  KInductionProblem problem;
  constexpr size_t x = 2;
  constexpr size_t y = 3;
  constexpr size_t w = 4;
  constexpr size_t a = 5;
  constexpr size_t b = 6;
  constexpr size_t reset = 7;
  problem.state0Symbols = {x, y, w, a, b};
  problem.inputSymbols = {reset};
  problem.allSymbols = {x, y, w, a, b, reset};
  problem.resetBootstrapCycles = 1;
  problem.resetBootstrapInputs = {{reset, true}};
  problem.transitions0.emplace_back(
      x,
      BoolExpr::And(
          BoolExpr::Not(BoolExpr::Var(reset)),
          BoolExpr::And(BoolExpr::Var(y), BoolExpr::Not(BoolExpr::Var(w)))));
  // y and w reset to equivalent XNOR forms that are not reduced by the cheap
  // structural implication rules. This keeps the test focused on the bounded
  // expression-SAT shortcut instead of the faster syntactic reset proofs.
  problem.transitions0.emplace_back(
      y,
      BoolExpr::Or(
          BoolExpr::And(BoolExpr::Var(a), BoolExpr::Var(b)),
          BoolExpr::And(BoolExpr::Not(BoolExpr::Var(a)), BoolExpr::Not(BoolExpr::Var(b)))));
  problem.transitions0.emplace_back(
      w,
      BoolExpr::Not(BoolExpr::Xor(BoolExpr::Var(a), BoolExpr::Var(b))));
  problem.transitions0.emplace_back(a, BoolExpr::Var(a));
  problem.transitions0.emplace_back(b, BoolExpr::Var(b));
  problem.bad = BoolExpr::Var(x);
  problem.property = BoolExpr::Not(problem.bad);
  problem.inductionProperty = problem.property;
  problem.inductionBad = problem.bad;

  ASSERT_FALSE(
      findBaseCounterexample(
          problem, KEPLER_FORMAL::Config::SolverType::KISSAT, 2)
          .has_value());

  const ScopedEnvVar pdrStats("KEPLER_SEC_PDR_STATS", "1");
  const ScopedEnvVar pdrStatsInterval("KEPLER_SEC_PDR_STATS_INTERVAL", "1");
  const ScopedEnvVar resetDiag("KEPLER_SEC_PDR_RESET_SHORTCUT_DIAG", "1");
  const ScopedEnvVar kiDiag("KEPLER_SEC_KI_DIAG", "1");
  testing::internal::CaptureStderr();
  PDREngine engine(
      problem,
      KEPLER_FORMAL::Config::SolverType::KISSAT,
      PDREngine::kDefaultPredecessorProjectionLimit,
      PDREngine::kDefaultPreciseBadCubeStateLimit,
      /*useExactFrameClauses=*/false,
      /*maxPredecessorQueries=*/0,
      /*refineProjectedCounterexamples=*/true,
      PDREngine::kDefaultBoundedRootGeneralizationAttempts,
      /*learnValidatedBadFormulaClauses=*/false,
      /*useExactResetFrontierChecks=*/false);
  const auto result = engine.run(3);
  const std::string stderrOutput = testing::internal::GetCapturedStderr();

  EXPECT_EQ(result.status, PDRStatus::Equivalent);
  EXPECT_NE(
      stderrOutput.find("reset-specialized expression conflict"),
      std::string::npos)
      << stderrOutput;
  EXPECT_NE(
      stderrOutput.find("reset-specialized expression solver_profile=reset_expression"),
      std::string::npos)
      << stderrOutput;
  EXPECT_EQ(stderrOutput.find("reset frontier cube coi"), std::string::npos)
      << stderrOutput;
}

TEST_F(SequentialEquivalenceStrategyTests,
       PDREngineCanonicalizesInitialEqualitiesBeforeResetExpressionSatCap) {
  KInductionProblem problem;
  constexpr size_t x = 2;
  constexpr size_t y = 3;
  constexpr size_t w = 4;
  constexpr size_t reset = 5;
  constexpr size_t firstA = 6;
  constexpr size_t parityWidth = 385;
  constexpr size_t firstB = firstA + parityWidth;

  problem.state0Symbols = {x, y, w};
  problem.inputSymbols = {reset};
  problem.allSymbols = {x, y, w, reset};
  std::vector<size_t> aSymbols;
  std::vector<size_t> bSymbols;
  aSymbols.reserve(parityWidth);
  bSymbols.reserve(parityWidth);
  for (size_t index = 0; index < parityWidth; ++index) {
    const size_t a = firstA + index;
    const size_t b = firstB + index;
    aSymbols.push_back(a);
    bSymbols.push_back(b);
    problem.state0Symbols.push_back(a);
    problem.state0Symbols.push_back(b);
    problem.allSymbols.push_back(a);
    problem.allSymbols.push_back(b);
    problem.initialStateEqualityPairs.emplace_back(a, b);
    problem.transitions0.emplace_back(a, BoolExpr::Var(a));
    problem.transitions0.emplace_back(b, BoolExpr::Var(b));
  }

  auto leftAssociatedXor = [](const std::vector<size_t>& symbols) {
    BoolExpr* expr = BoolExpr::Var(symbols.front());
    for (size_t index = 1; index < symbols.size(); ++index) {
      expr = BoolExpr::Xor(expr, BoolExpr::Var(symbols[index]));
    }
    return expr;
  };
  auto rightAssociatedXor = [](const std::vector<size_t>& symbols) {
    BoolExpr* expr = BoolExpr::Var(symbols.back());
    for (size_t index = symbols.size() - 1; index-- > 0;) {
      expr = BoolExpr::Xor(BoolExpr::Var(symbols[index]), expr);
    }
    return expr;
  };

  problem.resetBootstrapCycles = 1;
  problem.resetBootstrapInputs = {{reset, true}};
  problem.transitions0.emplace_back(
      x,
      BoolExpr::And(
          BoolExpr::Not(BoolExpr::Var(reset)),
          BoolExpr::And(BoolExpr::Var(y), BoolExpr::Not(BoolExpr::Var(w)))));
  // The two parity cones are equivalent only after substituting the initial
  // SEC equality pairs a[i] == b[i]. Raw support closure contains both sides
  // and crosses the reset-expression SAT cap; the shortcut must canonicalize
  // those equalities before applying the cap so it can prove the contradiction
  // locally instead of falling into the sampled wide reset-frontier query.
  problem.transitions0.emplace_back(y, leftAssociatedXor(aSymbols));
  problem.transitions0.emplace_back(w, rightAssociatedXor(bSymbols));
  problem.bad = BoolExpr::Var(x);
  problem.property = BoolExpr::Not(problem.bad);
  problem.inductionProperty = problem.property;
  problem.inductionBad = problem.bad;

  ASSERT_FALSE(
      findBaseCounterexample(
          problem, KEPLER_FORMAL::Config::SolverType::KISSAT, 2)
          .has_value());

  const ScopedEnvVar pdrStats("KEPLER_SEC_PDR_STATS", "1");
  const ScopedEnvVar pdrStatsInterval("KEPLER_SEC_PDR_STATS_INTERVAL", "1");
  const ScopedEnvVar resetDiag("KEPLER_SEC_PDR_RESET_SHORTCUT_DIAG", "1");
  testing::internal::CaptureStderr();
  PDREngine engine(
      problem,
      KEPLER_FORMAL::Config::SolverType::KISSAT,
      PDREngine::kDefaultPredecessorProjectionLimit,
      PDREngine::kDefaultPreciseBadCubeStateLimit,
      /*useExactFrameClauses=*/false,
      /*maxPredecessorQueries=*/0,
      /*refineProjectedCounterexamples=*/true,
      PDREngine::kDefaultBoundedRootGeneralizationAttempts,
      /*learnValidatedBadFormulaClauses=*/false,
      /*useExactResetFrontierChecks=*/false);
  const auto result = engine.run(3);
  const std::string stderrOutput = testing::internal::GetCapturedStderr();

  EXPECT_EQ(result.status, PDRStatus::Equivalent);
  EXPECT_NE(
      stderrOutput.find("reset-specialized expression conflict"),
      std::string::npos)
      << stderrOutput;
  EXPECT_NE(
      stderrOutput.find("via=affine_xor"),
      std::string::npos)
      << stderrOutput;
  EXPECT_EQ(
      stderrOutput.find("reset-specialized expression solve cube=2"),
      std::string::npos)
      << stderrOutput;
  EXPECT_EQ(
      stderrOutput.find("reset-specialized expression solver_profile=pdr"),
      std::string::npos)
      << stderrOutput;
  EXPECT_EQ(
      stderrOutput.find("miss reason=full_sat_support_cap cube=2"),
      std::string::npos)
      << stderrOutput;
  EXPECT_EQ(stderrOutput.find("reset frontier cube coi"), std::string::npos)
      << stderrOutput;
}

TEST_F(SequentialEquivalenceStrategyTests,
       PDREngineStructurallyBlocksAffineXorResetExpressionConflict) {
  KInductionProblem problem;
  constexpr size_t x = 2;
  constexpr size_t y = 3;
  constexpr size_t w = 4;
  constexpr size_t reset = 5;
  constexpr size_t firstA = 6;
  constexpr size_t parityWidth = 96;
  constexpr size_t firstB = firstA + parityWidth;

  problem.state0Symbols = {x, y, w};
  problem.inputSymbols = {reset};
  problem.allSymbols = {x, y, w, reset};
  std::vector<size_t> aSymbols;
  std::vector<size_t> bSymbols;
  aSymbols.reserve(parityWidth);
  bSymbols.reserve(parityWidth);
  for (size_t index = 0; index < parityWidth; ++index) {
    const size_t a = firstA + index;
    const size_t b = firstB + index;
    aSymbols.push_back(a);
    bSymbols.push_back(b);
    problem.state0Symbols.push_back(a);
    problem.state0Symbols.push_back(b);
    problem.allSymbols.push_back(a);
    problem.allSymbols.push_back(b);
    problem.initialStateEqualityPairs.emplace_back(a, b);
    problem.transitions0.emplace_back(a, BoolExpr::Var(a));
    problem.transitions0.emplace_back(b, BoolExpr::Var(b));
  }

  auto leftAssociatedXor = [](const std::vector<size_t>& symbols) {
    BoolExpr* expr = BoolExpr::Var(symbols.front());
    for (size_t index = 1; index < symbols.size(); ++index) {
      expr = BoolExpr::Xor(expr, BoolExpr::Var(symbols[index]));
    }
    return expr;
  };
  auto rightAssociatedXor = [](const std::vector<size_t>& symbols) {
    BoolExpr* expr = BoolExpr::Var(symbols.back());
    for (size_t index = symbols.size() - 1; index-- > 0;) {
      expr = BoolExpr::Xor(BoolExpr::Var(symbols[index]), expr);
    }
    return expr;
  };

  problem.resetBootstrapCycles = 1;
  problem.resetBootstrapInputs = {{reset, true}};
  problem.transitions0.emplace_back(
      x,
      BoolExpr::And(
          BoolExpr::Not(BoolExpr::Var(reset)),
          BoolExpr::And(BoolExpr::Var(y), BoolExpr::Not(BoolExpr::Var(w)))));
  problem.transitions0.emplace_back(y, leftAssociatedXor(aSymbols));
  problem.transitions0.emplace_back(w, rightAssociatedXor(bSymbols));
  problem.bad = BoolExpr::Var(x);
  problem.property = BoolExpr::Not(problem.bad);
  problem.inductionProperty = problem.property;
  problem.inductionBad = problem.bad;

  const ScopedEnvVar pdrStats("KEPLER_SEC_PDR_STATS", "1");
  const ScopedEnvVar pdrStatsInterval("KEPLER_SEC_PDR_STATS_INTERVAL", "1");
  const ScopedEnvVar resetDiag("KEPLER_SEC_PDR_RESET_SHORTCUT_DIAG", "1");
  const ScopedEnvVar proofConflictLimit(
      "KEPLER_SEC_PDR_RESET_EXPRESSION_CONFLICT_LIMIT", "0");
  testing::internal::CaptureStderr();
  PDREngine engine(
      problem,
      KEPLER_FORMAL::Config::SolverType::KISSAT,
      PDREngine::kDefaultPredecessorProjectionLimit,
      PDREngine::kDefaultPreciseBadCubeStateLimit,
      /*useExactFrameClauses=*/false,
      /*maxPredecessorQueries=*/0,
      /*refineProjectedCounterexamples=*/true,
      PDREngine::kDefaultBoundedRootGeneralizationAttempts,
      /*learnValidatedBadFormulaClauses=*/false,
      /*useExactResetFrontierChecks=*/false);
  const auto result = engine.run(3);
  const std::string stderrOutput = testing::internal::GetCapturedStderr();

  // This guards the AES-sized parity shape sampled in PDR: equivalent XOR
  // reset cones can be only associatively different after SEC init equality
  // substitution.  The structural affine-XOR pass should learn the conflict
  // without relying on the optional reset-expression SAT shortcut.
  EXPECT_EQ(result.status, PDRStatus::Equivalent);
  EXPECT_NE(
      stderrOutput.find("via=affine_xor"),
      std::string::npos)
      << stderrOutput;
  EXPECT_EQ(
      stderrOutput.find("reset-specialized expression solve cube=2"),
      std::string::npos)
      << stderrOutput;
}

TEST_F(SequentialEquivalenceStrategyTests,
       PDREngineMinimizesResetSpecializedExpressionSatConflictToPair) {
  KInductionProblem problem;
  constexpr size_t x = 2;
  constexpr size_t y = 3;
  constexpr size_t w = 4;
  constexpr size_t e0 = 5;
  constexpr size_t e1 = 6;
  constexpr size_t a = 7;
  constexpr size_t b = 8;
  constexpr size_t reset = 9;
  problem.state0Symbols = {x, y, w, e0, e1, a, b};
  problem.inputSymbols = {reset};
  problem.allSymbols = {x, y, w, e0, e1, a, b, reset};
  problem.resetBootstrapCycles = 1;
  problem.resetBootstrapInputs = {{reset, true}};
  BoolExpr* badDriver = BoolExpr::And(
      BoolExpr::And(BoolExpr::Var(y), BoolExpr::Not(BoolExpr::Var(w))),
      BoolExpr::And(BoolExpr::Var(e0), BoolExpr::Var(e1)));
  problem.transitions0.emplace_back(
      x,
      BoolExpr::And(BoolExpr::Not(BoolExpr::Var(reset)), badDriver));
  problem.transitions0.emplace_back(
      y,
      BoolExpr::And(
          BoolExpr::Or(BoolExpr::Var(a), BoolExpr::Var(b)),
          BoolExpr::Or(BoolExpr::Var(a), BoolExpr::Not(BoolExpr::Var(b)))));
  problem.transitions0.emplace_back(w, BoolExpr::Var(a));
  problem.transitions0.emplace_back(e0, BoolExpr::Var(e0));
  problem.transitions0.emplace_back(e1, BoolExpr::Var(e1));
  problem.transitions0.emplace_back(a, BoolExpr::Var(a));
  problem.transitions0.emplace_back(b, BoolExpr::Var(b));
  problem.bad = BoolExpr::Var(x);
  problem.property = BoolExpr::Not(problem.bad);
  problem.inductionProperty = problem.property;
  problem.inductionBad = problem.bad;

  ASSERT_FALSE(
      findBaseCounterexample(
          problem, KEPLER_FORMAL::Config::SolverType::KISSAT, 2)
          .has_value());

  const ScopedEnvVar pdrStats("KEPLER_SEC_PDR_STATS", "1");
  const ScopedEnvVar pdrStatsInterval("KEPLER_SEC_PDR_STATS_INTERVAL", "1");
  const ScopedEnvVar resetDiag("KEPLER_SEC_PDR_RESET_SHORTCUT_DIAG", "1");
  const ScopedEnvVar kiDiag("KEPLER_SEC_KI_DIAG", "1");
  testing::internal::CaptureStderr();
  PDREngine engine(
      problem,
      KEPLER_FORMAL::Config::SolverType::KISSAT,
      /*predecessorProjectionLimit=*/32,
      /*preciseBadCubeStateLimit=*/32,
      /*useExactFrameClauses=*/false,
      /*maxPredecessorQueries=*/0,
      /*refineProjectedCounterexamples=*/true,
      PDREngine::kDefaultBoundedRootGeneralizationAttempts,
      /*learnValidatedBadFormulaClauses=*/false,
      /*useExactResetFrontierChecks=*/false);
  const auto result = engine.run(3);
  const std::string stderrOutput = testing::internal::GetCapturedStderr();

  EXPECT_EQ(result.status, PDRStatus::Equivalent);
  EXPECT_NE(
      stderrOutput.find("via=pair_probe"),
      std::string::npos)
      << stderrOutput;
  EXPECT_NE(
      stderrOutput.find("->2 via=pair_probe"),
      std::string::npos)
      << stderrOutput;
  EXPECT_EQ(stderrOutput.find("reset frontier cube coi"), std::string::npos)
      << stderrOutput;
}

TEST_F(SequentialEquivalenceStrategyTests,
       PDREngineOrdersResetExpressionPairProbesBySupport) {
  KInductionProblem problem;
  constexpr size_t x = 2;
  constexpr size_t y = 3;
  constexpr size_t w = 4;
  constexpr size_t e0 = 5;
  constexpr size_t a = 6;
  constexpr size_t b = 7;
  constexpr size_t reset = 8;
  constexpr size_t firstWideLeaf = 9;
  constexpr size_t wideLeafCount = 12;
  problem.state0Symbols = {x, y, w, e0, a, b};
  problem.inputSymbols = {reset};
  problem.allSymbols = {x, y, w, e0, a, b, reset};
  for (size_t index = 0; index < wideLeafCount; ++index) {
    const size_t symbol = firstWideLeaf + index;
    problem.state0Symbols.push_back(symbol);
    problem.allSymbols.push_back(symbol);
  }
  problem.resetBootstrapCycles = 1;
  problem.resetBootstrapInputs = {{reset, true}};
  problem.transitions0.emplace_back(
      x,
      BoolExpr::And(
          BoolExpr::Not(BoolExpr::Var(reset)),
          BoolExpr::And(
              BoolExpr::And(BoolExpr::Var(y), BoolExpr::Var(w)),
              BoolExpr::Not(BoolExpr::Var(e0)))));
  problem.transitions0.emplace_back(
      y,
      BoolExpr::And(
          BoolExpr::Or(BoolExpr::Var(a), BoolExpr::Var(b)),
          BoolExpr::Or(BoolExpr::Var(a), BoolExpr::Not(BoolExpr::Var(b)))));
  problem.transitions0.emplace_back(w, BoolExpr::Not(BoolExpr::Var(a)));
  BoolExpr* wideExpr = BoolExpr::Var(firstWideLeaf);
  for (size_t index = 1; index < wideLeafCount; ++index) {
    wideExpr =
        BoolExpr::Xor(wideExpr, BoolExpr::Var(firstWideLeaf + index));
  }
  problem.transitions0.emplace_back(e0, wideExpr);
  problem.transitions0.emplace_back(a, BoolExpr::Var(a));
  problem.transitions0.emplace_back(b, BoolExpr::Var(b));
  for (size_t index = 0; index < wideLeafCount; ++index) {
    const size_t symbol = firstWideLeaf + index;
    problem.transitions0.emplace_back(symbol, BoolExpr::Var(symbol));
  }
  problem.bad = BoolExpr::Var(x);
  problem.property = BoolExpr::Not(problem.bad);
  problem.inductionProperty = problem.property;
  problem.inductionBad = problem.bad;

  ASSERT_FALSE(
      findBaseCounterexample(
          problem, KEPLER_FORMAL::Config::SolverType::KISSAT, 2)
          .has_value());

  const ScopedEnvVar pdrStats("KEPLER_SEC_PDR_STATS", "1");
  const ScopedEnvVar pdrStatsInterval("KEPLER_SEC_PDR_STATS_INTERVAL", "1");
  const ScopedEnvVar resetDiag("KEPLER_SEC_PDR_RESET_SHORTCUT_DIAG", "1");
  const ScopedEnvVar kiDiag("KEPLER_SEC_KI_DIAG", "1");
  testing::internal::CaptureStderr();
  PDREngine engine(
      problem,
      KEPLER_FORMAL::Config::SolverType::KISSAT,
      /*predecessorProjectionLimit=*/32,
      /*preciseBadCubeStateLimit=*/32,
      /*useExactFrameClauses=*/false,
      /*maxPredecessorQueries=*/0,
      /*refineProjectedCounterexamples=*/true,
      PDREngine::kDefaultBoundedRootGeneralizationAttempts,
      /*learnValidatedBadFormulaClauses=*/false,
      /*useExactResetFrontierChecks=*/false);
  const auto result = engine.run(3);
  const std::string stderrOutput = testing::internal::GetCapturedStderr();

  EXPECT_EQ(result.status, PDRStatus::Equivalent);
  // The conflicting pair is same-valued but has tiny support; the opposite
  // valued pairs pull in the wide e0 cone.  Probe support first so sampled AES
  // failures do not spend time proving wide SAT distractor pairs.
  EXPECT_NE(
      stderrOutput.find(
          "reset-specialized expression solve cube=2 target_step=1 support=2 "),
      std::string::npos)
      << stderrOutput;
  EXPECT_NE(
      stderrOutput.find("via=pair_probe"),
      std::string::npos)
      << stderrOutput;
  EXPECT_EQ(
      stderrOutput.find("reset-specialized expression solve cube=2 support=13"),
      std::string::npos)
      << stderrOutput;
  EXPECT_EQ(
      stderrOutput.find("reset-specialized expression solve cube=2 support=14"),
      std::string::npos)
      << stderrOutput;
  EXPECT_EQ(stderrOutput.find("reset frontier cube coi"), std::string::npos)
      << stderrOutput;
}

TEST_F(SequentialEquivalenceStrategyTests,
       PDREngineContinuesResetExpressionPairProbesPastSatDistractors) {
  KInductionProblem problem;
  constexpr size_t x = 2;
  constexpr size_t d0 = 3;
  constexpr size_t d1 = 4;
  constexpr size_t d2 = 5;
  constexpr size_t d3 = 6;
  constexpr size_t y = 7;
  constexpr size_t w = 8;
  constexpr size_t p0 = 9;
  constexpr size_t p1 = 10;
  constexpr size_t p2 = 11;
  constexpr size_t p3 = 12;
  constexpr size_t a = 13;
  constexpr size_t b = 14;
  constexpr size_t reset = 15;
  problem.state0Symbols = {x, d0, d1, d2, d3, y, w, p0, p1, p2, p3, a, b};
  problem.inputSymbols = {reset};
  problem.allSymbols = {
      x, d0, d1, d2, d3, y, w, p0, p1, p2, p3, a, b, reset};
  problem.resetBootstrapCycles = 1;
  problem.resetBootstrapInputs = {{reset, true}};
  problem.transitions0.emplace_back(
      x,
      BoolExpr::And(
          BoolExpr::Not(BoolExpr::Var(reset)),
          BoolExpr::And(
              BoolExpr::And(BoolExpr::Var(d0), BoolExpr::Var(d1)),
              BoolExpr::And(
                  BoolExpr::And(BoolExpr::Var(d2), BoolExpr::Var(d3)),
                  BoolExpr::And(BoolExpr::Var(y),
                                BoolExpr::Not(BoolExpr::Var(w)))))));
  problem.transitions0.emplace_back(d0, BoolExpr::Var(p0));
  problem.transitions0.emplace_back(d1, BoolExpr::Var(p1));
  problem.transitions0.emplace_back(d2, BoolExpr::Var(p2));
  problem.transitions0.emplace_back(d3, BoolExpr::Var(p3));
  problem.transitions0.emplace_back(y, BoolExpr::Xor(BoolExpr::Var(a), BoolExpr::Var(b)));
  problem.transitions0.emplace_back(
      w,
      BoolExpr::Or(
          BoolExpr::And(BoolExpr::Var(a), BoolExpr::Not(BoolExpr::Var(b))),
          BoolExpr::And(BoolExpr::Not(BoolExpr::Var(a)), BoolExpr::Var(b))));
  problem.transitions0.emplace_back(p0, BoolExpr::Var(p0));
  problem.transitions0.emplace_back(p1, BoolExpr::Var(p1));
  problem.transitions0.emplace_back(p2, BoolExpr::Var(p2));
  problem.transitions0.emplace_back(p3, BoolExpr::Var(p3));
  problem.transitions0.emplace_back(a, BoolExpr::Var(a));
  problem.transitions0.emplace_back(b, BoolExpr::Var(b));
  problem.bad = BoolExpr::Var(x);
  problem.property = BoolExpr::Not(problem.bad);
  problem.inductionProperty = problem.property;
  problem.inductionBad = problem.bad;

  ASSERT_FALSE(
      findBaseCounterexample(
          problem, KEPLER_FORMAL::Config::SolverType::KISSAT, 2)
          .has_value());

  const ScopedEnvVar pdrStats("KEPLER_SEC_PDR_STATS", "1");
  const ScopedEnvVar pdrStatsInterval("KEPLER_SEC_PDR_STATS_INTERVAL", "1");
  const ScopedEnvVar resetDiag("KEPLER_SEC_PDR_RESET_SHORTCUT_DIAG", "1");
  testing::internal::CaptureStderr();
  PDREngine engine(
      problem,
      KEPLER_FORMAL::Config::SolverType::KISSAT,
      /*predecessorProjectionLimit=*/32,
      /*preciseBadCubeStateLimit=*/32,
      /*useExactFrameClauses=*/false,
      /*maxPredecessorQueries=*/0,
      /*refineProjectedCounterexamples=*/true,
      PDREngine::kDefaultBoundedRootGeneralizationAttempts,
      /*learnValidatedBadFormulaClauses=*/false,
      /*useExactResetFrontierChecks=*/false);
  const auto result = engine.run(3);
  const std::string stderrOutput = testing::internal::GetCapturedStderr();

  EXPECT_EQ(result.status, PDRStatus::Equivalent);
  // Boolean-equivalent but structurally different reset expressions should
  // still shrink a wide reset cube through the SAT pair-probe path before any
  // exact reset-frontier query is needed.
  EXPECT_NE(
      stderrOutput.find("reset-specialized expression conflict cube=7->2 via=pair_probe"),
      std::string::npos)
      << stderrOutput;
  EXPECT_EQ(stderrOutput.find("reset frontier cube coi"), std::string::npos)
      << stderrOutput;
}

TEST_F(SequentialEquivalenceStrategyTests,
       PDREngineFindsResetExpressionTripleConflictWhenPairsAreSat) {
  KInductionProblem problem;
  constexpr size_t x = 2;
  constexpr size_t y = 3;
  constexpr size_t w = 4;
  constexpr size_t z = 5;
  constexpr size_t d = 6;
  constexpr size_t a = 7;
  constexpr size_t b = 8;
  constexpr size_t reset = 9;
  problem.state0Symbols = {x, y, w, z, d, a, b};
  problem.inputSymbols = {reset};
  problem.allSymbols = {x, y, w, z, d, a, b, reset};
  problem.resetBootstrapCycles = 1;
  problem.resetBootstrapInputs = {{reset, true}};
  problem.transitions0.emplace_back(
      x,
      BoolExpr::And(
          BoolExpr::Not(BoolExpr::Var(reset)),
          BoolExpr::And(
              BoolExpr::And(BoolExpr::Var(y), BoolExpr::Var(w)),
              BoolExpr::And(BoolExpr::Var(z), BoolExpr::Var(d)))));
  problem.transitions0.emplace_back(y, BoolExpr::Var(a));
  problem.transitions0.emplace_back(w, BoolExpr::Var(b));
  problem.transitions0.emplace_back(z, BoolExpr::Xor(BoolExpr::Var(a), BoolExpr::Var(b)));
  problem.transitions0.emplace_back(d, BoolExpr::Var(d));
  problem.transitions0.emplace_back(a, BoolExpr::Var(a));
  problem.transitions0.emplace_back(b, BoolExpr::Var(b));
  problem.bad = BoolExpr::Var(x);
  problem.property = BoolExpr::Not(problem.bad);
  problem.inductionProperty = problem.property;
  problem.inductionBad = problem.bad;

  ASSERT_FALSE(
      findBaseCounterexample(
          problem, KEPLER_FORMAL::Config::SolverType::KISSAT, 2)
          .has_value());

  const ScopedEnvVar pdrStats("KEPLER_SEC_PDR_STATS", "1");
  const ScopedEnvVar pdrStatsInterval("KEPLER_SEC_PDR_STATS_INTERVAL", "1");
  const ScopedEnvVar resetDiag("KEPLER_SEC_PDR_RESET_SHORTCUT_DIAG", "1");
  testing::internal::CaptureStderr();
  PDREngine engine(
      problem,
      KEPLER_FORMAL::Config::SolverType::KISSAT,
      /*predecessorProjectionLimit=*/32,
      /*preciseBadCubeStateLimit=*/32,
      /*useExactFrameClauses=*/false,
      /*maxPredecessorQueries=*/0,
      /*refineProjectedCounterexamples=*/true,
      PDREngine::kDefaultBoundedRootGeneralizationAttempts,
      /*learnValidatedBadFormulaClauses=*/false,
      /*useExactResetFrontierChecks=*/false);
  const auto result = engine.run(3);
  const std::string stderrOutput = testing::internal::GetCapturedStderr();

  EXPECT_EQ(result.status, PDRStatus::Equivalent);
  // a=1, b=1, and a^b=1 is impossible, but every pair of those literals is
  // satisfiable.  The triple probe should learn that smaller reset-image
  // conflict before the optional full-cube SAT fallback.
  EXPECT_NE(
      stderrOutput.find(
          "reset-specialized expression conflict cube=5->3 via=triple_probe"),
      std::string::npos)
      << stderrOutput;
  EXPECT_EQ(stderrOutput.find("reset frontier cube coi"), std::string::npos)
      << stderrOutput;
}

KInductionProblem makeWideResetExpressionSatShortcutProblem(
    size_t wideLeafCount) {
  KInductionProblem problem;
  constexpr size_t x = 2;
  constexpr size_t y = 3;
  constexpr size_t w = 4;
  constexpr size_t a = 5;
  constexpr size_t reset = 6;
  constexpr size_t firstWideLeaf = 7;
  problem.state0Symbols = {x, y, w, a};
  problem.inputSymbols = {reset};
  problem.allSymbols = {x, y, w, a, reset};
  for (size_t index = 0; index < wideLeafCount; ++index) {
    const size_t symbol = firstWideLeaf + index;
    problem.state0Symbols.push_back(symbol);
    problem.allSymbols.push_back(symbol);
  }
  problem.resetBootstrapCycles = 1;
  problem.resetBootstrapInputs = {{reset, true}};
  problem.transitions0.emplace_back(
      x,
      BoolExpr::And(
          BoolExpr::Not(BoolExpr::Var(reset)),
          BoolExpr::And(BoolExpr::Var(y), BoolExpr::Var(w))));
  BoolExpr* wideExpr = BoolExpr::Var(firstWideLeaf);
  for (size_t index = 1; index < wideLeafCount; ++index) {
    wideExpr =
        BoolExpr::Xor(wideExpr, BoolExpr::Var(firstWideLeaf + index));
  }
  problem.transitions0.emplace_back(y, wideExpr);
  problem.transitions0.emplace_back(w, BoolExpr::Var(a));
  problem.transitions0.emplace_back(a, BoolExpr::Var(a));
  for (size_t index = 0; index < wideLeafCount; ++index) {
    const size_t symbol = firstWideLeaf + index;
    problem.transitions0.emplace_back(symbol, BoolExpr::Var(symbol));
  }
  problem.bad = BoolExpr::Var(x);
  problem.property = BoolExpr::Not(problem.bad);
  problem.inductionProperty = problem.property;
  problem.inductionBad = problem.bad;
  return problem;
}

KInductionProblem makeWideMultiLiteralResetExpressionSatShortcutProblem(
    size_t wideLeafCount) {
  KInductionProblem problem;
  constexpr size_t x = 2;
  constexpr size_t y = 3;
  constexpr size_t w = 4;
  constexpr size_t extra0 = 5;
  constexpr size_t extra1 = 6;
  constexpr size_t a = 7;
  constexpr size_t reset = 8;
  constexpr size_t firstWideLeaf = 9;
  problem.state0Symbols = {x, y, w, extra0, extra1, a};
  problem.inputSymbols = {reset};
  problem.allSymbols = {x, y, w, extra0, extra1, a, reset};
  for (size_t index = 0; index < wideLeafCount; ++index) {
    const size_t symbol = firstWideLeaf + index;
    problem.state0Symbols.push_back(symbol);
    problem.allSymbols.push_back(symbol);
  }
  problem.resetBootstrapCycles = 1;
  problem.resetBootstrapInputs = {{reset, true}};
  BoolExpr* rootCubeDriver = BoolExpr::And(
      BoolExpr::Var(y),
      BoolExpr::And(BoolExpr::Var(w), BoolExpr::Var(extra0)));
  rootCubeDriver = BoolExpr::And(rootCubeDriver, BoolExpr::Var(extra1));
  problem.transitions0.emplace_back(
      x,
      BoolExpr::And(BoolExpr::Not(BoolExpr::Var(reset)), rootCubeDriver));
  BoolExpr* wideExpr = BoolExpr::Var(firstWideLeaf);
  for (size_t index = 1; index < wideLeafCount; ++index) {
    wideExpr =
        BoolExpr::Xor(wideExpr, BoolExpr::Var(firstWideLeaf + index));
  }
  problem.transitions0.emplace_back(y, wideExpr);
  problem.transitions0.emplace_back(w, BoolExpr::Var(a));
  problem.transitions0.emplace_back(extra0, BoolExpr::Var(extra0));
  problem.transitions0.emplace_back(extra1, BoolExpr::Var(extra1));
  problem.transitions0.emplace_back(a, BoolExpr::Var(a));
  for (size_t index = 0; index < wideLeafCount; ++index) {
    const size_t symbol = firstWideLeaf + index;
    problem.transitions0.emplace_back(symbol, BoolExpr::Var(symbol));
  }
  problem.bad = BoolExpr::Var(x);
  problem.property = BoolExpr::Not(problem.bad);
  problem.inductionProperty = problem.property;
  problem.inductionBad = problem.bad;
  return problem;
}

TEST_F(SequentialEquivalenceStrategyTests,
       PDREngineAttemptsModerateWideResetExpressionSatShortcut) {
  KInductionProblem problem =
      makeWideResetExpressionSatShortcutProblem(/*wideLeafCount=*/128);

  const ScopedEnvVar pdrStats("KEPLER_SEC_PDR_STATS", "1");
  const ScopedEnvVar pdrStatsInterval("KEPLER_SEC_PDR_STATS_INTERVAL", "1");
  const ScopedEnvVar resetDiag("KEPLER_SEC_PDR_RESET_SHORTCUT_DIAG", "1");
  testing::internal::CaptureStderr();
  PDREngine engine(
      problem,
      KEPLER_FORMAL::Config::SolverType::KISSAT,
      PDREngine::kDefaultPredecessorProjectionLimit,
      PDREngine::kDefaultPreciseBadCubeStateLimit,
      /*useExactFrameClauses=*/false,
      /*maxPredecessorQueries=*/0,
      /*refineProjectedCounterexamples=*/true,
      PDREngine::kDefaultBoundedRootGeneralizationAttempts,
      /*learnValidatedBadFormulaClauses=*/false,
      /*useExactResetFrontierChecks=*/false);
  (void)engine.run(3);
  const std::string stderrOutput = testing::internal::GetCapturedStderr();

  // AES sampling kept useful support-129/135 reset-image pair proofs. This
  // guarded case keeps only local proof shapes eligible for the
  // reset-expression SAT path; whether the particular cube is SAT or UNSAT
  // remains a solver result.
  EXPECT_NE(
      stderrOutput.find("reset-specialized expression solve"),
      std::string::npos)
      << stderrOutput;
  EXPECT_NE(
      stderrOutput.find("support=129"),
      std::string::npos)
      << stderrOutput;
  EXPECT_EQ(stderrOutput.find("miss reason=full_sat_support_cap"),
            std::string::npos)
      << stderrOutput;
  EXPECT_EQ(stderrOutput.find("reset frontier cube coi"), std::string::npos)
      << stderrOutput;
}

TEST_F(SequentialEquivalenceStrategyTests,
       PDREngineSkipsResetExpressionShortcutWhenResourceLimitHits) {
  KInductionProblem problem =
      makeWideResetExpressionSatShortcutProblem(/*wideLeafCount=*/128);

  const ScopedEnvVar pdrStats("KEPLER_SEC_PDR_STATS", "1");
  const ScopedEnvVar pdrStatsInterval("KEPLER_SEC_PDR_STATS_INTERVAL", "1");
  const ScopedEnvVar resetDiag("KEPLER_SEC_PDR_RESET_SHORTCUT_DIAG", "1");
  const ScopedEnvVar proofConflictLimit(
      "KEPLER_SEC_PDR_RESET_EXPRESSION_CONFLICT_LIMIT", "0");
  testing::internal::CaptureStderr();
  PDREngine engine(
      problem,
      KEPLER_FORMAL::Config::SolverType::KISSAT,
      PDREngine::kDefaultPredecessorProjectionLimit,
      PDREngine::kDefaultPreciseBadCubeStateLimit,
      /*useExactFrameClauses=*/false,
      /*maxPredecessorQueries=*/0,
      /*refineProjectedCounterexamples=*/true,
      PDREngine::kDefaultBoundedRootGeneralizationAttempts,
      /*learnValidatedBadFormulaClauses=*/false,
      /*useExactResetFrontierChecks=*/false);
  (void)engine.run(3);
  const std::string stderrOutput = testing::internal::GetCapturedStderr();

  // Reset-expression SAT is an optional shortcut. If Kissat hits the local
  // resource cap, PDR must report a miss and continue through the normal
  // validation/refinement path instead of treating UNKNOWN as UNSAT.
  EXPECT_NE(
      stderrOutput.find("miss reason=solver_resource_limit"),
      std::string::npos)
      << stderrOutput;
  EXPECT_EQ(
      stderrOutput.find("reset-specialized expression conflict"),
      std::string::npos)
      << stderrOutput;
}

TEST_F(SequentialEquivalenceStrategyTests,
       PDREngineSkipsBroadMultiLiteralResetExpressionSatShortcut) {
  KInductionProblem problem =
      makeWideMultiLiteralResetExpressionSatShortcutProblem(
          /*wideLeafCount=*/600);

  const ScopedEnvVar pdrStats("KEPLER_SEC_PDR_STATS", "1");
  const ScopedEnvVar pdrStatsInterval("KEPLER_SEC_PDR_STATS_INTERVAL", "1");
  const ScopedEnvVar resetDiag("KEPLER_SEC_PDR_RESET_SHORTCUT_DIAG", "1");
  testing::internal::CaptureStderr();
  PDREngine engine(
      problem,
      KEPLER_FORMAL::Config::SolverType::KISSAT,
      PDREngine::kDefaultPredecessorProjectionLimit,
      PDREngine::kDefaultPreciseBadCubeStateLimit,
      /*useExactFrameClauses=*/false,
      /*maxPredecessorQueries=*/0,
      /*refineProjectedCounterexamples=*/true,
      PDREngine::kDefaultBoundedRootGeneralizationAttempts,
      /*learnValidatedBadFormulaClauses=*/false,
      /*useExactResetFrontierChecks=*/false);
  (void)engine.run(3);
  const std::string stderrOutput = testing::internal::GetCapturedStderr();

  // Sampling showed that admitting broad four-literal reset-image cubes into
  // the full SAT shortcut simply moved the wall from exact reset-frontier BMC
  // into Kissat.  Pair/triple probes are still allowed above, but the complete
  // multi-literal SAT fallback must stay below the smaller support cap.
  EXPECT_NE(
      stderrOutput.find("miss reason=full_sat_support_cap"),
      std::string::npos)
      << stderrOutput;
  EXPECT_EQ(
      stderrOutput.find("reset-specialized expression solve cube=5 support=603"),
      std::string::npos)
      << stderrOutput;
  EXPECT_EQ(stderrOutput.find("reset frontier cube coi"), std::string::npos)
      << stderrOutput;
}

TEST_F(SequentialEquivalenceStrategyTests,
       PDREngineSkipsHighSupportSmallResetExpressionSatShortcut) {
  KInductionProblem problem =
      makeWideResetExpressionSatShortcutProblem(/*wideLeafCount=*/900);

  const ScopedEnvVar pdrStats("KEPLER_SEC_PDR_STATS", "1");
  const ScopedEnvVar pdrStatsInterval("KEPLER_SEC_PDR_STATS_INTERVAL", "1");
  const ScopedEnvVar resetDiag("KEPLER_SEC_PDR_RESET_SHORTCUT_DIAG", "1");
  testing::internal::CaptureStderr();
  PDREngine engine(
      problem,
      KEPLER_FORMAL::Config::SolverType::KISSAT,
      PDREngine::kDefaultPredecessorProjectionLimit,
      PDREngine::kDefaultPreciseBadCubeStateLimit,
      /*useExactFrameClauses=*/false,
      /*maxPredecessorQueries=*/0,
      /*refineProjectedCounterexamples=*/true,
      PDREngine::kDefaultBoundedRootGeneralizationAttempts,
      /*learnValidatedBadFormulaClauses=*/false,
      /*useExactResetFrontierChecks=*/false);
  (void)engine.run(3);
  const std::string stderrOutput = testing::internal::GetCapturedStderr();

  // The useful sampled AES shortcuts had support 129/135. Wider small cubes
  // still fall through before opening Kissat, so this optional proof path
  // cannot become a whole-chip SAT query.
  EXPECT_NE(
      stderrOutput.find("miss reason=full_sat_support_cap"),
      std::string::npos)
      << stderrOutput;
  EXPECT_EQ(
      stderrOutput.find("reset-specialized expression solve cube=3 support=901"),
      std::string::npos)
      << stderrOutput;
  EXPECT_EQ(stderrOutput.find("reset frontier cube coi"), std::string::npos)
      << stderrOutput;
}

TEST_F(SequentialEquivalenceStrategyTests,
       PDREngineUsesOneShotResetValidationForFinalRootCegar) {
  KInductionProblem problem =
      makeWideResetExpressionSatShortcutProblem(/*wideLeafCount=*/900);

  const ScopedEnvVar pdrStats("KEPLER_SEC_PDR_STATS", "1");
  const ScopedEnvVar pdrStatsInterval("KEPLER_SEC_PDR_STATS_INTERVAL", "1");
  const ScopedEnvVar resetDiag("KEPLER_SEC_PDR_RESET_SHORTCUT_DIAG", "1");
  const ScopedEnvVar kiDiag("KEPLER_SEC_KI_DIAG", "1");
  testing::internal::CaptureStderr();
  PDREngine engine(
      problem,
      KEPLER_FORMAL::Config::SolverType::KISSAT,
      PDREngine::kDefaultPredecessorProjectionLimit,
      PDREngine::kDefaultPreciseBadCubeStateLimit,
      /*useExactFrameClauses=*/false,
      /*maxPredecessorQueries=*/0,
      /*refineProjectedCounterexamples=*/true,
      PDREngine::kDefaultBoundedRootGeneralizationAttempts,
      /*learnValidatedBadFormulaClauses=*/false,
      /*useExactResetFrontierChecks=*/false);
  (void)engine.run(3);
  const std::string stderrOutput = testing::internal::GetCapturedStderr();

  // Final projected-counterexample repair asks small root-cube reachability
  // questions. Sampled AES runs showed the cached Glucose assumption path
  // spending the wall time before learning any reset-frontier fact, so this
  // path uses the one-shot unit-clause validator instead.
  EXPECT_NE(
      stderrOutput.find("mode=one_shot_unit_clauses"),
      std::string::npos)
      << stderrOutput;
  EXPECT_EQ(
      stderrOutput.find("mode=cached_assumptions"),
      std::string::npos)
      << stderrOutput;
  EXPECT_NE(
      stderrOutput.find("reset-specialized concrete-frame conflict"),
      std::string::npos)
      << stderrOutput;
}

TEST_F(SequentialEquivalenceStrategyTests,
       PDREngineSkipsVeryWideResetExpressionSatShortcut) {
  KInductionProblem problem =
      makeWideResetExpressionSatShortcutProblem(/*wideLeafCount=*/1032);

  const ScopedEnvVar pdrStats("KEPLER_SEC_PDR_STATS", "1");
  const ScopedEnvVar pdrStatsInterval("KEPLER_SEC_PDR_STATS_INTERVAL", "1");
  const ScopedEnvVar resetDiag("KEPLER_SEC_PDR_RESET_SHORTCUT_DIAG", "1");
  testing::internal::CaptureStderr();
  PDREngine engine(
      problem,
      KEPLER_FORMAL::Config::SolverType::KISSAT,
      PDREngine::kDefaultPredecessorProjectionLimit,
      PDREngine::kDefaultPreciseBadCubeStateLimit,
      /*useExactFrameClauses=*/false,
      /*maxPredecessorQueries=*/0,
      /*refineProjectedCounterexamples=*/true,
      PDREngine::kDefaultBoundedRootGeneralizationAttempts,
      /*learnValidatedBadFormulaClauses=*/false,
      /*useExactResetFrontierChecks=*/false);
  (void)engine.run(3);
  const std::string stderrOutput = testing::internal::GetCapturedStderr();

  // Reset-expression SAT is only a shortcut.  If the local reset support is
  // broader than the bounded ASIC-sized proof path and no cheap relation proof
  // applies, skip the optional SAT query and let the caller's exact
  // validation/refinement path decide.
  EXPECT_NE(
      stderrOutput.find("miss reason=full_sat_support_cap"),
      std::string::npos)
      << stderrOutput;
  EXPECT_EQ(
      stderrOutput.find("reset-specialized expression solve cube=2 support=1033"),
      std::string::npos)
      << stderrOutput;
  EXPECT_EQ(stderrOutput.find("reset frontier cube coi"), std::string::npos)
      << stderrOutput;
}

TEST_F(SequentialEquivalenceStrategyTests,
       PDREngineFiltersUnrelatedStartupEqualitiesFromResetExpressionSat) {
  KInductionProblem problem;
  constexpr size_t x = 2;
  constexpr size_t y = 3;
  constexpr size_t w = 4;
  constexpr size_t a = 5;
  constexpr size_t b = 6;
  constexpr size_t reset = 7;
  constexpr size_t firstUnrelated = 8;
  constexpr size_t unrelatedPairs = 16;
  problem.state0Symbols = {x, y, w, a, b};
  problem.inputSymbols = {reset};
  problem.allSymbols = {x, y, w, a, b, reset};
  for (size_t index = 0; index < unrelatedPairs; ++index) {
    const size_t lhs = firstUnrelated + index * 2;
    const size_t rhs = lhs + 1;
    problem.state0Symbols.push_back(lhs);
    problem.state1Symbols.push_back(rhs);
    problem.allSymbols.push_back(lhs);
    problem.allSymbols.push_back(rhs);
    problem.initialStateEqualityPairs.emplace_back(lhs, rhs);
  }
  problem.resetBootstrapCycles = 1;
  problem.resetBootstrapInputs = {{reset, true}};
  problem.transitions0.emplace_back(
      x,
      BoolExpr::And(
          BoolExpr::Not(BoolExpr::Var(reset)),
          BoolExpr::And(BoolExpr::Var(y), BoolExpr::Not(BoolExpr::Var(w)))));
  problem.transitions0.emplace_back(
      y,
      BoolExpr::And(
          BoolExpr::Or(BoolExpr::Var(a), BoolExpr::Var(b)),
          BoolExpr::Or(BoolExpr::Var(a), BoolExpr::Not(BoolExpr::Var(b)))));
  problem.transitions0.emplace_back(w, BoolExpr::Var(a));
  problem.transitions0.emplace_back(a, BoolExpr::Var(a));
  problem.transitions0.emplace_back(b, BoolExpr::Var(b));
  problem.bad = BoolExpr::Var(x);
  problem.property = BoolExpr::Not(problem.bad);
  problem.inductionProperty = problem.property;
  problem.inductionBad = problem.bad;

  ASSERT_FALSE(
      findBaseCounterexample(
          problem, KEPLER_FORMAL::Config::SolverType::KISSAT, 2)
          .has_value());

  const ScopedEnvVar pdrStats("KEPLER_SEC_PDR_STATS", "1");
  const ScopedEnvVar pdrStatsInterval("KEPLER_SEC_PDR_STATS_INTERVAL", "1");
  const ScopedEnvVar resetDiag("KEPLER_SEC_PDR_RESET_SHORTCUT_DIAG", "1");
  const ScopedEnvVar kiDiag("KEPLER_SEC_KI_DIAG", "1");
  testing::internal::CaptureStderr();
  PDREngine engine(
      problem,
      KEPLER_FORMAL::Config::SolverType::KISSAT,
      PDREngine::kDefaultPredecessorProjectionLimit,
      PDREngine::kDefaultPreciseBadCubeStateLimit,
      /*useExactFrameClauses=*/false,
      /*maxPredecessorQueries=*/0,
      /*refineProjectedCounterexamples=*/true,
      PDREngine::kDefaultBoundedRootGeneralizationAttempts,
      /*learnValidatedBadFormulaClauses=*/false,
      /*useExactResetFrontierChecks=*/false);
  const auto result = engine.run(3);
  const std::string stderrOutput = testing::internal::GetCapturedStderr();

  EXPECT_EQ(result.status, PDRStatus::Equivalent);
  // The reset cube depends only on a and b.  Unrelated startup equalities must
  // not be streamed into the per-cube SAT fallback.  The pair probe may prove
  // the conflict before the full cube is queried, but the local proof should
  // still stay restricted to the actual reset-expression support.
  EXPECT_NE(
      stderrOutput.find(
          "reset-specialized expression solve cube=2 target_step=1 support=2 "
          "initial_equalities=0 bootstrap_equalities=0"),
      std::string::npos)
      << stderrOutput;
  EXPECT_EQ(stderrOutput.find("reset frontier cube coi"), std::string::npos)
      << stderrOutput;
}

TEST_F(SequentialEquivalenceStrategyTests,
       PDREngineFiltersUnrelatedBootstrapEqualitiesFromResetExpressionSat) {
  KInductionProblem problem;
  constexpr size_t x = 2;
  constexpr size_t y = 3;
  constexpr size_t w = 4;
  constexpr size_t a = 5;
  constexpr size_t b = 6;
  constexpr size_t reset = 7;
  constexpr size_t unrelated0 = 8;
  constexpr size_t unrelated1 = 9;
  constexpr size_t unrelatedLeaf0 = 10;
  constexpr size_t unrelatedLeaf1 = 11;
  problem.state0Symbols = {x, y, w, a, b, unrelated0, unrelatedLeaf0};
  problem.state1Symbols = {unrelated1, unrelatedLeaf1};
  problem.inputSymbols = {reset};
  problem.allSymbols = {
      x, y, w, a, b, reset, unrelated0, unrelated1, unrelatedLeaf0,
      unrelatedLeaf1};
  problem.resetBootstrapCycles = 1;
  problem.resetBootstrapInputs = {{reset, true}};
  problem.bootstrapStateEqualityPairs = {{unrelated0, unrelated1}};
  problem.transitions0.emplace_back(
      x,
      BoolExpr::And(
          BoolExpr::Not(BoolExpr::Var(reset)),
          BoolExpr::And(BoolExpr::Var(y), BoolExpr::Not(BoolExpr::Var(w)))));
  problem.transitions0.emplace_back(
      y,
      BoolExpr::And(
          BoolExpr::Or(BoolExpr::Var(a), BoolExpr::Var(b)),
          BoolExpr::Or(BoolExpr::Var(a), BoolExpr::Not(BoolExpr::Var(b)))));
  problem.transitions0.emplace_back(w, BoolExpr::Var(a));
  problem.transitions0.emplace_back(a, BoolExpr::Var(a));
  problem.transitions0.emplace_back(b, BoolExpr::Var(b));
  problem.transitions0.emplace_back(unrelated0, BoolExpr::Var(unrelatedLeaf0));
  problem.transitions1.emplace_back(unrelated1, BoolExpr::Var(unrelatedLeaf1));
  problem.transitions0.emplace_back(unrelatedLeaf0, BoolExpr::Var(unrelatedLeaf0));
  problem.transitions1.emplace_back(unrelatedLeaf1, BoolExpr::Var(unrelatedLeaf1));
  problem.bad = BoolExpr::Var(x);
  problem.property = BoolExpr::Not(problem.bad);
  problem.inductionProperty = problem.property;
  problem.inductionBad = problem.bad;

  ASSERT_FALSE(
      findBaseCounterexample(
          problem, KEPLER_FORMAL::Config::SolverType::KISSAT, 2)
          .has_value());

  const ScopedEnvVar pdrStats("KEPLER_SEC_PDR_STATS", "1");
  const ScopedEnvVar pdrStatsInterval("KEPLER_SEC_PDR_STATS_INTERVAL", "1");
  const ScopedEnvVar resetDiag("KEPLER_SEC_PDR_RESET_SHORTCUT_DIAG", "1");
  const ScopedEnvVar kiDiag("KEPLER_SEC_KI_DIAG", "1");
  testing::internal::CaptureStderr();
  PDREngine engine(
      problem,
      KEPLER_FORMAL::Config::SolverType::KISSAT,
      PDREngine::kDefaultPredecessorProjectionLimit,
      PDREngine::kDefaultPreciseBadCubeStateLimit,
      /*useExactFrameClauses=*/false,
      /*maxPredecessorQueries=*/0,
      /*refineProjectedCounterexamples=*/true,
      PDREngine::kDefaultBoundedRootGeneralizationAttempts,
      /*learnValidatedBadFormulaClauses=*/false,
      /*useExactResetFrontierChecks=*/false);
  const auto result = engine.run(3);
  const std::string stderrOutput = testing::internal::GetCapturedStderr();

  EXPECT_EQ(result.status, PDRStatus::Equivalent);
  // Bootstrap equality expressions are valid reset-frontier constraints, but
  // unrelated ones must not pull extra reset cones into a local cube proof.
  EXPECT_NE(
      stderrOutput.find(
          "reset-specialized expression solve cube=2 target_step=1 support=2 "
          "initial_equalities=0 bootstrap_equalities=0"),
      std::string::npos)
      << stderrOutput;
  EXPECT_EQ(stderrOutput.find("reset frontier cube coi"), std::string::npos)
      << stderrOutput;
}

TEST_F(SequentialEquivalenceStrategyTests,
       PDREngineUsesResetSpecializedInitialEqualitiesBeforeExactRootResetFrontier) {
  KInductionProblem problem;
  constexpr size_t x = 2;
  constexpr size_t y = 3;
  constexpr size_t w = 4;
  constexpr size_t a0 = 5;
  constexpr size_t a1 = 6;
  constexpr size_t reset = 7;
  problem.state0Symbols = {x, y, a0};
  problem.state1Symbols = {w, a1};
  problem.inputSymbols = {reset};
  problem.allSymbols = {x, y, w, a0, a1, reset};
  problem.resetBootstrapCycles = 1;
  problem.resetBootstrapInputs = {{reset, true}};
  problem.initialStateEqualityPairs = {{a0, a1}};
  problem.transitions0.emplace_back(
      x,
      BoolExpr::And(
          BoolExpr::Not(BoolExpr::Var(reset)),
          BoolExpr::And(BoolExpr::Var(y), BoolExpr::Not(BoolExpr::Var(w)))));
  // The post-reset relation y == w is not visible in the reset expressions
  // alone: y depends on a0 and w depends on a1. It becomes provable only after
  // applying the SEC frame-0 equality a0 == a1. AES samples hit this shape as a
  // tiny root cube that otherwise fell into the expensive concrete reset-frontier
  // SAT unroll.
  problem.transitions0.emplace_back(y, BoolExpr::Var(a0));
  problem.transitions1.emplace_back(w, BoolExpr::Var(a1));
  problem.transitions0.emplace_back(a0, BoolExpr::Var(a0));
  problem.transitions1.emplace_back(a1, BoolExpr::Var(a1));
  problem.bad = BoolExpr::Var(x);
  problem.property = BoolExpr::Not(problem.bad);
  problem.inductionProperty = problem.property;
  problem.inductionBad = problem.bad;

  ASSERT_FALSE(
      findBaseCounterexample(
          problem, KEPLER_FORMAL::Config::SolverType::KISSAT, 2)
          .has_value());

  const ScopedEnvVar pdrStats("KEPLER_SEC_PDR_STATS", "1");
  const ScopedEnvVar pdrStatsInterval("KEPLER_SEC_PDR_STATS_INTERVAL", "1");
  const ScopedEnvVar kiDiag("KEPLER_SEC_KI_DIAG", "1");
  testing::internal::CaptureStderr();
  PDREngine engine(
      problem,
      KEPLER_FORMAL::Config::SolverType::KISSAT,
      PDREngine::kDefaultPredecessorProjectionLimit,
      PDREngine::kDefaultPreciseBadCubeStateLimit,
      /*useExactFrameClauses=*/false,
      /*maxPredecessorQueries=*/0,
      /*refineProjectedCounterexamples=*/true,
      PDREngine::kDefaultBoundedRootGeneralizationAttempts,
      /*learnValidatedBadFormulaClauses=*/false,
      /*useExactResetFrontierChecks=*/false);
  const auto result = engine.run(3);
  const std::string stderrOutput = testing::internal::GetCapturedStderr();

  EXPECT_EQ(result.status, PDRStatus::Equivalent);
  EXPECT_NE(
      stderrOutput.find("reset-specialized expression conflict"),
      std::string::npos)
      << stderrOutput;
  EXPECT_EQ(stderrOutput.find("reset frontier cube coi"), std::string::npos)
      << stderrOutput;
}

TEST_F(SequentialEquivalenceStrategyTests,
       PDREngineUsesResetSpecializedBootstrapEqualitiesBeforeExpressionSat) {
  KInductionProblem problem;
  constexpr size_t x = 2;
  constexpr size_t y = 3;
  constexpr size_t w = 4;
  constexpr size_t a0 = 5;
  constexpr size_t a1 = 6;
  constexpr size_t reset = 7;
  problem.state0Symbols = {x, y, a0};
  problem.state1Symbols = {w, a1};
  problem.inputSymbols = {reset};
  problem.allSymbols = {x, y, w, a0, a1, reset};
  problem.resetBootstrapCycles = 1;
  problem.resetBootstrapInputs = {{reset, true}};
  problem.bootstrapStateEqualityPairs = {{a0, a1}};
  problem.transitions0.emplace_back(
      x,
      BoolExpr::And(
          BoolExpr::Not(BoolExpr::Var(reset)),
          BoolExpr::And(BoolExpr::Var(y), BoolExpr::Not(BoolExpr::Var(w)))));
  // The reset cube y=1,w=0 is excluded by the post-bootstrap equality
  // a0 == a1 after substituting y'=a0 and w'=a1. This should be detected as a
  // relation conflict before invoking the broader reset-expression SAT query.
  problem.transitions0.emplace_back(y, BoolExpr::Var(a0));
  problem.transitions1.emplace_back(w, BoolExpr::Var(a1));
  problem.transitions0.emplace_back(a0, BoolExpr::Var(a0));
  problem.transitions1.emplace_back(a1, BoolExpr::Var(a1));
  problem.bad = BoolExpr::Var(x);
  problem.property = BoolExpr::Not(problem.bad);
  problem.inductionProperty = problem.property;
  problem.inductionBad = problem.bad;

  ASSERT_FALSE(
      findBaseCounterexample(
          problem, KEPLER_FORMAL::Config::SolverType::KISSAT, 2)
          .has_value());

  const ScopedEnvVar pdrStats("KEPLER_SEC_PDR_STATS", "1");
  const ScopedEnvVar pdrStatsInterval("KEPLER_SEC_PDR_STATS_INTERVAL", "1");
  const ScopedEnvVar resetDiag("KEPLER_SEC_PDR_RESET_SHORTCUT_DIAG", "1");
  const ScopedEnvVar kiDiag("KEPLER_SEC_KI_DIAG", "1");
  testing::internal::CaptureStderr();
  PDREngine engine(
      problem,
      KEPLER_FORMAL::Config::SolverType::KISSAT,
      PDREngine::kDefaultPredecessorProjectionLimit,
      PDREngine::kDefaultPreciseBadCubeStateLimit,
      /*useExactFrameClauses=*/false,
      /*maxPredecessorQueries=*/0,
      /*refineProjectedCounterexamples=*/true,
      PDREngine::kDefaultBoundedRootGeneralizationAttempts,
      /*learnValidatedBadFormulaClauses=*/false,
      /*useExactResetFrontierChecks=*/false);
  const auto result = engine.run(3);
  const std::string stderrOutput = testing::internal::GetCapturedStderr();

  EXPECT_EQ(result.status, PDRStatus::Equivalent);
  EXPECT_NE(
      stderrOutput.find("via=bootstrap_relation"),
      std::string::npos)
      << stderrOutput;
  EXPECT_EQ(
      stderrOutput.find("reset-specialized expression solver_profile=pdr"),
      std::string::npos)
      << stderrOutput;
  EXPECT_EQ(stderrOutput.find("reset frontier cube coi"), std::string::npos)
      << stderrOutput;
}

TEST_F(SequentialEquivalenceStrategyTests,
       PDREngineRewritesBootstrapEqualitiesInsideResetExpressions) {
  KInductionProblem problem;
  constexpr size_t x = 2;
  constexpr size_t y = 3;
  constexpr size_t w = 4;
  constexpr size_t a0 = 5;
  constexpr size_t a1 = 6;
  constexpr size_t shared = 7;
  constexpr size_t reset = 8;
  problem.state0Symbols = {x, y, a0, shared};
  problem.state1Symbols = {w, a1};
  problem.inputSymbols = {reset};
  problem.allSymbols = {x, y, w, a0, a1, shared, reset};
  problem.resetBootstrapCycles = 1;
  problem.resetBootstrapInputs = {{reset, true}};
  problem.bootstrapStateEqualityPairs = {{a0, a1}};
  problem.transitions0.emplace_back(
      x,
      BoolExpr::And(
          BoolExpr::Not(BoolExpr::Var(reset)),
          BoolExpr::And(BoolExpr::Var(y), BoolExpr::Not(BoolExpr::Var(w)))));
  // y and w are not directly equal expressions. They become equal only after
  // rewriting the children a0/a1 through the bootstrap equality, matching the
  // AES reset-image shape that sampled inside the exact reset-frontier SAT
  // unroll.
  problem.transitions0.emplace_back(
      y, BoolExpr::And(BoolExpr::Var(a0), BoolExpr::Var(shared)));
  problem.transitions1.emplace_back(
      w, BoolExpr::And(BoolExpr::Var(a1), BoolExpr::Var(shared)));
  problem.transitions0.emplace_back(a0, BoolExpr::Var(a0));
  problem.transitions1.emplace_back(a1, BoolExpr::Var(a1));
  problem.transitions0.emplace_back(shared, BoolExpr::Var(shared));
  problem.bad = BoolExpr::Var(x);
  problem.property = BoolExpr::Not(problem.bad);
  problem.inductionProperty = problem.property;
  problem.inductionBad = problem.bad;

  ASSERT_FALSE(
      findBaseCounterexample(
          problem, KEPLER_FORMAL::Config::SolverType::KISSAT, 2)
          .has_value());

  const ScopedEnvVar pdrStats("KEPLER_SEC_PDR_STATS", "1");
  const ScopedEnvVar pdrStatsInterval("KEPLER_SEC_PDR_STATS_INTERVAL", "1");
  const ScopedEnvVar resetDiag("KEPLER_SEC_PDR_RESET_SHORTCUT_DIAG", "1");
  const ScopedEnvVar proofConflictLimit(
      "KEPLER_SEC_PDR_RESET_EXPRESSION_CONFLICT_LIMIT", "0");
  testing::internal::CaptureStderr();
  PDREngine engine(
      problem,
      KEPLER_FORMAL::Config::SolverType::KISSAT,
      PDREngine::kDefaultPredecessorProjectionLimit,
      PDREngine::kDefaultPreciseBadCubeStateLimit,
      /*useExactFrameClauses=*/false,
      /*maxPredecessorQueries=*/0,
      /*refineProjectedCounterexamples=*/true,
      PDREngine::kDefaultBoundedRootGeneralizationAttempts,
      /*learnValidatedBadFormulaClauses=*/false,
      /*useExactResetFrontierChecks=*/false);
  const auto result = engine.run(3);
  const std::string stderrOutput = testing::internal::GetCapturedStderr();

  EXPECT_EQ(result.status, PDRStatus::Equivalent);
  EXPECT_NE(
      stderrOutput.find("via=bootstrap_rewrite"),
      std::string::npos)
      << stderrOutput;
  EXPECT_EQ(
      stderrOutput.find("reset-specialized expression solve cube=2"),
      std::string::npos)
      << stderrOutput;
  EXPECT_EQ(stderrOutput.find("reset frontier cube coi"), std::string::npos)
      << stderrOutput;
}

TEST_F(SequentialEquivalenceStrategyTests,
       PDREngineUsesResetExpressionImplicationBeforeExactFrontier) {
  KInductionProblem problem;
  constexpr size_t x = 2;
  constexpr size_t guard = 3;
  constexpr size_t payload = 4;
  constexpr size_t a0 = 5;
  constexpr size_t a1 = 6;
  constexpr size_t reset = 7;
  problem.state0Symbols = {x, guard, payload, a0};
  problem.state1Symbols = {a1};
  problem.inputSymbols = {reset};
  problem.allSymbols = {x, guard, payload, a0, a1, reset};
  problem.resetBootstrapCycles = 1;
  problem.resetBootstrapInputs = {{reset, true}};
  problem.bootstrapStateEqualityPairs = {{a0, a1}};
  problem.transitions0.emplace_back(
      x,
      BoolExpr::And(
          BoolExpr::Not(BoolExpr::Var(reset)),
          BoolExpr::And(
              BoolExpr::Not(BoolExpr::Var(guard)),
              BoolExpr::Var(payload))));
  // payload' implies guard' after rewriting a0/a1 through the bootstrap
  // equality. The cube guard=0,payload=1 is therefore impossible, but the
  // expressions are not equivalent, so the reset-specialized proof must learn
  // the implication structurally instead of falling into the exact SAT unroll.
  problem.transitions0.emplace_back(guard, BoolExpr::Var(a0));
  problem.transitions0.emplace_back(
      payload, BoolExpr::And(BoolExpr::Var(a1), BoolExpr::Var(payload)));
  problem.transitions0.emplace_back(a0, BoolExpr::Var(a0));
  problem.transitions1.emplace_back(a1, BoolExpr::Var(a1));
  problem.bad = BoolExpr::Var(x);
  problem.property = BoolExpr::Not(problem.bad);
  problem.inductionProperty = problem.property;
  problem.inductionBad = problem.bad;

  ASSERT_FALSE(
      findBaseCounterexample(
          problem, KEPLER_FORMAL::Config::SolverType::KISSAT, 2)
          .has_value());

  const ScopedEnvVar pdrStats("KEPLER_SEC_PDR_STATS", "1");
  const ScopedEnvVar pdrStatsInterval("KEPLER_SEC_PDR_STATS_INTERVAL", "1");
  const ScopedEnvVar resetDiag("KEPLER_SEC_PDR_RESET_SHORTCUT_DIAG", "1");
  const ScopedEnvVar proofConflictLimit(
      "KEPLER_SEC_PDR_RESET_EXPRESSION_CONFLICT_LIMIT", "0");
  testing::internal::CaptureStderr();
  PDREngine engine(
      problem,
      KEPLER_FORMAL::Config::SolverType::KISSAT,
      PDREngine::kDefaultPredecessorProjectionLimit,
      PDREngine::kDefaultPreciseBadCubeStateLimit,
      /*useExactFrameClauses=*/false,
      /*maxPredecessorQueries=*/0,
      /*refineProjectedCounterexamples=*/true,
      PDREngine::kDefaultBoundedRootGeneralizationAttempts,
      /*learnValidatedBadFormulaClauses=*/false,
      /*useExactResetFrontierChecks=*/false);
  const auto result = engine.run(3);
  const std::string stderrOutput = testing::internal::GetCapturedStderr();

  EXPECT_EQ(result.status, PDRStatus::Equivalent);
  EXPECT_NE(
      stderrOutput.find("via=bootstrap_rewrite_implication"),
      std::string::npos)
      << stderrOutput;
  EXPECT_EQ(
      stderrOutput.find("reset-specialized expression solve cube=2"),
      std::string::npos)
      << stderrOutput;
  EXPECT_EQ(stderrOutput.find("reset frontier cube coi"), std::string::npos)
      << stderrOutput;
}

TEST_F(SequentialEquivalenceStrategyTests,
       PDREngineUsesResetSpecializedExpressionSatForWideRootCubes) {
  KInductionProblem problem;
  constexpr size_t x = 2;
  constexpr size_t y = 3;
  constexpr size_t w = 4;
  constexpr size_t a0 = 5;
  constexpr size_t a1 = 6;
  constexpr size_t reset = 7;
  constexpr size_t firstExtra = 8;
  constexpr size_t extraCount = 9;

  problem.state0Symbols = {x, y, a0};
  problem.state1Symbols = {w, a1};
  problem.inputSymbols = {reset};
  problem.allSymbols = {x, y, w, a0, a1, reset};
  problem.resetBootstrapCycles = 1;
  problem.resetBootstrapInputs = {{reset, true}};
  problem.initialStateEqualityPairs = {{a0, a1}};

  BoolExpr* rootCubeDriver =
      BoolExpr::And(BoolExpr::Var(y), BoolExpr::Not(BoolExpr::Var(w)));
  for (size_t index = 0; index < extraCount; ++index) {
    const size_t symbol = firstExtra + index;
    problem.state0Symbols.push_back(symbol);
    problem.allSymbols.push_back(symbol);
    problem.transitions0.emplace_back(symbol, BoolExpr::Var(symbol));
    rootCubeDriver = BoolExpr::And(rootCubeDriver, BoolExpr::Var(symbol));
  }

  problem.transitions0.emplace_back(
      x,
      BoolExpr::And(BoolExpr::Not(BoolExpr::Var(reset)), rootCubeDriver));
  // This wide root cube is reset-unreachable only after substituting the reset
  // expressions y'=a0 and w'=a1 and applying the SEC frame-0 equality a0 == a1.
  // AES produced the same shape with 108 literals; falling back to exact
  // reset-frontier SAT there was the sampled runtime wall.
  problem.transitions0.emplace_back(y, BoolExpr::Var(a0));
  problem.transitions1.emplace_back(w, BoolExpr::Var(a1));
  problem.transitions0.emplace_back(a0, BoolExpr::Var(a0));
  problem.transitions1.emplace_back(a1, BoolExpr::Var(a1));
  problem.bad = BoolExpr::Var(x);
  problem.property = BoolExpr::Not(problem.bad);
  problem.inductionProperty = problem.property;
  problem.inductionBad = problem.bad;

  ASSERT_FALSE(
      findBaseCounterexample(
          problem, KEPLER_FORMAL::Config::SolverType::KISSAT, 2)
          .has_value());

  const ScopedEnvVar pdrStats("KEPLER_SEC_PDR_STATS", "1");
  const ScopedEnvVar pdrStatsInterval("KEPLER_SEC_PDR_STATS_INTERVAL", "1");
  const ScopedEnvVar kiDiag("KEPLER_SEC_KI_DIAG", "1");
  testing::internal::CaptureStderr();
  PDREngine engine(
      problem,
      KEPLER_FORMAL::Config::SolverType::KISSAT,
      /*predecessorProjectionLimit=*/32,
      /*preciseBadCubeStateLimit=*/32,
      /*useExactFrameClauses=*/false,
      /*maxPredecessorQueries=*/0,
      /*refineProjectedCounterexamples=*/true,
      PDREngine::kDefaultBoundedRootGeneralizationAttempts,
      /*learnValidatedBadFormulaClauses=*/false,
      /*useExactResetFrontierChecks=*/false);
  const auto result = engine.run(3);
  const std::string stderrOutput = testing::internal::GetCapturedStderr();

  EXPECT_EQ(result.status, PDRStatus::Equivalent);
  EXPECT_NE(
      stderrOutput.find("reset-specialized expression conflict"),
      std::string::npos)
      << stderrOutput;
  EXPECT_EQ(stderrOutput.find("reset frontier cube coi"), std::string::npos)
      << stderrOutput;
}

TEST_F(SequentialEquivalenceStrategyTests,
       PDREngineCanonicalizesResetSpecializedExpressionsBeforeSat) {
  KInductionProblem problem;
  constexpr size_t x0 = 2;
  constexpr size_t x1 = 3;
  constexpr size_t y = 4;
  constexpr size_t w = 5;
  constexpr size_t e0 = 6;
  constexpr size_t e1 = 7;
  constexpr size_t a = 8;
  constexpr size_t b = 9;
  constexpr size_t reset = 10;

  problem.state0Symbols = {x0, x1, y, w, e0, e1, a, b};
  problem.inputSymbols = {reset};
  problem.allSymbols = {x0, x1, y, w, e0, e1, a, b, reset};
  problem.resetBootstrapCycles = 1;
  problem.resetBootstrapInputs = {{reset, true}};
  const auto gatedBad =
      [&](BoolExpr* extra) {
        return BoolExpr::And(
            BoolExpr::Not(BoolExpr::Var(reset)),
            BoolExpr::And(
                BoolExpr::And(BoolExpr::Var(y), BoolExpr::Not(BoolExpr::Var(w))),
                extra));
      };
  problem.transitions0.emplace_back(x0, gatedBad(BoolExpr::Var(e0)));
  problem.transitions0.emplace_back(x1, gatedBad(BoolExpr::Var(e1)));
  // Both bad predecessors are reset-unreachable for the same reason:
  // y' = a | (a & b) is Boolean-equivalent to w' = a. The sampled AES run was
  // spending time in the reset-specialized SAT fallback for this shape, so the
  // canonical pass should learn the conflict before invoking that solver.
  problem.transitions0.emplace_back(
      y,
      BoolExpr::Or(BoolExpr::Var(a),
                   BoolExpr::And(BoolExpr::Var(a), BoolExpr::Var(b))));
  problem.transitions0.emplace_back(w, BoolExpr::Var(a));
  problem.transitions0.emplace_back(e0, BoolExpr::Var(e0));
  problem.transitions0.emplace_back(e1, BoolExpr::Var(e1));
  problem.transitions0.emplace_back(a, BoolExpr::Var(a));
  problem.transitions0.emplace_back(b, BoolExpr::Var(b));
  problem.bad = BoolExpr::Or(BoolExpr::Var(x0), BoolExpr::Var(x1));
  problem.property = BoolExpr::Not(problem.bad);
  problem.inductionProperty = problem.property;
  problem.inductionBad = problem.bad;

  ASSERT_FALSE(
      findBaseCounterexample(
          problem, KEPLER_FORMAL::Config::SolverType::KISSAT, 2)
          .has_value());

  const ScopedEnvVar pdrStats("KEPLER_SEC_PDR_STATS", "1");
  const ScopedEnvVar pdrStatsInterval("KEPLER_SEC_PDR_STATS_INTERVAL", "1");
  const ScopedEnvVar resetDiag("KEPLER_SEC_PDR_RESET_SHORTCUT_DIAG", "1");
  const ScopedEnvVar kiDiag("KEPLER_SEC_KI_DIAG", "1");
  testing::internal::CaptureStderr();
  PDREngine engine(
      problem,
      KEPLER_FORMAL::Config::SolverType::KISSAT,
      /*predecessorProjectionLimit=*/32,
      /*preciseBadCubeStateLimit=*/32,
      /*useExactFrameClauses=*/false,
      /*maxPredecessorQueries=*/0,
      /*refineProjectedCounterexamples=*/true,
      PDREngine::kDefaultBoundedRootGeneralizationAttempts,
      /*learnValidatedBadFormulaClauses=*/false,
      /*useExactResetFrontierChecks=*/false);
  const auto result = engine.run(3);
  const std::string stderrOutput = testing::internal::GetCapturedStderr();

  EXPECT_EQ(result.status, PDRStatus::Equivalent);
  EXPECT_NE(
      stderrOutput.find("via=canonical"),
      std::string::npos)
      << stderrOutput;
  EXPECT_EQ(stderrOutput.find("reset frontier cube coi"), std::string::npos)
      << stderrOutput;
}

TEST_F(SequentialEquivalenceStrategyTests,
       PDREngineValidatedBadFormulaLearningRepairsBeforePostBootstrapPrecheck) {
  KInductionProblem problem;
  problem.state0Symbols = {2, 3};
  problem.inputSymbols = {4};
  problem.allSymbols = {2, 3, 4};
  problem.resetBootstrapCycles = 1;
  problem.resetBootstrapInputs = {{4, false}};
  problem.bootstrapStateAssignments = {{2, false}};
  problem.transitions0.emplace_back(2, BoolExpr::And(BoolExpr::Var(4), BoolExpr::Var(3)));
  problem.transitions0.emplace_back(3, BoolExpr::createFalse());
  problem.bad = BoolExpr::Var(2);
  problem.property = BoolExpr::Not(problem.bad);
  problem.inductionProperty = problem.property;
  problem.inductionBad = problem.bad;

  ASSERT_FALSE(
      findBaseCounterexample(
          problem, KEPLER_FORMAL::Config::SolverType::KISSAT, 1)
          .has_value());

  const ScopedEnvVar pdrStats("KEPLER_SEC_PDR_STATS", "1");
  const ScopedEnvVar pdrStatsInterval("KEPLER_SEC_PDR_STATS_INTERVAL", "1");
  const ScopedEnvVar kiDiag("KEPLER_SEC_KI_DIAG", "1");
  testing::internal::CaptureStderr();
  PDREngine engine(
      problem,
      KEPLER_FORMAL::Config::SolverType::KISSAT,
      PDREngine::kDefaultPredecessorProjectionLimit,
      PDREngine::kDefaultPreciseBadCubeStateLimit,
      /*useExactFrameClauses=*/false,
      /*maxPredecessorQueries=*/0,
      /*refineProjectedCounterexamples=*/true,
      PDREngine::kDefaultBoundedRootGeneralizationAttempts,
      /*learnValidatedBadFormulaClauses=*/true,
      /*useExactResetFrontierChecks=*/true);
  const auto result = engine.run(3);
  const std::string stderrOutput = testing::internal::GetCapturedStderr();

  EXPECT_EQ(result.status, PDRStatus::Equivalent);
  EXPECT_NE(
      stderrOutput.find(
          "refined projected counterexample with validated bad-formula clauses"),
      std::string::npos)
      << stderrOutput;
  EXPECT_NE(
      stderrOutput.find("k-induction base coi"),
      std::string::npos)
      << stderrOutput;
  EXPECT_EQ(stderrOutput.find("reset frontier cube coi"), std::string::npos)
      << stderrOutput;
}

TEST_F(SequentialEquivalenceStrategyTests,
       PDREngineExactResetFrontierBlocksBeforeRootMinimization) {
  KInductionProblem problem;
  constexpr size_t x = 2;
  constexpr size_t y = 3;
  constexpr size_t w = 4;
  constexpr size_t z = 5;
  constexpr size_t reset = 6;
  problem.state0Symbols = {x, y, w, z};
  problem.inputSymbols = {reset};
  problem.allSymbols = {x, y, w, z, reset};
  problem.resetBootstrapCycles = 1;
  problem.resetBootstrapInputs = {{reset, true}};
  problem.transitions0.emplace_back(
      x,
      BoolExpr::And(
          BoolExpr::Not(BoolExpr::Var(reset)),
          BoolExpr::And(BoolExpr::Var(y), BoolExpr::Not(BoolExpr::Var(w)))));
  // The concrete reset step creates y == w, but that relation is intentionally
  // not summarized in F0. Exact reset-frontier predecessor checks should block
  // the abstract predecessor before PDR learns a root obligation and starts any
  // optional root-cube minimization work.
  problem.transitions0.emplace_back(y, BoolExpr::Var(w));
  problem.transitions0.emplace_back(w, BoolExpr::Var(w));
  problem.transitions0.emplace_back(z, BoolExpr::Var(z));
  problem.bad = BoolExpr::And(BoolExpr::Var(x), BoolExpr::Var(z));
  problem.property = BoolExpr::Not(problem.bad);
  problem.inductionProperty = problem.property;
  problem.inductionBad = problem.bad;

  ASSERT_FALSE(
      findBaseCounterexample(
          problem, KEPLER_FORMAL::Config::SolverType::KISSAT, 2)
          .has_value());

  const ScopedEnvVar pdrStats("KEPLER_SEC_PDR_STATS", "1");
  const ScopedEnvVar pdrStatsInterval("KEPLER_SEC_PDR_STATS_INTERVAL", "1");
  const ScopedEnvVar kiDiag("KEPLER_SEC_KI_DIAG", "1");
  testing::internal::CaptureStderr();
  PDREngine engine(
      problem,
      KEPLER_FORMAL::Config::SolverType::KISSAT,
      PDREngine::kDefaultPredecessorProjectionLimit,
      PDREngine::kDefaultPreciseBadCubeStateLimit,
      /*useExactFrameClauses=*/false,
      /*maxPredecessorQueries=*/0,
      /*refineProjectedCounterexamples=*/true,
      PDREngine::kDefaultBoundedRootGeneralizationAttempts,
      /*learnValidatedBadFormulaClauses=*/false,
      /*useExactResetFrontierChecks=*/true);
  const auto result = engine.run(3);
  const std::string stderrOutput = testing::internal::GetCapturedStderr();

  EXPECT_EQ(result.status, PDRStatus::Equivalent);
  EXPECT_NE(stderrOutput.find("post_bootstrap_steps=1"), std::string::npos)
      << stderrOutput;
  EXPECT_NE(stderrOutput.find("exact_reset_frontier=1 result=unsat"), std::string::npos)
      << stderrOutput;
  EXPECT_EQ(stderrOutput.find("reset-frontier core"), std::string::npos)
      << stderrOutput;
  EXPECT_EQ(
      stderrOutput.find("post_bootstrap_steps=0 frames=2 "
                        "solver_symbols=5 transition_targets=4 cube_literals=1"),
      std::string::npos)
      << stderrOutput;
}

TEST_F(SequentialEquivalenceStrategyTests,
       PDREngineSkipsExactResetPrecheckForUnprojectedPredecessorQuery) {
  KInductionProblem problem;
  constexpr size_t x = 2;
  constexpr size_t y = 3;
  constexpr size_t w = 4;
  constexpr size_t z = 5;
  constexpr size_t reset = 6;
  problem.state0Symbols = {x, y, w, z};
  problem.inputSymbols = {reset};
  problem.allSymbols = {x, y, w, z, reset};
  problem.resetBootstrapCycles = 1;
  problem.resetBootstrapInputs = {{reset, true}};
  problem.transitions0.emplace_back(
      x,
      BoolExpr::And(
          BoolExpr::Not(BoolExpr::Var(reset)),
          BoolExpr::And(BoolExpr::Var(y), BoolExpr::Not(BoolExpr::Var(w)))));
  problem.transitions0.emplace_back(y, BoolExpr::Var(w));
  problem.transitions0.emplace_back(w, BoolExpr::Var(w));
  problem.transitions0.emplace_back(z, BoolExpr::Var(z));
  problem.bad = BoolExpr::And(BoolExpr::Var(x), BoolExpr::Var(z));
  problem.property = BoolExpr::Not(problem.bad);
  problem.inductionProperty = problem.property;
  problem.inductionBad = problem.bad;

  const ScopedEnvVar pdrStats("KEPLER_SEC_PDR_STATS", "1");
  const ScopedEnvVar pdrStatsInterval("KEPLER_SEC_PDR_STATS_INTERVAL", "1");
  const ScopedEnvVar kiDiag("KEPLER_SEC_KI_DIAG", "1");
  testing::internal::CaptureStderr();
  PDREngine engine(
      problem,
      KEPLER_FORMAL::Config::SolverType::KISSAT,
      /*predecessorProjectionLimit=*/0,
      PDREngine::kDefaultPreciseBadCubeStateLimit,
      /*useExactFrameClauses=*/true,
      /*maxPredecessorQueries=*/0,
      /*refineProjectedCounterexamples=*/true,
      PDREngine::kDefaultBoundedRootGeneralizationAttempts,
      /*learnValidatedBadFormulaClauses=*/false,
      /*useExactResetFrontierChecks=*/true);
  const auto result = engine.run(3);
  const std::string stderrOutput = testing::internal::GetCapturedStderr();

  EXPECT_EQ(result.status, PDRStatus::Equivalent);
  EXPECT_NE(
      stderrOutput.find("exact_reset_frontier=skipped"),
      std::string::npos)
      << stderrOutput;
  // In unprojected mode the normal predecessor SAT query is already exact.
  // Do not spend the sampled AES wall time on an extra one-step reset-image
  // query before that exact predecessor query has a chance to run.
  EXPECT_EQ(
      stderrOutput.find("reset frontier cube coi post_bootstrap_steps=1"),
      std::string::npos)
      << stderrOutput;
}

TEST_F(SequentialEquivalenceStrategyTests,
       PDREngineValidatedLearningKeepsRootResetFrontierRefinementDisabled) {
  KInductionProblem problem;
  constexpr size_t x = 2;
  constexpr size_t y = 3;
  constexpr size_t w = 4;
  constexpr size_t z = 5;
  constexpr size_t reset = 6;
  problem.state0Symbols = {x, y, w, z};
  problem.inputSymbols = {reset};
  problem.allSymbols = {x, y, w, z, reset};
  problem.resetBootstrapCycles = 1;
  problem.resetBootstrapInputs = {{reset, true}};
  problem.transitions0.emplace_back(
      x,
      BoolExpr::And(
          BoolExpr::Not(BoolExpr::Var(reset)),
          BoolExpr::And(BoolExpr::Var(y), BoolExpr::Not(BoolExpr::Var(w)))));
  problem.transitions0.emplace_back(y, BoolExpr::Var(w));
  problem.transitions0.emplace_back(w, BoolExpr::Var(w));
  problem.transitions0.emplace_back(z, BoolExpr::Var(z));
  problem.bad = BoolExpr::And(BoolExpr::Var(x), BoolExpr::Var(z));
  problem.property = BoolExpr::Not(problem.bad);
  problem.inductionProperty = problem.property;
  problem.inductionBad = problem.bad;

  ASSERT_FALSE(
      findBaseCounterexample(
          problem, KEPLER_FORMAL::Config::SolverType::KISSAT, 2)
          .has_value());

  const ScopedEnvVar pdrStats("KEPLER_SEC_PDR_STATS", "1");
  const ScopedEnvVar pdrStatsInterval("KEPLER_SEC_PDR_STATS_INTERVAL", "1");
  const ScopedEnvVar kiDiag("KEPLER_SEC_KI_DIAG", "1");
  testing::internal::CaptureStderr();
  PDREngine engine(
      problem,
      KEPLER_FORMAL::Config::SolverType::KISSAT,
      PDREngine::kDefaultPredecessorProjectionLimit,
      PDREngine::kDefaultPreciseBadCubeStateLimit,
      /*useExactFrameClauses=*/false,
      /*maxPredecessorQueries=*/0,
      /*refineProjectedCounterexamples=*/true,
      PDREngine::kDefaultBoundedRootGeneralizationAttempts,
      /*learnValidatedBadFormulaClauses=*/true,
      /*useExactResetFrontierChecks=*/true);
  const auto result = engine.run(3);
  const std::string stderrOutput = testing::internal::GetCapturedStderr();

  EXPECT_EQ(result.status, PDRStatus::Equivalent);
  EXPECT_NE(
      stderrOutput.find(
          "refined projected counterexample with validated bad-formula clauses"),
      std::string::npos)
      << stderrOutput;
  EXPECT_EQ(stderrOutput.find("reset frontier cube coi post_bootstrap_steps=0"),
            std::string::npos)
      << stderrOutput;
  EXPECT_EQ(stderrOutput.find("reset-frontier core"), std::string::npos)
      << stderrOutput;
}

TEST_F(SequentialEquivalenceStrategyTests,
       ResetFrontierReachabilityExtractsSmallUnreachableCubeCore) {
  KInductionProblem problem;
  constexpr size_t resetForcedLow = 2;
  constexpr size_t freeState0 = 3;
  constexpr size_t freeState1 = 4;
  constexpr size_t reset = 5;
  problem.state0Symbols = {resetForcedLow, freeState0, freeState1};
  problem.inputSymbols = {reset};
  problem.allSymbols = {resetForcedLow, freeState0, freeState1, reset};
  problem.resetBootstrapCycles = 1;
  problem.resetBootstrapInputs = {{reset, true}};
  problem.bootstrapStateAssignments = {{resetForcedLow, false}};
  problem.transitions0.emplace_back(
      resetForcedLow,
      BoolExpr::And(
          BoolExpr::Not(BoolExpr::Var(reset)),
          BoolExpr::Var(resetForcedLow)));
  problem.transitions0.emplace_back(freeState0, BoolExpr::Var(freeState0));
  problem.transitions0.emplace_back(freeState1, BoolExpr::Var(freeState1));

  const TransitionExprResolver transitionByState(problem);
  const auto context =
      makeResetFrontierReachabilityContext(problem, transitionByState);
  const std::vector<std::pair<size_t, bool>> wideUnreachableCube = {
      {resetForcedLow, true}, {freeState0, true}, {freeState1, false}};

  ASSERT_FALSE(isStateCubeReachableAtResetFrontier(
      *context,
      KEPLER_FORMAL::Config::SolverType::KISSAT,
      wideUnreachableCube,
      0));
  ASSERT_FALSE(isStateCubeReachableAtResetFrontier(
      *context,
      KEPLER_FORMAL::Config::SolverType::KISSAT,
      std::vector<std::pair<size_t, bool>>{{resetForcedLow, true}},
      0));
  const auto core = findResetFrontierUnreachableCubeCore(
      *context,
      KEPLER_FORMAL::Config::SolverType::KISSAT,
      wideUnreachableCube,
      0);

  ASSERT_TRUE(core.has_value());
  EXPECT_LT(core->size(), wideUnreachableCube.size());
  EXPECT_FALSE(isStateCubeReachableAtResetFrontier(
      *context, KEPLER_FORMAL::Config::SolverType::KISSAT, *core, 0));
  EXPECT_NE(
      std::find(
          core->begin(), core->end(), std::pair<size_t, bool>{resetForcedLow, true}),
      core->end());
}

TEST_F(SequentialEquivalenceStrategyTests,
       ResetFrontierReachabilityOneShotMatchesCachedAssumptionSolver) {
  KInductionProblem problem;
  constexpr size_t resetForcedLow = 2;
  constexpr size_t freeState = 3;
  constexpr size_t reset = 4;
  problem.state0Symbols = {resetForcedLow, freeState};
  problem.inputSymbols = {reset};
  problem.allSymbols = {resetForcedLow, freeState, reset};
  problem.resetBootstrapCycles = 1;
  problem.resetBootstrapInputs = {{reset, true}};
  problem.bootstrapStateAssignments = {{resetForcedLow, false}};
  problem.transitions0.emplace_back(
      resetForcedLow,
      BoolExpr::And(
          BoolExpr::Not(BoolExpr::Var(reset)),
          BoolExpr::Var(resetForcedLow)));
  problem.transitions0.emplace_back(freeState, BoolExpr::Var(freeState));

  const TransitionExprResolver transitionByState(problem);
  const auto context =
      makeResetFrontierReachabilityContext(problem, transitionByState);
  const std::vector<std::pair<size_t, bool>> unreachableCube = {
      {resetForcedLow, true}, {freeState, true}};
  const std::vector<std::pair<size_t, bool>> reachableCube = {
      {resetForcedLow, false}, {freeState, true}};

  // The one-shot path is the same exact bounded-prefix query as the cached
  // assumption solver, but it gives final PDR candidate validation a way to use
  // the selected SEC solver instead of a long-lived incremental Glucose query.
  EXPECT_EQ(
      isStateCubeReachableAtResetFrontier(
          *context,
          KEPLER_FORMAL::Config::SolverType::KISSAT,
          unreachableCube,
          0),
      isStateCubeReachableAtResetFrontierOneShot(
          *context,
          KEPLER_FORMAL::Config::SolverType::KISSAT,
          unreachableCube,
          0));
  EXPECT_EQ(
      isStateCubeReachableAtResetFrontier(
          *context,
          KEPLER_FORMAL::Config::SolverType::KISSAT,
          reachableCube,
          0),
      isStateCubeReachableAtResetFrontierOneShot(
          *context,
          KEPLER_FORMAL::Config::SolverType::KISSAT,
          reachableCube,
          0));
}

TEST_F(SequentialEquivalenceStrategyTests,
       ResetFrontierReachabilitySkipsDanglingInitialEqualityTails) {
  KInductionProblem problem;
  constexpr size_t y = 2;
  constexpr size_t x = 3;
  constexpr size_t equalityTailBase = 100;
  constexpr size_t equalityTailLength = 20;
  problem.state0Symbols = {y, x};
  problem.allSymbols = {y, x};
  for (size_t offset = 0; offset < equalityTailLength; ++offset) {
    const size_t symbol = equalityTailBase + offset;
    problem.state0Symbols.push_back(symbol);
    problem.allSymbols.push_back(symbol);
  }
  problem.transitions0.emplace_back(y, BoolExpr::Var(x));
  problem.transitions0.emplace_back(x, BoolExpr::Var(x));
  problem.initialStateEqualityPairs.emplace_back(x, equalityTailBase);
  for (size_t offset = 1; offset < equalityTailLength; ++offset) {
    problem.initialStateEqualityPairs.emplace_back(
        equalityTailBase + offset - 1, equalityTailBase + offset);
  }

  const TransitionExprResolver transitionByState(problem);
  const auto context =
      makeResetFrontierReachabilityContext(problem, transitionByState);

  // The equality tail is existential-only: no cube literal, transition, or
  // initial assignment observes the far end.  Closing the whole tail is exact
  // but wasteful; AES PDR samples showed these dangling relational tails
  // inflating final reset-frontier SAT queries.
  const ScopedEnvVar kiDiag("KEPLER_SEC_KI_DIAG", "1");
  testing::internal::CaptureStderr();
  EXPECT_TRUE(isStateCubeReachableAtResetFrontierOneShot(
      *context,
      KEPLER_FORMAL::Config::SolverType::KISSAT,
      std::vector<std::pair<size_t, bool>>{{y, true}},
      1));
  const std::string stderrOutput = testing::internal::GetCapturedStderr();

  EXPECT_NE(stderrOutput.find("solver_symbols=2"), std::string::npos)
      << stderrOutput;
}

TEST_F(SequentialEquivalenceStrategyTests,
       ResetFrontierReachabilityRelaxedPostBootstrapOneShotCanAvoidExactCoi) {
  KInductionProblem problem;
  constexpr size_t observed = 2;
  constexpr size_t bootstrapGuard = 3;
  constexpr size_t reset = 4;
  constexpr size_t equalityTailBase = 100;
  constexpr size_t equalityTailLength = 32;
  problem.state0Symbols = {observed, bootstrapGuard};
  problem.inputSymbols = {reset};
  problem.allSymbols = {observed, bootstrapGuard, reset};
  problem.resetBootstrapCycles = 1;
  problem.resetBootstrapInputs = {{reset, true}};
  problem.bootstrapStateAssignments = {{bootstrapGuard, false}};
  problem.transitions0.emplace_back(observed, BoolExpr::Var(bootstrapGuard));
  problem.transitions0.emplace_back(bootstrapGuard, BoolExpr::Var(bootstrapGuard));
  for (size_t offset = 0; offset < equalityTailLength; ++offset) {
    const size_t symbol = equalityTailBase + offset;
    problem.state0Symbols.push_back(symbol);
    problem.allSymbols.push_back(symbol);
    problem.transitions0.emplace_back(symbol, BoolExpr::Var(symbol));
  }
  problem.bootstrapStateEqualityPairs.emplace_back(
      bootstrapGuard, equalityTailBase);
  for (size_t offset = 1; offset < equalityTailLength; ++offset) {
    problem.bootstrapStateEqualityPairs.emplace_back(
        equalityTailBase + offset - 1, equalityTailBase + offset);
  }

  const TransitionExprResolver transitionByState(problem);
  const auto context =
      makeResetFrontierReachabilityContext(problem, transitionByState);

  const ScopedEnvVar kiDiag("KEPLER_SEC_KI_DIAG", "1");
  testing::internal::CaptureStderr();
  EXPECT_FALSE(isStateCubeReachableAtResetFrontierOneShot(
      *context,
      KEPLER_FORMAL::Config::SolverType::KISSAT,
      std::vector<std::pair<size_t, bool>>{{observed, true}},
      1));
  const std::string stderrOutput = testing::internal::GetCapturedStderr();

  // The relaxed precheck drops only startup equality closure, so UNSAT remains
  // a sound reset-frontier proof. It should avoid opening the exact COI that
  // would pull the whole bootstrap equality tail into this local contradiction.
  EXPECT_NE(
      stderrOutput.find("reset frontier relaxed one-shot cube coi"),
      std::string::npos)
      << stderrOutput;
  EXPECT_EQ(
      stderrOutput.find("reset frontier one-shot cube coi"),
      std::string::npos)
      << stderrOutput;
}

TEST_F(SequentialEquivalenceStrategyTests,
       ResetFrontierReachabilityRelaxedPostBootstrapCachedCanAvoidExactCoi) {
  KInductionProblem problem;
  constexpr size_t observed = 2;
  constexpr size_t bootstrapGuard = 3;
  constexpr size_t reset = 4;
  constexpr size_t equalityTailBase = 100;
  constexpr size_t equalityTailLength = 32;
  problem.state0Symbols = {observed, bootstrapGuard};
  problem.inputSymbols = {reset};
  problem.allSymbols = {observed, bootstrapGuard, reset};
  problem.resetBootstrapCycles = 1;
  problem.resetBootstrapInputs = {{reset, true}};
  problem.bootstrapStateAssignments = {{bootstrapGuard, false}};
  problem.transitions0.emplace_back(observed, BoolExpr::Var(bootstrapGuard));
  problem.transitions0.emplace_back(bootstrapGuard, BoolExpr::Var(bootstrapGuard));
  for (size_t offset = 0; offset < equalityTailLength; ++offset) {
    const size_t symbol = equalityTailBase + offset;
    problem.state0Symbols.push_back(symbol);
    problem.allSymbols.push_back(symbol);
    problem.transitions0.emplace_back(symbol, BoolExpr::Var(symbol));
  }
  problem.bootstrapStateEqualityPairs.emplace_back(
      bootstrapGuard, equalityTailBase);
  for (size_t offset = 1; offset < equalityTailLength; ++offset) {
    problem.bootstrapStateEqualityPairs.emplace_back(
        equalityTailBase + offset - 1, equalityTailBase + offset);
  }

  const TransitionExprResolver transitionByState(problem);
  const auto context =
      makeResetFrontierReachabilityContext(problem, transitionByState);

  const ScopedEnvVar kiDiag("KEPLER_SEC_KI_DIAG", "1");
  testing::internal::CaptureStderr();
  EXPECT_FALSE(isStateCubeReachableAtResetFrontier(
      *context,
      KEPLER_FORMAL::Config::SolverType::KISSAT,
      std::vector<std::pair<size_t, bool>>{{observed, true}},
      1));
  const std::string stderrOutput = testing::internal::GetCapturedStderr();

  // Cached-assumption validation is the PDR hot path. It should use the same
  // sound relaxed UNSAT precheck as one-shot validation before opening the
  // wider exact Glucose assumption solver sampled in AES.
  EXPECT_NE(
      stderrOutput.find("reset frontier relaxed cached cube coi"),
      std::string::npos)
      << stderrOutput;
  EXPECT_EQ(
      stderrOutput.find("reset frontier cube coi"),
      std::string::npos)
      << stderrOutput;
}

TEST_F(SequentialEquivalenceStrategyTests,
       ResetFrontierReachabilitySkipsBroadRelaxedCachedPrecheck) {
  KInductionProblem problem;
  constexpr size_t observed = 2;
  constexpr size_t reset = 3;
  constexpr size_t supportBase = 100;
  constexpr size_t supportCount = 300;
  problem.state0Symbols = {observed};
  problem.inputSymbols = {reset};
  problem.allSymbols = {observed, reset};
  problem.resetBootstrapCycles = 1;
  problem.resetBootstrapInputs = {{reset, true}};

  BoolExpr* observedNext = BoolExpr::createFalse();
  for (size_t offset = 0; offset < supportCount; ++offset) {
    const size_t symbol = supportBase + offset;
    problem.state0Symbols.push_back(symbol);
    problem.allSymbols.push_back(symbol);
    problem.transitions0.emplace_back(symbol, BoolExpr::Var(symbol));
    observedNext = BoolExpr::Or(observedNext, BoolExpr::Var(symbol));
  }
  problem.transitions0.emplace_back(observed, observedNext);

  const TransitionExprResolver transitionByState(problem);
  const auto context =
      makeResetFrontierReachabilityContext(problem, transitionByState);

  const ScopedEnvVar kiDiag("KEPLER_SEC_KI_DIAG", "1");
  testing::internal::CaptureStderr();
  EXPECT_TRUE(isStateCubeReachableAtResetFrontier(
      *context,
      KEPLER_FORMAL::Config::SolverType::KISSAT,
      std::vector<std::pair<size_t, bool>>{{observed, true}},
      1));
  const std::string stderrOutput = testing::internal::GetCapturedStderr();

  // The relaxed precheck is only a local UNSAT shortcut. If it still pulls a
  // broad transition surface, skip solving it and fall through to the exact
  // cached reset-frontier query instead of creating an unbounded PDR wall.
  EXPECT_NE(
      stderrOutput.find(
          "reset frontier relaxed cached precheck skipped reason=coi_cap"),
      std::string::npos)
      << stderrOutput;
  EXPECT_NE(
      stderrOutput.find("reset frontier cube coi"),
      std::string::npos)
      << stderrOutput;
}

TEST_F(SequentialEquivalenceStrategyTests,
       ResetFrontierReachabilityUsesValidatedFrameInvariantAfterStartup) {
  KInductionProblem problem;
  constexpr size_t x = 2;
  constexpr size_t y = 3;
  constexpr size_t z = 4;
  constexpr size_t reset = 5;
  problem.state0Symbols = {x, y, z};
  problem.inputSymbols = {reset};
  problem.allSymbols = {x, y, z, reset};
  problem.resetBootstrapCycles = 1;
  problem.resetBootstrapInputs = {{reset, true}};
  problem.transitions0.emplace_back(
      x,
      BoolExpr::Not(makeEqualityExpr(BoolExpr::Var(y), BoolExpr::Var(z))));
  problem.transitions0.emplace_back(y, BoolExpr::Var(y));
  problem.transitions0.emplace_back(z, BoolExpr::Var(z));

  const TransitionExprResolver transitionByState(problem);
  const std::vector<std::pair<size_t, bool>> targetCube = {{x, true}};
  const auto plainContext =
      makeResetFrontierReachabilityContext(problem, transitionByState);
  ASSERT_TRUE(isStateCubeReachableAtResetFrontierOneShot(
      *plainContext,
      KEPLER_FORMAL::Config::SolverType::KISSAT,
      targetCube,
      1));

  // PDR validates the invariant separately before passing it into this helper.
  // The bounded transition prefix is unchanged, but from the startup frontier
  // onward y==z makes x unreachable one post-bootstrap step later.
  BoolExpr* frameInvariant =
      makeEqualityExpr(BoolExpr::Var(y), BoolExpr::Var(z));
  const auto invariantContext =
      makeResetFrontierReachabilityContext(
          problem, transitionByState, frameInvariant);

  const ScopedEnvVar kiDiag("KEPLER_SEC_KI_DIAG", "1");
  testing::internal::CaptureStderr();
  EXPECT_FALSE(isStateCubeReachableAtResetFrontierOneShot(
      *invariantContext,
      KEPLER_FORMAL::Config::SolverType::KISSAT,
      targetCube,
      1));
  const std::string stderrOutput = testing::internal::GetCapturedStderr();

  EXPECT_NE(
      stderrOutput.find("frame_invariant_symbols=2"),
      std::string::npos)
      << stderrOutput;
}

TEST_F(SequentialEquivalenceStrategyTests,
       ResetFrontierReachabilityRejectsTransitiveKnownFactConflictBeforeSat) {
  KInductionProblem problem;
  constexpr size_t stateA = 2;
  constexpr size_t stateB = 3;
  constexpr size_t stateC = 4;
  constexpr size_t reset = 5;
  problem.state0Symbols = {stateA, stateB, stateC};
  problem.inputSymbols = {reset};
  problem.allSymbols = {stateA, stateB, stateC, reset};
  problem.resetBootstrapCycles = 1;
  problem.resetBootstrapInputs = {{reset, true}};
  // The reset frontier contains a == b and b == c, so a != c is impossible
  // even though no direct equality pair mentions both cube literals.
  problem.bootstrapStateEqualityPairs = {{stateA, stateB}, {stateB, stateC}};

  const TransitionExprResolver transitionByState(problem);
  const auto context =
      makeResetFrontierReachabilityContext(problem, transitionByState);

  const ScopedEnvVar kiDiag("KEPLER_SEC_KI_DIAG", "1");
  testing::internal::CaptureStderr();
  EXPECT_FALSE(isStateCubeReachableAtResetFrontier(
      *context,
      KEPLER_FORMAL::Config::SolverType::KISSAT,
      std::vector<std::pair<size_t, bool>>{{stateA, true}, {stateC, false}},
      0));
  const std::string stderrOutput = testing::internal::GetCapturedStderr();

  EXPECT_NE(
      stderrOutput.find("reset frontier known facts exclude cube"),
      std::string::npos)
      << stderrOutput;
  EXPECT_EQ(
      stderrOutput.find("reset frontier cube coi"),
      std::string::npos)
      << stderrOutput;
}

TEST_F(SequentialEquivalenceStrategyTests,
       ResetFrontierReachabilityReusesCachedUnreachableCores) {
  KInductionProblem problem;
  constexpr size_t resetForcedLow = 2;
  constexpr size_t neighborState0 = 3;
  constexpr size_t neighborState1 = 4;
  constexpr size_t reset = 5;
  problem.state0Symbols = {resetForcedLow, neighborState0, neighborState1};
  problem.inputSymbols = {reset};
  problem.allSymbols = {resetForcedLow, neighborState0, neighborState1, reset};
  problem.resetBootstrapCycles = 1;
  problem.resetBootstrapInputs = {{reset, true}};
  problem.bootstrapStateAssignments = {{resetForcedLow, false}};
  problem.transitions0.emplace_back(
      resetForcedLow,
      BoolExpr::And(
          BoolExpr::Not(BoolExpr::Var(reset)),
          BoolExpr::Var(resetForcedLow)));
  problem.transitions0.emplace_back(neighborState0, BoolExpr::Var(neighborState0));
  problem.transitions0.emplace_back(neighborState1, BoolExpr::Var(neighborState1));

  const TransitionExprResolver transitionByState(problem);
  const auto context =
      makeResetFrontierReachabilityContext(problem, transitionByState);
  const std::vector<std::pair<size_t, bool>> firstUnreachableCube = {
      {resetForcedLow, true}, {neighborState0, true}, {neighborState1, false}};
  const std::vector<std::pair<size_t, bool>> neighboringUnreachableCube = {
      {resetForcedLow, true}, {neighborState0, false}};

  ASSERT_FALSE(isStateCubeReachableAtResetFrontier(
      *context,
      KEPLER_FORMAL::Config::SolverType::KISSAT,
      firstUnreachableCube,
      0));

  const ScopedEnvVar kiDiag("KEPLER_SEC_KI_DIAG", "1");
  testing::internal::CaptureStderr();
  EXPECT_FALSE(isStateCubeReachableAtResetFrontier(
      *context,
      KEPLER_FORMAL::Config::SolverType::KISSAT,
      neighboringUnreachableCube,
      0));
  const std::string stderrOutput = testing::internal::GetCapturedStderr();

  EXPECT_NE(
      stderrOutput.find("reset frontier cached unreachable core hit"),
      std::string::npos)
      << stderrOutput;
}

TEST_F(SequentialEquivalenceStrategyTests,
       ResetFrontierReachabilityCachesPostBootstrapFailedAssumptionCores) {
  KInductionProblem problem;
  constexpr size_t resetForcedLow = 2;
  constexpr size_t neighborState0 = 3;
  constexpr size_t neighborState1 = 4;
  constexpr size_t reset = 5;
  problem.state0Symbols = {resetForcedLow, neighborState0, neighborState1};
  problem.inputSymbols = {reset};
  problem.allSymbols = {resetForcedLow, neighborState0, neighborState1, reset};
  problem.resetBootstrapCycles = 1;
  problem.resetBootstrapInputs = {{reset, true}};
  problem.bootstrapStateAssignments = {{resetForcedLow, false}};
  problem.transitions0.emplace_back(
      resetForcedLow,
      BoolExpr::And(
          BoolExpr::Not(BoolExpr::Var(reset)),
          BoolExpr::Var(resetForcedLow)));
  problem.transitions0.emplace_back(neighborState0, BoolExpr::Var(neighborState0));
  problem.transitions0.emplace_back(neighborState1, BoolExpr::Var(neighborState1));

  const TransitionExprResolver transitionByState(problem);
  const auto context =
      makeResetFrontierReachabilityContext(problem, transitionByState);
  const std::vector<std::pair<size_t, bool>> firstUnreachableCube = {
      {resetForcedLow, true}, {neighborState0, true}, {neighborState1, false}};
  const std::vector<std::pair<size_t, bool>> neighboringUnreachableCube = {
      {resetForcedLow, true}, {neighborState0, false}};

  ASSERT_FALSE(isStateCubeReachableAtResetFrontier(
      *context,
      KEPLER_FORMAL::Config::SolverType::KISSAT,
      firstUnreachableCube,
      1));

  const ScopedEnvVar kiDiag("KEPLER_SEC_KI_DIAG", "1");
  testing::internal::CaptureStderr();
  EXPECT_FALSE(isStateCubeReachableAtResetFrontier(
      *context,
      KEPLER_FORMAL::Config::SolverType::KISSAT,
      neighboringUnreachableCube,
      1));
  const std::string stderrOutput = testing::internal::GetCapturedStderr();

  EXPECT_NE(
      stderrOutput.find("reset frontier relaxed cached cube coi"),
      std::string::npos)
      << stderrOutput;
  EXPECT_EQ(
      stderrOutput.find("reset frontier cube coi"),
      std::string::npos)
      << stderrOutput;
}

TEST_F(SequentialEquivalenceStrategyTests,
       ResetFrontierReachabilityUsesPriorCoreAsSafePrefixBlocker) {
  KInductionProblem problem;
  constexpr size_t resetForcedLow = 2;
  constexpr size_t reset = 3;
  problem.state0Symbols = {resetForcedLow};
  problem.inputSymbols = {reset};
  problem.allSymbols = {resetForcedLow, reset};
  problem.resetBootstrapCycles = 1;
  problem.resetBootstrapInputs = {{reset, true}};
  problem.transitions0.emplace_back(
      resetForcedLow,
      BoolExpr::And(
          BoolExpr::Not(BoolExpr::Var(reset)),
          BoolExpr::Var(resetForcedLow)));

  const TransitionExprResolver transitionByState(problem);
  const auto context =
      makeResetFrontierReachabilityContext(problem, transitionByState);
  const std::vector<std::pair<size_t, bool>> unreachableCube = {
      {resetForcedLow, true}};

  ASSERT_FALSE(isStateCubeReachableAtResetFrontier(
      *context,
      KEPLER_FORMAL::Config::SolverType::KISSAT,
      unreachableCube,
      0));

  const ScopedEnvVar kiDiag("KEPLER_SEC_KI_DIAG", "1");
  testing::internal::CaptureStderr();
  EXPECT_FALSE(isStateCubeReachableAtResetFrontier(
      *context,
      KEPLER_FORMAL::Config::SolverType::KISSAT,
      unreachableCube,
      1));
  const std::string stderrOutput = testing::internal::GetCapturedStderr();

  EXPECT_NE(
      stderrOutput.find("reset frontier previous unreachable blockers=1"),
      std::string::npos)
      << stderrOutput;
}

TEST_F(SequentialEquivalenceStrategyTests,
       ResetFrontierReachabilityCachesPostBootstrapOneShotFailures) {
  KInductionProblem problem;
  constexpr size_t resetForcedLow = 2;
  constexpr size_t neighborState = 3;
  constexpr size_t reset = 4;
  problem.state0Symbols = {resetForcedLow, neighborState};
  problem.inputSymbols = {reset};
  problem.allSymbols = {resetForcedLow, neighborState, reset};
  problem.resetBootstrapCycles = 1;
  problem.resetBootstrapInputs = {{reset, true}};
  problem.bootstrapStateAssignments = {{resetForcedLow, false}};
  problem.transitions0.emplace_back(
      resetForcedLow,
      BoolExpr::And(
          BoolExpr::Not(BoolExpr::Var(reset)),
          BoolExpr::Var(resetForcedLow)));
  problem.transitions0.emplace_back(neighborState, BoolExpr::Var(neighborState));

  const TransitionExprResolver transitionByState(problem);
  const auto context =
      makeResetFrontierReachabilityContext(problem, transitionByState);
  const std::vector<std::pair<size_t, bool>> unreachableCube = {
      {resetForcedLow, true}, {neighborState, false}};

  // One-shot PDR prechecks at post-bootstrap depths must populate the shared
  // unreachable-core cache too; otherwise a repeated target rebuilds the same
  // reset COI instead of taking the cheap cache hit.
  ASSERT_FALSE(isStateCubeReachableAtResetFrontierOneShot(
      *context,
      KEPLER_FORMAL::Config::SolverType::KISSAT,
      unreachableCube,
      1));

  const ScopedEnvVar kiDiag("KEPLER_SEC_KI_DIAG", "1");
  testing::internal::CaptureStderr();
  EXPECT_FALSE(isStateCubeReachableAtResetFrontier(
      *context,
      KEPLER_FORMAL::Config::SolverType::KISSAT,
      unreachableCube,
      1));
  const std::string stderrOutput = testing::internal::GetCapturedStderr();

  EXPECT_NE(
      stderrOutput.find("reset frontier cached unreachable core hit"),
      std::string::npos)
      << stderrOutput;
  EXPECT_EQ(
      stderrOutput.find("reset frontier cube coi"),
      std::string::npos)
      << stderrOutput;
}

TEST_F(SequentialEquivalenceStrategyTests,
       LazyTransitionSupportCacheIsSharedAcrossResolversWithoutDagRemap) {
  KInductionProblem problem;
  constexpr size_t combinedState = 10;
  constexpr size_t combinedInput = 11;
  constexpr size_t localState = 2;
  constexpr size_t localInput = 3;
  BoolExpr* localNext =
      BoolExpr::And(BoolExpr::Var(localState), BoolExpr::Var(localInput));

  auto lazyTransitions = std::make_shared<LazyTransitionStore>();
  lazyTransitions->localToCombinedByDesign[0].emplace(localState, combinedState);
  lazyTransitions->localToCombinedByDesign[0].emplace(localInput, combinedInput);
  lazyTransitions->sourceByStateSymbol.emplace(
      combinedState, LazyTransitionSource{0, localNext});
  problem.lazyTransitions = lazyTransitions;
  problem.state0Symbols = {combinedState};
  problem.inputSymbols = {combinedInput};
  problem.allSymbols = {combinedState, combinedInput};

  {
    const TransitionExprResolver transitionByState(problem);
    const auto& support = transitionByState.support(combinedState);
    EXPECT_EQ(support, (std::set<size_t>{combinedState, combinedInput}));
    EXPECT_EQ(transitionByState.nodeCount(combinedState), 3u);
  }

  ASSERT_NE(
      lazyTransitions->supportByStateSymbol.find(combinedState),
      lazyTransitions->supportByStateSymbol.end());
  ASSERT_NE(
      lazyTransitions->nodeCountByStateSymbol.find(combinedState),
      lazyTransitions->nodeCountByStateSymbol.end());
  // Support and node-count queries must not force a lazy BoolExpr remap. In
  // BlackParrot PDR those queries happen while rebuilding reset-frontier COIs
  // across many output batches; sharing this metadata avoids repeatedly
  // walking the same source DAGs before any transition needs SAT encoding.
  EXPECT_TRUE(lazyTransitions->remappedByStateSymbol.empty());

  const TransitionExprResolver secondTransitionByState(problem);
  EXPECT_EQ(
      secondTransitionByState.support(combinedState),
      (std::set<size_t>{combinedState, combinedInput}));
  EXPECT_EQ(secondTransitionByState.nodeCount(combinedState), 3u);
  EXPECT_TRUE(lazyTransitions->remappedByStateSymbol.empty());
}

TEST_F(SequentialEquivalenceStrategyTests,
       ResetFrontierReachabilityReusesWiderCachedSolverForSubsetCube) {
  KInductionProblem problem;
  constexpr size_t resetForcedLow = 2;
  constexpr size_t neighborState0 = 3;
  constexpr size_t neighborState1 = 4;
  constexpr size_t reset = 5;
  problem.state0Symbols = {resetForcedLow, neighborState0, neighborState1};
  problem.inputSymbols = {reset};
  problem.allSymbols = {resetForcedLow, neighborState0, neighborState1, reset};
  problem.resetBootstrapCycles = 1;
  problem.resetBootstrapInputs = {{reset, true}};
  problem.bootstrapStateAssignments = {{resetForcedLow, false}};
  problem.transitions0.emplace_back(
      resetForcedLow,
      BoolExpr::And(
          BoolExpr::Not(BoolExpr::Var(reset)),
          BoolExpr::Var(resetForcedLow)));
  problem.transitions0.emplace_back(neighborState0, BoolExpr::Var(neighborState0));
  problem.transitions0.emplace_back(neighborState1, BoolExpr::Var(neighborState1));

  const TransitionExprResolver transitionByState(problem);
  const auto context =
      makeResetFrontierReachabilityContext(problem, transitionByState);
  const std::vector<std::pair<size_t, bool>> wideReachableCube = {
      {resetForcedLow, false}, {neighborState0, true}, {neighborState1, false}};
  const std::vector<std::pair<size_t, bool>> subsetReachableCube = {
      {resetForcedLow, false}, {neighborState0, false}};

  ASSERT_TRUE(isStateCubeReachableAtResetFrontier(
      *context,
      KEPLER_FORMAL::Config::SolverType::KISSAT,
      wideReachableCube,
      1));

  // PDR often checks neighboring cubes where a previous reset-frontier solver
  // already covers a wider COI. Reusing that exact solver avoids rebuilding
  // transition support and clauses for every small cube variant.
  const ScopedEnvVar kiDiag("KEPLER_SEC_KI_DIAG", "1");
  testing::internal::CaptureStderr();
  EXPECT_TRUE(isStateCubeReachableAtResetFrontier(
      *context,
      KEPLER_FORMAL::Config::SolverType::KISSAT,
      subsetReachableCube,
      1));
  const std::string stderrOutput = testing::internal::GetCapturedStderr();

  EXPECT_NE(
      stderrOutput.find("reset frontier solver superset cache hit"),
      std::string::npos)
      << stderrOutput;
}

TEST_F(SequentialEquivalenceStrategyTests,
       PDREngineSkipsExactResetPrecheckAboveConfiguredSupportLimit) {
  KInductionProblem problem;
  constexpr size_t y = 2;
  constexpr size_t reset = 100;
  constexpr size_t supportBase = 200;
  constexpr size_t supportCount = 300;
  problem.state0Symbols.push_back(y);
  problem.allSymbols.push_back(y);
  BoolExpr* nextY = BoolExpr::createFalse();
  problem.bootstrapStateAssignments.push_back({y, false});
  for (size_t index = 0; index < supportCount; ++index) {
    const size_t symbol = supportBase + index;
    problem.state0Symbols.push_back(symbol);
    problem.allSymbols.push_back(symbol);
    problem.bootstrapStateAssignments.push_back({symbol, false});
    problem.transitions0.emplace_back(symbol, BoolExpr::Var(symbol));
    nextY = BoolExpr::Or(nextY, BoolExpr::Var(symbol));
  }
  problem.inputSymbols = {reset};
  problem.allSymbols.push_back(reset);
  problem.resetBootstrapCycles = 1;
  problem.resetBootstrapInputs = {{reset, true}};
  problem.transitions0.emplace_back(y, nextY);
  problem.bad = BoolExpr::Var(y);
  problem.property = BoolExpr::Not(problem.bad);
  problem.inductionProperty = problem.property;
  problem.inductionBad = problem.bad;

  const ScopedEnvVar pdrStats("KEPLER_SEC_PDR_STATS", "1");
  const ScopedEnvVar pdrStatsInterval("KEPLER_SEC_PDR_STATS_INTERVAL", "1");
  const ScopedEnvVar exactResetPrecheckLimit(
      "KEPLER_SEC_PDR_EXACT_RESET_PRECHECK_SUPPORT_LIMIT", "256");
  testing::internal::CaptureStderr();
  PDREngine engine(problem, KEPLER_FORMAL::Config::SolverType::KISSAT);
  const auto result = engine.run(2);
  const std::string stderrOutput = testing::internal::GetCapturedStderr();

  EXPECT_EQ(result.status, PDRStatus::Equivalent);
  EXPECT_NE(
      stderrOutput.find("exact_reset_frontier=skipped"),
      std::string::npos);
}

TEST_F(SequentialEquivalenceStrategyTests,
       PDREngineProjectsLevelZeroResetPredecessorsAfterConcretePrecheck) {
  KInductionProblem problem;
  constexpr size_t y = 2;
  constexpr size_t reset = 3;
  constexpr size_t supportBase = 100;
  constexpr size_t supportCount = 64;
  problem.state0Symbols.push_back(y);
  problem.inputSymbols = {reset};
  problem.allSymbols = {y, reset};
  problem.resetBootstrapCycles = 1;
  problem.resetBootstrapInputs = {{reset, true}};
  problem.bootstrapStateAssignments.push_back({y, false});

  BoolExpr* nextY = BoolExpr::createFalse();
  for (size_t index = 0; index < supportCount; ++index) {
    const size_t symbol = supportBase + index;
    problem.state0Symbols.push_back(symbol);
    problem.allSymbols.push_back(symbol);
    // Make the concrete reset predecessor real, but leave a wide support cone.
    // PDR should not carry the full 64-bit support cube after the exact
    // reset-frontier precheck already established concrete reachability.
    problem.bootstrapStateAssignments.push_back({symbol, index == 0});
    problem.transitions0.emplace_back(symbol, BoolExpr::Var(symbol));
    nextY = BoolExpr::Or(nextY, BoolExpr::Var(symbol));
  }
  problem.transitions0.emplace_back(y, nextY);
  problem.bad = BoolExpr::Var(y);
  problem.property = BoolExpr::Not(problem.bad);
  problem.inductionProperty = problem.property;
  problem.inductionBad = problem.bad;

  const ScopedEnvVar pdrStats("KEPLER_SEC_PDR_STATS", "1");
  const ScopedEnvVar pdrStatsInterval("KEPLER_SEC_PDR_STATS_INTERVAL", "1");
  testing::internal::CaptureStderr();
  PDREngine engine(
      problem,
      KEPLER_FORMAL::Config::SolverType::KISSAT,
      /*predecessorProjectionLimit=*/8,
      /*preciseBadCubeStateLimit=*/PDREngine::kDefaultPreciseBadCubeStateLimit);
  const auto result = engine.run(2);
  const std::string stderrOutput = testing::internal::GetCapturedStderr();

  EXPECT_EQ(result.status, PDRStatus::Different);
  EXPECT_NE(
      stderrOutput.find("exact_reset_frontier=1 result=sat"),
      std::string::npos)
      << stderrOutput;
  EXPECT_NE(stderrOutput.find("predecessor_cube=1"), std::string::npos)
      << stderrOutput;
}

TEST_F(SequentialEquivalenceStrategyTests,
       PDREngineConstrainsResetInputsOnFirstPostBootstrapStep) {
  KInductionProblem problem;
  problem.state0Symbols = {2};
  problem.inputSymbols = {3, 4};
  problem.allSymbols = {2, 3, 4};
  problem.resetBootstrapCycles = 1;
  problem.resetBootstrapInputs = {{3, true}, {4, false}};
  // The concrete reset prefix drives x=0, then deasserts the reset controls as
  // r=0 and g=1.  The abstract PDR F[0] summary contains only x=0, so a
  // level-0 predecessor query that forgets reset-input deassertion can invent
  // r=1,g=1 on the first normal step and falsely reach x'=1.
  problem.bootstrapStateAssignments = {{2, false}};
  problem.transitions0.emplace_back(
      2, BoolExpr::And(BoolExpr::Var(3), BoolExpr::Var(4)));
  problem.bad = BoolExpr::Var(2);
  problem.property = BoolExpr::Not(problem.bad);
  problem.inductionProperty = problem.property;
  problem.inductionBad = problem.bad;

  EXPECT_FALSE(
      findBaseCounterexample(
          problem, KEPLER_FORMAL::Config::SolverType::KISSAT, 1)
          .has_value());

  PDREngine engine(problem, KEPLER_FORMAL::Config::SolverType::KISSAT);
  const auto result = engine.run(3);

  EXPECT_EQ(result.status, PDRStatus::Equivalent);
}

TEST_F(SequentialEquivalenceStrategyTests,
       PDREngineConstrainsResetInputsInPostBootstrapBadQueries) {
  KInductionProblem problem;
  problem.state0Symbols = {2};
  problem.inputSymbols = {3, 4};
  problem.allSymbols = {2, 3, 4};
  problem.resetBootstrapCycles = 1;
  problem.resetBootstrapInputs = {{3, true}, {4, false}};
  problem.bootstrapStateAssignments = {{2, false}};
  problem.transitions0.emplace_back(2, BoolExpr::createFalse());
  // The bad predicate is input-only. PDR must still apply the post-reset
  // deasserted reset controls before deciding whether this is a real bad frame.
  problem.bad = BoolExpr::And(BoolExpr::Var(3), BoolExpr::Var(4));
  problem.property = BoolExpr::Not(problem.bad);
  problem.inductionProperty = problem.property;
  problem.inductionBad = problem.bad;

  EXPECT_FALSE(
      findBaseCounterexample(
          problem, KEPLER_FORMAL::Config::SolverType::KISSAT, 2)
          .has_value());

  PDREngine engine(problem, KEPLER_FORMAL::Config::SolverType::KISSAT);
  const auto result = engine.run(3);

  EXPECT_EQ(result.status, PDRStatus::Equivalent);
}

TEST_F(SequentialEquivalenceStrategyTests,
       PDREngineDoesNotLoopOnProjectedResetFrontierRefinements) {
  KInductionProblem problem;
  constexpr size_t a = 2;
  constexpr size_t b = 3;
  constexpr size_t y = 4;
  constexpr size_t reset = 5;
  problem.state0Symbols = {a, b, y};
  problem.inputSymbols = {reset};
  problem.allSymbols = {a, b, y, reset};
  problem.resetBootstrapCycles = 1;
  problem.resetBootstrapInputs = {{reset, true}};

  BoolExpr* resetDeasserted = BoolExpr::Not(BoolExpr::Var(reset));
  problem.transitions0.emplace_back(
      a, BoolExpr::And(resetDeasserted, BoolExpr::Var(a)));
  problem.transitions0.emplace_back(
      b, BoolExpr::And(resetDeasserted, BoolExpr::Var(b)));
  problem.transitions0.emplace_back(
      y,
      BoolExpr::And(
          resetDeasserted,
          BoolExpr::Or(BoolExpr::Var(a), BoolExpr::Var(b))));
  problem.bad = BoolExpr::Var(y);
  problem.property = BoolExpr::Not(problem.bad);
  problem.inductionProperty = problem.property;
  problem.inductionBad = problem.bad;

  ASSERT_FALSE(
      findBaseCounterexample(
          problem, KEPLER_FORMAL::Config::SolverType::KISSAT, 2)
          .has_value());

  // Force the same condition sampled on BlackParrot: projected F[0] encoding
  // can omit one reset-frontier refinement even though the full frame already
  // blocks the predecessor cube. PDR must not keep re-enqueuing that stale
  // projected predecessor.
  const ScopedEnvVar clauseLimit(
      "KEPLER_SEC_PDR_PROJECTED_FRAME_CLAUSE_LIMIT", "1");
  PDREngine engine(
      problem,
      KEPLER_FORMAL::Config::SolverType::KISSAT,
      /*predecessorProjectionLimit=*/PDREngine::kDefaultPredecessorProjectionLimit,
      /*preciseBadCubeStateLimit=*/PDREngine::kDefaultPreciseBadCubeStateLimit,
      /*useExactFrameClauses=*/false,
      /*maxPredecessorQueries=*/100);
  const auto result = engine.run(3);

  EXPECT_EQ(result.status, PDRStatus::Equivalent);
}

TEST_F(SequentialEquivalenceStrategyTests,
       PDREngineExactRetriesWhenProjectedPredecessorIsAlreadyBlocked) {
  KInductionProblem problem;
  problem.state0Symbols = {2, 3};
  problem.allSymbols = {2, 3};
  problem.initialCondition = BoolExpr::And(
      BoolExpr::Not(BoolExpr::Var(2)),
      BoolExpr::Not(BoolExpr::Var(3)));
  problem.initialStateAssignments = {{2, false}, {3, false}};
  problem.initializedStateCount = 2;
  problem.totalStateCount = 2;
  problem.transitions0.emplace_back(2, BoolExpr::Var(2));
  problem.transitions0.emplace_back(3, BoolExpr::Var(2));
  problem.bad = BoolExpr::Var(3);
  problem.property = BoolExpr::Not(problem.bad);
  problem.inductionProperty = problem.property;
  problem.inductionBad = problem.bad;

  // With a one-literal predecessor projection, the level-2 bad obligation for
  // b=1 first projects to a=1.  PDR then learns !a in F1 while blocking that
  // predecessor.  Re-querying b=1 against a projected frame can rediscover the
  // now-blocked a=1 cube forever unless the engine retries the parent query
  // against the exact learned frame before re-enqueueing it.
  PDREngine engine(
      problem,
      KEPLER_FORMAL::Config::SolverType::KISSAT,
      1,
      1);
  const auto result = engine.run(4);

  EXPECT_EQ(result.status, PDRStatus::Equivalent);
}

TEST_F(SequentialEquivalenceStrategyTests,
       PDREngineCapsProjectedFrameRefinementsBeforeExactRetry) {
  KInductionProblem problem;
  constexpr size_t a = 2;
  constexpr size_t b = 3;
  constexpr size_t y = 4;
  constexpr size_t reset = 5;
  problem.state0Symbols = {a, b, y};
  problem.inputSymbols = {reset};
  problem.allSymbols = {a, b, y, reset};
  problem.resetBootstrapCycles = 1;
  problem.resetBootstrapInputs = {{reset, true}};

  BoolExpr* resetDeasserted = BoolExpr::Not(BoolExpr::Var(reset));
  problem.transitions0.emplace_back(
      a, BoolExpr::And(resetDeasserted, BoolExpr::Var(a)));
  problem.transitions0.emplace_back(
      b, BoolExpr::And(resetDeasserted, BoolExpr::Var(b)));
  problem.transitions0.emplace_back(
      y,
      BoolExpr::And(
          resetDeasserted,
          BoolExpr::Or(BoolExpr::Var(a), BoolExpr::Var(b))));
  problem.bad = BoolExpr::Var(y);
  problem.property = BoolExpr::Not(problem.bad);
  problem.inductionProperty = problem.property;
  problem.inductionBad = problem.bad;

  ASSERT_FALSE(
      findBaseCounterexample(
          problem, KEPLER_FORMAL::Config::SolverType::KISSAT, 2)
          .has_value());

  // Force projected frame repair to see one omitted blocker, then cap it so
  // the same obligation immediately retries with exact frame clauses. This
  // protects the BlackParrot case where projected repair kept adding many local
  // blockers for the same obligation before reaching the exact retry.
  const ScopedEnvVar pdrStats("KEPLER_SEC_PDR_STATS", "1");
  const ScopedEnvVar pdrStatsInterval("KEPLER_SEC_PDR_STATS_INTERVAL", "1");
  const ScopedEnvVar clauseLimit(
      "KEPLER_SEC_PDR_PROJECTED_FRAME_CLAUSE_LIMIT", "1");
  const ScopedEnvVar refinementLimit(
      "KEPLER_SEC_PDR_PROJECTED_FRAME_REFINEMENT_LIMIT", "1");
  testing::internal::CaptureStderr();
  PDREngine engine(
      problem,
      KEPLER_FORMAL::Config::SolverType::KISSAT,
      1,
      1,
      /*useExactFrameClauses=*/false,
      /*maxPredecessorQueries=*/50);
  const auto result = engine.run(3);
  const std::string stderrOutput = testing::internal::GetCapturedStderr();

  EXPECT_EQ(result.status, PDRStatus::Equivalent);
  EXPECT_NE(
      stderrOutput.find("projected-frame refinement cap reached"),
      std::string::npos);
}

TEST_F(SequentialEquivalenceStrategyTests,
       PDREngineRefinesProjectedCounterexampleWithBoundedReachability) {
  KInductionProblem problem;
  problem.state0Symbols = {2, 3, 4};
  problem.allSymbols = {2, 3, 4};
  problem.initialCondition = BoolExpr::And(
      BoolExpr::And(BoolExpr::Not(BoolExpr::Var(2)),
                    BoolExpr::Not(BoolExpr::Var(3))),
      BoolExpr::Not(BoolExpr::Var(4)));
  problem.initialStateAssignments = {{2, false}, {3, false}, {4, false}};
  problem.initializedStateCount = 3;
  problem.totalStateCount = 3;
  problem.transitions0.emplace_back(2, BoolExpr::createTrue());
  problem.transitions0.emplace_back(3, BoolExpr::createFalse());
  problem.transitions0.emplace_back(
      4, BoolExpr::And(BoolExpr::Var(2), BoolExpr::Var(3)));
  problem.bad = BoolExpr::Var(4);
  problem.property = BoolExpr::Not(problem.bad);
  problem.inductionProperty = problem.property;
  problem.inductionBad = problem.bad;

  ASSERT_FALSE(
      findBaseCounterexample(
          problem, KEPLER_FORMAL::Config::SolverType::KISSAT, 3)
          .has_value());

  // The full predecessor of z=1 needs both x=1 and y=1, but a one-literal
  // projected obligation may keep only x=1.  Since x=1 is reachable while y=1
  // is not, PDR must refine the spurious bounded path instead of reporting a
  // counterexample for the projected cube.
  PDREngine engine(
      problem,
      KEPLER_FORMAL::Config::SolverType::KISSAT,
      /*predecessorProjectionLimit=*/1,
      /*preciseBadCubeStateLimit=*/1);
  const auto result = engine.run(3);

  EXPECT_EQ(result.status, PDRStatus::Equivalent);
}

TEST_F(SequentialEquivalenceStrategyTests,
       PDREngineCanDeferProjectedCounterexampleValidationToCaller) {
  KInductionProblem problem;
  problem.state0Symbols = {2, 3, 4};
  problem.allSymbols = {2, 3, 4};
  problem.initialCondition = BoolExpr::And(
      BoolExpr::And(BoolExpr::Not(BoolExpr::Var(2)),
                    BoolExpr::Not(BoolExpr::Var(3))),
      BoolExpr::Not(BoolExpr::Var(4)));
  problem.initialStateAssignments = {{2, false}, {3, false}, {4, false}};
  problem.initializedStateCount = 3;
  problem.totalStateCount = 3;
  problem.transitions0.emplace_back(2, BoolExpr::createTrue());
  problem.transitions0.emplace_back(3, BoolExpr::createFalse());
  problem.transitions0.emplace_back(
      4, BoolExpr::And(BoolExpr::Var(2), BoolExpr::Var(3)));
  problem.bad = BoolExpr::Var(4);
  problem.property = BoolExpr::Not(problem.bad);
  problem.inductionProperty = problem.property;
  problem.inductionBad = problem.bad;

  ASSERT_FALSE(
      findBaseCounterexample(
          problem, KEPLER_FORMAL::Config::SolverType::KISSAT, 3)
          .has_value());

  // SEC strategy validates every PDR "Different" result with concrete BMC.
  // Its projected precision stages can therefore return the abstract candidate
  // immediately instead of doing the same bounded-prefix validation inside PDR.
  PDREngine engine(
      problem,
      KEPLER_FORMAL::Config::SolverType::KISSAT,
      /*predecessorProjectionLimit=*/1,
      /*preciseBadCubeStateLimit=*/1,
      /*useExactFrameClauses=*/false,
      /*maxPredecessorQueries=*/0,
      /*refineProjectedCounterexamples=*/false);
  const auto result = engine.run(3);

  EXPECT_EQ(result.status, PDRStatus::Different);
  EXPECT_EQ(result.bound, 2u);
}

TEST_F(SequentialEquivalenceStrategyTests,
       PDREngineGeneralizesUnreachableProjectedCounterexampleRoot) {
  KInductionProblem problem;
  problem.state0Symbols = {2, 3, 4, 5};
  problem.allSymbols = {2, 3, 4, 5};
  problem.initialCondition = BoolExpr::And(
      BoolExpr::And(BoolExpr::Not(BoolExpr::Var(2)),
                    BoolExpr::Not(BoolExpr::Var(3))),
      BoolExpr::And(BoolExpr::Not(BoolExpr::Var(4)),
                    BoolExpr::Not(BoolExpr::Var(5))));
  problem.initialStateAssignments = {
      {2, false}, {3, false}, {4, false}, {5, false}};
  problem.initializedStateCount = 4;
  problem.totalStateCount = 4;
  problem.transitions0.emplace_back(2, BoolExpr::createTrue());
  problem.transitions0.emplace_back(3, BoolExpr::createFalse());
  problem.transitions0.emplace_back(4, BoolExpr::createTrue());
  problem.transitions0.emplace_back(
      5,
      BoolExpr::And(
          BoolExpr::And(BoolExpr::Var(2), BoolExpr::Var(3)),
          BoolExpr::Var(4)));
  problem.bad = BoolExpr::And(BoolExpr::Var(5), BoolExpr::Var(4));
  problem.property = BoolExpr::Not(problem.bad);
  problem.inductionProperty = problem.property;
  problem.inductionBad = problem.bad;

  ASSERT_FALSE(
      findBaseCounterexample(
          problem, KEPLER_FORMAL::Config::SolverType::KISSAT, 3)
          .has_value());

  // The projected predecessor can keep only the reachable x=1 literal and
  // therefore reaches Init abstractly. The concrete bad root still includes
  // b=1, which is unreachable because y is permanently false. PDR should learn
  // the exact bounded generalization b=0 rather than refining just b=1,z=1.
  const ScopedEnvVar pdrStats("KEPLER_SEC_PDR_STATS", "1");
  testing::internal::CaptureStderr();
  PDREngine engine(
      problem,
      KEPLER_FORMAL::Config::SolverType::KISSAT,
      /*predecessorProjectionLimit=*/1,
      /*preciseBadCubeStateLimit=*/2);
  const auto result = engine.run(3);
  const std::string stderrOutput = testing::internal::GetCapturedStderr();

  EXPECT_EQ(result.status, PDRStatus::Equivalent);
  EXPECT_NE(
      stderrOutput.find("refined projected counterexample bad_frame=2 root_cube=2->1"),
      std::string::npos);
}

TEST_F(SequentialEquivalenceStrategyTests,
       PDREngineCanRefineProjectedCounterexampleWithoutRootGeneralization) {
  KInductionProblem problem;
  problem.state0Symbols = {2, 3, 4, 5};
  problem.allSymbols = {2, 3, 4, 5};
  problem.initialCondition = BoolExpr::And(
      BoolExpr::And(BoolExpr::Not(BoolExpr::Var(2)),
                    BoolExpr::Not(BoolExpr::Var(3))),
      BoolExpr::And(BoolExpr::Not(BoolExpr::Var(4)),
                    BoolExpr::Not(BoolExpr::Var(5))));
  problem.initialStateAssignments = {
      {2, false}, {3, false}, {4, false}, {5, false}};
  problem.initializedStateCount = 4;
  problem.totalStateCount = 4;
  problem.transitions0.emplace_back(2, BoolExpr::createTrue());
  problem.transitions0.emplace_back(3, BoolExpr::createFalse());
  problem.transitions0.emplace_back(4, BoolExpr::createTrue());
  problem.transitions0.emplace_back(
      5,
      BoolExpr::And(
          BoolExpr::And(BoolExpr::Var(2), BoolExpr::Var(3)),
          BoolExpr::Var(4)));
  problem.bad = BoolExpr::And(BoolExpr::Var(5), BoolExpr::Var(4));
  problem.property = BoolExpr::Not(problem.bad);
  problem.inductionProperty = problem.property;
  problem.inductionBad = problem.bad;

  ASSERT_FALSE(
      findBaseCounterexample(
          problem, KEPLER_FORMAL::Config::SolverType::KISSAT, 3)
          .has_value());

  const ScopedEnvVar pdrStats("KEPLER_SEC_PDR_STATS", "1");
  testing::internal::CaptureStderr();
  PDREngine engine(
      problem,
      KEPLER_FORMAL::Config::SolverType::KISSAT,
      /*predecessorProjectionLimit=*/1,
      /*preciseBadCubeStateLimit=*/2,
      /*useExactFrameClauses=*/false,
      /*maxPredecessorQueries=*/0,
      /*refineProjectedCounterexamples=*/true,
      /*maxBoundedRootGeneralizationAttempts=*/0);
  const auto result = engine.run(3);
  const std::string stderrOutput = testing::internal::GetCapturedStderr();

  EXPECT_EQ(result.status, PDRStatus::Equivalent);
  EXPECT_NE(
      stderrOutput.find(
          "concrete cube reachability begin cube=2 max_step=2 "
          "mode=one_shot_unit_clauses"),
      std::string::npos);
  EXPECT_EQ(
      stderrOutput.find(
          "concrete cube reachability begin cube=2 max_step=2 "
          "mode=cached_assumptions"),
      std::string::npos);
  EXPECT_NE(
      stderrOutput.find("refined projected counterexample bad_frame=2 root_cube=2->2 checks=0"),
      std::string::npos);
}

TEST_F(SequentialEquivalenceStrategyTests,
       PDREngineUsesResetSpecializedConcreteFrameConflictBeforeBmcUnroll) {
  KInductionProblem problem;
  constexpr size_t x = 2;
  constexpr size_t y = 3;
  constexpr size_t gate = 4;
  constexpr size_t badState = 5;
  constexpr size_t reset = 6;
  problem.state0Symbols = {x, y, gate, badState};
  problem.inputSymbols = {reset};
  problem.allSymbols = {x, y, gate, badState, reset};
  problem.resetBootstrapCycles = 1;
  problem.resetBootstrapInputs = {{reset, true}};
  problem.transitions0.emplace_back(x, BoolExpr::Not(BoolExpr::Var(reset)));
  problem.transitions0.emplace_back(y, BoolExpr::createFalse());
  problem.transitions0.emplace_back(gate, BoolExpr::Not(BoolExpr::Var(reset)));
  problem.transitions0.emplace_back(
      badState,
      BoolExpr::And(
          BoolExpr::And(BoolExpr::Var(x), BoolExpr::Var(y)),
          BoolExpr::Var(gate)));
  problem.bad = BoolExpr::And(BoolExpr::Var(badState), BoolExpr::Var(gate));
  problem.property = BoolExpr::Not(problem.bad);
  problem.inductionProperty = problem.property;
  problem.inductionBad = problem.bad;

  ASSERT_FALSE(
      findBaseCounterexample(
          problem, KEPLER_FORMAL::Config::SolverType::KISSAT, 2)
          .has_value());

  const ScopedEnvVar pdrStats("KEPLER_SEC_PDR_STATS", "1");
  const ScopedEnvVar pdrStatsInterval("KEPLER_SEC_PDR_STATS_INTERVAL", "1");
  const ScopedEnvVar resetDiag("KEPLER_SEC_PDR_RESET_SHORTCUT_DIAG", "1");
  testing::internal::CaptureStderr();
  PDREngine engine(
      problem,
      KEPLER_FORMAL::Config::SolverType::KISSAT,
      /*predecessorProjectionLimit=*/1,
      /*preciseBadCubeStateLimit=*/2,
      /*useExactFrameClauses=*/false,
      /*maxPredecessorQueries=*/0,
      /*refineProjectedCounterexamples=*/true,
      /*maxBoundedRootGeneralizationAttempts=*/0,
      /*learnValidatedBadFormulaClauses=*/false,
      /*useExactResetFrontierChecks=*/false);
  const auto result = engine.run(3);
  const std::string stderrOutput = testing::internal::GetCapturedStderr();

  EXPECT_EQ(result.status, PDRStatus::Equivalent);
  EXPECT_NE(
      stderrOutput.find(
          "concrete cube reachability step step=1 result=unsat"),
      std::string::npos)
      << stderrOutput;
  EXPECT_EQ(
      stderrOutput.find("one-shot cube coi post_bootstrap_steps=1"),
      std::string::npos)
      << stderrOutput;
}

TEST_F(SequentialEquivalenceStrategyTests,
       PDREngineUsesCheckedResetFramePropertyWithStructuredInitFacts) {
  KInductionProblem problem;
  constexpr size_t badState = 2;
  constexpr size_t eqLhs = 3;
  constexpr size_t eqRhs = 4;
  constexpr size_t reset = 5;

  problem.state0Symbols = {badState, eqLhs, eqRhs};
  problem.inputSymbols = {reset};
  problem.allSymbols = {badState, eqLhs, eqRhs, reset};
  problem.resetBootstrapCycles = 1;
  problem.resetBootstrapInputs = {{reset, true}};
  // This unrelated structured fact makes PDR use the sparse structured-init
  // path. The regression was that this path skipped the checked F[0] property.
  problem.bootstrapStateEqualityPairs = {{eqLhs, eqRhs}};
  problem.transitions0.emplace_back(
      badState,
      BoolExpr::And(BoolExpr::Not(BoolExpr::Var(reset)), BoolExpr::Var(badState)));
  problem.transitions0.emplace_back(eqLhs, BoolExpr::createFalse());
  problem.transitions0.emplace_back(eqRhs, BoolExpr::createFalse());
  problem.bad = BoolExpr::Var(badState);
  problem.property = BoolExpr::Not(problem.bad);
  problem.inductionProperty = problem.property;
  problem.inductionBad = problem.bad;

  ASSERT_FALSE(
      findBaseCounterexample(
          problem, KEPLER_FORMAL::Config::SolverType::KISSAT, 2)
          .has_value());

  const ScopedEnvVar pdrStats("KEPLER_SEC_PDR_STATS", "1");
  const ScopedEnvVar pdrStatsInterval("KEPLER_SEC_PDR_STATS_INTERVAL", "1");
  testing::internal::CaptureStderr();
  PDREngine engine(
      problem,
      KEPLER_FORMAL::Config::SolverType::KISSAT,
      /*predecessorProjectionLimit=*/0,
      /*preciseBadCubeStateLimit=*/1,
      /*useExactFrameClauses=*/true,
      /*maxPredecessorQueries=*/0,
      /*refineProjectedCounterexamples=*/false,
      PDREngine::kDefaultBoundedRootGeneralizationAttempts,
      /*learnValidatedBadFormulaClauses=*/false,
      /*useExactResetFrontierChecks=*/false);
  const auto result = engine.run(2);
  const std::string stderrOutput = testing::internal::GetCapturedStderr();

  EXPECT_EQ(result.status, PDRStatus::Equivalent) << stderrOutput;
  EXPECT_NE(stderrOutput.find(" result=unsat"), std::string::npos)
      << stderrOutput;
  EXPECT_EQ(stderrOutput.find("counterexample candidate reached init"),
            std::string::npos)
      << stderrOutput;
}

TEST_F(SequentialEquivalenceStrategyTests,
       PDREngineCanLearnValidatedBadFormulaClausesAfterRejectedTrace) {
  KInductionProblem problem;
  problem.state0Symbols = {2, 3, 4, 5};
  problem.allSymbols = {2, 3, 4, 5};
  problem.initialCondition = BoolExpr::And(
      BoolExpr::And(BoolExpr::Not(BoolExpr::Var(2)),
                    BoolExpr::Not(BoolExpr::Var(3))),
      BoolExpr::And(BoolExpr::Not(BoolExpr::Var(4)),
                    BoolExpr::Not(BoolExpr::Var(5))));
  problem.initialStateAssignments = {
      {2, false}, {3, false}, {4, false}, {5, false}};
  problem.initializedStateCount = 4;
  problem.totalStateCount = 4;
  problem.transitions0.emplace_back(2, BoolExpr::createTrue());
  problem.transitions0.emplace_back(3, BoolExpr::createFalse());
  problem.transitions0.emplace_back(4, BoolExpr::createTrue());
  problem.transitions0.emplace_back(
      5,
      BoolExpr::And(
          BoolExpr::And(BoolExpr::Var(2), BoolExpr::Var(3)),
          BoolExpr::Var(4)));
  problem.bad = BoolExpr::And(BoolExpr::Var(5), BoolExpr::Var(4));
  problem.property = BoolExpr::Not(problem.bad);
  problem.inductionProperty = problem.property;
  problem.inductionBad = problem.bad;

  ASSERT_FALSE(
      findBaseCounterexample(
          problem, KEPLER_FORMAL::Config::SolverType::KISSAT, 3)
          .has_value());

  const ScopedEnvVar pdrStats("KEPLER_SEC_PDR_STATS", "1");
  testing::internal::CaptureStderr();
  PDREngine engine(
      problem,
      KEPLER_FORMAL::Config::SolverType::KISSAT,
      /*predecessorProjectionLimit=*/1,
      /*preciseBadCubeStateLimit=*/2,
      /*useExactFrameClauses=*/false,
      /*maxPredecessorQueries=*/0,
      /*refineProjectedCounterexamples=*/true,
      /*maxBoundedRootGeneralizationAttempts=*/0,
      /*learnValidatedBadFormulaClauses=*/true);
  const auto result = engine.run(3);
  const std::string stderrOutput = testing::internal::GetCapturedStderr();

  EXPECT_EQ(result.status, PDRStatus::Equivalent);
  EXPECT_NE(
      stderrOutput.find(
          "refined projected counterexample with validated bad-formula clauses"),
      std::string::npos);
}

TEST_F(SequentialEquivalenceStrategyTests,
       PDREngineLearnsValidatedBadFormulaClausesPerOutputInBatchedSecSlice) {
  KInductionProblem problem;
  const std::vector<std::vector<size_t>> outputStateGroups = {
      {2, 4, 5, 6, 7, 8},
      {9, 11, 12, 13, 14, 15}};

  BoolExpr* init = BoolExpr::createTrue();
  auto makeConjunction = [](const std::vector<size_t>& symbols) {
    BoolExpr* expr = BoolExpr::createTrue();
    for (const auto symbol : symbols) {
      expr = BoolExpr::And(expr, BoolExpr::Var(symbol));
    }
    return BoolExpr::simplify(expr);
  };

  auto addState = [&](size_t symbol, BoolExpr* next) {
    problem.state0Symbols.push_back(symbol);
    problem.allSymbols.push_back(symbol);
    problem.initialStateAssignments.push_back({symbol, false});
    init = BoolExpr::And(init, BoolExpr::Not(BoolExpr::Var(symbol)));
    problem.transitions0.emplace_back(symbol, next);
  };
  auto addOutputGroup = [&](size_t base) {
    addState(base + 0, BoolExpr::createTrue());
    addState(base + 1, BoolExpr::createFalse());
    addState(base + 2, BoolExpr::createTrue());
    addState(
        base + 3,
        BoolExpr::And(
            BoolExpr::And(BoolExpr::Var(base + 0), BoolExpr::Var(base + 1)),
            BoolExpr::Var(base + 2)));
    addState(base + 4, BoolExpr::createTrue());
    addState(base + 5, BoolExpr::createTrue());
    addState(base + 6, BoolExpr::createTrue());
  };

  addOutputGroup(2);
  addOutputGroup(9);
  for (const auto& group : outputStateGroups) {
    for (const auto symbol : group) {
      // Each per-output bad predicate is small enough to learn directly, but
      // the combined batched bad predicate has 12 state symbols. This guards
      // the BlackParrot case where the useful refinement is per observed output
      // rather than over the whole output-batch support union.
      ASSERT_NE(
          std::find(
              problem.state0Symbols.begin(), problem.state0Symbols.end(), symbol),
          problem.state0Symbols.end());
    }
  }

  BoolExpr* output0 = makeConjunction(outputStateGroups[0]);
  BoolExpr* output1 = makeConjunction(outputStateGroups[1]);
  problem.observedOutputExprs0 = {output0, output1};
  problem.observedOutputExprs1 = {
      BoolExpr::createFalse(), BoolExpr::createFalse()};
  problem.observedOutputNames = {"o0", "o1"};
  problem.initialCondition = BoolExpr::simplify(init);
  problem.initializedStateCount = 14;
  problem.totalStateCount = 14;
  problem.bad = BoolExpr::simplify(BoolExpr::Or(output0, output1));
  problem.property = BoolExpr::Not(problem.bad);
  problem.inductionProperty = problem.property;
  problem.inductionBad = problem.bad;

  ASSERT_FALSE(
      findBaseCounterexample(
          problem, KEPLER_FORMAL::Config::SolverType::KISSAT, 3)
          .has_value());

  const ScopedEnvVar pdrStats("KEPLER_SEC_PDR_STATS", "1");
  testing::internal::CaptureStderr();
  PDREngine engine(
      problem,
      KEPLER_FORMAL::Config::SolverType::KISSAT,
      /*predecessorProjectionLimit=*/2,
      /*preciseBadCubeStateLimit=*/2,
      /*useExactFrameClauses=*/false,
      /*maxPredecessorQueries=*/0,
      /*refineProjectedCounterexamples=*/true,
      /*maxBoundedRootGeneralizationAttempts=*/0,
      /*learnValidatedBadFormulaClauses=*/true);
  const auto result = engine.run(3);
  const std::string stderrOutput = testing::internal::GetCapturedStderr();

  EXPECT_EQ(result.status, PDRStatus::Equivalent);
  EXPECT_NE(
      stderrOutput.find(
          "refined projected counterexample with validated bad-formula clauses"),
      std::string::npos)
      << stderrOutput;
  EXPECT_NE(stderrOutput.find(" clauses=2"), std::string::npos)
      << stderrOutput;
}

TEST_F(SequentialEquivalenceStrategyTests,
       PDREngineRepairsBroadValidatedBadFormulaLearningPerOutput) {
  KInductionProblem problem;
  BoolExpr* init = BoolExpr::createTrue();
  auto makeConjunction = [](const std::vector<size_t>& symbols) {
    BoolExpr* expr = BoolExpr::createTrue();
    for (const auto symbol : symbols) {
      expr = BoolExpr::And(expr, BoolExpr::Var(symbol));
    }
    return BoolExpr::simplify(expr);
  };

  std::vector<BoolExpr*> outputs;
  size_t nextSymbol = 2;
  for (size_t output = 0; output < 10; ++output) {
    const size_t base = nextSymbol;
    nextSymbol += 7;
    std::vector<size_t> group;
    group.reserve(6);
    for (size_t offset = 0; offset < 6; ++offset) {
      const size_t symbol = base + offset;
      group.push_back(symbol);
      problem.state0Symbols.push_back(symbol);
      problem.allSymbols.push_back(symbol);
      problem.initialStateAssignments.push_back({symbol, false});
      init = BoolExpr::And(init, BoolExpr::Not(BoolExpr::Var(symbol)));
    }

    // One permanently false bit keeps every per-output conjunction unreachable,
    // while the projected bad cube remains small enough to exercise PDR's
    // concrete root-cube refinement after broad bad-formula validation is
    // deliberately skipped.
    problem.transitions0.emplace_back(base + 0, BoolExpr::createTrue());
    problem.transitions0.emplace_back(base + 1, BoolExpr::createFalse());
    problem.transitions0.emplace_back(base + 2, BoolExpr::createTrue());
    problem.transitions0.emplace_back(base + 3, BoolExpr::createTrue());
    problem.transitions0.emplace_back(base + 4, BoolExpr::createTrue());
    problem.transitions0.emplace_back(base + 5, BoolExpr::createTrue());

    outputs.push_back(makeConjunction(group));
    problem.observedOutputNames.push_back("o" + std::to_string(output));
  }

  problem.observedOutputExprs0 = outputs;
  problem.observedOutputExprs1.assign(outputs.size(), BoolExpr::createFalse());
  problem.initialCondition = BoolExpr::simplify(init);
  problem.initializedStateCount = problem.state0Symbols.size();
  problem.totalStateCount = problem.state0Symbols.size();
  problem.bad = BoolExpr::createFalse();
  for (auto* outputExpr : outputs) {
    problem.bad = BoolExpr::Or(problem.bad, outputExpr);
  }
  problem.bad = BoolExpr::simplify(problem.bad);
  problem.property = BoolExpr::Not(problem.bad);
  problem.inductionProperty = problem.property;
  problem.inductionBad = problem.bad;

  ASSERT_FALSE(
      findBaseCounterexample(
          problem, KEPLER_FORMAL::Config::SolverType::KISSAT, 3)
          .has_value());

  const ScopedEnvVar pdrStats("KEPLER_SEC_PDR_STATS", "1");
  testing::internal::CaptureStderr();
  PDREngine engine(
      problem,
      KEPLER_FORMAL::Config::SolverType::KISSAT,
      /*predecessorProjectionLimit=*/2,
      /*preciseBadCubeStateLimit=*/2,
      /*useExactFrameClauses=*/false,
      /*maxPredecessorQueries=*/0,
      /*refineProjectedCounterexamples=*/true,
      /*maxBoundedRootGeneralizationAttempts=*/0,
      /*learnValidatedBadFormulaClauses=*/true);
  const auto result = engine.run(3);
  const std::string stderrOutput = testing::internal::GetCapturedStderr();

  EXPECT_EQ(result.status, PDRStatus::Equivalent);
  EXPECT_NE(
      stderrOutput.find("skipped broad bad-formula validation"),
      std::string::npos)
      << stderrOutput;
  EXPECT_NE(
      stderrOutput.find(
          "per-output validated bad-formula clauses bad_frame=1 outputs=1 clauses=1"),
      std::string::npos)
      << stderrOutput;
}

TEST_F(SequentialEquivalenceStrategyTests,
       PDREngineReturnsInconclusiveWhenZeroBudgetNeedsFrames) {
  KInductionProblem problem;
  problem.state0Symbols = {2};
  problem.allSymbols = {2};
  problem.transitions0.emplace_back(2, BoolExpr::createTrue());
  problem.initialCondition = BoolExpr::Not(BoolExpr::Var(2));
  problem.initializedStateCount = 1;
  problem.totalStateCount = 1;
  problem.bad = BoolExpr::Var(2);
  problem.property = BoolExpr::Not(problem.bad);
  problem.inductionProperty = BoolExpr::createTrue();
  problem.inductionBad = BoolExpr::createFalse();

  PDREngine engine(problem, KEPLER_FORMAL::Config::SolverType::KISSAT);
  const auto result = engine.run(0);

  EXPECT_EQ(result.status, PDRStatus::Inconclusive);
  EXPECT_EQ(result.bound, 0u);
}

TEST_F(SequentialEquivalenceStrategyTests,
       PDREngineSeedsInductiveStateEqualitiesAndComplementedDesign1Pairs) {
  KInductionProblem problem;
  problem.state0Symbols = {2, 3};
  problem.state1Symbols = {4, 5};
  problem.allSymbols = {2, 3, 4, 5};
  problem.complementedStatePairs1 = {{4, 5}};
  problem.inductiveStateEqualityPairs = {{2, 3}};
  problem.transitions0.emplace_back(2, BoolExpr::Var(3));
  problem.transitions0.emplace_back(3, BoolExpr::createFalse());
  problem.transitions1.emplace_back(4, BoolExpr::createFalse());
  problem.initialCondition = BoolExpr::And(
      BoolExpr::And(BoolExpr::Not(BoolExpr::Var(2)), BoolExpr::Not(BoolExpr::Var(3))),
      BoolExpr::Not(BoolExpr::Var(4)));
  problem.initializedStateCount = 3;
  problem.totalStateCount = 4;
  problem.bad = BoolExpr::Var(2);
  problem.property = BoolExpr::Not(problem.bad);
  problem.inductionProperty = problem.property;
  problem.inductionBad = problem.bad;

  const ScopedEnvVar secPdrTrace("KEPLER_SEC_PDR_TRACE", "1");
  testing::internal::CaptureStderr();
  PDREngine engine(problem, KEPLER_FORMAL::Config::SolverType::KISSAT);
  const auto result = engine.run(2);
  const std::string stderrOutput = testing::internal::GetCapturedStderr();

  EXPECT_EQ(result.status, PDRStatus::Equivalent);
  EXPECT_NE(stderrOutput.find("F[1]"), std::string::npos);
}

TEST_F(SequentialEquivalenceStrategyTests,
       SynthesizedResetInferencePropagatesThroughLongBootstrapPipeline) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* primitives =
      NLLibrary::create(db, NLLibrary::Type::Primitives, NLName("prims"));
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* invModel = createInvModel(primitives);
  auto* andModel = createAnd2Model(primitives);
  auto* top = createBootstrapPipelineTopWithStages(
      library, "top", invModel, andModel, 12);

  const auto model = SequentialDesignModel::extract(top);

  EXPECT_FALSE(model.hasUnsupportedFeatures());
  EXPECT_EQ(model.initialStateValueByKey.size(), model.stateBits.size());
}

TEST_F(SequentialEquivalenceStrategyTests,
       SynthesizedResetInferenceScalesPastLargeStateCutoff) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* primitives =
      NLLibrary::create(db, NLLibrary::Type::Primitives, NLName("prims"));
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* invModel = createInvModel(primitives);
  auto* andModel = createAnd2Model(primitives);
  auto* top = createBootstrapPipelineTopWithStages(
      library, "top", invModel, andModel, 2200);

  const auto model = SequentialDesignModel::extract(top);

  EXPECT_FALSE(model.hasUnsupportedFeatures());
  EXPECT_EQ(model.initialStateValueByKey.size(), model.stateBits.size());
}

TEST_F(SequentialEquivalenceStrategyTests,
       StructuralStateInvariantRefinesConstantsUnknownVarsAndInvalidNodes) {
  const SignalKey a0 = makeSignalKey("a0");
  const SignalKey b0 = makeSignalKey("b0");
  const SignalKey c0 = makeSignalKey("c0");
  const SignalKey a1 = makeSignalKey("a1");
  const SignalKey b1 = makeSignalKey("b1");
  const SignalKey c1 = makeSignalKey("c1");
  BoolExpr invalid0;
  BoolExpr invalid1;

  SequentialDesignModel model0;
  model0.stateBits = {a0, b0, c0};
  model0.inputVarByKey.emplace(a0, 2);
  model0.inputVarByKey.emplace(b0, 3);
  model0.inputVarByKey.emplace(c0, 4);
  model0.initialStateValueByKey.emplace(a0, false);
  model0.initialStateValueByKey.emplace(b0, true);
  model0.initialStateValueByKey.emplace(c0, false);
  model0.nextStateExprByStateKey.emplace(a0, BoolExpr::createFalse());
  model0.nextStateExprByStateKey.emplace(b0, BoolExpr::Var(99));
  model0.nextStateExprByStateKey.emplace(c0, &invalid0);
  model0.complementedStateRelations.push_back({a0, b0});

  SequentialDesignModel model1;
  model1.stateBits = {b1, c1, a1};
  model1.inputVarByKey.emplace(a1, 5);
  model1.inputVarByKey.emplace(b1, 6);
  model1.inputVarByKey.emplace(c1, 7);
  model1.initialStateValueByKey.emplace(a1, false);
  model1.initialStateValueByKey.emplace(b1, true);
  model1.initialStateValueByKey.emplace(c1, false);
  model1.nextStateExprByStateKey.emplace(a1, BoolExpr::createFalse());
  model1.nextStateExprByStateKey.emplace(b1, BoolExpr::Var(123));
  model1.nextStateExprByStateKey.emplace(c1, &invalid1);
  model1.complementedStateRelations.push_back({a1, b1});

  const auto aligned = inferStructurallyEquivalentStatePairs(
      model0, model1, AlignedSignals{});

  EXPECT_EQ(aligned.names.size(), 3u);
}

TEST_F(SequentialEquivalenceStrategyTests,
       StructuralStateInvariantReturnsEmptyWhenOneSideHasNoState) {
  SequentialDesignModel model0;
  SequentialDesignModel model1;
  model1.stateBits = {makeSignalKey("s1")};
  model1.inputVarByKey.emplace(model1.stateBits.front(), 2);
  model1.nextStateExprByStateKey.emplace(model1.stateBits.front(), BoolExpr::createFalse());

  const auto aligned = inferStructurallyEquivalentStatePairs(
      model0, model1, AlignedSignals{});

  EXPECT_TRUE(aligned.names.empty());
}

TEST_F(SequentialEquivalenceStrategyTests,
       StructuralStateInvariantReturnsEmptyWhenBothSidesHaveNoState) {
  SequentialDesignModel model0;
  SequentialDesignModel model1;

  const auto aligned = inferStructurallyEquivalentStatePairs(
      model0, model1, AlignedSignals{});

  EXPECT_TRUE(aligned.names.empty());
}

TEST_F(SequentialEquivalenceStrategyTests,
       StructuralStateInvariantHandlesNullNextStateExpressions) {
  const SignalKey null0 = makeSignalKey("null0");
  const SignalKey false0 = makeSignalKey("false0");
  const SignalKey null1 = makeSignalKey("null1");
  const SignalKey false1 = makeSignalKey("false1");

  SequentialDesignModel model0;
  model0.stateBits = {null0, false0};
  model0.inputVarByKey.emplace(null0, 2);
  model0.inputVarByKey.emplace(false0, 3);
  model0.nextStateExprByStateKey.emplace(null0, nullptr);
  model0.nextStateExprByStateKey.emplace(false0, BoolExpr::createFalse());

  SequentialDesignModel model1;
  model1.stateBits = {false1, null1};
  model1.inputVarByKey.emplace(false1, 4);
  model1.inputVarByKey.emplace(null1, 5);
  model1.nextStateExprByStateKey.emplace(false1, BoolExpr::createFalse());
  model1.nextStateExprByStateKey.emplace(null1, nullptr);

  const auto aligned = inferStructurallyEquivalentStatePairs(
      model0, model1, AlignedSignals{});

  EXPECT_EQ(aligned.names.size(), 2u);
}

TEST_F(SequentialEquivalenceStrategyTests,
       SequentialDesignModelExtractSupportsGenericComplementedStateNames) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* primitives =
      NLLibrary::create(db, NLLibrary::Type::Primitives, NLName("prims"));
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* model = createNamedComplementSequentialModel(
      primitives, "DFF_STATE_STATEN", "STATE", "STATEN");
  auto* top = createSequentialOutputPairTop(
      library, "top", model, "STATE", "STATEN");

  const auto extracted = SequentialDesignModel::extract(top);

  EXPECT_FALSE(extracted.hasUnsupportedFeatures());
  ASSERT_EQ(extracted.complementedStateRelations.size(), 1u);
  EXPECT_EQ(
      extracted.complementedStateRelations.front().primaryKey,
      extracted.stateBits.front());
}

TEST_F(SequentialEquivalenceStrategyTests,
       SequentialDesignModelExtractTracksVectorStateBitsPerOutputTerm) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* primitives =
      NLLibrary::create(db, NLLibrary::Type::Primitives, NLName("prims"));
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* model = createBusSequentialModel(primitives, "DFF_BUS");
  auto* top = createBusSequentialTop(library, "top", model);

  const auto extracted = SequentialDesignModel::extract(top);

  EXPECT_FALSE(extracted.hasUnsupportedFeatures());
  ASSERT_EQ(extracted.stateBits.size(), 2u);

  const auto in0Key = findKeyByDisplayName(extracted, "in[0]");
  const auto in1Key = findKeyByDisplayName(extracted, "in[1]");
  const auto q0Key = findKeyByDisplayName(extracted, "ff0.Q[0]");
  const auto q1Key = findKeyByDisplayName(extracted, "ff0.Q[1]");

  auto* q0Expr = extracted.nextStateExprByStateKey.at(q0Key);
  auto* q1Expr = extracted.nextStateExprByStateKey.at(q1Key);
  EXPECT_TRUE(q0Expr->evaluate({{extracted.inputVarByKey.at(in0Key), true},
                                {extracted.inputVarByKey.at(in1Key), false}}));
  EXPECT_FALSE(q1Expr->evaluate({{extracted.inputVarByKey.at(in0Key), true},
                                 {extracted.inputVarByKey.at(in1Key), false}}));
  EXPECT_FALSE(q0Expr->evaluate({{extracted.inputVarByKey.at(in0Key), false},
                                 {extracted.inputVarByKey.at(in1Key), true}}));
  EXPECT_TRUE(q1Expr->evaluate({{extracted.inputVarByKey.at(in0Key), false},
                                {extracted.inputVarByKey.at(in1Key), true}}));
}

TEST_F(SequentialEquivalenceStrategyTests,
       SequentialDesignModelExtractModelsStructuredMemoryWithoutBoundaryFallback) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* primitives =
      NLLibrary::create(db, NLLibrary::Type::Primitives, NLName("prims"));
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* model = createSinglePortMemoryModel(primitives, "MEM1P");
  auto* top = createSinglePortMemoryTop(library, "top", model);

  const auto extracted = SequentialDesignModel::extract(top);

  auto hasBoundaryRoleName = [&](const std::vector<SignalKey>& keys,
                                 const std::string& prefix) {
    return std::any_of(keys.begin(), keys.end(), [&](const SignalKey& key) {
      const auto it = extracted.displayNameByKey.find(key);
      return it != extracted.displayNameByKey.end() &&
             it->second.rfind(prefix, 0) == 0;
    });
  };

  EXPECT_FALSE(extracted.hasUnsupportedFeatures());
  EXPECT_TRUE(extracted.abstractedSequentialBoundaries.empty());
  EXPECT_FALSE(hasBoundaryRoleName(extracted.internalBoundaryInputKeys, "mem0."));
  EXPECT_FALSE(hasBoundaryRoleName(extracted.internalBoundaryOutputKeys, "mem0."));
  EXPECT_FALSE(extracted.stateBits.empty());
  EXPECT_FALSE(extracted.nextStateExprByStateKey.empty());
}

TEST_F(SequentialEquivalenceStrategyTests,
       SequentialDesignModelExtractModelsImportedLibertyMemoryWithoutOpaqueBoundaryTerms) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* primitives =
      NLLibrary::create(db, NLLibrary::Type::Primitives, NLName("prims"));
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* model = loadLibertyMemoryModel(
      primitives, "fakeram45_64x32.lib", "fakeram45_64x32");
  auto* top = createMirroredInstanceTop(library, "top", model);

  const auto extracted = SequentialDesignModel::extract(top);

  auto hasBoundaryRoleName = [&](const std::vector<SignalKey>& keys,
                                 const std::string& prefix) {
    return std::any_of(keys.begin(), keys.end(), [&](const SignalKey& key) {
      const auto it = extracted.displayNameByKey.find(key);
      return it != extracted.displayNameByKey.end() &&
             it->second.rfind(prefix, 0) == 0;
    });
  };

  EXPECT_FALSE(extracted.hasUnsupportedFeatures());
  EXPECT_TRUE(extracted.abstractedSequentialBoundaries.empty());
  EXPECT_FALSE(hasBoundaryRoleName(extracted.internalBoundaryInputKeys, "mem0."));
  EXPECT_FALSE(hasBoundaryRoleName(extracted.internalBoundaryOutputKeys, "mem0."));
  EXPECT_FALSE(extracted.stateBits.empty());
  EXPECT_FALSE(extracted.nextStateExprByStateKey.empty());
}

TEST_F(
    SequentialEquivalenceStrategyTests,
    StructuredMemoryDependencyBatchBuildsRealCva6PerfCounterReadAddressRoot) {
  const auto context = resolveCva6SourceContextForSecTests();
  if (!context.has_value()) {
    GTEST_SKIP()
        << "CVA6 source tree is not available for the real-source SEC memory regression test";
  }

  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* top = loadRealCva6PerfCountersTargetConfigTopForSecTests(
      library,
      *context,
      "real_cva6_perf_counters_module_with_target_config_sec_memory_probe");

  detail::ScopedDnlContextForTest dnlContext(top);
  auto* dnl = dnlContext.dnl();
  ASSERT_NE(dnl, nullptr);
  auto requestedTermID = detail::findTermByDisplayNameForTest(
      dnl, "dut.generic_counter_q_mem.RADDR[18]");
  if (!requestedTermID.has_value()) {
    // Different CVA6 target configs can infer a narrower generated memory
    // address port. The dependency regression only needs a real RADDR bit, not
    // a specific width-dependent index.
    requestedTermID = detail::findFirstTermByDisplayPrefixForTest(
        dnl, "dut.generic_counter_q_mem.RADDR[");
  }
  ASSERT_TRUE(requestedTermID.has_value());

  const auto probe =
      detail::probeRequestedBuilderOutputForTest(dnl, *requestedTermID);
  std::ostringstream normalizationChain;
  for (size_t index = 0; index < probe.normalizationChain.size(); ++index) {
    if (index != 0) {
      normalizationChain << " -> ";
    }
    normalizationChain << probe.normalizationChain[index];
  }
  std::ostringstream supportTerms;
  for (size_t index = 0; index < probe.rootSupportTerms.size(); ++index) {
    if (index != 0) {
      supportTerms << " | ";
    }
    supportTerms << probe.rootSupportTerms[index];
  }
  std::ostringstream combinationalInputs;
  for (size_t index = 0; index < probe.rootCombinationalInputs.size(); ++index) {
    if (index != 0) {
      combinationalInputs << " | ";
    }
    combinationalInputs << probe.rootCombinationalInputs[index];
  }
  std::ostringstream driverSpine;
  for (size_t index = 0; index < probe.driverSpine.size(); ++index) {
    if (index != 0) {
      driverSpine << " -> ";
    }
    driverSpine << probe.driverSpine[index];
  }

  ASSERT_TRUE(probe.normalizedRoot.has_value())
      << "normalization chain: " << normalizationChain.str();
  EXPECT_TRUE(probe.hasBuiltExpr)
      << "normalized root " << probe.normalizedRootName
      << " model=" << probe.normalizedRootModelName
      << " did not yield a valid clause-builder expression; support terms: "
      << supportTerms.str()
      << "; combinational inputs: " << combinationalInputs.str()
      << "; driver spine: " << driverSpine.str();
  EXPECT_FALSE(probe.hasSkip)
      << "normalized root " << probe.normalizedRootName
      << " model=" << probe.normalizedRootModelName
      << " was skipped: " << probe.skipDetail
      << "; support terms: " << supportTerms.str()
      << "; combinational inputs: " << combinationalInputs.str()
      << "; driver spine: " << driverSpine.str();
}

TEST_F(
    SequentialEquivalenceStrategyTests,
    StructuredMemoryDependencyBatchBuildsRealCva6TopPerfCounterWriteEnableRoot) {
  const auto context = resolveCva6SourceContextForSecTests();
  if (!context.has_value()) {
    GTEST_SKIP()
        << "CVA6 source tree is not available for the real-source SEC memory regression test";
  }

  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  const auto paths = buildExpandedCva6SlangArgsForSecTests(*context, "cva6");
  auto* top = loadSystemVerilogTopFromPaths(library, "cva6", paths);

  detail::ScopedDnlContextForTest dnlContext(top);
  auto* dnl = dnlContext.dnl();
  ASSERT_NE(dnl, nullptr);
  const auto requestedTermID = detail::findTermByDisplayNameForTest(
      dnl, "cva6_gen_perf_counter_perf_counters_i.generic_counter_q_mem.WE[1]");
  ASSERT_TRUE(requestedTermID.has_value());

  const auto skippedReportPath =
      std::filesystem::current_path() / "skipped_no_driver_pos.txt";
  std::filesystem::remove(skippedReportPath);
  const bool previousReportSkippedPOs =
      KEPLER_FORMAL::Config::getReportSkippedPOs();
  KEPLER_FORMAL::Config::setReportSkippedPOs(true);
  const auto probe =
      detail::probeRequestedBuilderOutputForTest(dnl, *requestedTermID);
  KEPLER_FORMAL::Config::setReportSkippedPOs(previousReportSkippedPOs);
  std::ostringstream normalizationChain;
  for (size_t index = 0; index < probe.normalizationChain.size(); ++index) {
    if (index != 0) {
      normalizationChain << " -> ";
    }
    normalizationChain << probe.normalizationChain[index];
  }
  std::ostringstream supportTerms;
  for (size_t index = 0; index < probe.rootSupportTerms.size(); ++index) {
    if (index != 0) {
      supportTerms << " | ";
    }
    supportTerms << probe.rootSupportTerms[index];
  }
  std::ostringstream combinationalInputs;
  for (size_t index = 0; index < probe.rootCombinationalInputs.size(); ++index) {
    if (index != 0) {
      combinationalInputs << " | ";
    }
    combinationalInputs << probe.rootCombinationalInputs[index];
  }
  std::ostringstream driverSpine;
  for (size_t index = 0; index < probe.driverSpine.size(); ++index) {
    if (index != 0) {
      driverSpine << " -> ";
    }
    driverSpine << probe.driverSpine[index];
  }
  std::string skippedReport;
  if (std::ifstream skippedReportFile(skippedReportPath);
      skippedReportFile.good()) {
    std::ostringstream report;
    report << skippedReportFile.rdbuf();
    skippedReport = report.str();
  }

  ASSERT_TRUE(probe.normalizedRoot.has_value())
      << "normalization chain: " << normalizationChain.str();
  EXPECT_TRUE(probe.hasBuiltExpr)
      << "normalized root " << probe.normalizedRootName
      << " model=" << probe.normalizedRootModelName
      << " did not yield a valid clause-builder expression; support terms: "
      << supportTerms.str()
      << "; combinational inputs: " << combinationalInputs.str()
      << "; driver spine: " << driverSpine.str()
      << "; skipped report: " << skippedReport;
  EXPECT_FALSE(probe.hasSkip)
      << "normalized root " << probe.normalizedRootName
      << " model=" << probe.normalizedRootModelName
      << " was skipped: " << probe.skipDetail
      << "; support terms: " << supportTerms.str()
      << "; combinational inputs: " << combinationalInputs.str()
      << "; driver spine: " << driverSpine.str()
      << "; skipped report: " << skippedReport;
}

TEST_F(
    SequentialEquivalenceStrategyTests,
    StructuredMemoryDependencyBatchBuildsRealCva6TopPerfCounterWriteDataSliceRoot) {
  const auto context = resolveCva6SourceContextForSecTests();
  if (!context.has_value()) {
    GTEST_SKIP()
        << "CVA6 source tree is not available for the real-source SEC memory regression test";
  }

  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  const auto paths = buildExpandedCva6SlangArgsForSecTests(*context, "cva6");
  auto* top = loadSystemVerilogTopFromPaths(library, "cva6", paths);

  detail::ScopedDnlContextForTest dnlContext(top);
  auto* dnl = dnlContext.dnl();
  ASSERT_NE(dnl, nullptr);
  auto requestedTermID = detail::findTermByDisplayNameForTest(
      dnl,
      "cva6_gen_perf_counter_perf_counters_i.generic_counter_q_mem.WDATA[384]");
  if (!requestedTermID.has_value()) {
    // Keep the probe tied to the generated WDATA port while allowing the local
    // CVA6 config to choose a smaller packed memory width.
    requestedTermID = detail::findFirstTermByDisplayPrefixForTest(
        dnl,
        "cva6_gen_perf_counter_perf_counters_i.generic_counter_q_mem.WDATA[");
  }
  ASSERT_TRUE(requestedTermID.has_value());

  const auto skippedNoDriverReportPath =
      std::filesystem::current_path() / "skipped_no_driver_pos.txt";
  const auto skippedLogicalLoopReportPath =
      std::filesystem::current_path() / "skipped_logical_loop_pos.txt";
  std::filesystem::remove(skippedNoDriverReportPath);
  std::filesystem::remove(skippedLogicalLoopReportPath);
  const bool previousReportSkippedPOs =
      KEPLER_FORMAL::Config::getReportSkippedPOs();
  KEPLER_FORMAL::Config::setReportSkippedPOs(true);
  const auto probe =
      detail::probeRequestedBuilderOutputForTest(dnl, *requestedTermID);
  KEPLER_FORMAL::Config::setReportSkippedPOs(previousReportSkippedPOs);
  std::ostringstream normalizationChain;
  for (size_t index = 0; index < probe.normalizationChain.size(); ++index) {
    if (index != 0) {
      normalizationChain << " -> ";
    }
    normalizationChain << probe.normalizationChain[index];
  }
  std::ostringstream supportTerms;
  for (size_t index = 0; index < probe.rootSupportTerms.size(); ++index) {
    if (index != 0) {
      supportTerms << " | ";
    }
    supportTerms << probe.rootSupportTerms[index];
  }
  std::ostringstream combinationalInputs;
  for (size_t index = 0; index < probe.rootCombinationalInputs.size(); ++index) {
    if (index != 0) {
      combinationalInputs << " | ";
    }
    combinationalInputs << probe.rootCombinationalInputs[index];
  }
  std::ostringstream driverSpine;
  for (size_t index = 0; index < probe.driverSpine.size(); ++index) {
    if (index != 0) {
      driverSpine << " -> ";
    }
    driverSpine << probe.driverSpine[index];
  }
  auto readReportFile = [](const std::filesystem::path& path) {
    std::string contents;
    if (std::ifstream file(path); file.good()) {
      std::ostringstream buffer;
      buffer << file.rdbuf();
      contents = buffer.str();
    }
    return contents;
  };
  const auto skippedNoDriverReport = readReportFile(skippedNoDriverReportPath);
  const auto skippedLogicalLoopReport =
      readReportFile(skippedLogicalLoopReportPath);

  ASSERT_TRUE(probe.normalizedRoot.has_value())
      << "normalization chain: " << normalizationChain.str();
  EXPECT_TRUE(probe.hasBuiltExpr)
      << "normalized root " << probe.normalizedRootName
      << " model=" << probe.normalizedRootModelName
      << " did not yield a valid clause-builder expression; support terms: "
      << supportTerms.str()
      << "; combinational inputs: " << combinationalInputs.str()
      << "; driver spine: " << driverSpine.str()
      << "; skipped no-driver report: " << skippedNoDriverReport
      << "; skipped logical-loop report: " << skippedLogicalLoopReport;
  EXPECT_FALSE(probe.hasSkip)
      << "normalized root " << probe.normalizedRootName
      << " model=" << probe.normalizedRootModelName
      << " was skipped: " << probe.skipDetail
      << "; support terms: " << supportTerms.str()
      << "; combinational inputs: " << combinationalInputs.str()
      << "; driver spine: " << driverSpine.str()
      << "; skipped no-driver report: " << skippedNoDriverReport
      << "; skipped logical-loop report: " << skippedLogicalLoopReport;
}

TEST_F(
    SequentialEquivalenceStrategyTests,
    SequentialDesignModelExtractModelsRealCva6PerfCountersTargetConfigMemoryWithoutBoundaryFallback) {
  const auto context = resolveCva6SourceContextForSecTests();
  if (!context.has_value()) {
    GTEST_SKIP()
        << "CVA6 source tree is not available for the real-source SEC memory regression test";
  }

  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* top = loadRealCva6PerfCountersTargetConfigTopForSecTests(
      library,
      *context,
      "real_cva6_perf_counters_module_with_target_config_sec_memory_supported");

  const auto extracted = SequentialDesignModel::extract(top);
  auto hasBoundaryRoleName = [&](const std::vector<SignalKey>& keys,
                                 const std::string& needle) {
    return std::any_of(keys.begin(), keys.end(), [&](const SignalKey& key) {
      const auto it = extracted.displayNameByKey.find(key);
      return it != extracted.displayNameByKey.end() &&
             it->second.find(needle) != std::string::npos;
    });
  };

  // Guard the exact configured CVA6 perf-counter memory path that fails in
  // full SEC runs: the inferred memory should stay inside the sequential model
  // instead of leaking back out as generic boundary terms.
  EXPECT_FALSE(extracted.hasUnsupportedFeatures());
  EXPECT_TRUE(extracted.abstractedSequentialBoundaries.empty());
  EXPECT_FALSE(
      hasBoundaryRoleName(extracted.internalBoundaryInputKeys, "generic_counter_q_mem"));
  EXPECT_FALSE(
      hasBoundaryRoleName(extracted.internalBoundaryOutputKeys, "generic_counter_q_mem"));
}

TEST_F(SequentialEquivalenceStrategyTests,
       SequentialDesignModelExtractModelsInferredMemoryWithConstantFalseCommitGuard) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* top = loadSystemVerilogTopFromSource(
      library,
      "qd_next_indexed_commit_constant_false_guard_skip_supported",
      R"(module qd_next_indexed_commit_constant_false_guard_skip_supported(
  input  logic       clk_i,
  input  logic [1:0] addr_i,
  input  logic [7:0] data_i,
  output logic [7:0] data_o
);
  logic [7:0] mem_q [0:3];
  logic [7:0] mem_d [0:3];
  logic [7:0] mem_next [0:3];

  always_comb begin
    mem_d = mem_q;
    mem_d[addr_i] = data_i;
  end

  always_comb begin
    for (int i = 0; i < 4; i++) begin
      mem_next[i] = mem_d[i];
      if (i == 0) begin
        mem_next[i] = mem_q[i];
      end
    end
  end

  always_ff @(posedge clk_i) begin
    mem_q <= mem_next;
  end

  assign data_o = mem_q[addr_i];
endmodule
)");

  const auto extracted = SequentialDesignModel::extract(top);

  auto hasBoundaryRoleName = [&](const std::vector<SignalKey>& keys,
                                 const std::string& prefix) {
    return std::any_of(keys.begin(), keys.end(), [&](const SignalKey& key) {
      const auto it = extracted.displayNameByKey.find(key);
      return it != extracted.displayNameByKey.end() &&
             it->second.rfind(prefix, 0) == 0;
    });
  };

  EXPECT_FALSE(extracted.hasUnsupportedFeatures());
  EXPECT_TRUE(extracted.abstractedSequentialBoundaries.empty());
  EXPECT_FALSE(hasBoundaryRoleName(extracted.internalBoundaryInputKeys, "mem_q"));
  EXPECT_FALSE(hasBoundaryRoleName(extracted.internalBoundaryOutputKeys, "mem_q"));
  EXPECT_FALSE(extracted.stateBits.empty());
  EXPECT_FALSE(extracted.nextStateExprByStateKey.empty());
  EXPECT_TRUE(extracted.skippedObservedOutputs.empty());
}

TEST_F(SequentialEquivalenceStrategyTests,
       SequentialDesignModelExtractReportsStructuredMemoryDependencyNameForUndrivenAddressBit) {
  // Regression guard for CVA6 diag runs: structured-memory dependency
  // materialization may skip an internal root, and the skip diagnostic must
  // describe that root without using stale DNL terminals after clause building.
  ScopedEnvVar secDiag("KEPLER_SEC_DIAG", "1");
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* top = loadSystemVerilogTopFromSource(
      library,
      "structured_memory_undriven_address_dependency",
      R"(module structured_memory_undriven_address_dependency(
  input  logic       clk_i,
  input  logic       we_i,
  input  logic       addr_i,
  input  logic [7:0] data_i,
  output logic [7:0] data_o
);
  logic [7:0] mem_q [0:3];
  logic       bad_addr_bit;

  always_ff @(posedge clk_i) begin
    if (we_i) begin
      mem_q[{1'b0, addr_i}] <= data_i;
    end
  end

  assign data_o = mem_q[{bad_addr_bit, addr_i}];
endmodule
)");

  const auto extracted = SequentialDesignModel::extract(top);

  EXPECT_FALSE(extracted.hasUnsupportedFeatures());
  EXPECT_FALSE(extracted.skippedObservedOutputs.empty());
  const auto hasStructuredMemorySkipDetail = std::any_of(
      extracted.connectivitySkipInfoByKey.begin(),
      extracted.connectivitySkipInfoByKey.end(),
      [](const auto& entry) {
        return entry.second.detail.find("Structured memory dependency") !=
                   std::string::npos &&
               entry.second.detail.find("mem_q_mem.RADDR[1]") !=
                   std::string::npos;
      });
  EXPECT_TRUE(hasStructuredMemorySkipDetail);
}

TEST_F(SequentialEquivalenceStrategyTests,
       SequentialDesignModelExtractSkipsUndrivenMemoryWriteEnablePort) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* primitives =
      NLLibrary::create(db, NLLibrary::Type::Primitives, NLName("prims"));
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* memoryModel = createSinglePortMemoryModel(primitives, "MEM_DISABLED_WE");
  auto* top = SNLDesign::create(
      library,
      SNLDesign::Type::Standard,
      NLName("structured_memory_undriven_write_enable_port"));
  auto* topClock =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("clk"));
  auto* topChipEnable =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("ce"));
  auto* topAddress =
      SNLBusTerm::create(top, SNLTerm::Direction::Input, 1, 0, NLName("addr"));
  auto* topWriteData =
      SNLBusTerm::create(top, SNLTerm::Direction::Input, 3, 0, NLName("wdata"));
  auto* topWriteMask =
      SNLBusTerm::create(top, SNLTerm::Direction::Input, 3, 0, NLName("wmask"));
  auto* topOut =
      SNLBusTerm::create(top, SNLTerm::Direction::Output, 3, 0, NLName("out"));

  auto* memory = SNLInstance::create(top, memoryModel, NLName("mem0"));
  auto* clockNet = SNLScalarNet::create(top, NLName("clk_net"));
  auto* chipEnableNet = SNLScalarNet::create(top, NLName("ce_net"));
  auto* undrivenWriteEnableNet = SNLScalarNet::create(top, NLName("we_net"));
  auto* addressNet = SNLBusNet::create(top, 1, 0, NLName("addr_net"));
  auto* writeDataNet = SNLBusNet::create(top, 3, 0, NLName("wdata_net"));
  auto* writeMaskNet = SNLBusNet::create(top, 3, 0, NLName("wmask_net"));
  auto* outNet = SNLBusNet::create(top, 3, 0, NLName("out_net"));

  topClock->setNet(clockNet);
  topChipEnable->setNet(chipEnableNet);
  memory->getInstTerm(memoryModel->getScalarTerm(NLName("CLK")))->setNet(clockNet);
  memory->getInstTerm(memoryModel->getScalarTerm(NLName("CE")))->setNet(chipEnableNet);
  memory->getInstTerm(memoryModel->getScalarTerm(NLName("WE")))
      ->setNet(undrivenWriteEnableNet);

  auto* modelAddress = memoryModel->getBusTerm(NLName("ADDR"));
  auto* modelWriteData = memoryModel->getBusTerm(NLName("WDATA"));
  auto* modelWriteMask = memoryModel->getBusTerm(NLName("WMASK"));
  auto* modelReadData = memoryModel->getBusTerm(NLName("RDATA"));
  for (int bit = 0; bit <= 1; ++bit) {
    topAddress->getBit(bit)->setNet(addressNet->getBit(bit));
    memory->getInstTerm(modelAddress->getBit(bit))->setNet(addressNet->getBit(bit));
  }
  for (int bit = 0; bit <= 3; ++bit) {
    topWriteData->getBit(bit)->setNet(writeDataNet->getBit(bit));
    topWriteMask->getBit(bit)->setNet(writeMaskNet->getBit(bit));
    topOut->getBit(bit)->setNet(outNet->getBit(bit));
    memory->getInstTerm(modelWriteData->getBit(bit))->setNet(writeDataNet->getBit(bit));
    memory->getInstTerm(modelWriteMask->getBit(bit))->setNet(writeMaskNet->getBit(bit));
    memory->getInstTerm(modelReadData->getBit(bit))->setNet(outNet->getBit(bit));
  }

  const auto extracted = SequentialDesignModel::extract(top);

  auto findInputVarContaining = [&](std::string_view needle) {
    std::optional<size_t> varID;
    for (const auto& key : extracted.environmentInputs) {
      const auto nameIt = extracted.displayNameByKey.find(key);
      const auto varIt = extracted.inputVarByKey.find(key);
      if (nameIt == extracted.displayNameByKey.end() ||
          varIt == extracted.inputVarByKey.end()) {
        continue;
      }
      if (nameIt->second.find(needle) != std::string::npos) {
        varID = varIt->second;
        break;
      }
    }
    return varID;
  };
  const auto disabledWriteDataVar = findInputVarContaining("wdata[0]");

  EXPECT_FALSE(extracted.hasUnsupportedFeatures());
  if (disabledWriteDataVar.has_value()) {
    for (const auto& [_, nextStateExpr] : extracted.nextStateExprByStateKey) {
      EXPECT_EQ(nextStateExpr->getSupportVars().count(*disabledWriteDataVar), 0u)
          << "An undriven write-enable port must not pull its write-data cone "
             "into the modeled memory transition";
    }
  }
}

TEST_F(SequentialEquivalenceStrategyTests,
       SequentialDesignModelExtractSkipsWholeMemoryForUndrivenWriteData) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* primitives =
      NLLibrary::create(db, NLLibrary::Type::Primitives, NLName("prims"));
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* memoryModel = createSinglePortMemoryModel(primitives, "MEM_FLOAT_WDATA");
  auto* top = createSinglePortMemoryTop(
      library, "structured_memory_undriven_write_data", memoryModel, 0);

  const auto extracted = SequentialDesignModel::extract(top);

  EXPECT_FALSE(extracted.hasUnsupportedFeatures());
  EXPECT_FALSE(extracted.connectivitySkipInfoByKey.empty());
  EXPECT_FALSE(extracted.skippedObservedOutputs.empty());
  EXPECT_TRUE(std::any_of(
      extracted.connectivitySkipInfoByKey.begin(),
      extracted.connectivitySkipInfoByKey.end(),
      [](const auto& entry) {
        return entry.second.detail.find("Structured memory dependency") !=
               std::string::npos;
      }));
}

TEST_F(SequentialEquivalenceStrategyTests,
       SequentialDesignModelExtractSkipsWholeMemoryForUndrivenReset) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* primitives =
      NLLibrary::create(db, NLLibrary::Type::Primitives, NLName("prims"));
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* memoryModel =
      createSinglePortMemoryModel(primitives, "MEM_FLOAT_RST", true);
  auto* top = createSinglePortMemoryTop(
      library,
      "structured_memory_undriven_reset",
      memoryModel,
      std::nullopt,
      true);

  const auto extracted = SequentialDesignModel::extract(top);

  EXPECT_FALSE(extracted.hasUnsupportedFeatures());
  EXPECT_FALSE(extracted.connectivitySkipInfoByKey.empty());
  EXPECT_FALSE(extracted.skippedObservedOutputs.empty());
  EXPECT_TRUE(std::any_of(
      extracted.connectivitySkipInfoByKey.begin(),
      extracted.connectivitySkipInfoByKey.end(),
      [](const auto& entry) {
        return entry.second.detail.find("Structured memory dependency") !=
               std::string::npos;
      }));
}

TEST_F(SequentialEquivalenceStrategyTests,
       SequentialDesignModelExtractModelsInferredStructMemoryWithLogicalOrCommitGuard) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* top = loadSystemVerilogTopFromSource(
      library,
      "qd_next_local_commit_logical_or_supported",
      R"(module qd_next_local_commit_logical_or_supported(
  input  logic       clk_i,
  input  logic [1:0] addr_i,
  input  logic [1:0] mode_i,
  input  logic [1:0] access_i,
  input  logic [3:0] payload_i,
  output logic [7:0] data_o
);
  typedef struct packed {
    logic [1:0] mode;
    logic [1:0] access;
    logic [3:0] payload;
  } entry_t;

  entry_t mem_q [0:3];
  entry_t mem_d [0:3];
  entry_t mem_next [0:3];

  always_comb begin
    mem_d = mem_q;
    mem_d[addr_i].mode = mode_i;
    mem_d[addr_i].access = access_i;
    mem_d[addr_i].payload = payload_i;
  end

  always_comb begin
    for (int i = 0; i < 4; i++) begin
      mem_next[i] = mem_d[i];
      if ((mem_d[i].mode == 2'b11) || (mem_d[i].access == 2'b01)) begin
        mem_next[i] = mem_q[i];
      end
    end
  end

  always_ff @(posedge clk_i) begin
    mem_q <= mem_next;
  end

  assign data_o = {mem_q[addr_i].mode, mem_q[addr_i].access, mem_q[addr_i].payload};
endmodule
)");

  const auto extracted = SequentialDesignModel::extract(top);

  auto hasBoundaryRoleName = [&](const std::vector<SignalKey>& keys,
                                 const std::string& prefix) {
    return std::any_of(keys.begin(), keys.end(), [&](const SignalKey& key) {
      const auto it = extracted.displayNameByKey.find(key);
      return it != extracted.displayNameByKey.end() &&
             it->second.rfind(prefix, 0) == 0;
    });
  };

  EXPECT_FALSE(extracted.hasUnsupportedFeatures());
  EXPECT_TRUE(extracted.abstractedSequentialBoundaries.empty());
  EXPECT_FALSE(hasBoundaryRoleName(extracted.internalBoundaryInputKeys, "mem_q"));
  EXPECT_FALSE(hasBoundaryRoleName(extracted.internalBoundaryOutputKeys, "mem_q"));
  EXPECT_FALSE(extracted.stateBits.empty());
  EXPECT_FALSE(extracted.nextStateExprByStateKey.empty());
  EXPECT_TRUE(extracted.skippedObservedOutputs.empty());
}

TEST_F(SequentialEquivalenceStrategyTests,
       SequentialDesignModelExtractSkipsCombinationalInstancesWithoutStateOutputs) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* primitives =
      NLLibrary::create(db, NLLibrary::Type::Primitives, NLName("prims"));
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* invModel = createInvModel(primitives);
  auto* top = createCombinationalInvTop(library, "top", invModel);

  const auto extracted = SequentialDesignModel::extract(top);

  EXPECT_FALSE(extracted.hasUnsupportedFeatures());
  EXPECT_TRUE(extracted.stateBits.empty());
  EXPECT_EQ(extracted.observedOutputs.size(), 1u);
}

TEST_F(SequentialEquivalenceStrategyTests,
       SequentialDesignModelExtractPropagatesNoDriverSkipsToStateAndOutputs) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* top = createPartialCoverageNoDriverTop(library, "top");

  const auto extracted = SequentialDesignModel::extract(top);

  EXPECT_FALSE(extracted.hasUnsupportedFeatures());
  EXPECT_EQ(extracted.totalObservedOutputCount(), 2u);
  EXPECT_EQ(extracted.coveredObservedOutputCount(), 1u);
  EXPECT_EQ(extracted.skippedObservedOutputs.size(), 1u);
  EXPECT_EQ(extracted.skippedStateBits.size(), 1u);
  EXPECT_NE(
      std::find(
          extracted.observedOutputs.begin(),
          extracted.observedOutputs.end(),
          findKeyByDisplayName(extracted, "good[0]")),
      extracted.observedOutputs.end());
  EXPECT_EQ(
      extracted.skippedObservedOutputs.front(),
      findKeyByDisplayName(extracted, "bad[0]"));
  const auto badKey = findKeyByDisplayName(extracted, "bad[0]");
  const auto stateKey = findKeyByDisplayName(extracted, "ff0.Q[0]");
  ASSERT_NE(extracted.connectivitySkipInfoByKey.find(badKey),
            extracted.connectivitySkipInfoByKey.end());
  ASSERT_NE(extracted.connectivitySkipInfoByKey.find(stateKey),
            extracted.connectivitySkipInfoByKey.end());
  EXPECT_EQ(
      extracted.connectivitySkipInfoByKey.at(stateKey).origin,
      ConnectivitySkipOrigin::NoDriver);
}

TEST_F(SequentialEquivalenceStrategyTests,
       SequentialDesignModelExtractPropagatesMultiDriverSkipsToStateAndOutputs) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* primitives =
      NLLibrary::create(db, NLLibrary::Type::Primitives, NLName("prims"));
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* invModel = createInvModel(primitives);
  auto* top = createPartialCoverageMultiDriverTop(library, "top", invModel);

  const auto extracted = SequentialDesignModel::extract(top);

  EXPECT_FALSE(extracted.hasUnsupportedFeatures());
  EXPECT_EQ(extracted.totalObservedOutputCount(), 2u);
  EXPECT_EQ(extracted.coveredObservedOutputCount(), 1u);
  EXPECT_EQ(extracted.skippedObservedOutputs.size(), 1u);
  EXPECT_EQ(extracted.skippedStateBits.size(), 1u);
  const auto badKey = findKeyByDisplayName(extracted, "bad[0]");
  const auto stateKey = findKeyByDisplayName(extracted, "ff0.Q[0]");
  ASSERT_NE(extracted.connectivitySkipInfoByKey.find(badKey),
            extracted.connectivitySkipInfoByKey.end());
  ASSERT_NE(extracted.connectivitySkipInfoByKey.find(stateKey),
            extracted.connectivitySkipInfoByKey.end());
  EXPECT_EQ(
      extracted.connectivitySkipInfoByKey.at(stateKey).origin,
      ConnectivitySkipOrigin::MultiDriver);
}

TEST_F(SequentialEquivalenceStrategyTests,
       SequentialDesignModelExtractPropagatesLogicalLoopSkipsToStateAndOutputs) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* top = createPartialCoverageLogicalLoopTop(library, "top");

  const auto extracted = SequentialDesignModel::extract(top);

  EXPECT_FALSE(extracted.hasUnsupportedFeatures());
  EXPECT_EQ(extracted.totalObservedOutputCount(), 2u);
  EXPECT_EQ(extracted.coveredObservedOutputCount(), 1u);
  EXPECT_EQ(extracted.skippedObservedOutputs.size(), 1u);
  EXPECT_EQ(extracted.skippedStateBits.size(), 1u);
  const auto badKey = findKeyByDisplayName(extracted, "bad[0]");
  const auto stateKey = findKeyByDisplayName(extracted, "ff0.Q[0]");
  ASSERT_NE(extracted.connectivitySkipInfoByKey.find(badKey),
            extracted.connectivitySkipInfoByKey.end());
  ASSERT_NE(extracted.connectivitySkipInfoByKey.find(stateKey),
            extracted.connectivitySkipInfoByKey.end());
  EXPECT_EQ(
      extracted.connectivitySkipInfoByKey.at(stateKey).origin,
      ConnectivitySkipOrigin::LogicalLoop);
}

TEST_F(SequentialEquivalenceStrategyTests,
       SequentialDesignModelExtractSupportsSetHighInitialState) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* primitives =
      NLLibrary::create(db, NLLibrary::Type::Primitives, NLName("prims"));
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* model = createSetOnlySequentialModel(primitives, "DFF_SET");
  auto* top = createSetOnlySequentialTop(library, "top", model);

  const auto extracted = SequentialDesignModel::extract(top);

  EXPECT_FALSE(extracted.hasUnsupportedFeatures());
  ASSERT_EQ(extracted.stateBits.size(), 1u);
  EXPECT_TRUE(extracted.initialStateValueByKey.at(extracted.stateBits.front()));
}

TEST_F(SequentialEquivalenceStrategyTests,
       SequentialDesignModelExtractPreservesSetHighControlSemantics) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* primitives =
      NLLibrary::create(db, NLLibrary::Type::Primitives, NLName("prims"));
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* model = createSetOnlySequentialModel(primitives, "DFF_SET");
  auto* top = createSetOnlySequentialTop(library, "top", model);

  const auto extracted = SequentialDesignModel::extract(top);
  const auto stateKey = extracted.stateBits.front();
  const auto inKey = findKeyByDisplayName(extracted, "in[0]");
  const auto setKey = findKeyByDisplayName(extracted, "set[0]");
  auto* expr = extracted.nextStateExprByStateKey.at(stateKey);

  EXPECT_TRUE(expr->evaluate(
      {{extracted.inputVarByKey.at(inKey), false},
       {extracted.inputVarByKey.at(setKey), true}}));
  EXPECT_TRUE(expr->evaluate(
      {{extracted.inputVarByKey.at(inKey), true},
       {extracted.inputVarByKey.at(setKey), false}}));
  EXPECT_FALSE(expr->evaluate(
      {{extracted.inputVarByKey.at(inKey), false},
       {extracted.inputVarByKey.at(setKey), false}}));
}

TEST_F(SequentialEquivalenceStrategyTests,
       SequentialDesignModelExtractSupportsResetHighInitialState) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* top = createDffreTop(library, "top");

  const auto extracted = SequentialDesignModel::extract(top);

  EXPECT_FALSE(extracted.hasUnsupportedFeatures());
  ASSERT_EQ(extracted.stateBits.size(), 1u);
  EXPECT_FALSE(extracted.initialStateValueByKey.at(extracted.stateBits.front()));
}

TEST_F(SequentialEquivalenceStrategyTests,
       SequentialDesignModelExtractPreservesEnableAndResetControlSemantics) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* top = createDffreTop(library, "top");

  const auto extracted = SequentialDesignModel::extract(top);
  const auto stateKey = extracted.stateBits.front();
  const auto inKey = findKeyByDisplayName(extracted, "in[0]");
  const auto enKey = findKeyByDisplayName(extracted, "en[0]");
  const auto rstKey = findKeyByDisplayName(extracted, "rst[0]");
  const size_t stateVar = extracted.inputVarByKey.at(stateKey);
  auto* expr = extracted.nextStateExprByStateKey.at(stateKey);

  EXPECT_FALSE(expr->evaluate(
      {{extracted.inputVarByKey.at(inKey), true},
       {extracted.inputVarByKey.at(enKey), true},
       {extracted.inputVarByKey.at(rstKey), true},
       {stateVar, true}}));
  EXPECT_TRUE(expr->evaluate(
      {{extracted.inputVarByKey.at(inKey), true},
       {extracted.inputVarByKey.at(enKey), true},
       {extracted.inputVarByKey.at(rstKey), false},
       {stateVar, false}}));
  EXPECT_TRUE(expr->evaluate(
      {{extracted.inputVarByKey.at(inKey), false},
       {extracted.inputVarByKey.at(enKey), false},
       {extracted.inputVarByKey.at(rstKey), false},
       {stateVar, true}}));
}

TEST_F(SequentialEquivalenceStrategyTests,
       SequentialDesignModelExtractRejectsNullTop) {
  EXPECT_THROW(
      static_cast<void>(SequentialDesignModel::extract(nullptr)),
      std::invalid_argument);
}

TEST_F(SequentialEquivalenceStrategyTests,
       SequentialDesignModelExtractRejectsMissingUniverse) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* primitives =
      NLLibrary::create(db, NLLibrary::Type::Primitives, NLName("prims"));
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* invModel = createInvModel(primitives);
  auto* top = createDffTop(library, "top", invModel, false, false);
  NLUniverse::get()->destroy();

  EXPECT_THROW(
      static_cast<void>(SequentialDesignModel::extract(top)),
      std::runtime_error);
}

TEST_F(SequentialEquivalenceStrategyTests,
       SequentialDesignModelExtractAbstractsUncomputableSequentialAsBoundaryByDefault) {
  ScopedSecBoundaryAbstraction boundaryAbstraction(true);
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* primitives =
      NLLibrary::create(db, NLLibrary::Type::Primitives, NLName("prims"));
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* model = createNoDataSequentialModel(primitives, "SEQ_NO_D");
  auto* top = createNoDataSequentialTop(library, "top", model);

  const auto extracted = SequentialDesignModel::extract(top);

  EXPECT_FALSE(extracted.hasUnsupportedFeatures());
  EXPECT_TRUE(extracted.stateBits.empty());
  EXPECT_NE(
      std::find(
          extracted.environmentInputs.begin(),
          extracted.environmentInputs.end(),
          findKeyByDisplayName(extracted, "ff0.Q[0]")),
      extracted.environmentInputs.end());
  EXPECT_NE(
      std::find(
          extracted.observedOutputs.begin(),
          extracted.observedOutputs.end(),
          findKeyByDisplayName(extracted, "ff0.CK[0]")),
      extracted.observedOutputs.end());
  ASSERT_EQ(extracted.abstractedSequentialBoundaries.size(), 1u);
  EXPECT_NE(
      extracted.abstractedSequentialBoundaries.front().find("ff0"),
      std::string::npos);
}

TEST_F(SequentialEquivalenceStrategyTests,
       SequentialDesignModelExtractAbstractsSequentialWithUnsupportedUpdatePinsAsBoundaryByDefault) {
  ScopedSecBoundaryAbstraction boundaryAbstraction(true);
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* primitives =
      NLLibrary::create(db, NLLibrary::Type::Primitives, NLName("prims"));
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* model = createExtraUpdatePinSequentialModel(primitives, "SEQ_ADDR");
  auto* top = createExtraUpdatePinSequentialTop(library, "top", model);

  const auto extracted = SequentialDesignModel::extract(top);

  EXPECT_FALSE(extracted.hasUnsupportedFeatures());
  EXPECT_TRUE(extracted.stateBits.empty());
  EXPECT_FALSE(extracted.abstractedSequentialBoundaries.empty());
  EXPECT_NE(
      extracted.abstractedSequentialBoundaries.front().find("update pin `A`"),
      std::string::npos);
}

TEST_F(SequentialEquivalenceStrategyTests,
       SequentialDesignModelExtractReportsUnsupportedSequentialWithoutDInput) {
  ScopedSecBoundaryAbstraction strictSequentialModeling(false);
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* primitives =
      NLLibrary::create(db, NLLibrary::Type::Primitives, NLName("prims"));
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* model = createNoDataSequentialModel(primitives, "SEQ_NO_D");
  auto* top = createNoDataSequentialTop(library, "top", model);

  const auto extracted = SequentialDesignModel::extract(top);

  EXPECT_TRUE(extracted.hasUnsupportedFeatures());
  EXPECT_FALSE(extracted.unsupportedReasons.empty());
}

TEST_F(SequentialEquivalenceStrategyTests,
       SequentialDesignModelExtractRejectsSequentialWithUnsupportedUpdatePinsInStrictMode) {
  ScopedSecBoundaryAbstraction strictSequentialModeling(false);
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* primitives =
      NLLibrary::create(db, NLLibrary::Type::Primitives, NLName("prims"));
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* model = createExtraUpdatePinSequentialModel(primitives, "SEQ_ADDR");
  auto* top = createExtraUpdatePinSequentialTop(library, "top", model);

  const auto extracted = SequentialDesignModel::extract(top);

  EXPECT_TRUE(extracted.hasUnsupportedFeatures());
  ASSERT_FALSE(extracted.unsupportedReasons.empty());
  EXPECT_NE(
      extracted.unsupportedReasons.front().find("update pin `A`"),
      std::string::npos);
}

TEST_F(SequentialEquivalenceStrategyTests,
       SequentialDesignModelExtractRejectsMultipleControlStyles) {
  ScopedSecBoundaryAbstraction strictSequentialModeling(false);
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* primitives =
      NLLibrary::create(db, NLLibrary::Type::Primitives, NLName("prims"));
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* model = createResetSetSequentialModel(primitives, "SEQ_RST_SET");
  auto* top = createResetSetSequentialTop(library, "top", model);

  const auto extracted = SequentialDesignModel::extract(top);

  EXPECT_TRUE(extracted.hasUnsupportedFeatures());
  ASSERT_FALSE(extracted.unsupportedReasons.empty());
  EXPECT_NE(
      extracted.unsupportedReasons.front().find("multiple control styles"),
      std::string::npos);
}

TEST_F(SequentialEquivalenceStrategyTests,
       SequentialDesignModelExtractMirrorsComplementedInitialStateValue) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* primitives =
      NLLibrary::create(db, NLLibrary::Type::Primitives, NLName("prims"));
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* model = createNamedComplementSetSequentialModel(
      primitives, "DFF_STATE_SET", "STATE", "STATEN");
  auto* top = createComplementedSetSequentialTop(
      library, "top", model, "STATE", "STATEN");

  const auto extracted = SequentialDesignModel::extract(top);

  ASSERT_EQ(extracted.stateBits.size(), 2u);
  ASSERT_EQ(extracted.initialStateValueByKey.size(), 2u);
  const auto& relation = extracted.complementedStateRelations.front();
  EXPECT_TRUE(extracted.initialStateValueByKey.at(relation.primaryKey));
  EXPECT_FALSE(extracted.initialStateValueByKey.at(relation.complementedKey));
}

TEST_F(SequentialEquivalenceStrategyTests,
       SequentialDesignModelExtractReportsSharedScalarDataForMultiOutputPrimitive) {
  ScopedSecBoundaryAbstraction strictSequentialModeling(false);
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* primitives =
      NLLibrary::create(db, NLLibrary::Type::Primitives, NLName("prims"));
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* model = createNamedComplementSequentialModel(
      primitives, "DFF_STATE_ALT", "STATE", "ALT");
  auto* top = createSequentialOutputPairTop(
      library, "top", model, "STATE", "ALT");

  const auto extracted = SequentialDesignModel::extract(top);

  EXPECT_TRUE(extracted.hasUnsupportedFeatures());
  ASSERT_FALSE(extracted.unsupportedReasons.empty());
  EXPECT_NE(
      extracted.unsupportedReasons.front().find("multiple independent state outputs"),
      std::string::npos);
  for (const auto& reason : extracted.unsupportedReasons) {
    EXPECT_EQ(reason.find("Missing next-state relation"), std::string::npos);
  }
}

TEST_F(SequentialEquivalenceStrategyTests,
       SequentialDesignModelExtractReportsSharedScalarDataForQAndUnrelatedOutput) {
  ScopedSecBoundaryAbstraction strictSequentialModeling(false);
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* primitives =
      NLLibrary::create(db, NLLibrary::Type::Primitives, NLName("prims"));
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* model = createNamedComplementSequentialModel(
      primitives, "DFF_Q_ALT", "Q", "ALT");
  auto* top = createSequentialOutputPairTop(
      library, "top", model, "Q", "ALT");

  const auto extracted = SequentialDesignModel::extract(top);

  EXPECT_TRUE(extracted.hasUnsupportedFeatures());
  ASSERT_FALSE(extracted.unsupportedReasons.empty());
  EXPECT_NE(
      extracted.unsupportedReasons.front().find("multiple independent state outputs"),
      std::string::npos);
  for (const auto& reason : extracted.unsupportedReasons) {
    EXPECT_EQ(reason.find("Missing next-state relation"), std::string::npos);
  }
}

TEST_F(SequentialEquivalenceStrategyTests,
       SequentialDesignModelExtractStopsBeforeConeBuildForUnsupportedPrimitiveInfo) {
  ScopedSecBoundaryAbstraction strictSequentialModeling(false);
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* primitives =
      NLLibrary::create(db, NLLibrary::Type::Primitives, NLName("prims"));
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* model = createNamedComplementSequentialModel(
      primitives, "DFF_STATE_ALT", "STATE", "ALT");
  auto* top = createSequentialOutputPairTop(
      library, "top", model, "STATE", "ALT");

  ScopedEnvVar secDiag("KEPLER_SEC_DIAG", "1");
  testing::internal::CaptureStderr();
  const auto extracted = SequentialDesignModel::extract(top);
  const std::string stderrOutput = testing::internal::GetCapturedStderr();

  EXPECT_TRUE(extracted.hasUnsupportedFeatures());
  EXPECT_NE(
      stderrOutput.find("SEC diag: extract(top) collect begin"),
      std::string::npos);
  EXPECT_NE(
      stderrOutput.find("SEC diag: extract(top) early unsupported exit before build"),
      std::string::npos);
  EXPECT_EQ(
      stderrOutput.find("SEC diag: extract(top) build begin"),
      std::string::npos);
}

TEST_F(SequentialEquivalenceStrategyTests,
       SequentialDesignModelExtractFindsPrimaryStateOutputWhenComplementAppearsFirst) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* primitives =
      NLLibrary::create(db, NLLibrary::Type::Primitives, NLName("prims"));
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* model = createComplementFirstSequentialModel(
      primitives, "DFF_STATEN_STATE", "STATE", "STATEN");
  auto* top = createSequentialOutputPairTop(
      library, "top", model, "STATE", "STATEN");

  const auto extracted = SequentialDesignModel::extract(top);

  EXPECT_FALSE(extracted.hasUnsupportedFeatures());
  ASSERT_EQ(extracted.complementedStateRelations.size(), 1u);
  EXPECT_EQ(
      extracted.complementedStateRelations.front().primaryKey,
      extracted.stateBits.front());
}

TEST_F(SequentialEquivalenceStrategyTests,
       MismatchedObservedOutputNamesAreReportedAsUnsupported) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* primitives =
      NLLibrary::create(db, NLLibrary::Type::Primitives, NLName("prims"));
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* invModel = createInvModel(primitives);
  auto* top0 = createNamedOutputDffTop(library, "top0", invModel, "out0");
  auto* top1 = createNamedOutputDffTop(library, "top1", invModel, "out1");

  SequentialEquivalenceStrategy strategy(top0, top1);
  const auto result = strategy.run(1);

  EXPECT_EQ(result.status, SequentialEquivalenceStatus::Unsupported);
  EXPECT_NE(result.reason.find("Mismatched observed output sets"), std::string::npos);
}

TEST_F(SequentialEquivalenceStrategyTests,
       MismatchedObservedOutputCountsAreReportedAsUnsupported) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* primitives =
      NLLibrary::create(db, NLLibrary::Type::Primitives, NLName("prims"));
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* invModel = createInvModel(primitives);
  auto* top0 = createNamedOutputDffTop(library, "top0", invModel, "out");
  auto* top1 = createExtraOutputDffTop(library, "top1", invModel);

  SequentialEquivalenceStrategy strategy(top0, top1);
  const auto result = strategy.run(1);

  EXPECT_EQ(result.status, SequentialEquivalenceStatus::Unsupported);
  EXPECT_NE(result.reason.find("Mismatched observed output sets"), std::string::npos);
}

TEST_F(SequentialEquivalenceStrategyTests,
       MismatchedInputNamesAreReportedAsUnsupported) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* primitives =
      NLLibrary::create(db, NLLibrary::Type::Primitives, NLName("prims"));
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* invModel = createInvModel(primitives);
  auto* top0 = createNamedInputDffTop(library, "top0", invModel, "in0");
  auto* top1 = createNamedInputDffTop(library, "top1", invModel, "in1");

  SequentialEquivalenceStrategy strategy(top0, top1);
  const auto result = strategy.run(1);

  EXPECT_EQ(result.status, SequentialEquivalenceStatus::Unsupported);
  EXPECT_NE(
      result.reason.find("Mismatched environment input sets"),
      std::string::npos);
}

TEST_F(SequentialEquivalenceStrategyTests,
       MismatchedInputCountsAreReportedAsUnsupported) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* primitives =
      NLLibrary::create(db, NLLibrary::Type::Primitives, NLName("prims"));
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* invModel = createInvModel(primitives);
  auto* top0 = createNamedInputDffTop(library, "top0", invModel, "in");
  auto* top1 = createExtraInputDffTop(library, "top1");

  SequentialEquivalenceStrategy strategy(top0, top1);
  const auto result = strategy.run(1);

  EXPECT_EQ(result.status, SequentialEquivalenceStatus::Unsupported);
  EXPECT_NE(
      result.reason.find("Mismatched environment input sets"),
      std::string::npos);
}

TEST_F(SequentialEquivalenceStrategyTests,
       TooSmallBoundRemainsInconclusiveBeforeCounterexampleDepth) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* top0 = createResetInitializedPipelineTop(library, "top0", false);
  auto* top1 = createResetInitializedPipelineTop(library, "top1", true);

  SequentialEquivalenceStrategy strategy(top0, top1);
  const auto result = strategy.run(2);

  EXPECT_EQ(result.status, SequentialEquivalenceStatus::Inconclusive);
  EXPECT_EQ(result.bound, 2u);
}

TEST_F(SequentialEquivalenceStrategyTests,
       ZeroBoundRemainsInconclusiveForEquivalentSequentialDesigns) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* primitives =
      NLLibrary::create(db, NLLibrary::Type::Primitives, NLName("prims"));
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* invModel = createInvModel(primitives);
  auto* top0 = createDffTop(library, "top0", invModel, false, false);
  auto* top1 = createDffTop(library, "top1", invModel, false, false);

  SequentialEquivalenceStrategy strategy(top0, top1);
  const auto result = strategy.run(0);

  EXPECT_EQ(result.status, SequentialEquivalenceStatus::Inconclusive);
  EXPECT_EQ(result.bound, 0u);
}

TEST_F(SequentialEquivalenceStrategyTests,
       DifferentResultIncludesCounterexampleTracebackDetails) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* primitives =
      NLLibrary::create(db, NLLibrary::Type::Primitives, NLName("prims"));
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* invModel = createInvModel(primitives);
  auto* top0 = createDffTop(library, "top0", invModel, false, false);
  auto* top1 = createDffTop(library, "top1", invModel, true, false);

  SequentialEquivalenceStrategy strategy(top0, top1);
  const auto result = strategy.run(3);

  EXPECT_EQ(result.status, SequentialEquivalenceStatus::Different);
  EXPECT_NE(result.reason.find("Input trace:"), std::string::npos);
  EXPECT_NE(
      result.reason.find("Observed output mismatches at cycle"),
      std::string::npos);
  EXPECT_NE(
      result.reason.find("Traceback for first differing point"),
      std::string::npos);
  EXPECT_NE(
      result.reason.find("design0 cone to environment inputs"),
      std::string::npos);
  EXPECT_NE(result.reason.find("cone terms only in design1"), std::string::npos);
}

TEST_F(SequentialEquivalenceStrategyTests,
       UnsupportedReasonsFromBothDesignsAreJoined) {
  ScopedSecBoundaryAbstraction strictSequentialModeling(false);
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* primitives =
      NLLibrary::create(db, NLLibrary::Type::Primitives, NLName("prims"));
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* unsupportedModel = createNamedComplementSequentialModel(
      primitives, "DFF_STATE_ALT", "STATE", "ALT");
  auto* top0 = createSequentialOutputPairTop(
      library, "top0", unsupportedModel, "STATE", "ALT");
  auto* top1 = createSequentialOutputPairTop(
      library, "top1", unsupportedModel, "STATE", "ALT");

  SequentialEquivalenceStrategy strategy(top0, top1);
  const auto result = strategy.run(1);

  EXPECT_EQ(result.status, SequentialEquivalenceStatus::Unsupported);
  EXPECT_FALSE(result.reason.empty());
}

TEST_F(SequentialEquivalenceStrategyTests,
       StrategyStopsBeforeSecondExtractionAndProofOnUnsupportedPrimitiveInfo) {
  ScopedSecBoundaryAbstraction strictSequentialModeling(false);
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* primitives =
      NLLibrary::create(db, NLLibrary::Type::Primitives, NLName("prims"));
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* unsupportedModel = createNamedComplementSequentialModel(
      primitives, "DFF_STATE_ALT", "STATE", "ALT");
  auto* invModel = createInvModel(primitives);
  auto* top0 = createSequentialOutputPairTop(
      library, "top0", unsupportedModel, "STATE", "ALT");
  auto* top1 = createDffTop(library, "top1", invModel, false, false);

  ScopedEnvVar secDiag("KEPLER_SEC_DIAG", "1");
  testing::internal::CaptureStderr();
  SequentialEquivalenceStrategy strategy(top0, top1);
  const auto result = strategy.run(1);
  const std::string stderrOutput = testing::internal::GetCapturedStderr();

  EXPECT_EQ(result.status, SequentialEquivalenceStatus::Unsupported);
  EXPECT_NE(stderrOutput.find("SEC diag: extracted design0"), std::string::npos);
  EXPECT_EQ(stderrOutput.find("SEC diag: extracted design1"), std::string::npos);
  EXPECT_EQ(stderrOutput.find("SEC diag: aligning inputs/outputs"), std::string::npos);
}

TEST_F(SequentialEquivalenceStrategyTests,
       EquivalentDesignsCanProveSecOnCoveredOutputsOnlyAfterNoDriverSkipping) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* top0 = createPartialCoverageNoDriverTop(library, "top0");
  auto* top1 = createPartialCoverageNoDriverTop(library, "top1");

  SequentialEquivalenceStrategy strategy(top0, top1);
  const auto result = strategy.run(2);

  EXPECT_EQ(result.status, SequentialEquivalenceStatus::Equivalent);
  EXPECT_EQ(result.coveredOutputs, 1u);
  EXPECT_EQ(result.totalOutputs, 2u);
  ASSERT_EQ(result.skippedObservedOutputs.size(), 1u);
  EXPECT_NE(result.skippedObservedOutputs.front().find("bad[0]"), std::string::npos);
  EXPECT_NE(result.skippedObservedOutputs.front().find("no-driver"), std::string::npos);
}

TEST_F(SequentialEquivalenceStrategyTests,
       EquivalentDesignsCanProveSecOnCoveredOutputsOnlyAfterMultiDriverSkipping) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* primitives =
      NLLibrary::create(db, NLLibrary::Type::Primitives, NLName("prims"));
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* invModel = createInvModel(primitives);
  auto* top0 = createPartialCoverageMultiDriverTop(library, "top0", invModel);
  auto* top1 = createPartialCoverageMultiDriverTop(library, "top1", invModel);

  SequentialEquivalenceStrategy strategy(top0, top1);
  const auto result = strategy.run(2);

  EXPECT_EQ(result.status, SequentialEquivalenceStatus::Equivalent);
  EXPECT_EQ(result.coveredOutputs, 1u);
  EXPECT_EQ(result.totalOutputs, 2u);
  ASSERT_EQ(result.skippedObservedOutputs.size(), 1u);
  EXPECT_NE(result.skippedObservedOutputs.front().find("bad[0]"), std::string::npos);
  EXPECT_NE(result.skippedObservedOutputs.front().find("multi-driver"), std::string::npos);
}

TEST_F(SequentialEquivalenceStrategyTests,
       EquivalentDesignsCanProveSecOnCoveredOutputsOnlyAfterLogicalLoopSkipping) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* top0 = createPartialCoverageLogicalLoopTop(library, "top0");
  auto* top1 = createPartialCoverageLogicalLoopTop(library, "top1");

  SequentialEquivalenceStrategy strategy(top0, top1);
  const auto result = strategy.run(2);

  EXPECT_EQ(result.status, SequentialEquivalenceStatus::Equivalent);
  EXPECT_EQ(result.coveredOutputs, 1u);
  EXPECT_EQ(result.totalOutputs, 2u);
  ASSERT_EQ(result.skippedObservedOutputs.size(), 1u);
  EXPECT_NE(result.skippedObservedOutputs.front().find("bad[0]"), std::string::npos);
  EXPECT_NE(
      result.skippedObservedOutputs.front().find("logical-loop"),
      std::string::npos);
}

TEST_F(SequentialEquivalenceStrategyTests,
       EquivalentDffDesignsReportTopBoundarySurface) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* primitives =
      NLLibrary::create(db, NLLibrary::Type::Primitives, NLName("prims"));
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* invModel = createInvModel(primitives);
  auto* top0 = createDffTop(library, "top0", invModel, false, false);
  auto* top1 = createDffTop(library, "top1", invModel, false, false);

  SequentialEquivalenceStrategy strategy(top0, top1);
  const auto result = strategy.run(2);

  auto hasRole = [&](const char* design, const char* signal, const char* role) {
    return std::any_of(
        result.extractedBoundaryReports.begin(),
        result.extractedBoundaryReports.end(),
        [&](const ExtractedBoundaryReportEntry& entry) {
          return entry.design == design && entry.signal == signal &&
                 std::find(entry.roles.begin(), entry.roles.end(), role) !=
                     entry.roles.end();
        });
  };

  EXPECT_EQ(result.status, SequentialEquivalenceStatus::Equivalent);
  EXPECT_TRUE(hasRole("design0", "clk[0]", "top_input"));
  EXPECT_TRUE(hasRole("design0", "in[0]", "top_input"));
  EXPECT_TRUE(hasRole("design0", "out[0]", "top_output"));
  EXPECT_TRUE(hasRole("design1", "clk[0]", "top_input"));
  EXPECT_TRUE(hasRole("design1", "in[0]", "top_input"));
  EXPECT_TRUE(hasRole("design1", "out[0]", "top_output"));
}

TEST_F(SequentialEquivalenceStrategyTests,
       EquivalentOpaqueLeafDesignsReportOpaqueInternalBoundaryTerms) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* primitives =
      NLLibrary::create(db, NLLibrary::Type::Primitives, NLName("prims"));
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* opaqueModel = createOpaqueLeafModel(primitives);
  auto* top0 = createOpaqueBoundaryTop(library, "top0", opaqueModel);
  auto* top1 = createOpaqueBoundaryTop(library, "top1", opaqueModel);

  SequentialEquivalenceStrategy strategy(top0, top1);
  const auto result = strategy.run(2);

  auto hasRole = [&](const char* design, const char* signal, const char* role) {
    return std::any_of(
        result.extractedBoundaryReports.begin(),
        result.extractedBoundaryReports.end(),
        [&](const ExtractedBoundaryReportEntry& entry) {
          return entry.design == design && entry.signal == signal &&
                 std::find(entry.roles.begin(), entry.roles.end(), role) !=
                     entry.roles.end();
        });
  };

  EXPECT_EQ(result.status, SequentialEquivalenceStatus::Equivalent);
  EXPECT_TRUE(hasRole("design0", "in[0]", "top_input"));
  EXPECT_TRUE(hasRole("design0", "out[0]", "top_output"));
  EXPECT_TRUE(hasRole("design0", "opaque0.Y[0]", "opaque_internal_input"));
  EXPECT_TRUE(hasRole("design0", "opaque0.A[0]", "opaque_internal_output"));
  EXPECT_TRUE(hasRole("design1", "opaque0.Y[0]", "opaque_internal_input"));
  EXPECT_TRUE(hasRole("design1", "opaque0.A[0]", "opaque_internal_output"));
}

TEST_F(SequentialEquivalenceStrategyTests,
       UnsupportedSequentialInterfacesCanBeAbstractedAsSecBoundariesByDefault) {
  ScopedSecBoundaryAbstraction boundaryAbstraction(true);
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* primitives =
      NLLibrary::create(db, NLLibrary::Type::Primitives, NLName("prims"));
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* unsupportedModel = createNoDataSequentialModel(primitives, "SEQ_NO_D");
  auto* top0 =
      createUnsupportedPrimitiveCoverageTop(library, "top0", unsupportedModel);
  auto* top1 =
      createUnsupportedPrimitiveCoverageTop(library, "top1", unsupportedModel);

  SequentialEquivalenceStrategy strategy(top0, top1);
  const auto result = strategy.run(2);

  auto hasRole = [&](const char* design, const char* signal, const char* role) {
    return std::any_of(
        result.extractedBoundaryReports.begin(),
        result.extractedBoundaryReports.end(),
        [&](const ExtractedBoundaryReportEntry& entry) {
          return entry.design == design && entry.signal == signal &&
                 std::find(entry.roles.begin(), entry.roles.end(), role) !=
                     entry.roles.end();
        });
  };

  EXPECT_EQ(result.status, SequentialEquivalenceStatus::Equivalent);
  EXPECT_FALSE(result.abstractedSequentialBoundaries.empty());
  EXPECT_TRUE(hasRole("design0", "clk[0]", "top_input"));
  EXPECT_TRUE(hasRole("design0", "in[0]", "top_input"));
  EXPECT_TRUE(hasRole("design0", "good[0]", "top_output"));
  EXPECT_TRUE(hasRole("design0", "bad[0]", "top_output"));
  EXPECT_FALSE(hasRole("design0", "ff0.Q[0]", "opaque_internal_input"));
  EXPECT_FALSE(hasRole("design0", "ff0.CK[0]", "opaque_internal_output"));
  EXPECT_TRUE(hasRole("design0", "ff0.Q[0]", "abstracted_sequential_state"));
  EXPECT_TRUE(hasRole("design0", "ff0.CK[0]", "abstracted_sequential_observed"));
  EXPECT_FALSE(hasRole("design1", "ff0.Q[0]", "opaque_internal_input"));
  EXPECT_FALSE(hasRole("design1", "ff0.CK[0]", "opaque_internal_output"));
  EXPECT_TRUE(hasRole("design1", "ff0.Q[0]", "abstracted_sequential_state"));
  EXPECT_TRUE(hasRole("design1", "ff0.CK[0]", "abstracted_sequential_observed"));
}

TEST_F(SequentialEquivalenceStrategyTests,
       UnsupportedPrimitiveInformationStillFailsEvenWithOtherCoveredOutputs) {
  ScopedSecBoundaryAbstraction strictSequentialModeling(false);
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* primitives =
      NLLibrary::create(db, NLLibrary::Type::Primitives, NLName("prims"));
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* unsupportedModel = createNoDataSequentialModel(primitives, "SEQ_NO_D");
  auto* top0 =
      createUnsupportedPrimitiveCoverageTop(library, "top0", unsupportedModel);
  auto* top1 =
      createUnsupportedPrimitiveCoverageTop(library, "top1", unsupportedModel);

  SequentialEquivalenceStrategy strategy(top0, top1);
  const auto result = strategy.run(2);

  EXPECT_EQ(result.status, SequentialEquivalenceStatus::Unsupported);
  EXPECT_TRUE(result.skippedObservedOutputs.empty());
  EXPECT_FALSE(result.reason.empty());
}

TEST_F(SequentialEquivalenceStrategyTests,
       DiagnosticModePrintsStrategyAndExtractionProgress) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* primitives =
      NLLibrary::create(db, NLLibrary::Type::Primitives, NLName("prims"));
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* invModel = createInvModel(primitives);
  auto* top0 = createDffTop(library, "top0", invModel, false, false);
  auto* top1 = createDffTop(library, "top1", invModel, false, false);

  ScopedEnvVar secDiag("KEPLER_SEC_DIAG", "1");
  testing::internal::CaptureStdout();
  testing::internal::CaptureStderr();
  SequentialEquivalenceStrategy strategy(top0, top1);
  const auto result = strategy.run(3);
  const std::string stdoutOutput = testing::internal::GetCapturedStdout();
  const std::string stderrOutput = testing::internal::GetCapturedStderr();

  EXPECT_EQ(result.status, SequentialEquivalenceStatus::Equivalent);
  EXPECT_NE(stderrOutput.find("SEC diag: start run"), std::string::npos);
  EXPECT_NE(
      stderrOutput.find("SEC diag: extract(top0) collect begin"),
      std::string::npos);
  EXPECT_NE(
      stderrOutput.find("SEC diag: remapped next-state formulas"),
      std::string::npos);
  EXPECT_NE(
      stderrOutput.find("SEC diag: entering legacy engine"),
      std::string::npos);
  EXPECT_NE(stdoutOutput.find("SEC diag: aligned_inputs="), std::string::npos);
  EXPECT_NE(stdoutOutput.find("SEC diag: property_is_true="), std::string::npos);
}

TEST_F(SequentialEquivalenceStrategyTests,
       ResetBootstrapInductionProvesPostResetInvariant) {
  KInductionProblem problem;
  problem.environmentInputNames = {"rst"};
  problem.observedOutputNames = {"out"};
  problem.inputSymbols = {2};
  problem.resetBootstrapInputs = {{2, true}};
  problem.bootstrapStateEqualityPairs = {{3, 4}};
  problem.inductiveStateEqualityPairs = {{3, 4}};
  problem.state0Symbols = {3};
  problem.state1Symbols = {4};
  problem.allSymbols = {2, 3, 4};
  problem.observedOutputExprs0 = {BoolExpr::Var(3)};
  problem.observedOutputExprs1 = {BoolExpr::Var(4)};
  problem.transitions0 = {{3, BoolExpr::Var(3)}};
  problem.transitions1 = {{4, BoolExpr::Var(4)}};
  problem.property =
      BoolExpr::Not(BoolExpr::Xor(BoolExpr::Var(3), BoolExpr::Var(4)));
  problem.bad = BoolExpr::Xor(BoolExpr::Var(3), BoolExpr::Var(4));
  problem.description = "bootstrap induction regression";

  KInductionEngine engine(problem, KEPLER_FORMAL::Config::SolverType::KISSAT);
  const auto result = engine.run(3);

  EXPECT_EQ(result.status, KInductionStatus::Equivalent);
  EXPECT_LE(result.bound, 3u);
}

TEST_F(SequentialEquivalenceStrategyTests,
       StrongerInductionInvariantClosesOutputOnlySecAtOneStep) {
  KInductionProblem problem;
  problem.observedOutputNames = {"out"};
  problem.state0Symbols = {2, 3};
  problem.state1Symbols = {4, 5};
  problem.allSymbols = {2, 3, 4, 5};
  problem.observedOutputExprs0 = {BoolExpr::Var(2)};
  problem.observedOutputExprs1 = {BoolExpr::Var(4)};
  problem.transitions0 = {{2, BoolExpr::Var(3)}, {3, BoolExpr::Var(3)}};
  problem.transitions1 = {{4, BoolExpr::Var(5)}, {5, BoolExpr::Var(5)}};
  problem.initialCondition = BoolExpr::And(
      BoolExpr::And(BoolExpr::Not(BoolExpr::Var(2)), BoolExpr::Not(BoolExpr::Var(3))),
      BoolExpr::And(BoolExpr::Not(BoolExpr::Var(4)), BoolExpr::Not(BoolExpr::Var(5))));
  problem.initializedStateCount = 4;
  problem.totalStateCount = 4;
  problem.property =
      BoolExpr::Not(BoolExpr::Xor(BoolExpr::Var(2), BoolExpr::Var(4)));
  problem.bad = BoolExpr::Xor(BoolExpr::Var(2), BoolExpr::Var(4));
  problem.description = "output-only SEC needs a stronger invariant";

  KInductionEngine withoutInvariant(
      problem, KEPLER_FORMAL::Config::SolverType::KISSAT);
  const auto withoutInvariantResult = withoutInvariant.run(1);
  EXPECT_EQ(withoutInvariantResult.status, KInductionStatus::Inconclusive);

  problem.inductionProperty = BoolExpr::And(
      BoolExpr::Not(BoolExpr::Xor(BoolExpr::Var(2), BoolExpr::Var(4))),
      BoolExpr::Not(BoolExpr::Xor(BoolExpr::Var(3), BoolExpr::Var(5))));
  problem.inductionBad = BoolExpr::Not(problem.inductionProperty);

  KInductionEngine withInvariant(
      problem, KEPLER_FORMAL::Config::SolverType::KISSAT);
  const auto withInvariantResult = withInvariant.run(1);
  EXPECT_EQ(withInvariantResult.status, KInductionStatus::Equivalent);
  EXPECT_EQ(withInvariantResult.bound, 1u);
}

TEST_F(SequentialEquivalenceStrategyTests,
       SequentialDesignModelDetailHelpersCoverNextStateAndInitErrors) {
  const std::unordered_map<naja::DNL::DNLID, BoolExpr*> outputExprByTerm = {
      {11, BoolExpr::Var(7)},
      {12, BoolExpr::Var(8)},
      {13, BoolExpr::Var(9)},
  };

  EXPECT_THROW(
      detail::buildNextStateExprForTest(5, {{"D", 11}}, {2, 3}, outputExprByTerm),
      std::runtime_error);
  EXPECT_THROW(
      detail::buildNextStateExprForTest(0, {{"D", 11}}, {1}, outputExprByTerm),
      std::runtime_error);
  EXPECT_THROW(
      detail::buildNextStateExprForTest(0, {}, {2}, outputExprByTerm),
      std::runtime_error);
  EXPECT_THROW(
      detail::buildNextStateExprForTest(
          0, {{"D", 11}, {"R", 12}, {"S", 13}}, {2}, outputExprByTerm),
      std::runtime_error);
  auto* holdExpr = detail::buildNextStateExprForTest(
      0, {{"D", 11}, {"E", 12}, {"RN", 13}}, {2}, outputExprByTerm);
  EXPECT_FALSE(holdExpr->evaluate({{2, true}, {7, true}, {8, true}, {9, false}}));
  EXPECT_TRUE(holdExpr->evaluate({{2, false}, {7, true}, {8, true}, {9, true}}));
  EXPECT_TRUE(holdExpr->evaluate({{2, true}, {7, false}, {8, false}, {9, true}}));
  auto* setExpr = detail::buildNextStateExprForTest(
      0, {{"D", 11}, {"S", 12}}, {2}, outputExprByTerm);
  EXPECT_TRUE(setExpr->evaluate({{2, false}, {7, false}, {8, true}}));
  EXPECT_FALSE(setExpr->evaluate({{2, false}, {7, false}, {8, false}}));

  EXPECT_EQ(
      detail::detectInitialStateValueForTest({{"R", 11}}),
      std::optional<bool>(false));
  EXPECT_EQ(
      detail::detectInitialStateValueForTest({{"RN", 11}}),
      std::optional<bool>(false));
  EXPECT_EQ(
      detail::detectInitialStateValueForTest({{"S", 11}}),
      std::optional<bool>(true));
  EXPECT_EQ(detail::detectInitialStateValueForTest({}), std::nullopt);
  EXPECT_THROW(
      detail::detectInitialStateValueForTest({{"R", 11}, {"S", 12}}),
      std::runtime_error);
}

TEST_F(SequentialEquivalenceStrategyTests,
       SequentialDesignModelDetailResetInferenceAndReachableStateHelpersCoverBranches) {
  const auto requiredOutputs = detail::selectRequiredBuilderOutputsForTest(
      {10, 11, 12, 13, 14},
      {10, 14},
      {12, 13, 13},
      {14});
  EXPECT_EQ(
      requiredOutputs,
      (std::vector<naja::DNL::DNLID>{10, 12, 13}));

  EXPECT_EQ(
      detail::getResetAssertionValueForTest("rst[0]"),
      std::optional<bool>(true));
  EXPECT_EQ(
      detail::getResetAssertionValueForTest("rst_n[0]"),
      std::optional<bool>(false));
  EXPECT_EQ(
      detail::getResetAssertionValueForTest("reset_i[0]"),
      std::optional<bool>(true));
  EXPECT_EQ(
      detail::getResetAssertionValueForTest("rst_ni[0]"),
      std::optional<bool>(false));
  EXPECT_EQ(detail::getResetAssertionValueForTest("enable[0]"), std::nullopt);

  const auto shared = BoolExpr::Not(BoolExpr::Var(3));
  EXPECT_EQ(detail::evaluateConstantUnderAssignmentsForTest(nullptr, {}), std::nullopt);
  EXPECT_EQ(
      detail::evaluateConstantUnderAssignmentsForTest(BoolExpr::Var(1), {}),
      std::optional<bool>(true));
  EXPECT_EQ(
      detail::evaluateConstantUnderAssignmentsForTest(BoolExpr::Var(0), {}),
      std::optional<bool>(false));
  EXPECT_EQ(
      detail::evaluateConstantUnderAssignmentsForTest(
          BoolExpr::And(shared, shared), {{3, false}}),
      std::optional<bool>(true));
  EXPECT_EQ(
      detail::evaluateConstantUnderAssignmentsForTest(
          BoolExpr::And(BoolExpr::createFalse(), BoolExpr::Var(99)), {}),
      std::optional<bool>(false));
  EXPECT_EQ(
      detail::evaluateConstantUnderAssignmentsForTest(
          BoolExpr::And(BoolExpr::Var(3), BoolExpr::Var(4)), {{3, false}, {4, true}}),
      std::optional<bool>(false));
  EXPECT_EQ(
      detail::evaluateConstantUnderAssignmentsForTest(
          BoolExpr::And(BoolExpr::Var(3), BoolExpr::Var(4)), {{3, true}, {4, false}}),
      std::optional<bool>(false));
  EXPECT_EQ(
      detail::evaluateConstantUnderAssignmentsForTest(
          BoolExpr::And(BoolExpr::Var(3), BoolExpr::Var(4)), {{3, true}, {4, true}}),
      std::optional<bool>(true));
  EXPECT_EQ(
      detail::evaluateConstantUnderAssignmentsForTest(
          BoolExpr::Or(BoolExpr::createTrue(), BoolExpr::Var(99)), {}),
      std::optional<bool>(true));
  EXPECT_EQ(
      detail::evaluateConstantUnderAssignmentsForTest(
          BoolExpr::Or(BoolExpr::Var(3), BoolExpr::Var(4)), {{3, true}, {4, false}}),
      std::optional<bool>(true));
  EXPECT_EQ(
      detail::evaluateConstantUnderAssignmentsForTest(
          BoolExpr::Or(BoolExpr::Var(3), BoolExpr::Var(4)), {{3, false}, {4, true}}),
      std::optional<bool>(true));
  EXPECT_EQ(
      detail::evaluateConstantUnderAssignmentsForTest(
          BoolExpr::Or(BoolExpr::Var(3), BoolExpr::Var(4)), {{3, false}, {4, false}}),
      std::optional<bool>(false));
  EXPECT_EQ(
      detail::evaluateConstantUnderAssignmentsForTest(
          BoolExpr::Xor(BoolExpr::Var(3), BoolExpr::Var(4)), {{3, true}, {4, false}}),
      std::optional<bool>(true));
  EXPECT_EQ(
      detail::evaluateConstantUnderAssignmentsForTest(
          BoolExpr::Xor(BoolExpr::Var(3), BoolExpr::Var(4)), {{3, true}}),
      std::nullopt);
  BoolExpr invalidExpr;
  EXPECT_EQ(
      detail::evaluateConstantUnderAssignmentsForTest(&invalidExpr, {}),
      std::nullopt);

  const auto rstKey = makeSignalKey("rst");
  const auto stateAKey = makeSignalKey("state_a");
  const auto stateBKey = makeSignalKey("state_b");
  const auto stateAComplementKey = makeSignalKey("state_a_n");

  SequentialDesignModel inferredModel;
  inferredModel.environmentInputs = {rstKey};
  inferredModel.stateBits = {stateAKey, stateBKey, stateAComplementKey};
  inferredModel.displayNameByKey[rstKey] = "rst[0]";
  inferredModel.inputVarByKey[rstKey] = 10;
  inferredModel.inputVarByKey[stateAKey] = 2;
  inferredModel.inputVarByKey[stateBKey] = 3;
  inferredModel.inputVarByKey[stateAComplementKey] = 4;
  inferredModel.nextStateExprByStateKey[stateAKey] = BoolExpr::Var(10);
  inferredModel.nextStateExprByStateKey[stateBKey] =
      BoolExpr::And(BoolExpr::Var(2), BoolExpr::createTrue());
  inferredModel.nextStateExprByStateKey[stateAComplementKey] =
      BoolExpr::Not(BoolExpr::Var(2));
  inferredModel.complementedStateRelations.push_back(
      {stateAKey, stateAComplementKey});

  detail::inferSynthesizedResetInitialStateValuesForTest(inferredModel);
  EXPECT_EQ(
      inferredModel.initialStateValueByKey.at(stateAKey),
      true);
  EXPECT_EQ(
      inferredModel.initialStateValueByKey.at(stateBKey),
      true);
  EXPECT_EQ(
      inferredModel.initialStateValueByKey.at(stateAComplementKey),
      false);

  const auto missingDisplayResetKey = makeSignalKey("rst_missing_display");
  const auto missingVarResetKey = makeSignalKey("rst_missing_var");
  const auto nullStateKey = makeSignalKey("null_state");
  const auto derivedStateKey = makeSignalKey("derived_state");
  const auto partnerPrimaryKey = makeSignalKey("partner_primary");
  const auto partnerComplementKey = makeSignalKey("partner_complement");

  SequentialDesignModel edgeCaseModel;
  edgeCaseModel.environmentInputs = {missingDisplayResetKey, missingVarResetKey, rstKey};
  edgeCaseModel.stateBits = {
      nullStateKey, derivedStateKey, partnerPrimaryKey, partnerComplementKey};
  edgeCaseModel.displayNameByKey[missingVarResetKey] = "rst[0]";
  edgeCaseModel.displayNameByKey[rstKey] = "rst[0]";
  edgeCaseModel.inputVarByKey[missingDisplayResetKey] = 30;
  edgeCaseModel.inputVarByKey[rstKey] = 31;
  edgeCaseModel.inputVarByKey[nullStateKey] = 2;
  edgeCaseModel.inputVarByKey[derivedStateKey] = 3;
  edgeCaseModel.inputVarByKey[partnerPrimaryKey] = 4;
  edgeCaseModel.inputVarByKey[partnerComplementKey] = 5;
  auto* sharedResetVar = BoolExpr::Var(31);
  edgeCaseModel.nextStateExprByStateKey[nullStateKey] = nullptr;
  edgeCaseModel.nextStateExprByStateKey[derivedStateKey] = BoolExpr::And(
      sharedResetVar, BoolExpr::Or(BoolExpr::Var(99), sharedResetVar));
  edgeCaseModel.nextStateExprByStateKey[partnerPrimaryKey] = BoolExpr::createFalse();
  edgeCaseModel.nextStateExprByStateKey[partnerComplementKey] = BoolExpr::createTrue();
  edgeCaseModel.initialStateValueByKey[partnerPrimaryKey] = false;
  edgeCaseModel.complementedStateRelations.push_back(
      {partnerPrimaryKey, partnerComplementKey});

  detail::inferSynthesizedResetInitialStateValuesForTest(edgeCaseModel);
  EXPECT_TRUE(edgeCaseModel.initialStateValueByKey.at(derivedStateKey));
  EXPECT_TRUE(edgeCaseModel.initialStateValueByKey.at(partnerComplementKey));

  const auto dependencyKnownKey = makeSignalKey("dependency_known");
  const auto dependencyDerivedKey = makeSignalKey("dependency_derived");
  SequentialDesignModel dependencyModel;
  dependencyModel.environmentInputs = {rstKey};
  dependencyModel.stateBits = {dependencyKnownKey, dependencyDerivedKey};
  dependencyModel.displayNameByKey[rstKey] = "rst[0]";
  dependencyModel.inputVarByKey[rstKey] = 40;
  dependencyModel.inputVarByKey[dependencyKnownKey] = 2;
  dependencyModel.inputVarByKey[dependencyDerivedKey] = 3;
  dependencyModel.initialStateValueByKey[dependencyKnownKey] = true;
  auto* sharedStateExpr = BoolExpr::Var(2);
  dependencyModel.nextStateExprByStateKey[dependencyKnownKey] = sharedStateExpr;
  dependencyModel.nextStateExprByStateKey[dependencyDerivedKey] = BoolExpr::And(
      sharedStateExpr,
      BoolExpr::Or(BoolExpr::Var(99), sharedStateExpr));

  detail::inferSynthesizedResetInitialStateValuesForTest(dependencyModel);
  EXPECT_TRUE(dependencyModel.initialStateValueByKey.at(dependencyDerivedKey));

  const auto derivedKey0 = makeSignalKey("derived0");
  const auto derivedKey1 = makeSignalKey("derived1");
  const auto xorKey = makeSignalKey("derived_xor");
  SequentialDesignModel bootstrapModel0;
  bootstrapModel0.environmentInputs = {rstKey};
  bootstrapModel0.stateBits = {derivedKey0, derivedKey1, xorKey};
  bootstrapModel0.displayNameByKey[rstKey] = "rst[0]";
  bootstrapModel0.inputVarByKey[rstKey] = 20;
  bootstrapModel0.inputVarByKey[derivedKey0] = 2;
  bootstrapModel0.inputVarByKey[derivedKey1] = 3;
  bootstrapModel0.inputVarByKey[xorKey] = 4;
  bootstrapModel0.initialStateValueByKey[derivedKey0] = true;
  bootstrapModel0.initialStateValueByKey[derivedKey1] = false;
  bootstrapModel0.nextStateExprByStateKey[derivedKey0] = BoolExpr::Var(2);
  bootstrapModel0.nextStateExprByStateKey[derivedKey1] = BoolExpr::Var(3);
  bootstrapModel0.nextStateExprByStateKey[xorKey] =
      BoolExpr::Xor(BoolExpr::Var(2), BoolExpr::Var(3));

  const auto bootstrapValues =
      detail::deriveResetBootstrapStateValuesForTest(bootstrapModel0, 1);
  EXPECT_EQ(bootstrapValues.at(xorKey), true);

  SequentialDesignModel bootstrapModel1 = bootstrapModel0;
  bootstrapModel1.initialStateValueByKey[derivedKey1] = true;

  AlignedSignals candidateStates;
  candidateStates.names = {"state_a", "state_b"};
  candidateStates.keys0 = {derivedKey0, derivedKey1};
  candidateStates.keys1 = {derivedKey0, derivedKey1};
  const auto anchoredStates = detail::filterStateEqualitiesByInitialValueForTest(
      bootstrapModel0, bootstrapModel1, candidateStates);
  ASSERT_EQ(anchoredStates.names.size(), 1u);
  EXPECT_EQ(anchoredStates.names.front(), "state_a");
}

TEST_F(SequentialEquivalenceStrategyTests,
       SequentialEquivalenceStrategyDetailFormattingHelpersCoverFallbackPaths) {
  EXPECT_EQ(detail::formatStringListForTest({}, 3), "<none>");
  EXPECT_EQ(
      detail::formatStringListForTest({"a", "b", "c"}, 2),
      "a, b, ... +1 more");

  EXPECT_NE(
      detail::formatConeLevelsForTest({}).find("<no traced cone terms>"),
      std::string::npos);

  std::vector<std::vector<std::string>> levels;
  for (size_t level = 0; level < 13; ++level) {
    std::vector<std::string> levelTerms;
    for (size_t term = 0; term < 13; ++term) {
      levelTerms.push_back(
          "term_" + std::to_string(level) + "_" + std::to_string(term));
    }
    levels.push_back(std::move(levelTerms));
  }
  const auto formattedLevels = detail::formatConeLevelsForTest(levels);
  EXPECT_NE(formattedLevels.find("... +1 more trace steps"), std::string::npos);
  EXPECT_NE(formattedLevels.find("... +1 more"), std::string::npos);

  KInductionResult noWitnessResult;
  EXPECT_TRUE(detail::formatCounterexampleWitnessForTest(
                  noWitnessResult, {}, {}, nullptr, nullptr)
                  .empty());

  KInductionResult emptyTraceResult;
  emptyTraceResult.witness = KInductionResult::CounterexampleWitness{
      .badFrame = 2,
      .inputTrace = {},
      .outputMismatches = {{"ghost[0]", true, false}},
  };
  const auto emptyTraceText = detail::formatCounterexampleWitnessForTest(
      emptyTraceResult, {}, {}, nullptr, nullptr);
  EXPECT_NE(emptyTraceText.find("Input trace: <none>"), std::string::npos);
  EXPECT_NE(emptyTraceText.find("Cone traceback unavailable:"), std::string::npos);

  KInductionResult noEnvTraceResult;
  noEnvTraceResult.witness = KInductionResult::CounterexampleWitness{
      .badFrame = 1,
      .inputTrace = {{{0, {}}}},
      .outputMismatches = {{"ghost[0]", false, true}},
  };
  const auto noEnvTraceText = detail::formatCounterexampleWitnessForTest(
      noEnvTraceResult, {}, {}, nullptr, nullptr);
  EXPECT_NE(
      noEnvTraceText.find("<no environment inputs>"),
      std::string::npos);

  KInductionResult noMismatchTraceResult;
  noMismatchTraceResult.witness = KInductionResult::CounterexampleWitness{
      .badFrame = 1,
      .inputTrace = {{{0, {{"in[0]", true}}}}},
      .outputMismatches = {},
  };
  const auto noMismatchTraceText = detail::formatCounterexampleWitnessForTest(
      noMismatchTraceResult, {}, {}, nullptr, nullptr);
  EXPECT_EQ(
      noMismatchTraceText.find("Traceback for first differing point"),
      std::string::npos);
}

TEST_F(SequentialEquivalenceStrategyTests,
       SequentialEquivalenceStrategyDetailAlignmentAndLookupExposeErrors) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* primitives =
      NLLibrary::create(db, NLLibrary::Type::Primitives, NLName("prims"));
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* invModel = createInvModel(primitives);
  auto* top0 = createDffTop(library, "top0", invModel, false, false);
  auto* top1 = createDffTop(library, "top1", invModel, false, false);

  const auto model0 = SequentialDesignModel::extract(top0);
  const auto model1 = SequentialDesignModel::extract(top1);

  KInductionResult missingSignalResult;
  missingSignalResult.witness = KInductionResult::CounterexampleWitness{
      .badFrame = 1,
      .inputTrace = {{{0, {{"in[0]", true}}}}},
      .outputMismatches = {{"ghost[0]", false, true}},
  };
  const auto missingSignalText = detail::formatCounterexampleWitnessForTest(
      missingSignalResult, model0, model1, top0, top1);
  EXPECT_NE(
      missingSignalText.find("design0 could not resolve the differing SEC signal back into the DNL"),
      std::string::npos);
  EXPECT_NE(
      missingSignalText.find("design1 could not resolve the differing SEC signal back into the DNL"),
      std::string::npos);

  KInductionResult topInputTraceResult;
  topInputTraceResult.witness = KInductionResult::CounterexampleWitness{
      .badFrame = 1,
      .inputTrace = {{{0, {{"in[0]", true}}}}},
      .outputMismatches = {{"in[0]", false, true}},
  };
  const auto topInputTraceText = detail::formatCounterexampleWitnessForTest(
      topInputTraceResult, model0, model1, top0, top1);
  EXPECT_NE(
      topInputTraceText.find("Observed output mismatches at cycle 1:"),
      std::string::npos);

  const auto inputKey = makeSignalKey("in");
  const auto outputKey = makeSignalKey("out");
  std::unordered_map<SignalKey, std::string, SignalKeyHash> displayNames0 = {
      {inputKey, "in[0]"},
  };
  std::unordered_map<SignalKey, std::string, SignalKeyHash> displayNames1 = {
      {inputKey, "in[0]"},
  };

  EXPECT_THROW(
      detail::alignSignalsByNameForTest(
          {inputKey}, displayNames0, {outputKey}, displayNames1, "inputs"),
      std::runtime_error);
  EXPECT_THROW(
      detail::alignSignalsByNameForTest(
          {inputKey, inputKey}, displayNames0, {inputKey}, displayNames1, "inputs"),
      std::runtime_error);

  auto* universe = NLUniverse::get();
  ASSERT_NE(universe, nullptr);
  universe->setTopDesign(top0);
  auto* dnl = naja::DNL::get();
  ASSERT_NE(dnl, nullptr);

  std::optional<naja::DNL::DNLID> outTermID;
  for (naja::DNL::DNLID termID = 0; termID < dnl->getDNLTerms().size(); ++termID) {
    const auto& term = dnl->getDNLTerminalFromID(termID);
    if (term.isNull() || !term.isTopPort()) {
      continue;
    }
    if (term.getSnlBitTerm()->getName().getString() == "out") {
      outTermID = termID;
      break;
    }
  }
  ASSERT_TRUE(outTermID.has_value());
  const auto outKey = detail::getTerminalPathKeyForTest(
      dnl->getDNLTerminalFromID(*outTermID));
  EXPECT_EQ(detail::findTermByKeyForTest(dnl, outKey), outTermID);

  SignalKey missingKey = outKey;
  ++missingKey.first.front();
  EXPECT_FALSE(detail::findTermByKeyForTest(dnl, missingKey).has_value());
}
