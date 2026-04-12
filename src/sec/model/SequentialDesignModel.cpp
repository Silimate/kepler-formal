// Copyright 2024-2026 keplertech.io
// SPDX-License-Identifier: GPL-3.0-only

#include "model/SequentialDesignModel.h"

#include <algorithm>
#include <cctype>
#include <cstdio>
#include <cstdlib>
#include <deque>
#include <optional>
#include <sstream>
#include <set>
#include <stdexcept>
#include <unordered_set>
#include <unordered_map>

#include "DNL.h"
#include "NLUniverse.h"
#include "SNLDesignModeling.h"
#include "SNLPath.h"
#include "common/BoolExprUtils.h"
#include "../../strategies/miter/BuildPrimaryOutputClauses.h"

namespace KEPLER_FORMAL::SEC {

namespace {

using PendingPinMap = std::unordered_map<std::string, naja::DNL::DNLID>;

struct StateOutputTerm {
  naja::DNL::DNLID termID = naja::DNL::DNLID_MAX;
  std::string pinName;
};

struct PendingTransition {
  SignalKey stateKey;
  naja::DNL::DNLID stateTermID = naja::DNL::DNLID_MAX;
  std::vector<SignalKey> complementedStateKeys;
  PendingPinMap pinTermIDs;
};

SignalKey getTerminalPathKey(const naja::DNL::DNLTerminalFull& terminal) {
  SignalKey key;
  const auto pathNames = terminal.getDNLInstance().getPath().getPathNames();
  key.first.reserve(pathNames.size() + 1);
  for (const auto& name : pathNames) {
    key.first.push_back(stableSignalKeyNameID(name.getString()));
  }
  key.first.push_back(
      stableSignalKeyNameID(terminal.getSnlBitTerm()->getName().getString()));
  key.second.push_back(
      static_cast<naja::NL::NLID::DesignObjectID>(terminal.getSnlBitTerm()->getBit()));
  return key;
}

std::string getTerminalDisplayName(const naja::DNL::DNLTerminalFull& terminal) {
  std::ostringstream oss;
  const auto pathNames = terminal.getDNLInstance().getPath().getPathNames();
  for (const auto& name : pathNames) {
    oss << name.getString() << ".";
  }
  oss << terminal.getSnlBitTerm()->getName().getString() << "["
      << terminal.getSnlBitTerm()->getBit() << "]";
  return oss.str();
}

std::string normalizePinName(const std::string& name) {
  std::string normalized = name;
  for (char& ch : normalized) {
    ch = static_cast<char>(std::toupper(static_cast<unsigned char>(ch)));
  }
  return normalized;
}

bool hasSuffix(const std::string& value, const std::string& suffix) {
  return value.size() >= suffix.size() &&
         value.compare(value.size() - suffix.size(), suffix.size(), suffix) == 0;
}

std::string stripComplementSuffix(const std::string& pinName) {
  if (hasSuffix(pinName, "N") || hasSuffix(pinName, "B")) {
    return pinName.substr(0, pinName.size() - 1);
  }
  return pinName;
}

const StateOutputTerm* findPrimaryStateOutput(
    const std::vector<StateOutputTerm>& stateOutputs) {
  // Prefer the conventional non-inverted state output when Liberty gives us
  // both Q and QN/QB for the same storage element.
  for (const auto& stateOutput : stateOutputs) {
    if (stateOutput.pinName == "Q") {
      return &stateOutput;
    }
  }

  for (const auto& stateOutput : stateOutputs) {
    const std::string baseName = stripComplementSuffix(stateOutput.pinName);
    if (baseName != stateOutput.pinName) {
      continue;
    }
    for (const auto& candidate : stateOutputs) {
      if (candidate.termID == stateOutput.termID) {
        continue;
      }
      if (stripComplementSuffix(candidate.pinName) == stateOutput.pinName &&
          candidate.pinName != stateOutput.pinName) {
        return &stateOutput;
      }
    }
  }

  return nullptr;
}

bool isComplementedStateOutput(const std::string& primaryPinName,
                               const std::string& candidatePinName) {
  return candidatePinName != primaryPinName &&
         stripComplementSuffix(candidatePinName) == primaryPinName;
}

bool isSequentialStateOutput(const naja::DNL::DNLTerminalFull& term) {
  if (term.isTopPort()) {
    return false;
  }
  return !naja::NL::SNLDesignModeling::getOutputRelatedClocks(
              term.getSnlBitTerm())
              .empty();
}

bool isSequentialNextStateInput(const naja::DNL::DNLTerminalFull& term) {
  if (term.isTopPort()) {
    return false;
  }
  return !naja::NL::SNLDesignModeling::getInputRelatedClocks(
              term.getSnlBitTerm())
              .empty();
}

BoolExpr* getRequiredOutputExpr(
    const PendingTransition& pending,
    const char* pinName,
    const std::unordered_map<naja::DNL::DNLID, BoolExpr*>& outputExprByTerm) {
  auto it = pending.pinTermIDs.find(pinName);
  if (it == pending.pinTermIDs.end()) {
    return nullptr;
  }
  auto exprIt = outputExprByTerm.find(it->second);
  if (exprIt == outputExprByTerm.end()) {
    throw std::runtime_error("Missing combinational expression for sequential pin `" +
                             std::string(pinName) + "`");
  }
  return exprIt->second;
}

BoolExpr* buildNextStateExpr(
    const PendingTransition& pending,
    const std::vector<size_t>& termDNLID2varID,
    const std::unordered_map<naja::DNL::DNLID, BoolExpr*>& outputExprByTerm) {
  if (pending.stateTermID >= termDNLID2varID.size()) {
    throw std::runtime_error("Sequential state term is out of range");
  }

  const size_t stateVarID = termDNLID2varID[pending.stateTermID];
  if (stateVarID < 2) {
    throw std::runtime_error("Sequential state bit was mapped to a constant");
  }

  BoolExpr* data = getRequiredOutputExpr(pending, "D", outputExprByTerm);
  if (data == nullptr) {
    throw std::runtime_error("Unsupported sequential primitive without D input");
  }

  BoolExpr* current = BoolExpr::Var(stateVarID);
  BoolExpr* next = data;

  // Supported hold semantics: Q' = E ? D : Q.
  if (BoolExpr* enable = getRequiredOutputExpr(pending, "E", outputExprByTerm)) {
    next = BoolExpr::Or(
        BoolExpr::And(enable, data),
        BoolExpr::And(BoolExpr::Not(enable), current));
  }

  const BoolExpr* resetHigh =
      getRequiredOutputExpr(pending, "R", outputExprByTerm);
  const BoolExpr* resetLow =
      getRequiredOutputExpr(pending, "RN", outputExprByTerm);
  const BoolExpr* setHigh =
      getRequiredOutputExpr(pending, "S", outputExprByTerm);

  int controlKinds = 0;
  controlKinds += resetHigh != nullptr ? 1 : 0;
  controlKinds += resetLow != nullptr ? 1 : 0;
  controlKinds += setHigh != nullptr ? 1 : 0;
  if (controlKinds > 1) {
    throw std::runtime_error(
        "Unsupported sequential primitive with multiple control styles");
  }

  // Support one control style at a time and fail loudly on more complex cells
  // so we do not silently prove the wrong transition system.
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

std::optional<bool> detectInitialStateValue(const PendingTransition& pending) {
  const bool hasResetHigh = pending.pinTermIDs.find("R") != pending.pinTermIDs.end();
  const bool hasResetLow = pending.pinTermIDs.find("RN") != pending.pinTermIDs.end();
  const bool hasSetHigh = pending.pinTermIDs.find("S") != pending.pinTermIDs.end();

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

bool isConstBoolExpr(BoolExpr* expr, bool value) {
  return expr != nullptr && expr->getOp() == Op::VAR &&
         expr->getId() == static_cast<size_t>(value ? 1 : 0);
}

std::optional<bool> evaluateConstantUnderAssignments(
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
      const auto operand =
          evaluateConstantUnderAssignments(expr->getLeft(), assignments, memo);
      if (operand.has_value()) {
        value = !*operand;
      }
      break;
    }
    case Op::AND: {
      const auto lhs =
          evaluateConstantUnderAssignments(expr->getLeft(), assignments, memo);
      if (lhs.has_value() && !*lhs) {
        value = false;
        break;
      }
      const auto rhs =
          evaluateConstantUnderAssignments(expr->getRight(), assignments, memo);
      if (rhs.has_value() && !*rhs) {
        value = false;
      } else if (lhs.has_value() && rhs.has_value()) {
        value = *lhs && *rhs;
      }
      break;
    }
    case Op::OR: {
      const auto lhs =
          evaluateConstantUnderAssignments(expr->getLeft(), assignments, memo);
      if (lhs.has_value() && *lhs) {
        value = true;
        break;
      }
      const auto rhs =
          evaluateConstantUnderAssignments(expr->getRight(), assignments, memo);
      if (rhs.has_value() && *rhs) {
        value = true;
      } else if (lhs.has_value() && rhs.has_value()) {
        value = *lhs || *rhs;
      }
      break;
    }
    case Op::XOR: {
      const auto lhs =
          evaluateConstantUnderAssignments(expr->getLeft(), assignments, memo);
      const auto rhs =
          evaluateConstantUnderAssignments(expr->getRight(), assignments, memo);
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

std::string normalizeSignalBaseName(const std::string& name) {
  std::string base = name;
  const auto bracket = base.find('[');
  if (bracket != std::string::npos) {
    base = base.substr(0, bracket);
  }
  return normalizePinName(base);
}

std::optional<bool> getResetAssertionValue(const std::string& displayName) {
  const std::string normalized = normalizeSignalBaseName(displayName);
  if (normalized == "RESET" || normalized == "RST") {
    return true;
  }
  if (normalized == "RESET_N" || normalized == "RESETN" ||
      normalized == "RST_N" || normalized == "RSTN") {
    return false;
  }
  return std::nullopt;
}

std::unordered_map<size_t, bool> collectResetAssignments(
    const SequentialDesignModel& model) {
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

void inferSynthesizedResetInitialStateValues(SequentialDesignModel& model) {
  const auto resetAssignments = collectResetAssignments(model);
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
  constexpr size_t kMaxResetSpecializedExprNodesForInitInference = 200000;
  const size_t resetSpecializedExprNodes =
      countUniqueExprNodes(resetSpecializedNextStateByKey);
  if (resetSpecializedExprNodes >
      kMaxResetSpecializedExprNodesForInitInference) {
    if (std::getenv("KEPLER_SEC_DIAG") != nullptr) {
      fprintf(
          stderr,
          "SEC diag: skip synthesized init inference for %zu reset-specialized nodes (limit=%zu)\n",
          resetSpecializedExprNodes,
          kMaxResetSpecializedExprNodesForInitInference);
      fflush(stderr);
    }
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
    const auto resetValue = evaluateConstantUnderAssignments(
        nextStateIt->second, assignments, memo);
    if (resetValue.has_value()) {
      recordKnownState(key, *resetValue);
    }
  }
}

}  // namespace

SequentialDesignModel SequentialDesignModel::extract(naja::NL::SNLDesign* top) {
  if (top == nullptr) {
    throw std::invalid_argument("SequentialDesignModel::extract: null top");
  }

  auto* universe = naja::NL::NLUniverse::get();
  if (universe == nullptr) {
    throw std::runtime_error("SequentialDesignModel::extract: NLUniverse not created");
  }

  SequentialDesignModel model;
  auto* previousTop = universe->getTopDesign();
  const bool secDiagEnabled = std::getenv("KEPLER_SEC_DIAG") != nullptr;

  naja::DNL::destroy();
  universe->setTopDesign(top);

  KEPLER_FORMAL::BuildPrimaryOutputClauses builder;
  // Reuse the existing miter frontend to discover the relevant boundary
  // signals before we ask it to build Boolean formulas.
  if (secDiagEnabled) {
    fprintf(
        stderr, "SEC diag: extract(%s) collect begin\n",
        top->getName().getString().c_str());
    fflush(stderr);
  }
  builder.collect();
  if (secDiagEnabled) {
    fprintf(
        stderr,
        "SEC diag: extract(%s) collect end inputs=%zu outputs=%zu\n",
        top->getName().getString().c_str(),
        builder.getInputs().size(),
        builder.getOutputs().size());
    fflush(stderr);
  }

  auto* dnl = naja::DNL::get();
  std::unordered_map<naja::DNL::DNLID, SignalKey> inputKeyByTerm;
  std::unordered_map<naja::DNL::DNLID, SignalKey> outputKeyByTerm;
  std::set<SignalKey, SignalKeyLess> environmentInputs;
  std::set<SignalKey, SignalKeyLess> stateBits;
  std::set<SignalKey, SignalKeyLess> observedOutputs;
  std::vector<PendingTransition> pendingTransitions;

  // The miter builder already exposes sequential outputs as "inputs" and
  // sequential next-state pins as "outputs"; we normalize those into SEC's
  // environment/state/output buckets here.
  for (const auto inputTermID : builder.getInputs()) {
    const auto& term = dnl->getDNLTerminalFromID(inputTermID);
    SignalKey key = getTerminalPathKey(term);
    inputKeyByTerm.emplace(inputTermID, key);
    model.displayNameByKey.try_emplace(key, getTerminalDisplayName(term));
    if (isSequentialStateOutput(term)) {
      stateBits.insert(key);
    } else {
      environmentInputs.insert(key);
    }
  }

  for (const auto outputTermID : builder.getOutputs()) {
    const auto& term = dnl->getDNLTerminalFromID(outputTermID);
    SignalKey key = getTerminalPathKey(term);
    outputKeyByTerm.emplace(outputTermID, key);
    model.displayNameByKey.try_emplace(key, getTerminalDisplayName(term));
    if (term.isTopPort()) {
      observedOutputs.insert(key);
    }
  }

  // Record enough pin information to reconstruct Q' after the combinational
  // Boolean expressions have been built.
  for (auto leafID : dnl->getLeaves()) {
    const auto& instance = dnl->getDNLInstanceFromID(leafID);
    if (!naja::NL::SNLDesignModeling::isSequential(instance.getSNLModel())) {
      continue;
    }

    PendingTransition pending;
    std::vector<StateOutputTerm> stateOutputs;
    for (naja::DNL::DNLID termID = instance.getTermIndexes().first;
         termID != naja::DNL::DNLID_MAX &&
         termID <= instance.getTermIndexes().second;
         ++termID) {
      const auto& term = dnl->getDNLTerminalFromID(termID);
      if (isSequentialStateOutput(term) &&
          term.getSnlBitTerm()->getDirection() !=
              naja::NL::SNLBitTerm::Direction::Input) {
        stateOutputs.push_back(
            {termID, normalizePinName(term.getSnlBitTerm()->getName().getString())});
      }
      if (isSequentialNextStateInput(term) &&
          term.getSnlBitTerm()->getDirection() !=
              naja::NL::SNLBitTerm::Direction::Output) {
        pending.pinTermIDs.emplace(
            normalizePinName(term.getSnlBitTerm()->getName().getString()),
            termID);
      }
    }

    if (stateOutputs.empty()) {
      continue;
    }

    const StateOutputTerm* primaryStateOutput =
        stateOutputs.size() == 1 ? &stateOutputs.front()
                                 : findPrimaryStateOutput(stateOutputs);
    if (primaryStateOutput == nullptr) {
      model.unsupportedReasons.push_back(
          "Unsupported sequential primitive with multiple state outputs in `" +
          instance.getSNLModel()->getName().getString() + "`");
      continue;
    }

    pending.stateTermID = primaryStateOutput->termID;
    pending.stateKey = inputKeyByTerm.at(pending.stateTermID);
    std::vector<ComplementedStateRelation> complementedRelations;
    // Accept the common "one storage bit, multiple observable outputs" Liberty
    // pattern and record which outputs are just inverted views of the primary
    // state bit.
    for (const auto& stateOutput : stateOutputs) {
      if (stateOutput.termID == pending.stateTermID) {
        continue;
      }
      if (!isComplementedStateOutput(
              primaryStateOutput->pinName, stateOutput.pinName)) {
        model.unsupportedReasons.push_back(
            "Unsupported sequential primitive with multiple state outputs in `" +
            instance.getSNLModel()->getName().getString() + "`");
        pending.stateTermID = naja::DNL::DNLID_MAX;
        break;
      }
      const SignalKey complementedKey = inputKeyByTerm.at(stateOutput.termID);
      pending.complementedStateKeys.push_back(complementedKey);
      complementedRelations.push_back({pending.stateKey, complementedKey});
    }
    if (pending.stateTermID == naja::DNL::DNLID_MAX) {
      continue;
    }
    model.complementedStateRelations.insert(
        model.complementedStateRelations.end(),
        complementedRelations.begin(),
        complementedRelations.end());
    pendingTransitions.push_back(std::move(pending));
  }

  // Materialize the combinational BoolExpr DAGs for the design boundary.
  if (secDiagEnabled) {
    fprintf(
        stderr, "SEC diag: extract(%s) build begin\n",
        top->getName().getString().c_str());
    fflush(stderr);
  }
  builder.build();
  if (secDiagEnabled) {
    fprintf(
        stderr, "SEC diag: extract(%s) build end\n",
        top->getName().getString().c_str());
    fflush(stderr);
  }

  model.environmentInputs.assign(environmentInputs.begin(), environmentInputs.end());
  model.stateBits.assign(stateBits.begin(), stateBits.end());
  model.observedOutputs.assign(observedOutputs.begin(), observedOutputs.end());
  if (secDiagEnabled) {
    fprintf(
        stderr,
        "SEC diag: extract(%s) boundary normalized env=%zu state=%zu outputs=%zu pending=%zu\n",
        top->getName().getString().c_str(),
        model.environmentInputs.size(),
        model.stateBits.size(),
        model.observedOutputs.size(),
        pendingTransitions.size());
    fflush(stderr);
  }

  const auto& termDNLID2varID = builder.getTermDNLID2VarID();
  // Preserve the symbolic variable chosen by the clause builder for each
  // aligned SEC input/state signal.
  for (const auto inputTermID : builder.getInputs()) {
    const auto keyIt = inputKeyByTerm.find(inputTermID);
    if (keyIt == inputKeyByTerm.end()) {
      continue;
    }
    if (inputTermID >= termDNLID2varID.size()) {
      continue;
    }
    const size_t varID = termDNLID2varID[inputTermID];
      if (varID < 2) {
        continue;
      }
      model.inputVarByKey.emplace(keyIt->second, varID);
  }
  if (secDiagEnabled) {
    fprintf(
        stderr,
        "SEC diag: extract(%s) mapped boundary vars=%zu\n",
        top->getName().getString().c_str(),
        model.inputVarByKey.size());
    fflush(stderr);
  }

  std::unordered_map<naja::DNL::DNLID, BoolExpr*> outputExprByTerm;
  const auto& outputTerms = builder.getOutputs();
  const auto& outputExprs = builder.getPOs();
  // Keep only the formulas that correspond to observed top-level outputs.
  for (size_t i = 0; i < outputTerms.size(); ++i) {
    outputExprByTerm.emplace(outputTerms[i], outputExprs[i]);
    const auto keyIt = outputKeyByTerm.find(outputTerms[i]);
    if (keyIt != outputKeyByTerm.end() &&
        observedOutputs.find(keyIt->second) != observedOutputs.end()) {
      model.observedOutputExprByKey.emplace(keyIt->second, outputExprs[i]);
    }
  }
  if (secDiagEnabled) {
    fprintf(
        stderr,
        "SEC diag: extract(%s) materialized output exprs observed=%zu total=%zu\n",
        top->getName().getString().c_str(),
        model.observedOutputExprByKey.size(),
        outputExprByTerm.size());
    fflush(stderr);
  }

  // Rebuild next-state equations for the supported sequential cells.
  for (const auto& pending : pendingTransitions) {
    try {
      const auto initialStateValue = detectInitialStateValue(pending);
      if (initialStateValue.has_value()) {
        model.initialStateValueByKey.emplace(pending.stateKey, *initialStateValue);
        for (const auto& complementedKey : pending.complementedStateKeys) {
          model.initialStateValueByKey.emplace(complementedKey, !*initialStateValue);
        }
      }

      BoolExpr* nextStateExpr =
          buildNextStateExpr(pending, termDNLID2varID, outputExprByTerm);
      model.nextStateExprByStateKey.emplace(pending.stateKey, nextStateExpr);
      // Liberty flops such as DFF_X1 expose both Q and QN. They share one
      // storage element, so complementary outputs inherit the same next-state
      // function with a logical inversion.
      for (const auto& complementedKey : pending.complementedStateKeys) {
        model.nextStateExprByStateKey.emplace(
            complementedKey,
            BoolExpr::Not(nextStateExpr));
      }
    } catch (const std::exception& e) {
      model.unsupportedReasons.push_back(
          "Unsupported sequential primitive for `" +
          signalKeyToString(pending.stateKey) + "`: " + e.what());
    }
  }
  if (secDiagEnabled) {
    fprintf(
        stderr,
        "SEC diag: extract(%s) rebuilt next-state exprs=%zu init=%zu\n",
        top->getName().getString().c_str(),
        model.nextStateExprByStateKey.size(),
        model.initialStateValueByKey.size());
    fflush(stderr);
  }

  // Inputs or state bits can disappear if the underlying BoolExpr builder
  // optimized them away to constants; remove them from the aligned interface.
  auto keepMappedInputs = [&](std::vector<SignalKey>& keys) {
    keys.erase(
        std::remove_if(
            keys.begin(),
            keys.end(),
            [&](const SignalKey& key) {
              return model.inputVarByKey.find(key) == model.inputVarByKey.end();
            }),
        keys.end());
  };
  keepMappedInputs(model.environmentInputs);
  keepMappedInputs(model.stateBits);
  if (secDiagEnabled) {
    fprintf(
        stderr,
        "SEC diag: extract(%s) filtered env=%zu state=%zu\n",
        top->getName().getString().c_str(),
        model.environmentInputs.size(),
        model.stateBits.size());
    fflush(stderr);
  }

  inferSynthesizedResetInitialStateValues(model);
  if (secDiagEnabled) {
    fprintf(
        stderr,
        "SEC diag: extract(%s) synthesized init inference done init=%zu\n",
        top->getName().getString().c_str(),
        model.initialStateValueByKey.size());
    fflush(stderr);
  }

  // Missing formulas mean we do not have a sound SEC model, so report the
  // design as unsupported instead of continuing with partial information.
  for (const auto& key : model.observedOutputs) {
    if (model.observedOutputExprByKey.find(key) == model.observedOutputExprByKey.end()) {
      model.unsupportedReasons.push_back(
          "Missing observed output expression for `" + signalKeyToString(key) + "`");
    }
  }
  for (const auto& key : model.stateBits) {
    if (model.nextStateExprByStateKey.find(key) == model.nextStateExprByStateKey.end()) {
      model.unsupportedReasons.push_back(
          "Missing next-state relation for `" + signalKeyToString(key) + "`");
    }
  }

  // Restore the original top design for callers that keep using the universe.
  if (previousTop != nullptr) {
    universe->setTopDesign(previousTop);
  }
  if (secDiagEnabled) {
    fprintf(stderr, "SEC diag: extract(%s) end\n", top->getName().getString().c_str());
    fflush(stderr);
  }

  return model;
}

namespace detail {

// Keep the branch-heavy sequential extraction helpers directly testable without
// changing the production SEC flow.
BoolExpr* buildNextStateExprForTest(
    size_t stateTermID,
    const std::unordered_map<std::string, naja::DNL::DNLID>& pinTermIDs,
    const std::vector<size_t>& termDNLID2varID,
    const std::unordered_map<naja::DNL::DNLID, BoolExpr*>& outputExprByTerm) {
  PendingTransition pending;
  pending.stateTermID = stateTermID;
  pending.pinTermIDs = pinTermIDs;
  return buildNextStateExpr(pending, termDNLID2varID, outputExprByTerm);
}

std::optional<bool> detectInitialStateValueForTest(
    const std::unordered_map<std::string, naja::DNL::DNLID>& pinTermIDs) {
  PendingTransition pending;
  pending.pinTermIDs = pinTermIDs;
  return detectInitialStateValue(pending);
}

std::optional<bool> evaluateConstantUnderAssignmentsForTest(
    BoolExpr* expr,
    const std::unordered_map<size_t, bool>& assignments) {
  std::unordered_map<BoolExpr*, std::optional<bool>> memo;
  return evaluateConstantUnderAssignments(expr, assignments, memo);
}

void inferSynthesizedResetInitialStateValuesForTest(SequentialDesignModel& model) {
  inferSynthesizedResetInitialStateValues(model);
}

std::optional<bool> getResetAssertionValueForTest(const std::string& displayName) {
  return getResetAssertionValue(displayName);
}

}  // namespace detail

}  // namespace KEPLER_FORMAL::SEC
