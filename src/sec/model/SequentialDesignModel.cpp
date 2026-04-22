// Copyright 2024-2026 keplertech.io
// SPDX-License-Identifier: GPL-3.0-only

#include "model/SequentialDesignModel.h"

#include <algorithm>
#include <cctype>
#include <cstdio>
#include <cstdlib>
#include <deque>
#include <limits>
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
#include "../../clauses/SNLLogicCloud.h"
#include "../../clauses/Tree2BoolExpr.h"
#include "../../config/Config.h"
#include "common/BoolExprUtils.h"
#include "../../strategies/miter/BuildPrimaryOutputClauses.h"

namespace KEPLER_FORMAL::SEC {

namespace {

struct PendingPinTerm {
  naja::DNL::DNLID termID = naja::DNL::DNLID_MAX;
  naja::NL::NLID::Bit bit = 0;
};

using PendingPinMap =
    std::unordered_map<std::string, std::vector<PendingPinTerm>>;

struct StateOutputTerm {
  naja::DNL::DNLID termID = naja::DNL::DNLID_MAX;
  std::string pinName;
  naja::NL::NLID::Bit bit = 0;
};

struct PendingTransition {
  SignalKey stateKey;
  naja::DNL::DNLID stateTermID = naja::DNL::DNLID_MAX;
  std::string statePinName;
  naja::NL::NLID::Bit stateBit = 0;
  size_t independentStateOutputCount = 0;
  size_t boundaryInfoIndex = std::numeric_limits<size_t>::max();
  std::vector<SignalKey> complementedStateKeys;
  PendingPinMap pinTermIDs;
};

struct BoundaryObservedTerm {
  naja::DNL::DNLID termID = naja::DNL::DNLID_MAX;
  SignalKey key;
};

struct InstanceBoundaryInfo {
  std::string instancePath;
  std::vector<SignalKey> stateKeys;
  std::vector<BoundaryObservedTerm> observedTerms;
};

struct BuiltObservedExpr {
  BoolExpr* expr = nullptr;
  std::optional<ConnectivitySkipInfo> connectivitySkip;
  std::string unsupportedReason;
};

using BuilderSkippedOutputInfo = KEPLER_FORMAL::BuildPrimaryOutputClauses::SkippedOutputInfo;
using BuilderSkippedOutputReason =
    KEPLER_FORMAL::BuildPrimaryOutputClauses::SkippedOutputReason;

std::string describeConnectivitySkipOrigin(ConnectivitySkipOrigin origin) {
  switch (origin) {
    case ConnectivitySkipOrigin::NoDriver:
      return "no-driver";
    case ConnectivitySkipOrigin::MultiDriver:
      return "multi-driver";
  }
  return "connectivity";  // LCOV_EXCL_LINE
}

std::optional<ConnectivitySkipInfo> getConnectivitySkipInfo(
    const BuilderSkippedOutputInfo& info) {
  switch (info.reason) {
    case BuilderSkippedOutputReason::NoDriver:
      return ConnectivitySkipInfo{ConnectivitySkipOrigin::NoDriver, info.detail};
    case BuilderSkippedOutputReason::MultiDriver:
      return ConnectivitySkipInfo{ConnectivitySkipOrigin::MultiDriver, info.detail};
    case BuilderSkippedOutputReason::LogicalLoop:
    case BuilderSkippedOutputReason::None:
    default:
      return std::nullopt;
  }
}

BuiltObservedExpr buildObservedExprForTerm(
    naja::DNL::DNLID termID,
    const std::unordered_map<naja::DNL::DNLID, BoolExpr*>& outputExprByTerm,
    const std::vector<naja::DNL::DNLID>& inputTerms,
    const std::vector<naja::DNL::DNLID>& outputTerms,
    const std::vector<size_t>& termDNLID2varID) {
  BuiltObservedExpr result;
  if (const auto exprIt = outputExprByTerm.find(termID);
      exprIt != outputExprByTerm.end()) {
    result.expr = exprIt->second;
    return result;
  }

  auto* dnl = naja::DNL::get();
  if (dnl == nullptr) {
    result.unsupportedReason = "DNL is not available while rebuilding a SEC boundary";
    return result;
  }

  std::vector<bool> isPIs(dnl->getNBterms(), false);
  for (const auto inputTermID : inputTerms) {
    if (inputTermID < isPIs.size()) {
      isPIs[inputTermID] = true;
    }
  }

  std::vector<bool> isPOs(dnl->getNBterms(), false);
  for (const auto outputTermID : outputTerms) {
    if (outputTermID < isPOs.size()) {
      isPOs[outputTermID] = true;
    }
  }
  auto describeTerm = [&](const naja::DNL::DNLTerminalFull& term) {
    return term.getSnlBitTerm()->getDesign()->getName().getString() + "." +
           term.getSnlBitTerm()->getName().getString() + "[" +
           std::to_string(term.getSnlBitTerm()->getBit()) + "]";
  };

  auto buildFromOutputTerm = [&](naja::DNL::DNLID outputTermID) {
    BuiltObservedExpr localResult;
    auto localIsPOs = isPOs;
    if (outputTermID < localIsPOs.size()) {
      localIsPOs[outputTermID] = true;
    }
    KEPLER_FORMAL::SNLLogicCloud cloud(outputTermID, isPIs, localIsPOs);
    cloud.compute();
    if (cloud.getTruthTable().isValid()) {
      cloud.getTruthTable().finalize();
      localResult.expr =
          KEPLER_FORMAL::Tree2BoolExpr::convert(cloud.getTruthTable(), termDNLID2varID);
      cloud.destroy();
      return localResult;
    }

    switch (cloud.getSkipReason()) {
      case KEPLER_FORMAL::SNLLogicCloud::SkipReason::NoDriver:
        localResult.connectivitySkip = ConnectivitySkipInfo{
            ConnectivitySkipOrigin::NoDriver, cloud.getSkipReasonText()};
        break;
      case KEPLER_FORMAL::SNLLogicCloud::SkipReason::MultiDriver:
        localResult.connectivitySkip = ConnectivitySkipInfo{
            ConnectivitySkipOrigin::MultiDriver, cloud.getSkipReasonText()};
        break;
      case KEPLER_FORMAL::SNLLogicCloud::SkipReason::LogicalLoop:
        localResult.unsupportedReason =
            "logical loop: " + cloud.getSkipReasonText();
        break;
      case KEPLER_FORMAL::SNLLogicCloud::SkipReason::None:
      default:
        localResult.unsupportedReason = "failed to build a Boolean expression";
        break;
    }
    cloud.destroy();
    return localResult;
  };

  std::unordered_set<naja::DNL::DNLID> visitedTerms;
  auto buildRecursively = [&](auto&& self,
                              naja::DNL::DNLID currentTermID) -> BuiltObservedExpr {
    BuiltObservedExpr localResult;
    if (!visitedTerms.insert(currentTermID).second) {
      localResult.unsupportedReason =
          "logical loop while rebuilding a SEC boundary";
      return localResult;
    }

    if (const auto exprIt = outputExprByTerm.find(currentTermID);
        exprIt != outputExprByTerm.end()) {
      localResult.expr = exprIt->second;
      return localResult;
    }

    if (currentTermID < termDNLID2varID.size() && isPIs[currentTermID]) {
      const size_t varID = termDNLID2varID[currentTermID];
      if (varID == 0) {
        localResult.expr = BoolExpr::createFalse();
        return localResult;
      }
      if (varID == 1) {
        localResult.expr = BoolExpr::createTrue();
        return localResult;
      }
      if (varID >= 2) {
        localResult.expr = BoolExpr::Var(varID);
        return localResult;
      }
    }

    const auto& term = dnl->getDNLTerminalFromID(currentTermID);
    if (term.getSnlBitTerm()->getDirection() !=
        naja::NL::SNLBitTerm::Direction::Output) {
      if (term.getIsoID() == naja::DNL::DNLID_MAX) {
        localResult.connectivitySkip = ConnectivitySkipInfo{
            ConnectivitySkipOrigin::NoDriver,
            "term `" + describeTerm(term) + "` is not connected"};
        return localResult;
      }

      const auto& iso = dnl->getDNLIsoDB().getIsoFromIsoIDconst(term.getIsoID());
      if (iso.isConstant0()) {
        localResult.expr = BoolExpr::createFalse();
        return localResult;
      }
      if (iso.isConstant1()) {
        localResult.expr = BoolExpr::createTrue();
        return localResult;
      }
      if (iso.getDrivers().empty()) {
        localResult.connectivitySkip = ConnectivitySkipInfo{
            ConnectivitySkipOrigin::NoDriver,
            "term `" + describeTerm(term) + "` has no drivers"};
        return localResult;
      }
      if (iso.getDrivers().size() > 1) {
        localResult.connectivitySkip = ConnectivitySkipInfo{
            ConnectivitySkipOrigin::MultiDriver,
            "term `" + describeTerm(term) + "` has multiple drivers"};
        return localResult;
      }
      return self(self, iso.getDrivers().front());
    }

    return buildFromOutputTerm(currentTermID);
  };

  return buildRecursively(buildRecursively, termID);
}

std::unordered_set<naja::DNL::DNLID> collectRequiredSequentialOutputTerms(
    const std::vector<PendingTransition>& pendingTransitions) {
  std::unordered_set<naja::DNL::DNLID> requiredTerms;
  for (const auto& pending : pendingTransitions) {
    for (const auto& [_, candidates] : pending.pinTermIDs) {
      for (const auto& candidate : candidates) {
        requiredTerms.insert(candidate.termID);
      }
    }
  }
  return requiredTerms;
}

std::vector<naja::DNL::DNLID> selectRequiredBuilderOutputs(
    const std::vector<naja::DNL::DNLID>& collectedOutputs,
    const std::unordered_set<naja::DNL::DNLID>& topOutputTerms,
    const std::unordered_set<naja::DNL::DNLID>& sequentialDependencyTerms,
    const std::unordered_set<naja::DNL::DNLID>& prunedBuilderOutputTerms) {
  std::vector<naja::DNL::DNLID> filteredOutputs;
  filteredOutputs.reserve(collectedOutputs.size());

  // Only materialize formulas that SEC will consume: user-visible outputs and
  // the update/control terms required to reconstruct supported sequentials.
  for (const auto outputTermID : collectedOutputs) {
    if (prunedBuilderOutputTerms.find(outputTermID) !=
        prunedBuilderOutputTerms.end()) {
      continue;
    }
    if (topOutputTerms.find(outputTermID) != topOutputTerms.end() ||
        sequentialDependencyTerms.find(outputTermID) !=
            sequentialDependencyTerms.end()) {
      filteredOutputs.push_back(outputTermID);
    }
  }

  return filteredOutputs;
}

struct MaterializedBuilderOutputs {
  std::vector<naja::DNL::DNLID> inputs;
  std::vector<naja::DNL::DNLID> outputs;
  std::vector<size_t> termDNLID2varID;
  std::unordered_map<naja::DNL::DNLID, BoolExpr*> outputExprByTerm;
  std::unordered_map<naja::DNL::DNLID, BuilderSkippedOutputInfo> skippedOutputsByTerm;
};

MaterializedBuilderOutputs materializeBuilderOutputs(
    const std::vector<naja::DNL::DNLID>& requestedOutputs,
    bool secDiagEnabled,
    const char* topName,
    const char* phaseLabel) {
  MaterializedBuilderOutputs result;

  KEPLER_FORMAL::BuildPrimaryOutputClauses builder;
  builder.collect();
  std::unordered_set<naja::DNL::DNLID> collectedOutputSet(
      builder.getOutputs().begin(), builder.getOutputs().end());
  std::vector<naja::DNL::DNLID> filteredOutputs;
  filteredOutputs.reserve(requestedOutputs.size());
  for (const auto outputTermID : requestedOutputs) {
    if (collectedOutputSet.find(outputTermID) != collectedOutputSet.end()) {
      filteredOutputs.push_back(outputTermID);
    }
  }
  builder.setOutputs(filteredOutputs);

  if (secDiagEnabled) {
    fprintf(
        stderr,
        "SEC diag: extract(%s) %s begin outputs=%zu\n",
        topName,
        phaseLabel,
        filteredOutputs.size());
    fflush(stderr);
  }
  builder.build();
  if (secDiagEnabled) {
    fprintf(
        stderr,
        "SEC diag: extract(%s) %s end outputs=%zu\n",
        topName,
        phaseLabel,
        filteredOutputs.size());
    fflush(stderr);
  }

  result.inputs = builder.getInputs();
  result.outputs = builder.getOutputs();
  result.termDNLID2varID = builder.getTermDNLID2VarID();
  result.skippedOutputsByTerm = builder.getSkippedOutputs();
  const auto& outputExprs = builder.getPOs();
  for (size_t i = 0; i < result.outputs.size(); ++i) {
    BoolExpr* expr = outputExprs[i];
    if (expr == nullptr || !expr->isValid()) {
      continue;
    }
    result.outputExprByTerm.emplace(result.outputs[i], expr);
  }

  return result;
}

std::optional<size_t> findSkippedStateDependency(
    BoolExpr* expr,
    const std::unordered_set<size_t>& skippedStateVars,
    std::unordered_map<BoolExpr*, std::optional<size_t>>& memo) {
  if (expr == nullptr || !expr->isValid()) {
    return std::nullopt;
  }

  if (auto it = memo.find(expr); it != memo.end()) {
    return it->second;
  }

  std::optional<size_t> dependency;
  switch (expr->getOp()) {
    case Op::VAR:
      if (expr->getId() >= 2 && skippedStateVars.find(expr->getId()) != skippedStateVars.end()) {
        dependency = expr->getId();
      }
      break;
    case Op::NOT:
      dependency =
          findSkippedStateDependency(expr->getLeft(), skippedStateVars, memo);
      break;
    case Op::AND:
    case Op::OR:
    case Op::XOR:
      dependency =
          findSkippedStateDependency(expr->getLeft(), skippedStateVars, memo);
      if (!dependency.has_value()) {
        dependency = findSkippedStateDependency(
            expr->getRight(), skippedStateVars, memo);
      }
      break;
    case Op::NONE:
    default:
      break;
  }

  memo.emplace(expr, dependency);
  return dependency;
}

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

bool isComplementedStateOutput(const std::string& primaryPinName,
                               const std::string& candidatePinName) {
  return candidatePinName != primaryPinName &&
         stripComplementSuffix(candidatePinName) == primaryPinName;
}

const StateOutputTerm* findComplementedPrimaryStateOutput(
    const StateOutputTerm& stateOutput,
    const std::vector<StateOutputTerm>& stateOutputs) {
  const std::string baseName = stripComplementSuffix(stateOutput.pinName);
  if (baseName == stateOutput.pinName) {
    return nullptr;
  }

  for (const auto& candidate : stateOutputs) {
    if (candidate.termID == stateOutput.termID || candidate.bit != stateOutput.bit) {
      continue;
    }
    if (candidate.pinName == baseName) {
      return &candidate;
    }
  }
  return nullptr;
}

size_t countIndependentStateOutputs(
    const std::vector<StateOutputTerm>& stateOutputs) {
  size_t count = 0;
  for (const auto& stateOutput : stateOutputs) {
    if (findComplementedPrimaryStateOutput(stateOutput, stateOutputs) != nullptr) {
      continue;
    }
    ++count;
  }
  return count;
}

std::optional<naja::DNL::DNLID> resolvePendingPinTermID(
    const PendingTransition& pending,
    const char* pinName) {
  const auto pinIt = pending.pinTermIDs.find(pinName);
  if (pinIt == pending.pinTermIDs.end()) {
    return std::nullopt;
  }

  const auto& candidates = pinIt->second;
  if (candidates.empty()) {
    return std::nullopt;
  }

  // Multi-bit sequential primitives must resolve update pins against the same
  // bit index as the current state output. This keeps vector flops aligned per
  // state term instead of collapsing the whole instance down to one pin map.
  if (candidates.size() > 1) {
    for (const auto& candidate : candidates) {
      if (candidate.bit == pending.stateBit) {
        return candidate.termID;
      }
    }
    throw std::runtime_error(
        "Missing bit-matched sequential pin `" + std::string(pinName) +
        "` for output `" + pending.statePinName + "[" +
        std::to_string(pending.stateBit) + "]`");
  }

  const bool isDataPin = std::string(pinName) == "D";
  if (isDataPin && pending.independentStateOutputCount > 1) {
    throw std::runtime_error(
        "Shared scalar D input cannot define multiple independent state outputs");
  }

  return candidates.front().termID;
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

bool isOptionalSequentialControlPin(const std::string& pinName) {
  return pinName == "E" || pinName == "R" || pinName == "RN" || pinName == "S";
}

bool isSupportedSequentialUpdatePin(const std::string& pinName) {
  return pinName == "D" || isOptionalSequentialControlPin(pinName);
}

BoolExpr* getRequiredOutputExpr(
    const PendingTransition& pending,
    const char* pinName,
    const std::unordered_map<naja::DNL::DNLID, BoolExpr*>& outputExprByTerm) {
  const auto resolvedTermID = resolvePendingPinTermID(pending, pinName);
  if (!resolvedTermID.has_value()) {
    return nullptr;
  }
  auto exprIt = outputExprByTerm.find(*resolvedTermID);
  if (exprIt == outputExprByTerm.end()) {
    throw std::runtime_error("Missing combinational expression for sequential pin `" +
                             std::string(pinName) + "`");
  }
  return exprIt->second;
}

void validatePendingTransitionShape(const PendingTransition& pending) {
  if (!resolvePendingPinTermID(pending, "D").has_value()) {
    throw std::runtime_error("Unsupported sequential primitive without D input");
  }

  for (const auto& [pinName, _] : pending.pinTermIDs) {
    if (!isSupportedSequentialUpdatePin(pinName)) {
      throw std::runtime_error(
          "Unsupported sequential primitive with update pin `" + pinName + "`");
    }
  }

  int controlKinds = 0;
  controlKinds += resolvePendingPinTermID(pending, "R").has_value() ? 1 : 0;
  controlKinds += resolvePendingPinTermID(pending, "RN").has_value() ? 1 : 0;
  controlKinds += resolvePendingPinTermID(pending, "S").has_value() ? 1 : 0;
  if (controlKinds > 1) {
    throw std::runtime_error(
        "Unsupported sequential primitive with multiple control styles");
  }
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
  const bool hasResetHigh = resolvePendingPinTermID(pending, "R").has_value();
  const bool hasResetLow = resolvePendingPinTermID(pending, "RN").has_value();
  const bool hasSetHigh = resolvePendingPinTermID(pending, "S").has_value();

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
  // Synthesized reset inference is only a proof-strengthening heuristic. Cap
  // the specialized DAG size aggressively so large SoCs do not spend most of
  // SEC extraction time trying to derive explicit reset values for every
  // register when the proof can proceed without them.
  constexpr size_t kMaxResetSpecializedExprNodesForInitInference = 50000;
  const size_t resetSpecializedExprNodes =
      countUniqueExprNodes(resetSpecializedNextStateByKey);
  if (std::getenv("KEPLER_SEC_DIAG") != nullptr) {
    fprintf(
        stderr,
        "SEC diag: reset-specialized next-state nodes=%zu limit=%zu states=%zu\n",
        resetSpecializedExprNodes,
        kMaxResetSpecializedExprNodesForInitInference,
        model.stateBits.size());
    fflush(stderr);
  }
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
  std::unordered_map<naja::DNL::DNLID, SignalKey> topOutputKeyByTerm;
  std::set<SignalKey, SignalKeyLess> environmentInputs;
  std::set<SignalKey, SignalKeyLess> stateBits;
  std::set<SignalKey, SignalKeyLess> allObservedOutputs;
  std::unordered_set<naja::DNL::DNLID> prunedBuilderOutputTerms;
  std::set<SignalKey, SignalKeyLess> abstractedBoundaryStateKeys;
  std::vector<std::pair<naja::DNL::DNLID, SignalKey>> abstractedBoundaryObservedTerms;
  std::unordered_set<SignalKey, SignalKeyHash> abstractedBoundaryObservedKeys;
  std::unordered_set<SignalKey, SignalKeyHash> unsupportedStateBits;
  std::vector<PendingTransition> pendingTransitions;
  std::vector<InstanceBoundaryInfo> instanceBoundaryInfos;
  const bool abstractUncomputableSequentialBoundaries =
      KEPLER_FORMAL::Config::getSecTreatUncomputableSeqAsBoundary();

  const auto topInstance = dnl->getTop();
  for (naja::DNL::DNLID termID = topInstance.getTermIndexes().first;
       termID != naja::DNL::DNLID_MAX && termID <= topInstance.getTermIndexes().second;
       ++termID) {
    const auto& term = dnl->getDNLTerminalFromID(termID);
    if (term.getSnlBitTerm()->getDirection() == naja::NL::SNLBitTerm::Direction::Input) {
      continue;
    }
    SignalKey key = getTerminalPathKey(term);
    topOutputKeyByTerm.emplace(termID, key);
    model.displayNameByKey.try_emplace(key, getTerminalDisplayName(term));
    allObservedOutputs.insert(key);
  }

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
  }

  // Record enough pin information to reconstruct Q' after the combinational
  // Boolean expressions have been built.
  for (auto leafID : dnl->getLeaves()) {
    const auto& instance = dnl->getDNLInstanceFromID(leafID);
    PendingPinMap pinTermIDs;
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
            {termID,
             normalizePinName(term.getSnlBitTerm()->getName().getString()),
             term.getSnlBitTerm()->getBit()});
      }
      if (isSequentialNextStateInput(term) &&
          term.getSnlBitTerm()->getDirection() !=
              naja::NL::SNLBitTerm::Direction::Output) {
        pinTermIDs[normalizePinName(term.getSnlBitTerm()->getName().getString())]
            .push_back({termID, term.getSnlBitTerm()->getBit()});
      }
    }

    if (stateOutputs.empty()) {
      continue;
    }

    InstanceBoundaryInfo boundaryInfo;
    boundaryInfo.instancePath = instance.getFullPath();
    std::set<SignalKey, SignalKeyLess> boundaryStateKeys;
    for (const auto& stateOutput : stateOutputs) {
      const auto keyIt = inputKeyByTerm.find(stateOutput.termID);
      if (keyIt != inputKeyByTerm.end()) {
        boundaryStateKeys.insert(keyIt->second);
      }
    }
    boundaryInfo.stateKeys.assign(boundaryStateKeys.begin(), boundaryStateKeys.end());

    std::set<SignalKey, SignalKeyLess> boundaryObservedKeys;
    for (naja::DNL::DNLID termID = instance.getTermIndexes().first;
         termID != naja::DNL::DNLID_MAX &&
         termID <= instance.getTermIndexes().second;
         ++termID) {
      const auto& term = dnl->getDNLTerminalFromID(termID);
      if (term.isNull() || term.getSnlBitTerm()->getDirection() ==
                               naja::NL::SNLBitTerm::Direction::Output) {
        continue;
      }
      const SignalKey key = getTerminalPathKey(term);
      model.displayNameByKey.try_emplace(key, getTerminalDisplayName(term));
      if (boundaryObservedKeys.insert(key).second) {
        boundaryInfo.observedTerms.push_back({termID, key});
      }
    }

    instanceBoundaryInfos.push_back(std::move(boundaryInfo));
    const size_t boundaryInfoIndex = instanceBoundaryInfos.size() - 1;

    auto markUnsupportedInstanceStateOutputs = [&]() {
      for (const auto& key : instanceBoundaryInfos[boundaryInfoIndex].stateKeys) {
        unsupportedStateBits.insert(key);
      }
    };
    auto abstractUnsupportedInstanceAsBoundary =
        [&](const std::string& reason) {
          const auto& info = instanceBoundaryInfos[boundaryInfoIndex];
          model.abstractedSequentialBoundaries.push_back(
              "Abstracted uncomputable sequential instance `" +
              info.instancePath + "` as a SEC boundary: " + reason);

          for (const auto& key : info.stateKeys) {
            abstractedBoundaryStateKeys.insert(key);
          }

          for (const auto& observedTerm : info.observedTerms) {
            if (abstractedBoundaryObservedKeys.insert(observedTerm.key).second) {
              abstractedBoundaryObservedTerms.emplace_back(
                  observedTerm.termID, observedTerm.key);
              allObservedOutputs.insert(observedTerm.key);
            }
            prunedBuilderOutputTerms.insert(observedTerm.termID);
          }
        };
    const size_t independentStateOutputCount =
        countIndependentStateOutputs(stateOutputs);

    // Track sequential behavior per state output bit. This keeps vector flops
    // and other multi-output sequential cells from being collapsed into a
    // single instance-wide transition record.
    const size_t pendingStart = pendingTransitions.size();
    const size_t complementedStart = model.complementedStateRelations.size();
    bool unsupportedInstance = false;
    bool abstractedUnsupportedInstance = false;
    std::string abstractedUnsupportedReason;
    for (const auto& stateOutput : stateOutputs) {
      if (findComplementedPrimaryStateOutput(stateOutput, stateOutputs) != nullptr) {
        continue;
      }

      PendingTransition pending;
      pending.stateTermID = stateOutput.termID;
      pending.stateKey = inputKeyByTerm.at(pending.stateTermID);
      pending.statePinName = stateOutput.pinName;
      pending.stateBit = stateOutput.bit;
      pending.independentStateOutputCount = independentStateOutputCount;
      pending.boundaryInfoIndex = boundaryInfoIndex;
      pending.pinTermIDs = pinTermIDs;

      std::vector<ComplementedStateRelation> complementedRelations;
      for (const auto& candidate : stateOutputs) {
        if (candidate.termID == stateOutput.termID || candidate.bit != stateOutput.bit) {
          continue;
        }
        if (!isComplementedStateOutput(stateOutput.pinName, candidate.pinName)) {
          continue;
        }
        const SignalKey complementedKey = inputKeyByTerm.at(candidate.termID);
        pending.complementedStateKeys.push_back(complementedKey);
        complementedRelations.push_back({pending.stateKey, complementedKey});
      }

      try {
        validatePendingTransitionShape(pending);
      } catch (const std::exception& e) {
        if (abstractUncomputableSequentialBoundaries) {
          abstractedUnsupportedInstance = true;
          abstractedUnsupportedReason = e.what();
          break;
        }
        const auto displayIt = model.displayNameByKey.find(pending.stateKey);
        model.unsupportedReasons.push_back(
            "Unsupported sequential primitive for `" +
            (displayIt == model.displayNameByKey.end()
                 ? signalKeyToString(pending.stateKey)
                 : displayIt->second) +
            "`: " + e.what());
        unsupportedStateBits.insert(pending.stateKey);
        for (const auto& complementedKey : pending.complementedStateKeys) {
          unsupportedStateBits.insert(complementedKey);
        }
        unsupportedInstance = true;
        continue;
      }

      model.complementedStateRelations.insert(
          model.complementedStateRelations.end(),
          complementedRelations.begin(),
          complementedRelations.end());
      pendingTransitions.push_back(std::move(pending));
    }

    if (abstractedUnsupportedInstance) {
      pendingTransitions.erase(
          pendingTransitions.begin() + static_cast<std::ptrdiff_t>(pendingStart),
          pendingTransitions.end());
      model.complementedStateRelations.erase(
          model.complementedStateRelations.begin() +
              static_cast<std::ptrdiff_t>(complementedStart),
          model.complementedStateRelations.end());
      abstractUnsupportedInstanceAsBoundary(abstractedUnsupportedReason);
      continue;
    }

    if (unsupportedInstance) {
      markUnsupportedInstanceStateOutputs();
    }
  }

  if (model.hasUnsupportedFeatures()) {
    // Primitive-modeling issues are structural, not proof-related. Report them
    // immediately so large designs fail fast before the expensive cone builder
    // tries to derive BoolExprs for a transition system we already know is
    // unsupported.
    if (previousTop != nullptr) {
      universe->setTopDesign(previousTop);
    }
    if (secDiagEnabled) {
      fprintf(
          stderr,
          "SEC diag: extract(%s) early unsupported exit before build\n",
          top->getName().getString().c_str());
      fflush(stderr);
    }
    return model;
  }

  std::vector<naja::DNL::DNLID> initialObservedTerms;
  initialObservedTerms.reserve(
      topOutputKeyByTerm.size() + abstractedBoundaryObservedTerms.size());
  std::unordered_set<naja::DNL::DNLID> initialObservedTermSet;
  for (const auto& [termID, _] : topOutputKeyByTerm) {
    if (initialObservedTermSet.insert(termID).second) {
      initialObservedTerms.push_back(termID);
    }
  }
  for (const auto& [termID, _] : abstractedBoundaryObservedTerms) {
    if (initialObservedTermSet.insert(termID).second) {
      initialObservedTerms.push_back(termID);
    }
  }
  std::unordered_set<naja::DNL::DNLID> collectedOutputSet(
      builder.getOutputs().begin(), builder.getOutputs().end());
  std::vector<naja::DNL::DNLID> initialMaterializedOutputs;
  initialMaterializedOutputs.reserve(initialObservedTerms.size());
  for (const auto outputTermID : initialObservedTerms) {
    if (collectedOutputSet.find(outputTermID) != collectedOutputSet.end()) {
      initialMaterializedOutputs.push_back(outputTermID);
    }
  }
  builder.setOutputs(initialMaterializedOutputs);
  if (secDiagEnabled) {
    fprintf(
        stderr,
        "SEC diag: extract(%s) abstracted_boundaries=%zu pruned_builder_outputs=%zu initial_observed_outputs=%zu\n",
        top->getName().getString().c_str(),
        model.abstractedSequentialBoundaries.size(),
        prunedBuilderOutputTerms.size(),
        initialMaterializedOutputs.size());
    fflush(stderr);
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

  for (const auto& key : abstractedBoundaryStateKeys) {
    stateBits.erase(key);
    environmentInputs.insert(key);
  }

  model.environmentInputs.assign(environmentInputs.begin(), environmentInputs.end());
  model.stateBits.assign(stateBits.begin(), stateBits.end());
  model.allObservedOutputs.assign(allObservedOutputs.begin(), allObservedOutputs.end());
  if (secDiagEnabled) {
    fprintf(
        stderr,
        "SEC diag: extract(%s) boundary normalized env=%zu state=%zu outputs=%zu pending=%zu\n",
        top->getName().getString().c_str(),
        model.environmentInputs.size(),
        model.stateBits.size(),
        model.allObservedOutputs.size(),
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
  auto skippedOutputsByTerm = builder.getSkippedOutputs();
  // Keep only the valid formulas produced by the clause builder. Invalid
  // clouds are classified below either as skippable connectivity gaps or as
  // hard unsupported logic (for example, logical loops).
  for (size_t i = 0; i < outputTerms.size(); ++i) {
    BoolExpr* expr = outputExprs[i];
    if (expr == nullptr || !expr->isValid()) {
      continue;
    }
    outputExprByTerm.emplace(outputTerms[i], expr);
  }

  for (const auto& [termID, key] : abstractedBoundaryObservedTerms) {
    if (const auto exprIt = outputExprByTerm.find(termID);
        exprIt != outputExprByTerm.end()) {
      model.observedOutputExprByKey.emplace(key, exprIt->second);
      continue;
    }
    if (const auto skippedIt = skippedOutputsByTerm.find(termID);
        skippedIt != skippedOutputsByTerm.end()) {
      if (auto skipInfo = getConnectivitySkipInfo(skippedIt->second);
          skipInfo.has_value()) {
        model.connectivitySkipInfoByKey.emplace(key, *skipInfo);
        continue;
      }
      model.unsupportedReasons.push_back(
          "Unsupported SEC boundary output `" + model.displayNameByKey.at(key) +
          "`: " + skippedIt->second.detail);
      continue;
    }

    const auto built = buildObservedExprForTerm(
        termID,
        outputExprByTerm,
        builder.getInputs(),
        builder.getOutputs(),
        termDNLID2varID);
    if (built.expr != nullptr) {
      model.observedOutputExprByKey.emplace(key, built.expr);
      continue;
    }
    if (built.connectivitySkip.has_value()) {
      model.connectivitySkipInfoByKey.emplace(key, *built.connectivitySkip);
      continue;
    }
    model.unsupportedReasons.push_back(
        "Unsupported SEC boundary output `" + model.displayNameByKey.at(key) +
        "`: " + built.unsupportedReason);
  }

  for (const auto& [termID, key] : topOutputKeyByTerm) {
    auto exprIt = outputExprByTerm.find(termID);
    if (exprIt != outputExprByTerm.end()) {
      model.observedOutputExprByKey.emplace(key, exprIt->second);
      continue;
    }

    auto skippedIt = skippedOutputsByTerm.find(termID);
    if (skippedIt != skippedOutputsByTerm.end()) {
      if (auto skipInfo = getConnectivitySkipInfo(skippedIt->second);
          skipInfo.has_value()) {
        model.connectivitySkipInfoByKey.emplace(key, *skipInfo);
        continue;
      }
      model.unsupportedReasons.push_back(
          "Unsupported observed output cone for `" + signalKeyToString(key) +
          "`: " + skippedIt->second.detail);
      continue;
    }

    model.unsupportedReasons.push_back(
        "Missing observed output expression for `" + signalKeyToString(key) + "`");
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
  auto markConnectivitySkippedState =
      [&](const SignalKey& key, const ConnectivitySkipInfo& info) {
        model.connectivitySkipInfoByKey.emplace(key, info);
      };
  auto markUnsupportedState = [&](const SignalKey& key) {
    unsupportedStateBits.insert(key);
  };
  std::set<SignalKey, SignalKeyLess> lateAbstractedBoundaryStateKeys;
  std::vector<std::pair<naja::DNL::DNLID, SignalKey>> lateAbstractedBoundaryObservedTerms;
  std::unordered_set<SignalKey, SignalKeyHash> lateAbstractedBoundaryObservedKeys;
  std::unordered_set<size_t> lateAbstractedBoundaryIndexes;
  auto recordLateAbstractedInstanceBoundary =
      [&](size_t boundaryInfoIndex, const std::string& reason) {
        if (boundaryInfoIndex == std::numeric_limits<size_t>::max()) {
          return;
        }
        if (!lateAbstractedBoundaryIndexes.insert(boundaryInfoIndex).second) {
          return;
        }

        const auto& info = instanceBoundaryInfos[boundaryInfoIndex];
        model.abstractedSequentialBoundaries.push_back(
            "Abstracted uncomputable sequential instance `" +
            info.instancePath + "` as a SEC boundary: " + reason);
        for (const auto& key : info.stateKeys) {
          lateAbstractedBoundaryStateKeys.insert(key);
        }
        for (const auto& observedTerm : info.observedTerms) {
          if (lateAbstractedBoundaryObservedKeys.insert(observedTerm.key).second) {
            lateAbstractedBoundaryObservedTerms.emplace_back(
                observedTerm.termID, observedTerm.key);
          }
        }
      };
  std::unordered_map<size_t, SignalKey> requiredStateKeyByVarID;
  requiredStateKeyByVarID.reserve(model.stateBits.size());
  for (const auto& key : model.stateBits) {
    const auto varIt = model.inputVarByKey.find(key);
    if (varIt == model.inputVarByKey.end()) {
      continue;
    }
    requiredStateKeyByVarID.emplace(varIt->second, key);
  }

  std::unordered_map<SignalKey, size_t, SignalKeyHash> pendingIndexByStateKey;
  pendingIndexByStateKey.reserve(pendingTransitions.size() * 2);
  for (size_t pendingIndex = 0; pendingIndex < pendingTransitions.size(); ++pendingIndex) {
    const auto& pending = pendingTransitions[pendingIndex];
    pendingIndexByStateKey.emplace(pending.stateKey, pendingIndex);
    for (const auto& complementedKey : pending.complementedStateKeys) {
      pendingIndexByStateKey.emplace(complementedKey, pendingIndex);
    }
  }

  std::unordered_set<SignalKey, SignalKeyHash> requiredStateKeys;
  std::unordered_set<size_t> requiredPendingIndexes;
  std::unordered_set<naja::DNL::DNLID> materializedOutputTerms(
      outputTerms.begin(), outputTerms.end());
  std::deque<size_t> pendingWorkQueue;
  auto enqueueRequiredStateKey = [&](const SignalKey& key) {
    requiredStateKeys.insert(key);
    const auto pendingIt = pendingIndexByStateKey.find(key);
    if (pendingIt != pendingIndexByStateKey.end() &&
        requiredPendingIndexes.insert(pendingIt->second).second) {
      pendingWorkQueue.push_back(pendingIt->second);
    }
  };
  auto enqueueStateDependenciesFromExpr = [&](BoolExpr* expr) {
    if (expr == nullptr || !expr->isValid()) {
      return;
    }
    for (const auto symbol : expr->getSupportVars()) {
      const auto stateIt = requiredStateKeyByVarID.find(symbol);
      if (stateIt == requiredStateKeyByVarID.end()) {
        continue;
      }
      enqueueRequiredStateKey(stateIt->second);
    }
  };

  for (const auto& [_, expr] : model.observedOutputExprByKey) {
    enqueueStateDependenciesFromExpr(expr);
  }

  while (!pendingWorkQueue.empty()) {
    std::vector<size_t> batchPendingIndexes;
    std::vector<naja::DNL::DNLID> batchOutputTerms;
    while (!pendingWorkQueue.empty()) {
      const size_t pendingIndex = pendingWorkQueue.front();
      pendingWorkQueue.pop_front();
      batchPendingIndexes.push_back(pendingIndex);

      const auto& pending = pendingTransitions[pendingIndex];
      requiredStateKeys.insert(pending.stateKey);
      for (const auto& complementedKey : pending.complementedStateKeys) {
        requiredStateKeys.insert(complementedKey);
      }

      for (const auto& [_, candidates] : pending.pinTermIDs) {
        for (const auto& candidate : candidates) {
          if (materializedOutputTerms.insert(candidate.termID).second) {
            batchOutputTerms.push_back(candidate.termID);
          }
        }
      }
    }

    if (!batchOutputTerms.empty()) {
      const auto dependencyOutputs = materializeBuilderOutputs(
          batchOutputTerms,
          secDiagEnabled,
          top->getName().getString().c_str(),
          "dependency build");
      for (const auto& [termID, expr] : dependencyOutputs.outputExprByTerm) {
        outputExprByTerm.emplace(termID, expr);
      }
      for (const auto& [termID, info] : dependencyOutputs.skippedOutputsByTerm) {
        skippedOutputsByTerm.emplace(termID, info);
      }
    }

    for (const auto pendingIndex : batchPendingIndexes) {
      const auto& pending = pendingTransitions[pendingIndex];
    std::optional<ConnectivitySkipInfo> skippedPinInfo;
    for (const auto& [pinName, _] : pending.pinTermIDs) {
      const auto resolvedPinTermID = resolvePendingPinTermID(pending, pinName.c_str());
      if (!resolvedPinTermID.has_value()) {
        continue;
      }
      auto skippedIt = skippedOutputsByTerm.find(*resolvedPinTermID);
      if (skippedIt == skippedOutputsByTerm.end()) {
        continue;
      }

      if (auto skipInfo = getConnectivitySkipInfo(skippedIt->second);
          skipInfo.has_value()) {
        if (skipInfo->origin == ConnectivitySkipOrigin::NoDriver &&
            isOptionalSequentialControlPin(pinName)) {
          continue;
        }
        skippedPinInfo = {
            skipInfo->origin,
            "Sequential pin `" + pinName + "` was skipped because " +
                skippedIt->second.detail,
        };
        break;
      }

      if (abstractUncomputableSequentialBoundaries) {
        recordLateAbstractedInstanceBoundary(
            pending.boundaryInfoIndex,
            "unsupported sequential pin `" + pinName + "`: " +
                skippedIt->second.detail);
        skippedPinInfo.reset();
        goto next_pending_transition;
      }

      model.unsupportedReasons.push_back(
          "Unsupported sequential primitive for `" +
          signalKeyToString(pending.stateKey) + "`: Sequential pin `" + pinName +
          "` is unsupported: " + skippedIt->second.detail);
      markUnsupportedState(pending.stateKey);
      for (const auto& complementedKey : pending.complementedStateKeys) {
        markUnsupportedState(complementedKey);
      }
      skippedPinInfo.reset();
      goto next_pending_transition;
    }

    if (skippedPinInfo.has_value()) {
      markConnectivitySkippedState(pending.stateKey, *skippedPinInfo);
      for (const auto& complementedKey : pending.complementedStateKeys) {
        markConnectivitySkippedState(complementedKey, *skippedPinInfo);
      }
      continue;
    }

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
      enqueueStateDependenciesFromExpr(nextStateExpr);
    } catch (const std::exception& e) {
      if (abstractUncomputableSequentialBoundaries) {
        recordLateAbstractedInstanceBoundary(
            pending.boundaryInfoIndex, e.what());
        continue;
      }

      model.unsupportedReasons.push_back(
          "Unsupported sequential primitive for `" +
          signalKeyToString(pending.stateKey) + "`: " + e.what());
      markUnsupportedState(pending.stateKey);
      for (const auto& complementedKey : pending.complementedStateKeys) {
        markUnsupportedState(complementedKey);
      }
    }
  next_pending_transition:;
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

  model.stateBits.erase(
      std::remove_if(
          model.stateBits.begin(),
          model.stateBits.end(),
          [&](const SignalKey& key) {
            return requiredStateKeys.find(key) == requiredStateKeys.end();
          }),
      model.stateBits.end());
  model.complementedStateRelations.erase(
      std::remove_if(
          model.complementedStateRelations.begin(),
          model.complementedStateRelations.end(),
          [&](const ComplementedStateRelation& relation) {
            return requiredStateKeys.find(relation.primaryKey) == requiredStateKeys.end() ||
                   requiredStateKeys.find(relation.complementedKey) ==
                       requiredStateKeys.end();
          }),
      model.complementedStateRelations.end());

  for (const auto& key : lateAbstractedBoundaryStateKeys) {
    model.nextStateExprByStateKey.erase(key);
    model.initialStateValueByKey.erase(key);
    if (std::find(model.environmentInputs.begin(), model.environmentInputs.end(), key) ==
        model.environmentInputs.end()) {
      model.environmentInputs.push_back(key);
    }
  }
  if (!lateAbstractedBoundaryStateKeys.empty()) {
    model.stateBits.erase(
        std::remove_if(
            model.stateBits.begin(),
            model.stateBits.end(),
            [&](const SignalKey& key) {
              return lateAbstractedBoundaryStateKeys.find(key) !=
                     lateAbstractedBoundaryStateKeys.end();
            }),
        model.stateBits.end());
    model.complementedStateRelations.erase(
        std::remove_if(
            model.complementedStateRelations.begin(),
            model.complementedStateRelations.end(),
            [&](const ComplementedStateRelation& relation) {
              return lateAbstractedBoundaryStateKeys.find(relation.primaryKey) !=
                         lateAbstractedBoundaryStateKeys.end() ||
                     lateAbstractedBoundaryStateKeys.find(relation.complementedKey) !=
                         lateAbstractedBoundaryStateKeys.end();
            }),
        model.complementedStateRelations.end());
  }

  for (const auto& [termID, key] : lateAbstractedBoundaryObservedTerms) {
    if (std::find(model.allObservedOutputs.begin(), model.allObservedOutputs.end(), key) ==
        model.allObservedOutputs.end()) {
      model.allObservedOutputs.push_back(key);
    }
    if (const auto exprIt = outputExprByTerm.find(termID);
        exprIt != outputExprByTerm.end()) {
      model.observedOutputExprByKey.emplace(key, exprIt->second);
      continue;
    }
    if (const auto skippedIt = skippedOutputsByTerm.find(termID);
        skippedIt != skippedOutputsByTerm.end()) {
      if (auto skipInfo = getConnectivitySkipInfo(skippedIt->second);
          skipInfo.has_value()) {
        model.connectivitySkipInfoByKey.emplace(key, *skipInfo);
        continue;
      }
      model.unsupportedReasons.push_back(
          "Unsupported SEC boundary output `" + model.displayNameByKey.at(key) +
          "`: " + skippedIt->second.detail);
      continue;
    }
    const auto built = buildObservedExprForTerm(
        termID,
        outputExprByTerm,
        builder.getInputs(),
        builder.getOutputs(),
        termDNLID2varID);
    if (built.expr != nullptr) {
      model.observedOutputExprByKey.emplace(key, built.expr);
      continue;
    }
    if (built.connectivitySkip.has_value()) {
      model.connectivitySkipInfoByKey.emplace(key, *built.connectivitySkip);
      continue;
    }
    model.unsupportedReasons.push_back(
        "Unsupported SEC boundary output `" + model.displayNameByKey.at(key) +
        "`: " + built.unsupportedReason);
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
  if (!unsupportedStateBits.empty()) {
    model.stateBits.erase(
        std::remove_if(
            model.stateBits.begin(),
            model.stateBits.end(),
            [&](const SignalKey& key) {
              if (unsupportedStateBits.find(key) == unsupportedStateBits.end()) {
                return false;
              }
              model.nextStateExprByStateKey.erase(key);
              model.initialStateValueByKey.erase(key);
              model.inputVarByKey.erase(key);
              return true;
            }),
        model.stateBits.end());
    model.complementedStateRelations.erase(
        std::remove_if(
            model.complementedStateRelations.begin(),
            model.complementedStateRelations.end(),
            [&](const ComplementedStateRelation& relation) {
              return unsupportedStateBits.find(relation.primaryKey) !=
                         unsupportedStateBits.end() ||
                     unsupportedStateBits.find(relation.complementedKey) !=
                         unsupportedStateBits.end();
            }),
        model.complementedStateRelations.end());
  }
  if (secDiagEnabled) {
    fprintf(
        stderr,
        "SEC diag: extract(%s) filtered env=%zu state=%zu\n",
        top->getName().getString().c_str(),
        model.environmentInputs.size(),
        model.stateBits.size());
    fflush(stderr);
  }

  std::unordered_map<size_t, SignalKey> stateKeyByVarID;
  for (const auto& key : model.stateBits) {
    const auto varIt = model.inputVarByKey.find(key);
    if (varIt == model.inputVarByKey.end()) {
      continue;
    }
    stateKeyByVarID.emplace(varIt->second, key);
  }

  bool changed = false;
  do {
    changed = false;
    std::unordered_set<size_t> skippedStateVars;
    for (const auto& key : model.stateBits) {
      if (model.connectivitySkipInfoByKey.find(key) == model.connectivitySkipInfoByKey.end()) {
        continue;
      }
      const auto varIt = model.inputVarByKey.find(key);
      if (varIt != model.inputVarByKey.end()) {
        skippedStateVars.insert(varIt->second);
      }
    }

    std::unordered_map<BoolExpr*, std::optional<size_t>> memo;
    for (const auto& key : model.stateBits) {
      if (model.connectivitySkipInfoByKey.find(key) != model.connectivitySkipInfoByKey.end()) {
        continue;
      }
      auto exprIt = model.nextStateExprByStateKey.find(key);
      if (exprIt == model.nextStateExprByStateKey.end()) {
        continue;
      }
      const auto dependency = findSkippedStateDependency(
          exprIt->second, skippedStateVars, memo);
      if (!dependency.has_value()) {
        continue;
      }
      const auto sourceKeyIt = stateKeyByVarID.find(*dependency);
      if (sourceKeyIt == stateKeyByVarID.end()) {
        continue;
      }
      const auto skipInfoIt =
          model.connectivitySkipInfoByKey.find(sourceKeyIt->second);
      if (skipInfoIt == model.connectivitySkipInfoByKey.end()) {
        continue;
      }
      model.connectivitySkipInfoByKey.emplace(
          key,
          ConnectivitySkipInfo{
              skipInfoIt->second.origin,
              "Depends on skipped state `" +
                  model.displayNameByKey.at(sourceKeyIt->second) +
                  "` whose cone traces to a " +
                  describeConnectivitySkipOrigin(skipInfoIt->second.origin) +
                  " issue",
          });
      changed = true;
    }

    std::unordered_map<BoolExpr*, std::optional<size_t>> outputMemo;
    for (const auto& key : model.allObservedOutputs) {
      if (model.connectivitySkipInfoByKey.find(key) != model.connectivitySkipInfoByKey.end()) {
        continue;
      }
      auto exprIt = model.observedOutputExprByKey.find(key);
      if (exprIt == model.observedOutputExprByKey.end()) {
        continue;
      }
      const auto dependency = findSkippedStateDependency(
          exprIt->second, skippedStateVars, outputMemo);
      if (!dependency.has_value()) {
        continue;
      }
      const auto sourceKeyIt = stateKeyByVarID.find(*dependency);
      if (sourceKeyIt == stateKeyByVarID.end()) {
        continue;
      }
      const auto skipInfoIt =
          model.connectivitySkipInfoByKey.find(sourceKeyIt->second);
      if (skipInfoIt == model.connectivitySkipInfoByKey.end()) {
        continue;
      }
      model.connectivitySkipInfoByKey.emplace(
          key,
          ConnectivitySkipInfo{
              skipInfoIt->second.origin,
              "Depends on skipped state `" +
                  model.displayNameByKey.at(sourceKeyIt->second) +
                  "` whose cone traces to a " +
                  describeConnectivitySkipOrigin(skipInfoIt->second.origin) +
                  " issue",
          });
      changed = true;
    }
  } while (changed);

  std::vector<SignalKey> legalStateBits;
  legalStateBits.reserve(model.stateBits.size());
  for (const auto& key : model.stateBits) {
    if (model.connectivitySkipInfoByKey.find(key) != model.connectivitySkipInfoByKey.end()) {
      model.skippedStateBits.push_back(key);
      model.nextStateExprByStateKey.erase(key);
      model.initialStateValueByKey.erase(key);
      model.inputVarByKey.erase(key);
      continue;
    }
    legalStateBits.push_back(key);
  }
  model.stateBits = std::move(legalStateBits);

  for (const auto& key : model.allObservedOutputs) {
    if (model.connectivitySkipInfoByKey.find(key) != model.connectivitySkipInfoByKey.end()) {
      model.skippedObservedOutputs.push_back(key);
      model.observedOutputExprByKey.erase(key);
      continue;
    }
    if (model.observedOutputExprByKey.find(key) != model.observedOutputExprByKey.end()) {
      model.observedOutputs.push_back(key);
    }
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
      const auto displayIt = model.displayNameByKey.find(key);
      model.unsupportedReasons.push_back(
          "Missing observed output expression for `" +
          (displayIt == model.displayNameByKey.end() ? signalKeyToString(key)
                                                     : displayIt->second) +
          "`");
    }
  }
  for (const auto& key : model.stateBits) {
    if (model.nextStateExprByStateKey.find(key) == model.nextStateExprByStateKey.end()) {
      const auto displayIt = model.displayNameByKey.find(key);
      model.unsupportedReasons.push_back(
          "Missing next-state relation for `" +
          (displayIt == model.displayNameByKey.end() ? signalKeyToString(key)
                                                     : displayIt->second) +
          "`");
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
  pending.independentStateOutputCount = 1;
  for (const auto& [pinName, termID] : pinTermIDs) {
    pending.pinTermIDs[pinName].push_back({termID, 0});
  }
  return buildNextStateExpr(pending, termDNLID2varID, outputExprByTerm);
}

std::optional<bool> detectInitialStateValueForTest(
    const std::unordered_map<std::string, naja::DNL::DNLID>& pinTermIDs) {
  PendingTransition pending;
  pending.independentStateOutputCount = 1;
  for (const auto& [pinName, termID] : pinTermIDs) {
    pending.pinTermIDs[pinName].push_back({termID, 0});
  }
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

std::vector<naja::DNL::DNLID> selectRequiredBuilderOutputsForTest(
    const std::vector<naja::DNL::DNLID>& collectedOutputs,
    const std::unordered_set<naja::DNL::DNLID>& topOutputTerms,
    const std::vector<naja::DNL::DNLID>& sequentialDependencyTerms,
    const std::unordered_set<naja::DNL::DNLID>& prunedBuilderOutputTerms) {
  return selectRequiredBuilderOutputs(
      collectedOutputs,
      topOutputTerms,
      std::unordered_set<naja::DNL::DNLID>(
          sequentialDependencyTerms.begin(), sequentialDependencyTerms.end()),
      prunedBuilderOutputTerms);
}

}  // namespace detail

}  // namespace KEPLER_FORMAL::SEC
