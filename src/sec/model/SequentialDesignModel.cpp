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
#include "NLDB0.h"
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

struct PendingMemoryReadPort {
  std::vector<naja::DNL::DNLID> addressTermIDs;
  std::vector<naja::DNL::DNLID> dataTermIDs;
};

struct PendingMemoryWritePort {
  std::vector<naja::DNL::DNLID> addressTermIDs;
  std::vector<naja::DNL::DNLID> dataTermIDs;
  std::vector<naja::DNL::DNLID> maskTermIDs;
  std::vector<naja::DNL::DNLID> enableTermIDs;
  std::vector<std::vector<naja::DNL::DNLID>> extraWriteInputTermIDs;
};

struct PendingMemoryCellState {
  SignalKey key;
  std::string displayName;
  size_t cellIndex = 0;
  size_t bitIndex = 0;
};

struct PendingMemoryReadOutput {
  SignalKey key;
  size_t portIndex = 0;
  size_t bitIndex = 0;
};

struct PendingMemoryInstance {
  size_t width = 0;
  size_t depth = 0;
  size_t abits = 0;
  naja::NL::SNLDesignModeling::MemoryResetMode resetMode =
      naja::NL::SNLDesignModeling::MemoryResetMode::None;
  std::optional<naja::DNL::DNLID> resetTermID;
  size_t boundaryInfoIndex = std::numeric_limits<size_t>::max();
  std::vector<PendingMemoryReadPort> readPorts;
  std::vector<PendingMemoryWritePort> writePorts;
  std::vector<PendingMemoryCellState> cellStates;
  std::vector<PendingMemoryReadOutput> readOutputs;
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

struct SequentialInstanceScan {
  PendingPinMap pinTermIDs;
  std::vector<StateOutputTerm> stateOutputs;
  InstanceBoundaryInfo boundaryInfo;
};

AbstractedSequentialBoundaryDetail makeAbstractedBoundaryDetail(
    const InstanceBoundaryInfo& info) {
  AbstractedSequentialBoundaryDetail detail;
  detail.instancePath = info.instancePath;
  detail.stateKeys = info.stateKeys;
  detail.observedKeys.reserve(info.observedTerms.size());
  for (const auto& observedTerm : info.observedTerms) {
    detail.observedKeys.push_back(observedTerm.key);
  }
  return detail;
}

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
    case ConnectivitySkipOrigin::LogicalLoop:
      return "logical-loop";
  }
  return "connectivity";  // LCOV_EXCL_LINE
}

const char* describeBuilderSkippedOutputReason(
    BuilderSkippedOutputReason reason) {
  switch (reason) {
    case BuilderSkippedOutputReason::NoDriver:
      return "no_driver";
    case BuilderSkippedOutputReason::MultiDriver:
      return "multi_driver";
    case BuilderSkippedOutputReason::LogicalLoop:
      return "logical_loop";
    case BuilderSkippedOutputReason::None:
      return "none";
  }
  return "unknown";  // LCOV_EXCL_LINE
}

std::optional<ConnectivitySkipInfo> getConnectivitySkipInfo(
    const BuilderSkippedOutputInfo& info) {
  switch (info.reason) {
    case BuilderSkippedOutputReason::NoDriver:
      return ConnectivitySkipInfo{ConnectivitySkipOrigin::NoDriver, info.detail};
    case BuilderSkippedOutputReason::MultiDriver:
      return ConnectivitySkipInfo{ConnectivitySkipOrigin::MultiDriver, info.detail};
    case BuilderSkippedOutputReason::LogicalLoop:
      return ConnectivitySkipInfo{
          ConnectivitySkipOrigin::LogicalLoop, info.detail};
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
    const std::vector<size_t>& termDNLID2varID,
    bool allowInternalLogicalLoopFrontier = false) {
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
    // SEC rebuilds internal observability roots for modeled memories and
    // abstracted boundaries. A transparent self-feedback branch under such an
    // internal root should become a frontier input instead of causing the whole
    // memory dependency to be skipped.
    KEPLER_FORMAL::SNLLogicCloud cloud(
        outputTermID,
        isPIs,
        localIsPOs,
        allowInternalLogicalLoopFrontier,
        false);
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
        localResult.connectivitySkip = ConnectivitySkipInfo{
            ConnectivitySkipOrigin::LogicalLoop, cloud.getSkipReasonText()};
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
      localResult.connectivitySkip = ConnectivitySkipInfo{
          ConnectivitySkipOrigin::LogicalLoop,
          "a logical loop was detected while rebuilding a SEC boundary"};
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

void appendUniqueTermIDs(
    std::vector<naja::DNL::DNLID>& dest,
    const std::vector<naja::DNL::DNLID>& src) {
  std::unordered_set<naja::DNL::DNLID> seen(dest.begin(), dest.end());
  for (const auto termID : src) {
    if (seen.insert(termID).second) {
      dest.push_back(termID);
    }
  }
}

void mergeBuilderTermVarIDs(
    std::vector<size_t>& dest,
    const std::vector<size_t>& src) {
  if (src.size() > dest.size()) {
    dest.resize(src.size(), 0);
  }
  for (size_t index = 0; index < src.size(); ++index) {
    if (dest[index] == 0) {
      dest[index] = src[index];
    }
  }
}

MaterializedBuilderOutputs materializeBuilderOutputs(
    const std::vector<naja::DNL::DNLID>& requestedOutputs,
    bool secDiagEnabled,
    const char* topName,
    const char* phaseLabel,
    bool allowInternalLogicalLoopFrontier = false) {
  MaterializedBuilderOutputs result;

  KEPLER_FORMAL::BuildPrimaryOutputClauses builder;
  builder.setRetainDnl(true);
  builder.collect();
  std::vector<naja::DNL::DNLID> normalizedRoots;
  normalizedRoots.reserve(requestedOutputs.size());
  std::unordered_map<naja::DNL::DNLID, std::vector<naja::DNL::DNLID>> requestedByRoot;
  std::unordered_set<naja::DNL::DNLID> seenRoots;
  auto* dnl = naja::DNL::get();
  const auto describeTerminal = [](const naja::DNL::DNLTerminalFull& terminal) {
    std::ostringstream oss;
    // Keep the debug label cheap: the full DNL instance path reconstruction is
    // surprisingly expensive on large designs and can dominate CVA6 diag runs.
    // The term ID is logged separately, so a compact model.pin[bit] label is
    // enough to correlate skipped roots back to the detailed skip reports.
    oss << terminal.getSnlBitTerm()->getDesign()->getName().getString() << "."
        << terminal.getSnlBitTerm()->getName().getString() << "["
        << terminal.getSnlBitTerm()->getBit() << "]";
    return oss.str();
  };
  const auto findBuildableOutputRoot = [&](naja::DNL::DNLID requestedTermID)
      -> std::optional<naja::DNL::DNLID> {
    std::unordered_set<naja::DNL::DNLID> visitedTerms;
    naja::DNL::DNLID currentTermID = requestedTermID;
    while (currentTermID != naja::DNL::DNLID_MAX &&
           visitedTerms.insert(currentTermID).second) {
      const auto& currentTerm = dnl->getDNLTerminalFromID(currentTermID);
      if (currentTerm.isNull()) {
        return std::nullopt;
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
        if (model != nullptr && NLDB0::isAssign(model)) {
          std::optional<naja::DNL::DNLID> passthroughDriver;
          for (auto* inputBitTerm : naja::NL::SNLDesignModeling::getCombinatorialInputs(
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
  };
  for (const auto requestedTermID : requestedOutputs) {
    const auto rootTermID = findBuildableOutputRoot(requestedTermID);
    if (!rootTermID.has_value()) {
      continue;
    }
    requestedByRoot[*rootTermID].push_back(requestedTermID);
    if (seenRoots.insert(*rootTermID).second) {
      normalizedRoots.push_back(*rootTermID);
    }
  }

  // Structured memory dependencies are often internal roots that SEC needs
  // even when the generic boundary collector would not classify them as
  // outputs. Root input-side dependency pins at their single-driver source so
  // the clause builder sees the actual combinational producer instead of the
  // sink pin on the memory instance.
  builder.setAllowInternalLogicalLoopFrontier(
      allowInternalLogicalLoopFrontier);
  builder.setOutputs(normalizedRoots);

  const bool traceDependencyRoots =
      secDiagEnabled &&
      std::string_view(phaseLabel).find("dependency build") !=
          std::string_view::npos;
  if (secDiagEnabled) {
    // Dependency batches on designs like CVA6 can include thousands of memory
    // pins. Logging every requested-to-root mapping is prohibitively expensive,
    // so the diagnostic path only prints summary begin/end markers here and
    // prints the detailed term mapping only for the roots that later skip.
    fprintf(
        stderr,
        "SEC diag: extract(%s) %s begin outputs=%zu\n",
        topName,
        phaseLabel,
        normalizedRoots.size());
    fflush(stderr);
  }
  builder.build();
  // BuildPrimaryOutputClauses owns a temporary DNL expansion and destroys the
  // singleton when build() completes. Rebuilding the full DNL here is very
  // expensive on CVA6, so only reacquire it when the detailed dependency-root
  // diagnostics actually need to print terminal names after the build.
  if (traceDependencyRoots) {
    dnl = naja::DNL::get();
  }
  if (secDiagEnabled) {
    fprintf(
        stderr,
        "SEC diag: extract(%s) %s end outputs=%zu\n",
        topName,
        phaseLabel,
        normalizedRoots.size());
    fflush(stderr);
  }

  result.inputs = builder.getInputs();
  result.outputs = builder.getOutputs();
  result.termDNLID2varID = builder.getTermDNLID2VarID();
  result.skippedOutputsByTerm = builder.getSkippedOutputs();
  if (traceDependencyRoots) {
    for (const auto& [rootTermID, skipInfo] : result.skippedOutputsByTerm) {
      const auto requestedIt = requestedByRoot.find(rootTermID);
      if (requestedIt == requestedByRoot.end()) {
        continue;
      }
      const auto& rootTerm = dnl->getDNLTerminalFromID(rootTermID);
      for (const auto requestedTermID : requestedIt->second) {
        const auto& requestedTerm = dnl->getDNLTerminalFromID(requestedTermID);
        fprintf(
            stderr,
            "SEC diag: extract(%s) %s skipped requested=%s term=%zu root=%s term=%zu reason=%s detail=%s\n",
            topName,
            phaseLabel,
            describeTerminal(requestedTerm).c_str(),
            requestedTermID,
            describeTerminal(rootTerm).c_str(),
            rootTermID,
            describeBuilderSkippedOutputReason(skipInfo.reason),
            skipInfo.detail.c_str());
      }
    }
  }
  const auto& outputExprs = builder.getPOs();
  for (size_t i = 0; i < result.outputs.size(); ++i) {
    BoolExpr* expr = outputExprs[i];
    if (expr == nullptr || !expr->isValid()) {
      continue;
    }
    result.outputExprByTerm.emplace(result.outputs[i], expr);
    if (const auto requestedIt = requestedByRoot.find(result.outputs[i]);
        requestedIt != requestedByRoot.end()) {
      for (const auto requestedTermID : requestedIt->second) {
        result.outputExprByTerm.emplace(requestedTermID, expr);
      }
    }
  }

  std::vector<std::pair<naja::DNL::DNLID, BuilderSkippedOutputInfo>> skippedAliases(
      result.skippedOutputsByTerm.begin(), result.skippedOutputsByTerm.end());
  for (const auto& [rootTermID, info] : skippedAliases) {
    if (const auto requestedIt = requestedByRoot.find(rootTermID);
        requestedIt != requestedByRoot.end()) {
      for (const auto requestedTermID : requestedIt->second) {
        result.skippedOutputsByTerm.emplace(requestedTermID, info);
      }
    }
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

BoolExpr* makeAndChain(const std::vector<BoolExpr*>& exprs) {
  if (exprs.empty()) {
    return BoolExpr::createTrue();
  }
  BoolExpr* result = exprs.front();
  for (size_t index = 1; index < exprs.size(); ++index) {
    result = BoolExpr::And(result, exprs[index]);
  }
  return result;
}

BoolExpr* makeIte(BoolExpr* condition, BoolExpr* whenTrue, BoolExpr* whenFalse) {
  return BoolExpr::Or(
      BoolExpr::And(condition, whenTrue),
      BoolExpr::And(BoolExpr::Not(condition), whenFalse));
}

BoolExpr* buildAddressEqualsExpr(
    const std::vector<BoolExpr*>& addressBits,
    size_t addressValue) {
  std::vector<BoolExpr*> equalities;
  equalities.reserve(addressBits.size());
  for (size_t bitIndex = 0; bitIndex < addressBits.size(); ++bitIndex) {
    const bool expected = ((addressValue >> bitIndex) & size_t{1}) != 0;
    equalities.push_back(expected ? addressBits[bitIndex]
                                  : BoolExpr::Not(addressBits[bitIndex]));
  }
  return makeAndChain(equalities);
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

struct ExtractContext {
  naja::NL::SNLDesign* top = nullptr;
  naja::NL::NLUniverse* universe = nullptr;
  naja::NL::SNLDesign* previousTop = nullptr;
  std::string topName;
  bool secDiagEnabled = false;
  bool abstractUncomputableSequentialBoundaries = false;
  KEPLER_FORMAL::BuildPrimaryOutputClauses builder;
  decltype(naja::DNL::get()) dnl = nullptr;
  std::unordered_map<naja::DNL::DNLID, SignalKey> inputKeyByTerm;
  std::unordered_map<naja::DNL::DNLID, SignalKey> outputKeyByTerm;
  std::unordered_map<naja::DNL::DNLID, SignalKey> topOutputKeyByTerm;
  std::set<SignalKey, SignalKeyLess> topInputKeys;
  std::set<SignalKey, SignalKeyLess> topOutputKeys;
  std::set<SignalKey, SignalKeyLess> internalBoundaryInputKeys;
  std::set<SignalKey, SignalKeyLess> internalBoundaryOutputKeys;
  std::set<SignalKey, SignalKeyLess> environmentInputs;
  std::set<SignalKey, SignalKeyLess> stateBits;
  std::set<SignalKey, SignalKeyLess> allObservedOutputs;
  std::unordered_set<naja::DNL::DNLID> prunedBuilderOutputTerms;
  std::set<SignalKey, SignalKeyLess> abstractedBoundaryStateKeys;
  std::vector<std::pair<naja::DNL::DNLID, SignalKey>> abstractedBoundaryObservedTerms;
  std::unordered_set<SignalKey, SignalKeyHash> abstractedBoundaryObservedKeys;
  std::unordered_set<SignalKey, SignalKeyHash> unsupportedStateBits;
  std::vector<PendingTransition> pendingTransitions;
  std::vector<PendingMemoryInstance> pendingMemoryInstances;
  std::vector<InstanceBoundaryInfo> instanceBoundaryInfos;
  std::unordered_map<naja::DNL::DNLID, bool> sequentialInstanceCache;
};

void collectInitialBuilderBoundary(ExtractContext& ctx) {
  naja::DNL::destroy();
  ctx.universe->setTopDesign(ctx.top);

  // Reuse the existing miter frontend to discover the relevant boundary
  // signals before we ask it to build Boolean formulas.
  if (ctx.secDiagEnabled) {
    fprintf(stderr, "SEC diag: extract(%s) collect begin\n", ctx.topName.c_str());
    fflush(stderr);
  }
  ctx.builder.collect();
  if (ctx.secDiagEnabled) {
    fprintf(
        stderr,
        "SEC diag: extract(%s) collect end inputs=%zu outputs=%zu\n",
        ctx.topName.c_str(),
        ctx.builder.getInputs().size(),
        ctx.builder.getOutputs().size());
    fflush(stderr);
  }

  ctx.dnl = naja::DNL::get();
}

void collectTopInterfaceTerms(ExtractContext& ctx, SequentialDesignModel& model) {
  const auto topInstance = ctx.dnl->getTop();
  for (naja::DNL::DNLID termID = topInstance.getTermIndexes().first;
       termID != naja::DNL::DNLID_MAX && termID <= topInstance.getTermIndexes().second;
       ++termID) {
    const auto& term = ctx.dnl->getDNLTerminalFromID(termID);
    SignalKey key = getTerminalPathKey(term);
    model.displayNameByKey.try_emplace(key, getTerminalDisplayName(term));
    if (term.getSnlBitTerm()->getDirection() ==
        naja::NL::SNLBitTerm::Direction::Input) {
      ctx.topInputKeys.insert(key);
      continue;
    }
    ctx.topOutputKeys.insert(key);
    ctx.topOutputKeyByTerm.emplace(termID, key);
    ctx.allObservedOutputs.insert(key);
  }
}

bool isSequentialInstanceTerm(ExtractContext& ctx,
                              const naja::DNL::DNLTerminalFull& term) {
  const auto& instance = term.getDNLInstance();
  const auto instanceID = instance.getID();
  if (const auto cached = ctx.sequentialInstanceCache.find(instanceID);
      cached != ctx.sequentialInstanceCache.end()) {
    return cached->second;
  }

  bool isSequentialInstance = false;
  for (naja::DNL::DNLID termID = instance.getTermIndexes().first;
       termID != naja::DNL::DNLID_MAX && termID <= instance.getTermIndexes().second;
       ++termID) {
    const auto& instanceTerm = ctx.dnl->getDNLTerminalFromID(termID);
    if (instanceTerm.isNull()) {
      continue;
    }
    if (isSequentialStateOutput(instanceTerm) ||
        isSequentialNextStateInput(instanceTerm)) {
      isSequentialInstance = true;
      break;
    }
  }

  ctx.sequentialInstanceCache.emplace(instanceID, isSequentialInstance);
  return isSequentialInstance;
}

void classifyBuilderBoundaryTerms(ExtractContext& ctx, SequentialDesignModel& model) {
  // The miter builder already exposes sequential outputs as "inputs" and
  // sequential next-state pins as "outputs"; we normalize those into SEC's
  // environment/state/output buckets here.
  for (const auto inputTermID : ctx.builder.getInputs()) {
    const auto& term = ctx.dnl->getDNLTerminalFromID(inputTermID);
    SignalKey key = getTerminalPathKey(term);
    ctx.inputKeyByTerm.emplace(inputTermID, key);
    model.displayNameByKey.try_emplace(key, getTerminalDisplayName(term));
    if (isSequentialStateOutput(term)) {
      ctx.stateBits.insert(key);
    } else {
      ctx.environmentInputs.insert(key);
      if (!term.isTopPort() && !isSequentialInstanceTerm(ctx, term)) {
        ctx.internalBoundaryInputKeys.insert(key);
      }
    }
  }

  for (const auto outputTermID : ctx.builder.getOutputs()) {
    const auto& term = ctx.dnl->getDNLTerminalFromID(outputTermID);
    SignalKey key = getTerminalPathKey(term);
    ctx.outputKeyByTerm.emplace(outputTermID, key);
    model.displayNameByKey.try_emplace(key, getTerminalDisplayName(term));
    if (ctx.topOutputKeys.find(key) == ctx.topOutputKeys.end() &&
        !isSequentialInstanceTerm(ctx, term)) {
      ctx.internalBoundaryOutputKeys.insert(key);
    }
  }
}

std::optional<SequentialInstanceScan> scanSequentialInstance(
    const naja::DNL::DNLInstanceFull& instance,
    const std::unordered_map<naja::DNL::DNLID, SignalKey>& inputKeyByTerm,
    SequentialDesignModel& model) {
  SequentialInstanceScan scan;
  scan.boundaryInfo.instancePath = instance.getFullPath();

  for (naja::DNL::DNLID termID = instance.getTermIndexes().first;
       termID != naja::DNL::DNLID_MAX &&
       termID <= instance.getTermIndexes().second;
       ++termID) {
    const auto& term = naja::DNL::get()->getDNLTerminalFromID(termID);
    if (isSequentialStateOutput(term) &&
        term.getSnlBitTerm()->getDirection() !=
            naja::NL::SNLBitTerm::Direction::Input) {
      scan.stateOutputs.push_back(
          {termID,
           normalizePinName(term.getSnlBitTerm()->getName().getString()),
           term.getSnlBitTerm()->getBit()});
    }
    if (isSequentialNextStateInput(term) &&
        term.getSnlBitTerm()->getDirection() !=
            naja::NL::SNLBitTerm::Direction::Output) {
      scan.pinTermIDs[normalizePinName(term.getSnlBitTerm()->getName().getString())]
          .push_back({termID, term.getSnlBitTerm()->getBit()});
    }
  }

  if (scan.stateOutputs.empty()) {
    return std::nullopt;
  }

  std::set<SignalKey, SignalKeyLess> boundaryStateKeys;
  for (const auto& stateOutput : scan.stateOutputs) {
    const auto keyIt = inputKeyByTerm.find(stateOutput.termID);
    if (keyIt != inputKeyByTerm.end()) {
      boundaryStateKeys.insert(keyIt->second);
    }
  }
  scan.boundaryInfo.stateKeys.assign(boundaryStateKeys.begin(), boundaryStateKeys.end());

  std::set<SignalKey, SignalKeyLess> boundaryObservedKeys;
  for (naja::DNL::DNLID termID = instance.getTermIndexes().first;
       termID != naja::DNL::DNLID_MAX &&
       termID <= instance.getTermIndexes().second;
       ++termID) {
    const auto& term = naja::DNL::get()->getDNLTerminalFromID(termID);
    if (term.isNull() ||
        term.getSnlBitTerm()->getDirection() == naja::NL::SNLBitTerm::Direction::Output) {
      continue;
    }
    const SignalKey key = getTerminalPathKey(term);
    model.displayNameByKey.try_emplace(key, getTerminalDisplayName(term));
    if (boundaryObservedKeys.insert(key).second) {
      scan.boundaryInfo.observedTerms.push_back({termID, key});
    }
  }

  return scan;
}

SignalKey makeMemoryCellStateKey(
    const naja::DNL::DNLInstanceFull& instance,
    size_t cellIndex,
    size_t bitIndex) {
  SignalKey key;
  const auto pathNames = instance.getPath().getPathNames();
  key.first.reserve(pathNames.size() + 1);
  for (const auto& name : pathNames) {
    key.first.push_back(stableSignalKeyNameID(name.getString()));
  }
  key.first.push_back(stableSignalKeyNameID("__MEM_CELL"));
  key.second.push_back(
      static_cast<naja::NL::NLID::DesignObjectID>(cellIndex));
  key.second.push_back(
      static_cast<naja::NL::NLID::DesignObjectID>(bitIndex));
  return key;
}

std::string makeMemoryCellStateDisplayName(
    const naja::DNL::DNLInstanceFull& instance,
    size_t cellIndex,
    size_t bitIndex) {
  std::ostringstream oss;
  oss << instance.getFullPath() << ".__MEM_CELL[" << cellIndex << "]["
      << bitIndex << "]";
  return oss.str();
}

std::unordered_map<const naja::NL::SNLBitTerm*, naja::DNL::DNLID>
collectInstanceTermIDByBitTerm(const naja::DNL::DNLInstanceFull& instance) {
  std::unordered_map<const naja::NL::SNLBitTerm*, naja::DNL::DNLID> termIDs;
  for (naja::DNL::DNLID termID = instance.getTermIndexes().first;
       termID != naja::DNL::DNLID_MAX &&
       termID <= instance.getTermIndexes().second;
       ++termID) {
    const auto& term = naja::DNL::get()->getDNLTerminalFromID(termID);
    if (term.isNull()) {
      continue;
    }
    termIDs.emplace(term.getSnlBitTerm(), termID);
  }
  return termIDs;
}

bool supportsStructuredMemoryModel(
    const naja::NL::SNLDesignModeling::MemoryInterface& interface) {
  if (!interface.isValid()) {
    return false;
  }
  for (const auto& readPort : interface.readPorts) {
    if (readPort.address.size() != interface.abits ||
        readPort.data.size() != interface.width) {
      return false;
    }
  }
  for (const auto& writePort : interface.writePorts) {
    if (writePort.address.size() != interface.abits ||
        writePort.data.size() != interface.width) {
      return false;
    }
    if (!writePort.mask.empty() && writePort.mask.size() != interface.width) {
      return false;
    }
    if (!writePort.extraWriteInputs.empty()) {
      return false;
    }
  }
  return true;
}

naja::DNL::DNLID getRequiredInstanceTermID(
    const std::unordered_map<const naja::NL::SNLBitTerm*, naja::DNL::DNLID>&
        termIDsByBitTerm,
    const naja::NL::SNLBitTerm* term,
    const std::string& instancePath,
    const char* context) {
  const auto termIt = termIDsByBitTerm.find(term);
  if (termIt == termIDsByBitTerm.end()) {
    throw std::runtime_error(
        "Missing DNL term for memory " + std::string(context) + " in instance `" +
        instancePath + "`");
  }
  return termIt->second;
}

bool isNoDriverTerm(naja::DNL::DNLID termID) {
  auto* dnl = naja::DNL::get();
  if (dnl == nullptr || termID == naja::DNL::DNLID_MAX) {
    return true;
  }
  const auto& term = dnl->getDNLTerminalFromID(termID);
  if (term.isNull() || term.getIsoID() == naja::DNL::DNLID_MAX) {
    return true;
  }
  const auto& iso = dnl->getDNLIsoDB().getIsoFromIsoIDconst(term.getIsoID());
  return !iso.isConstant() && iso.getDrivers().empty();
}

bool isConstantZeroTerm(naja::DNL::DNLID termID) {
  auto* dnl = naja::DNL::get();
  if (dnl == nullptr || termID == naja::DNL::DNLID_MAX) {
    return false;
  }
  const auto& term = dnl->getDNLTerminalFromID(termID);
  if (term.isNull() || term.getIsoID() == naja::DNL::DNLID_MAX) {
    return false;
  }
  return dnl->getDNLIsoDB().getIsoFromIsoIDconst(term.getIsoID()).isConstant0();
}

bool isDisabledMemoryWriteEnable(naja::DNL::DNLID termID) {
  // Some lowered memories expose fixed-width write ports even when a
  // particular port is unused by the RTL. In that shape the enable pin can
  // have a net but no leaf driver; treating it as an active symbolic input
  // would pull unrelated address/data cones into the SEC memory transition.
  // A constant-0 or undriven enable cannot assert in the concrete netlist, so
  // the whole write port is semantically inactive and should be ignored.
  return isConstantZeroTerm(termID) || isNoDriverTerm(termID);
}

void appendPendingMemoryInstance(
    ExtractContext& ctx,
    SequentialDesignModel& model,
    const naja::DNL::DNLInstanceFull& instance) {
  const auto interface =
      naja::NL::SNLDesignModeling::getMemoryInterface(instance.getSNLInstance());
  PendingMemoryInstance pending;
  pending.width = interface.width;
  pending.depth = interface.depth;
  pending.abits = interface.abits;
  pending.resetMode = interface.resetMode;

  InstanceBoundaryInfo boundaryInfo;
  boundaryInfo.instancePath = instance.getFullPath();
  for (naja::DNL::DNLID termID = instance.getTermIndexes().first;
       termID != naja::DNL::DNLID_MAX &&
       termID <= instance.getTermIndexes().second;
       ++termID) {
    const auto& term = naja::DNL::get()->getDNLTerminalFromID(termID);
    if (term.isNull() ||
        term.getSnlBitTerm()->getDirection() ==
            naja::NL::SNLBitTerm::Direction::Output) {
      continue;
    }
    const SignalKey key = getTerminalPathKey(term);
    model.displayNameByKey.try_emplace(key, getTerminalDisplayName(term));
    boundaryInfo.observedTerms.push_back({termID, key});
  }

  for (size_t cellIndex = 0; cellIndex < interface.depth; ++cellIndex) {
    for (size_t bitIndex = 0; bitIndex < interface.width; ++bitIndex) {
      auto key = makeMemoryCellStateKey(instance, cellIndex, bitIndex);
      auto displayName = makeMemoryCellStateDisplayName(instance, cellIndex, bitIndex);
      model.displayNameByKey.try_emplace(key, displayName);
      boundaryInfo.stateKeys.push_back(key);
      pending.cellStates.push_back({key, std::move(displayName), cellIndex, bitIndex});
    }
  }

  const auto termIDsByBitTerm = collectInstanceTermIDByBitTerm(instance);
  // Modeled memories always expose a reset terminal on the lowered primitive,
  // but SEC should only rebuild that cone when the memory semantics actually
  // use reset. Otherwise a disabled RST pin becomes a fake dependency surface.
  if (pending.resetMode != naja::NL::SNLDesignModeling::MemoryResetMode::None &&
      interface.reset != nullptr) {
    pending.resetTermID = getRequiredInstanceTermID(
        termIDsByBitTerm,
        interface.reset,
        boundaryInfo.instancePath,
        "reset");
  }
  pending.readPorts.reserve(interface.readPorts.size());
  for (size_t portIndex = 0; portIndex < interface.readPorts.size(); ++portIndex) {
    const auto& readPort = interface.readPorts[portIndex];
    PendingMemoryReadPort pendingReadPort;
    pendingReadPort.addressTermIDs.reserve(readPort.address.size());
    pendingReadPort.dataTermIDs.reserve(readPort.data.size());
    size_t bitIndex = 0;
    for (auto* addressTerm : readPort.address) {
      pendingReadPort.addressTermIDs.push_back(
          getRequiredInstanceTermID(
              termIDsByBitTerm,
              addressTerm,
              boundaryInfo.instancePath,
              "read-address"));
    }
    for (auto* dataTerm : readPort.data) {
      const auto termID = getRequiredInstanceTermID(
          termIDsByBitTerm, dataTerm, boundaryInfo.instancePath, "read-data");
      pendingReadPort.dataTermIDs.push_back(termID);
      const auto keyIt = ctx.inputKeyByTerm.find(termID);
      if (keyIt == ctx.inputKeyByTerm.end()) {
        throw std::runtime_error(
            "Missing SEC state key for memory read-data bit in instance `" +
            boundaryInfo.instancePath + "`");
      }
      pending.readOutputs.push_back({keyIt->second, portIndex, bitIndex});
      ++bitIndex;
    }
    pending.readPorts.push_back(std::move(pendingReadPort));
  }

  pending.writePorts.reserve(interface.writePorts.size());
  for (const auto& writePort : interface.writePorts) {
    std::vector<naja::DNL::DNLID> enableTermIDs;
    enableTermIDs.reserve(writePort.enables.size());
    for (auto* enableTerm : writePort.enables) {
      enableTermIDs.push_back(
          getRequiredInstanceTermID(
              termIDsByBitTerm,
              enableTerm,
              boundaryInfo.instancePath,
              "write-enable"));
    }
    if (std::any_of(
            enableTermIDs.begin(),
            enableTermIDs.end(),
            isDisabledMemoryWriteEnable)) {
      continue;
    }

    PendingMemoryWritePort pendingWritePort;
    pendingWritePort.addressTermIDs.reserve(writePort.address.size());
    pendingWritePort.dataTermIDs.reserve(writePort.data.size());
    pendingWritePort.maskTermIDs.reserve(writePort.mask.size());
    pendingWritePort.enableTermIDs = std::move(enableTermIDs);
    for (auto* addressTerm : writePort.address) {
      pendingWritePort.addressTermIDs.push_back(
          getRequiredInstanceTermID(
              termIDsByBitTerm,
              addressTerm,
              boundaryInfo.instancePath,
              "write-address"));
    }
    for (auto* dataTerm : writePort.data) {
      pendingWritePort.dataTermIDs.push_back(
          getRequiredInstanceTermID(
              termIDsByBitTerm, dataTerm, boundaryInfo.instancePath, "write-data"));
    }
    for (auto* maskTerm : writePort.mask) {
      pendingWritePort.maskTermIDs.push_back(
          getRequiredInstanceTermID(
              termIDsByBitTerm, maskTerm, boundaryInfo.instancePath, "write-mask"));
    }
    for (const auto& extraWriteTerms : writePort.extraWriteInputs) {
      std::vector<naja::DNL::DNLID> pendingExtraTerms;
      pendingExtraTerms.reserve(extraWriteTerms.size());
      for (auto* extraTerm : extraWriteTerms) {
        pendingExtraTerms.push_back(
            getRequiredInstanceTermID(
                termIDsByBitTerm,
                extraTerm,
                boundaryInfo.instancePath,
                "extra-write"));
      }
      pendingWritePort.extraWriteInputTermIDs.push_back(
          std::move(pendingExtraTerms));
    }
    pending.writePorts.push_back(std::move(pendingWritePort));
  }

  ctx.instanceBoundaryInfos.push_back(std::move(boundaryInfo));
  pending.boundaryInfoIndex = ctx.instanceBoundaryInfos.size() - 1;
  ctx.pendingMemoryInstances.push_back(std::move(pending));
}

void appendPendingTransitionsForInstance(
    ExtractContext& ctx,
    SequentialDesignModel& model,
    const SequentialInstanceScan& scan) {
  ctx.instanceBoundaryInfos.push_back(scan.boundaryInfo);
  const size_t boundaryInfoIndex = ctx.instanceBoundaryInfos.size() - 1;

  auto markUnsupportedInstanceStateOutputs = [&]() {
    for (const auto& key : ctx.instanceBoundaryInfos[boundaryInfoIndex].stateKeys) {
      ctx.unsupportedStateBits.insert(key);
    }
  };
  auto abstractUnsupportedInstanceAsBoundary = [&](const std::string& reason) {
    const auto& info = ctx.instanceBoundaryInfos[boundaryInfoIndex];
    model.abstractedSequentialBoundaries.push_back(
        "Abstracted uncomputable sequential instance `" + info.instancePath +
        "` as a SEC boundary: " + reason);
    model.abstractedSequentialBoundaryDetails.push_back(
        makeAbstractedBoundaryDetail(info));

    for (const auto& key : info.stateKeys) {
      ctx.abstractedBoundaryStateKeys.insert(key);
    }

    for (const auto& observedTerm : info.observedTerms) {
      if (ctx.abstractedBoundaryObservedKeys.insert(observedTerm.key).second) {
        ctx.abstractedBoundaryObservedTerms.emplace_back(observedTerm.termID, observedTerm.key);
        ctx.allObservedOutputs.insert(observedTerm.key);
      }
      ctx.prunedBuilderOutputTerms.insert(observedTerm.termID);
    }
  };

  const size_t independentStateOutputCount =
      countIndependentStateOutputs(scan.stateOutputs);
  const size_t pendingStart = ctx.pendingTransitions.size();
  const size_t complementedStart = model.complementedStateRelations.size();
  bool unsupportedInstance = false;
  bool abstractedUnsupportedInstance = false;
  std::string abstractedUnsupportedReason;

  // Track sequential behavior per state output bit. This keeps vector flops and
  // other multi-output sequential cells from being collapsed into a single
  // instance-wide transition record.
  for (const auto& stateOutput : scan.stateOutputs) {
    if (findComplementedPrimaryStateOutput(stateOutput, scan.stateOutputs) != nullptr) {
      continue;
    }

    PendingTransition pending;
    pending.stateTermID = stateOutput.termID;
    pending.stateKey = ctx.inputKeyByTerm.at(pending.stateTermID);
    pending.statePinName = stateOutput.pinName;
    pending.stateBit = stateOutput.bit;
    pending.independentStateOutputCount = independentStateOutputCount;
    pending.boundaryInfoIndex = boundaryInfoIndex;
    pending.pinTermIDs = scan.pinTermIDs;

    std::vector<ComplementedStateRelation> complementedRelations;
    for (const auto& candidate : scan.stateOutputs) {
      if (candidate.termID == stateOutput.termID || candidate.bit != stateOutput.bit) {
        continue;
      }
      if (!isComplementedStateOutput(stateOutput.pinName, candidate.pinName)) {
        continue;
      }
      const SignalKey complementedKey = ctx.inputKeyByTerm.at(candidate.termID);
      pending.complementedStateKeys.push_back(complementedKey);
      complementedRelations.push_back({pending.stateKey, complementedKey});
    }

    try {
      validatePendingTransitionShape(pending);
    } catch (const std::exception& e) {
      if (ctx.abstractUncomputableSequentialBoundaries) {
        abstractedUnsupportedInstance = true;
        abstractedUnsupportedReason = e.what();
        break;
      }
      const auto displayIt = model.displayNameByKey.find(pending.stateKey);
      model.unsupportedReasons.push_back(
          "Unsupported sequential primitive for `" +
          (displayIt == model.displayNameByKey.end() ? signalKeyToString(pending.stateKey)
                                                     : displayIt->second) +
          "`: " + e.what());
      ctx.unsupportedStateBits.insert(pending.stateKey);
      for (const auto& complementedKey : pending.complementedStateKeys) {
        ctx.unsupportedStateBits.insert(complementedKey);
      }
      unsupportedInstance = true;
      continue;
    }

    model.complementedStateRelations.insert(
        model.complementedStateRelations.end(),
        complementedRelations.begin(),
        complementedRelations.end());
    ctx.pendingTransitions.push_back(std::move(pending));
  }

  if (abstractedUnsupportedInstance) {
    ctx.pendingTransitions.erase(
        ctx.pendingTransitions.begin() + static_cast<std::ptrdiff_t>(pendingStart),
        ctx.pendingTransitions.end());
    model.complementedStateRelations.erase(
        model.complementedStateRelations.begin() +
            static_cast<std::ptrdiff_t>(complementedStart),
        model.complementedStateRelations.end());
    abstractUnsupportedInstanceAsBoundary(abstractedUnsupportedReason);
    return;
  }

  if (unsupportedInstance) {
    markUnsupportedInstanceStateOutputs();
  }
}

void collectSequentialTransitions(ExtractContext& ctx, SequentialDesignModel& model) {
  // Record enough pin information to reconstruct Q' after the combinational
  // Boolean expressions have been built.
  for (auto leafID : ctx.dnl->getLeaves()) {
    const auto& instance = ctx.dnl->getDNLInstanceFromID(leafID);
    if (naja::NL::SNLDesignModeling::hasMemoryInterface(
            instance.getSNLInstance()->getModel()) &&
        supportsStructuredMemoryModel(
            naja::NL::SNLDesignModeling::getMemoryInterface(
                instance.getSNLInstance()))) {
      appendPendingMemoryInstance(ctx, model, instance);
      continue;
    }
    const auto scan = scanSequentialInstance(instance, ctx.inputKeyByTerm, model);
    if (!scan.has_value()) {
      continue;
    }
    appendPendingTransitionsForInstance(ctx, model, *scan);
  }
}

std::vector<naja::DNL::DNLID> collectInitialObservedTerms(const ExtractContext& ctx) {
  std::vector<naja::DNL::DNLID> initialObservedTerms;
  initialObservedTerms.reserve(
      ctx.topOutputKeyByTerm.size() + ctx.abstractedBoundaryObservedTerms.size());
  std::unordered_set<naja::DNL::DNLID> initialObservedTermSet;
  for (const auto& [termID, _] : ctx.topOutputKeyByTerm) {
    if (initialObservedTermSet.insert(termID).second) {
      initialObservedTerms.push_back(termID);
    }
  }
  for (const auto& [termID, _] : ctx.abstractedBoundaryObservedTerms) {
    if (initialObservedTermSet.insert(termID).second) {
      initialObservedTerms.push_back(termID);
    }
  }
  return initialObservedTerms;
}

void buildInitialObservedOutputClouds(ExtractContext& ctx, SequentialDesignModel& model) {
  const auto initialObservedTerms = collectInitialObservedTerms(ctx);
  std::unordered_set<naja::DNL::DNLID> collectedOutputSet(
      ctx.builder.getOutputs().begin(), ctx.builder.getOutputs().end());
  std::vector<naja::DNL::DNLID> initialMaterializedOutputs;
  initialMaterializedOutputs.reserve(initialObservedTerms.size());
  for (const auto outputTermID : initialObservedTerms) {
    if (collectedOutputSet.find(outputTermID) != collectedOutputSet.end()) {
      initialMaterializedOutputs.push_back(outputTermID);
    }
  }
  ctx.builder.setOutputs(initialMaterializedOutputs);
  if (ctx.secDiagEnabled) {
    fprintf(
        stderr,
        "SEC diag: extract(%s) abstracted_boundaries=%zu pruned_builder_outputs=%zu initial_observed_outputs=%zu\n",
        ctx.topName.c_str(),
        model.abstractedSequentialBoundaries.size(),
        ctx.prunedBuilderOutputTerms.size(),
        initialMaterializedOutputs.size());
    fflush(stderr);
  }

  // Materialize the combinational BoolExpr DAGs for the design boundary.
  if (ctx.secDiagEnabled) {
    fprintf(stderr, "SEC diag: extract(%s) build begin\n", ctx.topName.c_str());
    fflush(stderr);
  }
  ctx.builder.build();
  if (ctx.secDiagEnabled) {
    fprintf(stderr, "SEC diag: extract(%s) build end\n", ctx.topName.c_str());
    fflush(stderr);
  }
}

void publishNormalizedBoundary(ExtractContext& ctx, SequentialDesignModel& model) {
  for (const auto& key : ctx.abstractedBoundaryStateKeys) {
    ctx.stateBits.erase(key);
    ctx.environmentInputs.insert(key);
  }

  model.topInputKeys.assign(ctx.topInputKeys.begin(), ctx.topInputKeys.end());
  model.topOutputKeys.assign(ctx.topOutputKeys.begin(), ctx.topOutputKeys.end());
  model.environmentInputs.assign(ctx.environmentInputs.begin(), ctx.environmentInputs.end());
  model.internalBoundaryInputKeys.assign(
      ctx.internalBoundaryInputKeys.begin(), ctx.internalBoundaryInputKeys.end());
  model.internalBoundaryOutputKeys.assign(
      ctx.internalBoundaryOutputKeys.begin(), ctx.internalBoundaryOutputKeys.end());
  model.stateBits.assign(ctx.stateBits.begin(), ctx.stateBits.end());
  model.allObservedOutputs.assign(ctx.allObservedOutputs.begin(), ctx.allObservedOutputs.end());
  if (ctx.secDiagEnabled) {
    fprintf(
        stderr,
        "SEC diag: extract(%s) boundary normalized env=%zu state=%zu outputs=%zu pending=%zu\n",
        ctx.topName.c_str(),
        model.environmentInputs.size(),
        model.stateBits.size(),
        model.allObservedOutputs.size(),
        ctx.pendingTransitions.size());
    fflush(stderr);
  }
}

void recordBoundaryInputVars(
    const ExtractContext& ctx,
    const std::vector<naja::DNL::DNLID>& builderInputs,
    const std::vector<size_t>& termDNLID2varID,
    SequentialDesignModel& model) {
  // Preserve the symbolic variable chosen by the clause builder for each
  // aligned SEC input/state signal.
  for (const auto inputTermID : builderInputs) {
    const auto keyIt = ctx.inputKeyByTerm.find(inputTermID);
    if (keyIt == ctx.inputKeyByTerm.end()) {
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
  if (ctx.secDiagEnabled) {
    fprintf(
        stderr,
        "SEC diag: extract(%s) mapped boundary vars=%zu\n",
        ctx.topName.c_str(),
        model.inputVarByKey.size());
    fflush(stderr);
  }
}

size_t getNextSyntheticVarID(const SequentialDesignModel& model) {
  size_t nextVarID = 2;
  for (const auto& [_, varID] : model.inputVarByKey) {
    nextVarID = std::max(nextVarID, varID + 1);
  }
  return nextVarID;
}

void assignStructuredMemoryStateVars(
    const ExtractContext& ctx,
    SequentialDesignModel& model) {
  size_t nextVarID = getNextSyntheticVarID(model);
  for (const auto& pendingMemory : ctx.pendingMemoryInstances) {
    for (const auto& cellState : pendingMemory.cellStates) {
      model.stateBits.push_back(cellState.key);
      model.inputVarByKey.emplace(cellState.key, nextVarID++);
    }
  }
}

std::vector<naja::DNL::DNLID> collectStructuredMemoryDependencyTerms(
    const ExtractContext& ctx) {
  std::vector<naja::DNL::DNLID> termIDs;
  std::unordered_set<naja::DNL::DNLID> seen;
  for (const auto& pendingMemory : ctx.pendingMemoryInstances) {
    if (pendingMemory.resetTermID.has_value() &&
        seen.insert(*pendingMemory.resetTermID).second) {
      termIDs.push_back(*pendingMemory.resetTermID);
    }
    for (const auto& readPort : pendingMemory.readPorts) {
      for (const auto termID : readPort.addressTermIDs) {
        if (seen.insert(termID).second) {
          termIDs.push_back(termID);
        }
      }
    }
    for (const auto& writePort : pendingMemory.writePorts) {
      for (const auto termID : writePort.addressTermIDs) {
        if (seen.insert(termID).second) {
          termIDs.push_back(termID);
        }
      }
      for (const auto termID : writePort.dataTermIDs) {
        if (seen.insert(termID).second) {
          termIDs.push_back(termID);
        }
      }
      for (const auto termID : writePort.maskTermIDs) {
        if (seen.insert(termID).second) {
          termIDs.push_back(termID);
        }
      }
      for (const auto termID : writePort.enableTermIDs) {
        if (seen.insert(termID).second) {
          termIDs.push_back(termID);
        }
      }
    }
  }
  return termIDs;
}

BoolExpr* getStructuredMemoryTermExprOrThrow(
    naja::DNL::DNLID termID,
    std::unordered_map<naja::DNL::DNLID, BoolExpr*>& outputExprByTerm,
    const std::unordered_map<naja::DNL::DNLID, BuilderSkippedOutputInfo>&
        skippedOutputsByTerm,
    const std::vector<naja::DNL::DNLID>& builderInputs,
    const std::vector<naja::DNL::DNLID>& builderOutputs,
    const std::vector<size_t>& termDNLID2varID) {
  if (const auto exprIt = outputExprByTerm.find(termID);
      exprIt != outputExprByTerm.end()) {
    return exprIt->second;
  }

  auto* dnl = naja::DNL::get();
  const std::string displayName =
      dnl == nullptr ? ("term#" + std::to_string(termID))
                     : getTerminalDisplayName(dnl->getDNLTerminalFromID(termID));

  if (const auto skippedIt = skippedOutputsByTerm.find(termID);
      skippedIt != skippedOutputsByTerm.end()) {
    if (const auto connectivitySkip = getConnectivitySkipInfo(skippedIt->second);
        connectivitySkip.has_value()) {
      throw std::runtime_error(
          "Structured memory dependency `" + displayName +
          "` was skipped because " + connectivitySkip->detail);
    }
    throw std::runtime_error(
        "Structured memory dependency `" + displayName +
        "` is unsupported: " + skippedIt->second.detail);
  }

  const auto built = buildObservedExprForTerm(
      termID,
      outputExprByTerm,
      builderInputs,
      builderOutputs,
      termDNLID2varID,
      true);
  if (built.expr != nullptr) {
    outputExprByTerm.emplace(termID, built.expr);
    return built.expr;
  }
  if (built.connectivitySkip.has_value()) {
    throw std::runtime_error(
        "Structured memory dependency `" + displayName +
        "` was skipped because " +
        built.connectivitySkip->detail);
  }
  throw std::runtime_error(
      "Structured memory dependency `" + displayName +
      "` is unsupported: " +
      built.unsupportedReason);
}

bool isNoDriverSkippedStructuredMemoryTerm(
    naja::DNL::DNLID termID,
    const std::unordered_map<naja::DNL::DNLID, BuilderSkippedOutputInfo>&
        skippedOutputsByTerm) {
  const auto skippedIt = skippedOutputsByTerm.find(termID);
  if (skippedIt == skippedOutputsByTerm.end()) {
    return false;
  }
  const auto connectivitySkip = getConnectivitySkipInfo(skippedIt->second);
  return connectivitySkip.has_value() &&
         connectivitySkip->origin == ConnectivitySkipOrigin::NoDriver;
}

bool isDisabledMemoryWriteEnable(
    naja::DNL::DNLID termID,
    const std::unordered_map<naja::DNL::DNLID, BuilderSkippedOutputInfo>&
        skippedOutputsByTerm) {
  return isDisabledMemoryWriteEnable(termID) ||
         isNoDriverSkippedStructuredMemoryTerm(termID, skippedOutputsByTerm);
}

void buildStructuredMemoryTransitions(
    const ExtractContext& ctx,
    SequentialDesignModel& model,
    const std::vector<naja::DNL::DNLID>& builderInputs,
    const std::vector<naja::DNL::DNLID>& builderOutputs,
    const std::vector<size_t>& termDNLID2varID,
    std::unordered_map<naja::DNL::DNLID, BoolExpr*>& outputExprByTerm,
    const std::unordered_map<naja::DNL::DNLID, BuilderSkippedOutputInfo>&
        skippedOutputsByTerm) {
  for (const auto& pendingMemory : ctx.pendingMemoryInstances) {
    std::vector<std::vector<BoolExpr*>> readAddressExprs;
    readAddressExprs.reserve(pendingMemory.readPorts.size());
    for (const auto& readPort : pendingMemory.readPorts) {
      std::vector<BoolExpr*> addressExprs;
      addressExprs.reserve(readPort.addressTermIDs.size());
      for (const auto termID : readPort.addressTermIDs) {
        // Structured-memory dependency materialization can add extra
        // boundary roots that were not present in the original top-output
        // build. Read-address reconstruction must use that merged frontier,
        // otherwise a dependency found in the batch phase can disappear when
        // we rebuild the per-port expressions here.
        addressExprs.push_back(getStructuredMemoryTermExprOrThrow(
            termID,
            outputExprByTerm,
            skippedOutputsByTerm,
            builderInputs,
            builderOutputs,
            termDNLID2varID));
      }
      readAddressExprs.push_back(std::move(addressExprs));
    }

    struct WritePortExprs {
      bool disabled = false;
      std::vector<BoolExpr*> addressExprs;
      std::vector<BoolExpr*> dataExprs;
      std::vector<BoolExpr*> maskExprs;
      std::vector<BoolExpr*> enableExprs;
    };
    std::vector<WritePortExprs> writePortExprs;
    writePortExprs.reserve(pendingMemory.writePorts.size());
    for (const auto& writePort : pendingMemory.writePorts) {
      WritePortExprs exprs;
      exprs.addressExprs.reserve(writePort.addressTermIDs.size());
      exprs.dataExprs.reserve(writePort.dataTermIDs.size());
      exprs.maskExprs.reserve(writePort.maskTermIDs.size());
      exprs.enableExprs.reserve(writePort.enableTermIDs.size());
      for (const auto termID : writePort.enableTermIDs) {
        if (isDisabledMemoryWriteEnable(termID, skippedOutputsByTerm)) {
          exprs.disabled = true;
          break;
        }
        exprs.enableExprs.push_back(getStructuredMemoryTermExprOrThrow(
            termID,
            outputExprByTerm,
            skippedOutputsByTerm,
            builderInputs,
            builderOutputs,
            termDNLID2varID));
      }
      if (exprs.disabled) {
        writePortExprs.push_back(std::move(exprs));
        continue;
      }
      for (const auto termID : writePort.addressTermIDs) {
        exprs.addressExprs.push_back(getStructuredMemoryTermExprOrThrow(
            termID,
            outputExprByTerm,
            skippedOutputsByTerm,
            builderInputs,
            builderOutputs,
            termDNLID2varID));
      }
      for (const auto termID : writePort.dataTermIDs) {
        exprs.dataExprs.push_back(getStructuredMemoryTermExprOrThrow(
            termID,
            outputExprByTerm,
            skippedOutputsByTerm,
            builderInputs,
            builderOutputs,
            termDNLID2varID));
      }
      for (const auto termID : writePort.maskTermIDs) {
        exprs.maskExprs.push_back(getStructuredMemoryTermExprOrThrow(
            termID,
            outputExprByTerm,
            skippedOutputsByTerm,
            builderInputs,
            builderOutputs,
            termDNLID2varID));
      }
      writePortExprs.push_back(std::move(exprs));
    }

    BoolExpr* resetExpr = nullptr;
    if (pendingMemory.resetTermID.has_value()) {
      resetExpr = getStructuredMemoryTermExprOrThrow(
          *pendingMemory.resetTermID,
          outputExprByTerm,
          skippedOutputsByTerm,
          builderInputs,
          builderOutputs,
          termDNLID2varID);
    }
    const auto resetAssertedExpr = [&]() -> BoolExpr* {
      switch (pendingMemory.resetMode) {
        case naja::NL::SNLDesignModeling::MemoryResetMode::AsyncLow:
        case naja::NL::SNLDesignModeling::MemoryResetMode::SyncLow:
          return resetExpr == nullptr ? nullptr : BoolExpr::Not(resetExpr);
        case naja::NL::SNLDesignModeling::MemoryResetMode::AsyncHigh:
        case naja::NL::SNLDesignModeling::MemoryResetMode::SyncHigh:
          return resetExpr;
        case naja::NL::SNLDesignModeling::MemoryResetMode::None:
        default:
          return nullptr;
      }
    }();

    std::vector<std::vector<BoolExpr*>> cellNextExprs(
        pendingMemory.depth,
        std::vector<BoolExpr*>(pendingMemory.width, nullptr));
    for (const auto& cellState : pendingMemory.cellStates) {
      const auto varIt = model.inputVarByKey.find(cellState.key);
      if (varIt == model.inputVarByKey.end()) {
        throw std::runtime_error(
            "Missing synthetic SEC variable for memory cell state `" +
            cellState.displayName + "`");
      }
      BoolExpr* next = BoolExpr::Var(varIt->second);
      for (size_t portIndex = 0; portIndex < pendingMemory.writePorts.size(); ++portIndex) {
        const auto& writePort = pendingMemory.writePorts[portIndex];
        const auto& exprs = writePortExprs[portIndex];
        if (exprs.disabled) {
          continue;
        }
        std::vector<BoolExpr*> conditions;
        conditions.reserve(2 + exprs.enableExprs.size());
        conditions.push_back(buildAddressEqualsExpr(
            exprs.addressExprs, cellState.cellIndex));
        for (auto* enableExpr : exprs.enableExprs) {
          conditions.push_back(enableExpr);
        }
        if (!exprs.maskExprs.empty()) {
          conditions.push_back(exprs.maskExprs[cellState.bitIndex]);
        }
        BoolExpr* writeCondition = makeAndChain(conditions);
        next = makeIte(
            writeCondition,
            exprs.dataExprs[cellState.bitIndex],
            next);
      }
      if (resetAssertedExpr != nullptr) {
        next = makeIte(resetAssertedExpr, BoolExpr::createFalse(), next);
        model.initialStateValueByKey.emplace(cellState.key, false);
      }
      model.nextStateExprByStateKey.emplace(cellState.key, next);
      cellNextExprs[cellState.cellIndex][cellState.bitIndex] = next;
    }

    for (const auto& readOutput : pendingMemory.readOutputs) {
      const auto varIt = model.inputVarByKey.find(readOutput.key);
      if (varIt == model.inputVarByKey.end()) {
        throw std::runtime_error(
            "Missing SEC variable for memory read-output state `" +
            signalKeyToString(readOutput.key) + "`");
      }
      const auto& addressExprs = readAddressExprs[readOutput.portIndex];
      BoolExpr* next = cellNextExprs[0][readOutput.bitIndex];
      for (size_t cellIndex = 1; cellIndex < pendingMemory.depth; ++cellIndex) {
        next = makeIte(
            buildAddressEqualsExpr(addressExprs, cellIndex),
            cellNextExprs[cellIndex][readOutput.bitIndex],
            next);
      }
      if (resetAssertedExpr != nullptr) {
        next = makeIte(resetAssertedExpr, BoolExpr::createFalse(), next);
        model.initialStateValueByKey.emplace(readOutput.key, false);
      }
      model.nextStateExprByStateKey.emplace(readOutput.key, next);
    }
  }
}

void materializeBoundaryObservedOutputs(
    const std::vector<std::pair<naja::DNL::DNLID, SignalKey>>& observedTerms,
    const std::unordered_map<naja::DNL::DNLID, BoolExpr*>& outputExprByTerm,
    const std::unordered_map<naja::DNL::DNLID, BuilderSkippedOutputInfo>& skippedOutputsByTerm,
    const std::vector<naja::DNL::DNLID>& builderInputs,
    const std::vector<naja::DNL::DNLID>& builderOutputs,
    const std::vector<size_t>& termDNLID2varID,
    SequentialDesignModel& model) {
  for (const auto& [termID, key] : observedTerms) {
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
        termID, outputExprByTerm, builderInputs, builderOutputs, termDNLID2varID);
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
}

void materializeTopObservedOutputs(
    const std::unordered_map<naja::DNL::DNLID, SignalKey>& topOutputKeyByTerm,
    const std::unordered_map<naja::DNL::DNLID, BoolExpr*>& outputExprByTerm,
    const std::unordered_map<naja::DNL::DNLID, BuilderSkippedOutputInfo>& skippedOutputsByTerm,
    SequentialDesignModel& model) {
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
}

struct RebuiltTransitionArtifacts {
  std::unordered_set<SignalKey, SignalKeyHash> requiredStateKeys;
  std::set<SignalKey, SignalKeyLess> lateAbstractedBoundaryStateKeys;
  std::vector<std::pair<naja::DNL::DNLID, SignalKey>> lateAbstractedBoundaryObservedTerms;
};

RebuiltTransitionArtifacts rebuildRequiredStateTransitions(
    ExtractContext& ctx,
    SequentialDesignModel& model,
    std::vector<naja::DNL::DNLID>& builderInputs,
    std::vector<naja::DNL::DNLID>& builderOutputs,
    std::vector<size_t>& termDNLID2varID,
    std::unordered_map<naja::DNL::DNLID, BoolExpr*>& outputExprByTerm,
    std::unordered_map<naja::DNL::DNLID, BuilderSkippedOutputInfo>& skippedOutputsByTerm) {
  RebuiltTransitionArtifacts artifacts;
  auto markConnectivitySkippedState =
      [&](const SignalKey& key, const ConnectivitySkipInfo& info) {
        model.connectivitySkipInfoByKey.emplace(key, info);
      };
  auto markUnsupportedState = [&](const SignalKey& key) {
    ctx.unsupportedStateBits.insert(key);
  };

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

        const auto& info = ctx.instanceBoundaryInfos[boundaryInfoIndex];
        if (ctx.secDiagEnabled) {
          fprintf(
              stderr,
              "SEC diag: extract(%s) late abstracted sequential instance `%s`: %s\n",
              ctx.topName.c_str(),
              info.instancePath.c_str(),
              reason.c_str());
          fflush(stderr);
        }
        model.abstractedSequentialBoundaries.push_back(
            "Abstracted uncomputable sequential instance `" +
            info.instancePath + "` as a SEC boundary: " + reason);
        model.abstractedSequentialBoundaryDetails.push_back(
            makeAbstractedBoundaryDetail(info));
        for (const auto& key : info.stateKeys) {
          artifacts.lateAbstractedBoundaryStateKeys.insert(key);
        }
        for (const auto& observedTerm : info.observedTerms) {
          if (lateAbstractedBoundaryObservedKeys.insert(observedTerm.key).second) {
            artifacts.lateAbstractedBoundaryObservedTerms.emplace_back(
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
  pendingIndexByStateKey.reserve(ctx.pendingTransitions.size() * 2);
  for (size_t pendingIndex = 0; pendingIndex < ctx.pendingTransitions.size(); ++pendingIndex) {
    const auto& pending = ctx.pendingTransitions[pendingIndex];
    pendingIndexByStateKey.emplace(pending.stateKey, pendingIndex);
    for (const auto& complementedKey : pending.complementedStateKeys) {
      pendingIndexByStateKey.emplace(complementedKey, pendingIndex);
    }
  }

  std::unordered_set<size_t> requiredPendingIndexes;
  std::unordered_set<naja::DNL::DNLID> materializedOutputTerms;
  materializedOutputTerms.reserve(outputExprByTerm.size());
  for (const auto& [termID, _] : outputExprByTerm) {
    materializedOutputTerms.insert(termID);
  }
  std::deque<size_t> pendingWorkQueue;
  std::deque<SignalKey> stateDependencyWorkQueue;
  std::unordered_set<SignalKey, SignalKeyHash> expandedStateDependencies;
  auto enqueueRequiredStateKey = [&](const SignalKey& key) {
    if (!artifacts.requiredStateKeys.insert(key).second) {
      return;
    }
    stateDependencyWorkQueue.push_back(key);
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

  // Follow the state/output dependency frontier lazily so SEC only rebuilds the
  // sequential update cones that can actually influence covered observations.
  // States with prebuilt next-state relations, such as structured memories,
  // participate in the same frontier expansion before we trim the SEC model.
  while (!stateDependencyWorkQueue.empty() || !pendingWorkQueue.empty()) {
    while (!stateDependencyWorkQueue.empty()) {
      const SignalKey key = stateDependencyWorkQueue.front();
      stateDependencyWorkQueue.pop_front();
      const auto nextStateIt = model.nextStateExprByStateKey.find(key);
      if (nextStateIt == model.nextStateExprByStateKey.end()) {
        continue;
      }
      if (!expandedStateDependencies.insert(key).second) {
        continue;
      }
      enqueueStateDependenciesFromExpr(nextStateIt->second);
    }

    if (pendingWorkQueue.empty()) {
      continue;
    }

    std::vector<size_t> batchPendingIndexes;
    std::vector<naja::DNL::DNLID> batchOutputTerms;
    while (!pendingWorkQueue.empty()) {
      const size_t pendingIndex = pendingWorkQueue.front();
      pendingWorkQueue.pop_front();
      batchPendingIndexes.push_back(pendingIndex);

      const auto& pending = ctx.pendingTransitions[pendingIndex];
      artifacts.requiredStateKeys.insert(pending.stateKey);
      for (const auto& complementedKey : pending.complementedStateKeys) {
        artifacts.requiredStateKeys.insert(complementedKey);
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
          batchOutputTerms, ctx.secDiagEnabled, ctx.topName.c_str(), "dependency build");
      appendUniqueTermIDs(builderInputs, dependencyOutputs.inputs);
      appendUniqueTermIDs(builderOutputs, dependencyOutputs.outputs);
      mergeBuilderTermVarIDs(termDNLID2varID, dependencyOutputs.termDNLID2varID);
      for (const auto& [termID, expr] : dependencyOutputs.outputExprByTerm) {
        outputExprByTerm.emplace(termID, expr);
      }
      for (const auto& [termID, info] : dependencyOutputs.skippedOutputsByTerm) {
        skippedOutputsByTerm.emplace(termID, info);
      }
    }

    for (const auto pendingIndex : batchPendingIndexes) {
      const auto& pending = ctx.pendingTransitions[pendingIndex];
      std::optional<ConnectivitySkipInfo> skippedPinInfo;
      bool abortPending = false;
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

        if (ctx.abstractUncomputableSequentialBoundaries) {
          recordLateAbstractedInstanceBoundary(
              pending.boundaryInfoIndex,
              "unsupported sequential pin `" + pinName + "`: " +
                  skippedIt->second.detail);
          abortPending = true;
          break;
        }

        model.unsupportedReasons.push_back(
            "Unsupported sequential primitive for `" + signalKeyToString(pending.stateKey) +
            "`: Sequential pin `" + pinName + "` is unsupported: " +
            skippedIt->second.detail);
        markUnsupportedState(pending.stateKey);
        for (const auto& complementedKey : pending.complementedStateKeys) {
          markUnsupportedState(complementedKey);
        }
        abortPending = true;
        break;
      }

      if (abortPending) {
        continue;
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
          model.nextStateExprByStateKey.emplace(complementedKey, BoolExpr::Not(nextStateExpr));
          if (artifacts.requiredStateKeys.find(complementedKey) !=
              artifacts.requiredStateKeys.end()) {
            stateDependencyWorkQueue.push_back(complementedKey);
          }
        }
        stateDependencyWorkQueue.push_back(pending.stateKey);
      } catch (const std::exception& e) {
        if (ctx.abstractUncomputableSequentialBoundaries) {
          recordLateAbstractedInstanceBoundary(pending.boundaryInfoIndex, e.what());
          continue;
        }

        model.unsupportedReasons.push_back(
            "Unsupported sequential primitive for `" + signalKeyToString(pending.stateKey) +
            "`: " + e.what());
        markUnsupportedState(pending.stateKey);
        for (const auto& complementedKey : pending.complementedStateKeys) {
          markUnsupportedState(complementedKey);
        }
      }
    }
  }

  if (ctx.secDiagEnabled) {
    fprintf(
        stderr,
        "SEC diag: extract(%s) rebuilt next-state exprs=%zu init=%zu\n",
        ctx.topName.c_str(),
        model.nextStateExprByStateKey.size(),
        model.initialStateValueByKey.size());
    fflush(stderr);
  }

  return artifacts;
}

void applyRebuiltTransitionArtifacts(
    const ExtractContext& ctx,
    const RebuiltTransitionArtifacts& artifacts,
    SequentialDesignModel& model,
    const std::vector<naja::DNL::DNLID>& builderInputs,
    const std::vector<naja::DNL::DNLID>& builderOutputs,
    const std::vector<size_t>& termDNLID2varID,
    const std::unordered_map<naja::DNL::DNLID, BoolExpr*>& outputExprByTerm,
    const std::unordered_map<naja::DNL::DNLID, BuilderSkippedOutputInfo>& skippedOutputsByTerm) {
  model.stateBits.erase(
      std::remove_if(
          model.stateBits.begin(),
          model.stateBits.end(),
          [&](const SignalKey& key) {
            return artifacts.requiredStateKeys.find(key) == artifacts.requiredStateKeys.end();
          }),
      model.stateBits.end());
  model.complementedStateRelations.erase(
      std::remove_if(
          model.complementedStateRelations.begin(),
          model.complementedStateRelations.end(),
          [&](const ComplementedStateRelation& relation) {
            return artifacts.requiredStateKeys.find(relation.primaryKey) ==
                       artifacts.requiredStateKeys.end() ||
                   artifacts.requiredStateKeys.find(relation.complementedKey) ==
                       artifacts.requiredStateKeys.end();
          }),
      model.complementedStateRelations.end());

  for (const auto& key : artifacts.lateAbstractedBoundaryStateKeys) {
    model.nextStateExprByStateKey.erase(key);
    model.initialStateValueByKey.erase(key);
    if (std::find(model.environmentInputs.begin(), model.environmentInputs.end(), key) ==
        model.environmentInputs.end()) {
      model.environmentInputs.push_back(key);
    }
  }
  if (!artifacts.lateAbstractedBoundaryStateKeys.empty()) {
    model.stateBits.erase(
        std::remove_if(
            model.stateBits.begin(),
            model.stateBits.end(),
            [&](const SignalKey& key) {
              return artifacts.lateAbstractedBoundaryStateKeys.find(key) !=
                     artifacts.lateAbstractedBoundaryStateKeys.end();
            }),
        model.stateBits.end());
    model.complementedStateRelations.erase(
        std::remove_if(
            model.complementedStateRelations.begin(),
            model.complementedStateRelations.end(),
            [&](const ComplementedStateRelation& relation) {
              return artifacts.lateAbstractedBoundaryStateKeys.find(relation.primaryKey) !=
                         artifacts.lateAbstractedBoundaryStateKeys.end() ||
                     artifacts.lateAbstractedBoundaryStateKeys.find(
                         relation.complementedKey) !=
                         artifacts.lateAbstractedBoundaryStateKeys.end();
            }),
        model.complementedStateRelations.end());
  }

  for (const auto& [_, key] : artifacts.lateAbstractedBoundaryObservedTerms) {
    if (std::find(model.allObservedOutputs.begin(), model.allObservedOutputs.end(), key) ==
        model.allObservedOutputs.end()) {
      model.allObservedOutputs.push_back(key);
    }
  }
  materializeBoundaryObservedOutputs(
      artifacts.lateAbstractedBoundaryObservedTerms,
      outputExprByTerm,
      skippedOutputsByTerm,
      builderInputs,
      builderOutputs,
      termDNLID2varID,
      model);
}

void filterUnsupportedAndUnmappedBoundary(ExtractContext& ctx, SequentialDesignModel& model) {
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
  if (!ctx.unsupportedStateBits.empty()) {
    model.stateBits.erase(
        std::remove_if(
            model.stateBits.begin(),
            model.stateBits.end(),
            [&](const SignalKey& key) {
              if (ctx.unsupportedStateBits.find(key) == ctx.unsupportedStateBits.end()) {
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
              return ctx.unsupportedStateBits.find(relation.primaryKey) !=
                         ctx.unsupportedStateBits.end() ||
                     ctx.unsupportedStateBits.find(relation.complementedKey) !=
                         ctx.unsupportedStateBits.end();
            }),
        model.complementedStateRelations.end());
  }
  if (ctx.secDiagEnabled) {
    fprintf(
        stderr,
        "SEC diag: extract(%s) filtered env=%zu state=%zu\n",
        ctx.topName.c_str(),
        model.environmentInputs.size(),
        model.stateBits.size());
    fflush(stderr);
  }
}

void propagateConnectivitySkipsThroughDependencies(SequentialDesignModel& model) {
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

    std::unordered_map<BoolExpr*, std::optional<size_t>> stateMemo;
    for (const auto& key : model.stateBits) {
      if (model.connectivitySkipInfoByKey.find(key) != model.connectivitySkipInfoByKey.end()) {
        continue;
      }
      auto exprIt = model.nextStateExprByStateKey.find(key);
      if (exprIt == model.nextStateExprByStateKey.end()) {
        continue;
      }
      const auto dependency =
          findSkippedStateDependency(exprIt->second, skippedStateVars, stateMemo);
      if (!dependency.has_value()) {
        continue;
      }
      const auto sourceKeyIt = stateKeyByVarID.find(*dependency);
      if (sourceKeyIt == stateKeyByVarID.end()) {
        continue;
      }
      const auto skipInfoIt = model.connectivitySkipInfoByKey.find(sourceKeyIt->second);
      if (skipInfoIt == model.connectivitySkipInfoByKey.end()) {
        continue;
      }
      model.connectivitySkipInfoByKey.emplace(
          key,
          ConnectivitySkipInfo{
              skipInfoIt->second.origin,
              "Depends on skipped state `" + model.displayNameByKey.at(sourceKeyIt->second) +
                  "` whose cone traces to a " +
                  describeConnectivitySkipOrigin(skipInfoIt->second.origin) + " issue",
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
      const auto dependency =
          findSkippedStateDependency(exprIt->second, skippedStateVars, outputMemo);
      if (!dependency.has_value()) {
        continue;
      }
      const auto sourceKeyIt = stateKeyByVarID.find(*dependency);
      if (sourceKeyIt == stateKeyByVarID.end()) {
        continue;
      }
      const auto skipInfoIt = model.connectivitySkipInfoByKey.find(sourceKeyIt->second);
      if (skipInfoIt == model.connectivitySkipInfoByKey.end()) {
        continue;
      }
      model.connectivitySkipInfoByKey.emplace(
          key,
          ConnectivitySkipInfo{
              skipInfoIt->second.origin,
              "Depends on skipped state `" + model.displayNameByKey.at(sourceKeyIt->second) +
                  "` whose cone traces to a " +
                  describeConnectivitySkipOrigin(skipInfoIt->second.origin) + " issue",
          });
      changed = true;
    }
  } while (changed);
}

void partitionCoveredSignals(SequentialDesignModel& model) {
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
}

void validateExtractedModel(SequentialDesignModel& model) {
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
}

void logExtractedModelDebugSummary(const ExtractContext& ctx,
                                   const SequentialDesignModel& model) {
  if (!ctx.secDiagEnabled) {
    return;
  }

  size_t structuredMemoryCellCount = 0;
  for (const auto& pendingMemory : ctx.pendingMemoryInstances) {
    structuredMemoryCellCount += pendingMemory.cellStates.size();
  }
  fprintf(
      stderr,
      "SEC diag: extract(%s) structured_memories=%zu structured_memory_cells=%zu abstracted_seq_boundaries=%zu opaque_inputs=%zu opaque_outputs=%zu\n",
      ctx.topName.c_str(),
      ctx.pendingMemoryInstances.size(),
      structuredMemoryCellCount,
      model.abstractedSequentialBoundaries.size(),
      model.internalBoundaryInputKeys.size(),
      model.internalBoundaryOutputKeys.size());

  auto formatSignal = [&](const SignalKey& key) {
    const auto nameIt = model.displayNameByKey.find(key);
    const auto varIt = model.inputVarByKey.find(key);
    std::ostringstream oss;
    oss << (nameIt == model.displayNameByKey.end() ? signalKeyToString(key)
                                                   : nameIt->second);
    if (varIt != model.inputVarByKey.end()) {
      oss << "@v" << varIt->second;
    }
    return oss.str();
  };

  std::ostringstream stateSummary;
  for (size_t index = 0; index < model.stateBits.size(); ++index) {
    if (index != 0) {
      stateSummary << ", ";
    }
    stateSummary << formatSignal(model.stateBits[index]);
  }
  fprintf(
      stderr,
      "SEC diag: extract(%s) kept_states=[%s]\n",
      ctx.topName.c_str(),
      stateSummary.str().c_str());

  for (const auto& key : model.observedOutputs) {
    const auto exprIt = model.observedOutputExprByKey.find(key);
    if (exprIt == model.observedOutputExprByKey.end() || exprIt->second == nullptr) {
      continue;
    }
    std::ostringstream supportSummary;
    bool first = true;
    for (const auto symbol : exprIt->second->getSupportVars()) {
      if (!first) {
        supportSummary << ", ";
      }
      first = false;
      supportSummary << "v" << symbol;
    }
    fprintf(
        stderr,
        "SEC diag: extract(%s) observed_support %s = [%s]\n",
        ctx.topName.c_str(),
        formatSignal(key).c_str(),
        supportSummary.str().c_str());
  }
  fflush(stderr);
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
  ExtractContext ctx{
      .top = top,
      .universe = universe,
      .previousTop = universe->getTopDesign(),
      .topName = top->getName().getString(),
      .secDiagEnabled = std::getenv("KEPLER_SEC_DIAG") != nullptr,
      .abstractUncomputableSequentialBoundaries =
          KEPLER_FORMAL::Config::getSecTreatUncomputableSeqAsBoundary(),
  };
  ctx.builder.setRetainDnl(true);

  // Phase 1: collect the raw boundary, classify top I/O vs sequential state,
  // and scan leaf sequentials so the later formula build knows what it must
  // reconstruct.
  collectInitialBuilderBoundary(ctx);
  collectTopInterfaceTerms(ctx, model);
  classifyBuilderBoundaryTerms(ctx, model);
  collectSequentialTransitions(ctx, model);

  if (model.hasUnsupportedFeatures()) {
    // Primitive-modeling issues are structural, not proof-related. Report them
    // immediately so large designs fail fast before the expensive cone builder
    // tries to derive BoolExprs for a transition system we already know is
    // unsupported.
    naja::DNL::destroy();
    if (ctx.previousTop != nullptr) {
      universe->setTopDesign(ctx.previousTop);
    }
    if (ctx.secDiagEnabled) {
      fprintf(
          stderr,
          "SEC diag: extract(%s) early unsupported exit before build\n",
          ctx.topName.c_str());
      fflush(stderr);
    }
    return model;
  }

  // Phase 2: build the initial boundary formulas for real top outputs plus any
  // already abstracted boundary terms, then publish the normalized SEC
  // interface and variable map.
  buildInitialObservedOutputClouds(ctx, model);
  publishNormalizedBoundary(ctx, model);

  std::vector<naja::DNL::DNLID> builderInputs = ctx.builder.getInputs();
  std::vector<naja::DNL::DNLID> builderOutputs = ctx.builder.getOutputs();
  std::vector<size_t> termDNLID2varID = ctx.builder.getTermDNLID2VarID();
  recordBoundaryInputVars(ctx, builderInputs, termDNLID2varID, model);

  std::unordered_map<naja::DNL::DNLID, BoolExpr*> outputExprByTerm;
  const auto& outputTerms = builderOutputs;
  const auto& outputExprs = ctx.builder.getPOs();
  auto skippedOutputsByTerm = ctx.builder.getSkippedOutputs();
  // Keep only the valid formulas produced by the clause builder. Invalid
  // clouds are classified below either as skippable SEC gaps or as hard
  // unsupported logic.
  for (size_t i = 0; i < outputTerms.size(); ++i) {
    BoolExpr* expr = outputExprs[i];
    if (expr == nullptr || !expr->isValid()) {
      continue;
    }
    outputExprByTerm.emplace(outputTerms[i], expr);
  }

  const auto structuredMemoryDependencyTerms =
      collectStructuredMemoryDependencyTerms(ctx);
  if (!structuredMemoryDependencyTerms.empty()) {
    const auto dependencyOutputs = materializeBuilderOutputs(
        structuredMemoryDependencyTerms,
        ctx.secDiagEnabled,
        ctx.topName.c_str(),
        "structured memory dependency build",
        true);
    appendUniqueTermIDs(builderInputs, dependencyOutputs.inputs);
    appendUniqueTermIDs(builderOutputs, dependencyOutputs.outputs);
    mergeBuilderTermVarIDs(termDNLID2varID, dependencyOutputs.termDNLID2varID);
    recordBoundaryInputVars(ctx, builderInputs, termDNLID2varID, model);
    for (const auto& [termID, expr] : dependencyOutputs.outputExprByTerm) {
      outputExprByTerm.emplace(termID, expr);
    }
    for (const auto& [termID, info] : dependencyOutputs.skippedOutputsByTerm) {
      skippedOutputsByTerm.emplace(termID, info);
    }
  }
  assignStructuredMemoryStateVars(ctx, model);

  // Phase 3: materialize the observed output formulas that SEC will actually
  // compare, classifying anything missing as either a skippable connectivity
  // gap or a hard unsupported boundary.
  materializeBoundaryObservedOutputs(
      ctx.abstractedBoundaryObservedTerms,
      outputExprByTerm,
      skippedOutputsByTerm,
      builderInputs,
      builderOutputs,
      termDNLID2varID,
      model);
  materializeTopObservedOutputs(
      ctx.topOutputKeyByTerm, outputExprByTerm, skippedOutputsByTerm, model);
  if (ctx.secDiagEnabled) {
    fprintf(
        stderr,
        "SEC diag: extract(%s) materialized output exprs observed=%zu total=%zu\n",
        ctx.topName.c_str(),
        model.observedOutputExprByKey.size(),
        outputExprByTerm.size());
    fflush(stderr);
  }

  if (!ctx.pendingMemoryInstances.empty()) {
    buildStructuredMemoryTransitions(
        ctx,
        model,
        builderInputs,
        builderOutputs,
        termDNLID2varID,
        outputExprByTerm,
        skippedOutputsByTerm);
  }

  // Phase 4: rebuild the next-state relations for just the state that is still
  // relevant to covered outputs, then fold any late boundary abstractions back
  // into the published interface.
  const auto rebuiltArtifacts = rebuildRequiredStateTransitions(
      ctx,
      model,
      builderInputs,
      builderOutputs,
      termDNLID2varID,
      outputExprByTerm,
      skippedOutputsByTerm);
  applyRebuiltTransitionArtifacts(
      ctx,
      rebuiltArtifacts,
      model,
      builderInputs,
      builderOutputs,
      termDNLID2varID,
      outputExprByTerm,
      skippedOutputsByTerm);
  filterUnsupportedAndUnmappedBoundary(ctx, model);

  // Phase 5: propagate connectivity skips through dependent state/output cones,
  // then partition the final interface into covered vs skipped signals.
  propagateConnectivitySkipsThroughDependencies(model);
  partitionCoveredSignals(model);

  inferSynthesizedResetInitialStateValues(model);
  logExtractedModelDebugSummary(ctx, model);
  if (ctx.secDiagEnabled) {
    fprintf(
        stderr,
        "SEC diag: extract(%s) synthesized init inference done init=%zu\n",
        ctx.topName.c_str(),
        model.initialStateValueByKey.size());
    fflush(stderr);
  }

  // Phase 6: make sure the remaining covered interface is complete before SEC
  // hands this model to the proof engines.
  validateExtractedModel(model);

  // Restore the original top design for callers that keep using the universe.
  naja::DNL::destroy();
  if (ctx.previousTop != nullptr) {
    universe->setTopDesign(ctx.previousTop);
  }
  if (ctx.secDiagEnabled) {
    fprintf(stderr, "SEC diag: extract(%s) end\n", ctx.topName.c_str());
    fflush(stderr);
  }

  return model;
}

}  // namespace KEPLER_FORMAL::SEC
