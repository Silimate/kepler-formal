// Copyright 2024-2026 keplertech.io
// SPDX-License-Identifier: GPL-3.0-only

#include "model/SequentialDesignModel.h"

#include <algorithm>
#include <cctype>
#include <set>
#include <stdexcept>
#include <unordered_map>

#include "DNL.h"
#include "NLUniverse.h"
#include "SNLDesignModeling.h"
#include "SNLPath.h"
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
    key.first.push_back(name.getID());
  }
  key.first.push_back(terminal.getSnlBitTerm()->getName().getID());
  key.second.push_back(
      static_cast<naja::NL::NLID::DesignObjectID>(terminal.getSnlBitTerm()->getBit()));
  return key;
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

  return BoolExpr::simplify(next);
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

  naja::DNL::destroy();
  universe->setTopDesign(top);

  KEPLER_FORMAL::BuildPrimaryOutputClauses builder;
  // Reuse the existing miter frontend to discover the relevant boundary
  // signals before we ask it to build Boolean formulas.
  builder.collect();

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
  builder.build();

  model.environmentInputs.assign(environmentInputs.begin(), environmentInputs.end());
  model.stateBits.assign(stateBits.begin(), stateBits.end());
  model.observedOutputs.assign(observedOutputs.begin(), observedOutputs.end());

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

  // Rebuild next-state equations for the supported sequential cells.
  for (const auto& pending : pendingTransitions) {
    try {
      BoolExpr* nextStateExpr =
          buildNextStateExpr(pending, termDNLID2varID, outputExprByTerm);
      model.nextStateExprByStateKey.emplace(pending.stateKey, nextStateExpr);
      // Liberty flops such as DFF_X1 expose both Q and QN. They share one
      // storage element, so complementary outputs inherit the same next-state
      // function with a logical inversion.
      for (const auto& complementedKey : pending.complementedStateKeys) {
        model.nextStateExprByStateKey.emplace(
            complementedKey,
            BoolExpr::simplify(BoolExpr::Not(nextStateExpr)));
      }
    } catch (const std::exception& e) {
      model.unsupportedReasons.push_back(
          "Unsupported sequential primitive for `" +
          signalKeyToString(pending.stateKey) + "`: " + e.what());
    }
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

  return model;
}

}  // namespace KEPLER_FORMAL::SEC
