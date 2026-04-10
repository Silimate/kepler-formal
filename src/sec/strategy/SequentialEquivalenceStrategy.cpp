// Copyright 2024-2026 keplertech.io
// SPDX-License-Identifier: GPL-3.0-only

#include "strategy/SequentialEquivalenceStrategy.h"

#include <algorithm>
#include <sstream>
#include <unordered_map>

#include "common/BoolExprUtils.h"
#include "kinduction/KInductionEngine.h"
#include "model/SequentialDesignModel.h"

namespace KEPLER_FORMAL::SEC {

namespace {

std::string joinReasons(const std::vector<std::string>& reasons) {
  std::ostringstream oss;
  for (size_t i = 0; i < reasons.size(); ++i) {
    if (i) {
      oss << " | ";
    }
    oss << reasons[i];
  }
  return oss.str();
}

std::string describeMismatchedKeys(const std::vector<SignalKey>& lhs,
                                   const std::vector<SignalKey>& rhs,
                                   const char* label) {
  std::ostringstream oss;
  oss << "Mismatched " << label << " sets";
  if (!lhs.empty()) {
    oss << " lhs=[";
    for (size_t i = 0; i < lhs.size(); ++i) {
      if (i) {
        oss << ", ";
      }
      oss << signalKeyToString(lhs[i]);
    }
    oss << "]";
  }
  if (!rhs.empty()) {
    oss << " rhs=[";
    for (size_t i = 0; i < rhs.size(); ++i) {
      if (i) {
        oss << ", ";
      }
      oss << signalKeyToString(rhs[i]);
    }
    oss << "]";
  }
  return oss.str();
}

bool keysMatch(const std::vector<SignalKey>& lhs,
               const std::vector<SignalKey>& rhs) {
  return lhs == rhs;
}

template <typename MapT>
void assignSymbols(const std::vector<SignalKey>& keys,
                   MapT& output,
                   std::vector<size_t>& allSymbols,
                   size_t& nextSymbol) {
  for (const auto& key : keys) {
    output.emplace(key, nextSymbol);
    allSymbols.push_back(nextSymbol);
    ++nextSymbol;
  }
}

std::unordered_map<size_t, size_t> buildLocalToCombinedMap(
    const SequentialDesignModel& model,
    const std::unordered_map<SignalKey, size_t, SignalKeyHash>& inputSymbols,
    const std::unordered_map<SignalKey, size_t, SignalKeyHash>& stateSymbols) {
  // Each design is extracted independently, so its BoolExpr variables must be
  // rewritten into a single shared symbol space before we can compare them.
  std::unordered_map<size_t, size_t> localToCombined;
  for (const auto& [key, localVar] : model.inputVarByKey) {
    if (auto it = inputSymbols.find(key); it != inputSymbols.end()) {
      localToCombined.emplace(localVar, it->second);
      continue;
    }
    if (auto it = stateSymbols.find(key); it != stateSymbols.end()) {
      localToCombined.emplace(localVar, it->second);
    }
  }
  return localToCombined;
}

}  // namespace

SequentialEquivalenceStrategy::SequentialEquivalenceStrategy(
    naja::NL::SNLDesign* top0,
    naja::NL::SNLDesign* top1,
    KEPLER_FORMAL::Config::SolverType solverType)
    : top0_(top0), top1_(top1), solverType_(solverType) {}

SequentialEquivalenceResult SequentialEquivalenceStrategy::run(size_t maxK) const {
  // Step 1: extract both tops into the same normalized SEC representation.
  SequentialDesignModel model0 = SequentialDesignModel::extract(top0_);
  SequentialDesignModel model1 = SequentialDesignModel::extract(top1_);

  if (model0.hasUnsupportedFeatures() || model1.hasUnsupportedFeatures()) {
    std::vector<std::string> reasons = model0.unsupportedReasons;
    reasons.insert(
        reasons.end(),
        model1.unsupportedReasons.begin(),
        model1.unsupportedReasons.end());
    return {
        SequentialEquivalenceStatus::Unsupported,
        0,
        joinReasons(reasons),
    };
  }

  // Step 2: SEC only makes sense when the observable interfaces align exactly.
  if (!keysMatch(model0.environmentInputs, model1.environmentInputs)) {
    return {
        SequentialEquivalenceStatus::Unsupported,
        0,
        describeMismatchedKeys(
            model0.environmentInputs, model1.environmentInputs, "environment input"),
    };
  }
  if (!keysMatch(model0.stateBits, model1.stateBits)) {
    return {
        SequentialEquivalenceStatus::Unsupported,
        0,
        describeMismatchedKeys(model0.stateBits, model1.stateBits, "state"),
    };
  }
  if (!keysMatch(model0.observedOutputs, model1.observedOutputs)) {
    return {
        SequentialEquivalenceStatus::Unsupported,
        0,
        describeMismatchedKeys(
            model0.observedOutputs, model1.observedOutputs, "observed output"),
    };
  }

  KInductionProblem problem;
  problem.environmentInputs = model0.environmentInputs;
  problem.stateBits = model0.stateBits;
  problem.observedOutputs = model0.observedOutputs;

  // Step 3: create the shared symbol space used by the combined SAT problem.
  // Inputs are shared, while each design gets its own copy of the state bits.
  std::unordered_map<SignalKey, size_t, SignalKeyHash> inputSymbols;
  std::unordered_map<SignalKey, size_t, SignalKeyHash> state0Symbols;
  std::unordered_map<SignalKey, size_t, SignalKeyHash> state1Symbols;
  size_t nextSymbol = 2;

  assignSymbols(problem.environmentInputs, inputSymbols, problem.allSymbols, nextSymbol);
  assignSymbols(problem.stateBits, state0Symbols, problem.allSymbols, nextSymbol);
  assignSymbols(problem.stateBits, state1Symbols, problem.allSymbols, nextSymbol);

  for (const auto& key : problem.environmentInputs) {
    problem.inputSymbols.push_back(inputSymbols.at(key));
  }
  for (const auto& key : problem.stateBits) {
    problem.state0Symbols.push_back(state0Symbols.at(key));
    problem.state1Symbols.push_back(state1Symbols.at(key));
  }
  for (const auto& relation : model0.complementedStateRelations) {
    problem.complementedStatePairs0.emplace_back(
        state0Symbols.at(relation.primaryKey),
        state0Symbols.at(relation.complementedKey));
  }
  for (const auto& relation : model1.complementedStateRelations) {
    problem.complementedStatePairs1.emplace_back(
        state1Symbols.at(relation.primaryKey),
        state1Symbols.at(relation.complementedKey));
  }

  const auto localToCombined0 =
      buildLocalToCombinedMap(model0, inputSymbols, state0Symbols);
  const auto localToCombined1 =
      buildLocalToCombinedMap(model1, inputSymbols, state1Symbols);

  std::unordered_map<BoolExpr*, BoolExpr*> remapMemo0;
  std::unordered_map<BoolExpr*, BoolExpr*> remapMemo1;
  std::unordered_map<SignalKey, BoolExpr*, SignalKeyHash> remappedOutputs0;
  std::unordered_map<SignalKey, BoolExpr*, SignalKeyHash> remappedOutputs1;
  std::unordered_map<SignalKey, BoolExpr*, SignalKeyHash> remappedNext0;
  std::unordered_map<SignalKey, BoolExpr*, SignalKeyHash> remappedNext1;

  // Step 4: rewrite both designs' formulas into that shared symbol space.
  for (const auto& key : problem.observedOutputs) {
    remappedOutputs0.emplace(
        key,
        remapBoolExprVariables(
            model0.observedOutputExprByKey.at(key), localToCombined0, remapMemo0));
    remappedOutputs1.emplace(
        key,
        remapBoolExprVariables(
            model1.observedOutputExprByKey.at(key), localToCombined1, remapMemo1));
  }

  for (const auto& key : problem.stateBits) {
    remappedNext0.emplace(
        key,
        remapBoolExprVariables(
            model0.nextStateExprByStateKey.at(key), localToCombined0, remapMemo0));
    remappedNext1.emplace(
        key,
        remapBoolExprVariables(
            model1.nextStateExprByStateKey.at(key), localToCombined1, remapMemo1));
  }

  // Step 5: build the SEC property. A frame is "good" when observed outputs
  // match and the two current state vectors are equal.
  BoolExpr* property = BoolExpr::createTrue();
  for (const auto& key : problem.observedOutputs) {
    property = BoolExpr::And(
        property,
        makeEqualityExpr(remappedOutputs0.at(key), remappedOutputs1.at(key)));
  }
  for (const auto& key : problem.stateBits) {
    property = BoolExpr::And(
        property,
        makeEqualityExpr(
            BoolExpr::Var(state0Symbols.at(key)),
            BoolExpr::Var(state1Symbols.at(key))));
    problem.transitions0.emplace_back(state0Symbols.at(key), remappedNext0.at(key));
    problem.transitions1.emplace_back(state1Symbols.at(key), remappedNext1.at(key));
  }

  problem.property = BoolExpr::simplify(property);
  problem.bad = BoolExpr::simplify(BoolExpr::Not(problem.property));
  problem.description = "SEC property with aligned outputs and state bits";

  // Step 6: hand the combined transition system to the k-induction solver.
  KInductionEngine engine(problem, solverType_);
  const auto result = engine.run(maxK);
  switch (result.status) {
    case KInductionStatus::Equivalent:
      return {SequentialEquivalenceStatus::Equivalent, result.bound, ""};
    case KInductionStatus::Different:
      return {SequentialEquivalenceStatus::Different, result.bound, ""};
    case KInductionStatus::Inconclusive:
    default:
      return {
          SequentialEquivalenceStatus::Inconclusive,
          result.bound,
          "Reached max_k without a proof or counterexample",
      };
  }
}

}  // namespace KEPLER_FORMAL::SEC
