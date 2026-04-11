// Copyright 2024-2026 keplertech.io
// SPDX-License-Identifier: GPL-3.0-only

#include "proof/ExactInterpolationEngine.h"

#include <algorithm>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/BoolExprUtils.h"
#include "kinduction/SatEncoding.h"

namespace KEPLER_FORMAL::SEC {

namespace {

BoolExpr* buildEqualityFormula(size_t lhs, size_t rhs) {
  return makeEqualityExpr(BoolExpr::Var(lhs), BoolExpr::Var(rhs));
}

BoolExpr* buildInitFormula(const KInductionProblem& problem) {
  BoolExpr* init = BoolExpr::createTrue();
  bool hasConstraint = false;

  if (problem.resetBootstrapCycles != 0) {
    for (const auto& [symbol, value] : problem.bootstrapStateAssignments) {
      init = BoolExpr::And(
          init, value ? BoolExpr::Var(symbol) : BoolExpr::Not(BoolExpr::Var(symbol)));
      hasConstraint = true;
    }
    for (const auto& [lhsSymbol, rhsSymbol] : problem.bootstrapStateEqualityPairs) {
      init = BoolExpr::And(init, buildEqualityFormula(lhsSymbol, rhsSymbol));
      hasConstraint = true;
    }
  } else {
    if (problem.initialCondition != nullptr) {
      init = BoolExpr::And(init, problem.initialCondition);
      hasConstraint = true;
    }
    for (const auto& [lhsSymbol, rhsSymbol] : problem.initialStateEqualityPairs) {
      init = BoolExpr::And(init, buildEqualityFormula(lhsSymbol, rhsSymbol));
      hasConstraint = true;
    }
  }

  if (!hasConstraint) {
    return nullptr;
  }
  return BoolExpr::simplify(init);
}

size_t nextFreshSymbol(const KInductionProblem& problem) {
  size_t nextSymbol = 2;
  for (const auto symbol : problem.allSymbols) {
    nextSymbol = std::max(nextSymbol, symbol + 1);
  }
  return nextSymbol;
}

std::unordered_map<size_t, size_t> allocateFreshSymbols(
    const std::vector<size_t>& originalSymbols,
    size_t& nextSymbol) {
  std::unordered_map<size_t, size_t> symbolMap;
  symbolMap.reserve(originalSymbols.size());
  for (const auto symbol : originalSymbols) {
    symbolMap.emplace(symbol, nextSymbol++);
  }
  return symbolMap;
}

BoolExpr* buildOneStepTransitionFormula(
    const KInductionProblem& problem,
    const std::unordered_map<size_t, size_t>& nextStateSymbols) {
  BoolExpr* transition = BoolExpr::createTrue();
  for (const auto& [stateSymbol, expr] : problem.transitions0) {
    transition = BoolExpr::And(
        transition,
        makeEqualityExpr(BoolExpr::Var(nextStateSymbols.at(stateSymbol)), expr));
  }
  for (const auto& [stateSymbol, expr] : problem.transitions1) {
    transition = BoolExpr::And(
        transition,
        makeEqualityExpr(BoolExpr::Var(nextStateSymbols.at(stateSymbol)), expr));
  }
  for (const auto& [primarySymbol, complementedSymbol] : problem.complementedStatePairs0) {
    transition = BoolExpr::And(
        transition,
        makeEqualityExpr(
            BoolExpr::Var(nextStateSymbols.at(complementedSymbol)),
            BoolExpr::Not(BoolExpr::Var(nextStateSymbols.at(primarySymbol)))));
  }
  for (const auto& [primarySymbol, complementedSymbol] : problem.complementedStatePairs1) {
    transition = BoolExpr::And(
        transition,
        makeEqualityExpr(
            BoolExpr::Var(nextStateSymbols.at(complementedSymbol)),
            BoolExpr::Not(BoolExpr::Var(nextStateSymbols.at(primarySymbol)))));
  }
  return BoolExpr::simplify(transition);
}

BoolExpr* buildCurrentStateLegality(const KInductionProblem& problem) {
  BoolExpr* legality = BoolExpr::createTrue();
  for (const auto& [primarySymbol, complementedSymbol] : problem.complementedStatePairs0) {
    legality = BoolExpr::And(
        legality,
        makeEqualityExpr(
            BoolExpr::Var(complementedSymbol), BoolExpr::Not(BoolExpr::Var(primarySymbol))));
  }
  for (const auto& [primarySymbol, complementedSymbol] : problem.complementedStatePairs1) {
    legality = BoolExpr::And(
        legality,
        makeEqualityExpr(
            BoolExpr::Var(complementedSymbol), BoolExpr::Not(BoolExpr::Var(primarySymbol))));
  }
  return BoolExpr::simplify(legality);
}

BoolExpr* remapFormula(
    BoolExpr* formula,
    const std::unordered_map<size_t, size_t>& symbolMap) {
  std::unordered_map<BoolExpr*, BoolExpr*> memo;
  return remapBoolExprVariables(formula, symbolMap, memo);
}

bool isSatisfiable(BoolExpr* formula,
                   KEPLER_FORMAL::Config::SolverType solverType) {
  if (formula == nullptr) {
    return false;
  }

  SATSolverWrapper solver(solverType);
  const auto support = formula->getSupportVars();
  std::unordered_map<size_t, int> leafLits;
  leafLits.reserve(support.size());
  for (const auto symbol : support) {
    if (symbol < 2) {
      continue;
    }
    leafLits.emplace(symbol, solver.newVar() + 2);
  }

  FrameFormulaEncoder encoder(solver, std::move(leafLits));
  solver.addClause({encoder.encode(formula)});
  return solver.solve();
}

BoolExpr* buildAssignmentCube(const std::vector<size_t>& symbols, size_t assignment) {
  BoolExpr* cube = BoolExpr::createTrue();
  for (size_t bit = 0; bit < symbols.size(); ++bit) {
    BoolExpr* literal = BoolExpr::Var(symbols[bit]);
    cube = BoolExpr::And(
        cube,
        (assignment & (size_t{1} << bit)) != 0 ? literal : BoolExpr::Not(literal));
  }
  return BoolExpr::simplify(cube);
}

BoolExpr* computeExactInterpolant(
    BoolExpr* lhs,
    BoolExpr* rhs,
    const std::vector<size_t>& sharedSymbols,
    KEPLER_FORMAL::Config::SolverType solverType) {
  if (lhs == nullptr || rhs == nullptr || sharedSymbols.empty()) {
    return nullptr;
  }
  if (isSatisfiable(BoolExpr::And(lhs, rhs), solverType)) {
    return nullptr;
  }

  BoolExpr* interpolant = BoolExpr::createFalse();
  const size_t assignmentCount = size_t{1} << sharedSymbols.size();
  for (size_t assignment = 0; assignment < assignmentCount; ++assignment) {
    BoolExpr* cube = buildAssignmentCube(sharedSymbols, assignment);
    if (isSatisfiable(BoolExpr::And(lhs, cube), solverType)) {
      interpolant = BoolExpr::Or(interpolant, cube);
    }
  }

  interpolant = BoolExpr::simplify(interpolant);
  if (isSatisfiable(BoolExpr::And(lhs, BoolExpr::Not(interpolant)), solverType)) {
    return nullptr;
  }
  if (isSatisfiable(BoolExpr::And(interpolant, rhs), solverType)) {
    return nullptr;
  }
  return interpolant;
}

bool isInductiveStateInvariant(
    const KInductionProblem& problem,
    BoolExpr* invariant,
    KEPLER_FORMAL::Config::SolverType solverType) {
  size_t nextSymbol = nextFreshSymbol(problem);
  const auto nextStateSymbols =
      allocateFreshSymbols(problem.combinedStateSymbols(), nextSymbol);
  BoolExpr* transition = buildOneStepTransitionFormula(problem, nextStateSymbols);
  BoolExpr* currentInvariant = BoolExpr::And(
      buildCurrentStateLegality(problem), invariant);
  std::unordered_map<size_t, size_t> remap = nextStateSymbols;
  BoolExpr* nextInvariant = remapFormula(invariant, remap);
  return !isSatisfiable(
      BoolExpr::And(currentInvariant, BoolExpr::And(transition, BoolExpr::Not(nextInvariant))),
      solverType);
}

}  // namespace

ExactInterpolationEngine::ExactInterpolationEngine(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType)
    : problem_(problem), solverType_(solverType) {}

std::optional<BoolExpr*> ExactInterpolationEngine::deriveOneStepReachableStateInvariant(
    size_t maxSharedStateBits) const {
  const std::vector<size_t> combinedStateSymbols = problem_.combinedStateSymbols();
  if (combinedStateSymbols.empty() || combinedStateSymbols.size() > maxSharedStateBits) {
    return std::nullopt;
  }

  BoolExpr* init = buildInitFormula(problem_);
  if (init == nullptr) {
    return std::nullopt;
  }

  size_t nextSymbol = nextFreshSymbol(problem_);
  const auto nextStateSymbols = allocateFreshSymbols(combinedStateSymbols, nextSymbol);
  const auto badInputSymbols = allocateFreshSymbols(problem_.inputSymbols, nextSymbol);

  BoolExpr* lhs = BoolExpr::And(
      init, buildOneStepTransitionFormula(problem_, nextStateSymbols));

  std::unordered_map<size_t, size_t> badRemap = nextStateSymbols;
  badRemap.insert(badInputSymbols.begin(), badInputSymbols.end());
  BoolExpr* rhs = remapFormula(problem_.bad, badRemap);

  std::vector<size_t> sharedSymbols;
  sharedSymbols.reserve(combinedStateSymbols.size());
  for (const auto symbol : combinedStateSymbols) {
    sharedSymbols.push_back(nextStateSymbols.at(symbol));
  }

  BoolExpr* interpolant =
      computeExactInterpolant(lhs, rhs, sharedSymbols, solverType_);
  if (interpolant == nullptr) {
    return std::nullopt;
  }

  std::unordered_map<size_t, size_t> restoreMap;
  restoreMap.reserve(nextStateSymbols.size());
  for (const auto& [originalSymbol, freshSymbol] : nextStateSymbols) {
    restoreMap.emplace(freshSymbol, originalSymbol);
  }

  BoolExpr* restored = BoolExpr::simplify(remapFormula(interpolant, restoreMap));
  if (!isInductiveStateInvariant(problem_, restored, solverType_)) {
    return std::nullopt;
  }
  return restored;
}

}  // namespace KEPLER_FORMAL::SEC
