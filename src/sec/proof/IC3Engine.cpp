// Copyright 2024-2026 keplertech.io
// SPDX-License-Identifier: GPL-3.0-only

#include "proof/IC3Engine.h"

#include <algorithm>
#include <optional>
#include <unordered_set>
#include <vector>

#include "common/BoolExprUtils.h"
#include "kinduction/SatEncoding.h"

namespace KEPLER_FORMAL::SEC {

namespace {

using StateCube = std::vector<std::pair<size_t, bool>>;

struct FrameClauses {
  std::vector<StateCube> blockedCubes;
};

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

void addComplementedStateRelations(
    SATSolverWrapper& solver,
    const FrameVariableStore& variables,
    const std::vector<std::pair<size_t, size_t>>& complementedStatePairs,
    size_t numFrames) {
  for (size_t frame = 0; frame < numFrames; ++frame) {
    for (const auto& [primarySymbol, complementedSymbol] : complementedStatePairs) {
      addLiteralEquivalence(
          solver,
          variables.getLiteral(complementedSymbol, frame),
          -variables.getLiteral(primarySymbol, frame));
    }
  }
}

void addTransitionRelation(SATSolverWrapper& solver,
                           const FrameVariableStore& variables,
                           const KInductionProblem& problem,
                           size_t frame) {
  FrameFormulaEncoder encoder(solver, variables.makeLeafLits(frame));
  for (const auto& [stateSymbol, expr] : problem.transitions0) {
    addLiteralEquivalence(
        solver,
        variables.getLiteral(stateSymbol, frame + 1),
        encoder.encode(expr));
  }
  for (const auto& [stateSymbol, expr] : problem.transitions1) {
    addLiteralEquivalence(
        solver,
        variables.getLiteral(stateSymbol, frame + 1),
        encoder.encode(expr));
  }
}

void addBlockedCubeClause(SATSolverWrapper& solver,
                          const FrameVariableStore& variables,
                          const StateCube& cube,
                          size_t frame) {
  std::vector<int> clause;
  clause.reserve(cube.size());
  for (const auto& [symbol, value] : cube) {
    clause.push_back(
        value ? -variables.getLiteral(symbol, frame) : variables.getLiteral(symbol, frame));
  }
  solver.addClause(clause);
}

void addCubeAssumptions(SATSolverWrapper& solver,
                        const FrameVariableStore& variables,
                        const StateCube& cube,
                        size_t frame) {
  for (const auto& [symbol, value] : cube) {
    solver.addClause(
        {value ? variables.getLiteral(symbol, frame) : -variables.getLiteral(symbol, frame)});
  }
}

void addFrameConstraints(SATSolverWrapper& solver,
                         const FrameVariableStore& variables,
                         const KInductionProblem& problem,
                         BoolExpr* initFormula,
                         const std::vector<FrameClauses>& frames,
                         size_t level,
                         size_t frame) {
  if (level == 0) {
    FrameFormulaEncoder encoder(solver, variables.makeLeafLits(frame));
    solver.addClause({encoder.encode(initFormula)});
    return;
  }

  for (const auto& cube : frames[level].blockedCubes) {
    addBlockedCubeClause(solver, variables, cube, frame);
  }
}

StateCube extractStateCube(const SATSolverWrapper& solver,
                           const FrameVariableStore& variables,
                           const std::vector<size_t>& stateSymbols,
                           size_t frame) {
  StateCube cube;
  cube.reserve(stateSymbols.size());
  for (const auto symbol : stateSymbols) {
    cube.emplace_back(symbol, solver.getLiteralValue(variables.getLiteral(symbol, frame)));
  }
  return cube;
}

std::string cubeKey(const StateCube& cube) {
  std::string key;
  key.reserve(cube.size() * 8);
  for (const auto& [symbol, value] : cube) {
    key += std::to_string(symbol);
    key.push_back('=');
    key.push_back(value ? '1' : '0');
    key.push_back(';');
  }
  return key;
}

bool cubeAlreadyBlocked(const FrameClauses& frame, const StateCube& cube) {
  const std::string key = cubeKey(cube);
  for (const auto& blockedCube : frame.blockedCubes) {
    if (cubeKey(blockedCube) == key) {
      return true;
    }
  }
  return false;
}

std::optional<StateCube> findBadCube(const KInductionProblem& problem,
                                     KEPLER_FORMAL::Config::SolverType solverType,
                                     BoolExpr* initFormula,
                                     const std::vector<FrameClauses>& frames,
                                     size_t level) {
  SATSolverWrapper solver(solverType);
  FrameVariableStore variables(solver, problem.allSymbols, 1);
  addComplementedStateRelations(solver, variables, problem.complementedStatePairs0, 1);
  addComplementedStateRelations(solver, variables, problem.complementedStatePairs1, 1);
  addFrameConstraints(solver, variables, problem, initFormula, frames, level, 0);
  FrameFormulaEncoder encoder(solver, variables.makeLeafLits(0));
  solver.addClause({encoder.encode(problem.bad)});
  if (!solver.solve()) {
    return std::nullopt;
  }
  return extractStateCube(solver, variables, problem.combinedStateSymbols(), 0);
}

std::optional<StateCube> findPredecessorCube(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    BoolExpr* initFormula,
    const std::vector<FrameClauses>& frames,
    size_t level,
    const StateCube& targetCube) {
  SATSolverWrapper solver(solverType);
  FrameVariableStore variables(solver, problem.allSymbols, 2);
  addComplementedStateRelations(solver, variables, problem.complementedStatePairs0, 2);
  addComplementedStateRelations(solver, variables, problem.complementedStatePairs1, 2);
  addFrameConstraints(solver, variables, problem, initFormula, frames, level, 0);
  addTransitionRelation(solver, variables, problem, 0);
  addCubeAssumptions(solver, variables, targetCube, 1);
  if (!solver.solve()) {
    return std::nullopt;
  }
  return extractStateCube(solver, variables, problem.combinedStateSymbols(), 0);
}

bool cubeSatisfiesInit(const KInductionProblem& problem,
                      KEPLER_FORMAL::Config::SolverType solverType,
                      BoolExpr* initFormula,
                      const StateCube& cube) {
  SATSolverWrapper solver(solverType);
  FrameVariableStore variables(solver, problem.allSymbols, 1);
  addComplementedStateRelations(solver, variables, problem.complementedStatePairs0, 1);
  addComplementedStateRelations(solver, variables, problem.complementedStatePairs1, 1);
  FrameFormulaEncoder encoder(solver, variables.makeLeafLits(0));
  solver.addClause({encoder.encode(initFormula)});
  addCubeAssumptions(solver, variables, cube, 0);
  return solver.solve();
}

bool canPropagateBlockedCube(const KInductionProblem& problem,
                             KEPLER_FORMAL::Config::SolverType solverType,
                             BoolExpr* initFormula,
                             const std::vector<FrameClauses>& frames,
                             size_t level,
                             const StateCube& cube) {
  SATSolverWrapper solver(solverType);
  FrameVariableStore variables(solver, problem.allSymbols, 2);
  addComplementedStateRelations(solver, variables, problem.complementedStatePairs0, 2);
  addComplementedStateRelations(solver, variables, problem.complementedStatePairs1, 2);
  addFrameConstraints(solver, variables, problem, initFormula, frames, level, 0);
  addTransitionRelation(solver, variables, problem, 0);
  addCubeAssumptions(solver, variables, cube, 1);
  return !solver.solve();
}

bool blockCubeRecursively(const KInductionProblem& problem,
                          KEPLER_FORMAL::Config::SolverType solverType,
                          BoolExpr* initFormula,
                          std::vector<FrameClauses>& frames,
                          const StateCube& cube,
                          size_t level,
                          size_t& counterexampleDepth) {
  if (level == 0) {
    counterexampleDepth = 0;
    return false;
  }

  while (true) {
    const auto predecessor = findPredecessorCube(
        problem, solverType, initFormula, frames, level - 1, cube);
    if (!predecessor.has_value()) {
      break;
    }

    if (cubeSatisfiesInit(problem, solverType, initFormula, *predecessor)) {
      counterexampleDepth = level;
      return false;
    }

    if (!blockCubeRecursively(
            problem, solverType, initFormula, frames, *predecessor, level - 1,
            counterexampleDepth)) {
      if (counterexampleDepth == 0) {
        counterexampleDepth = level;
      }
      return false;
    }
  }

  for (size_t i = 1; i <= level; ++i) {
    if (!cubeAlreadyBlocked(frames[i], cube)) {
      frames[i].blockedCubes.push_back(cube);
    }
  }
  return true;
}

void propagateBlockedCubes(const KInductionProblem& problem,
                           KEPLER_FORMAL::Config::SolverType solverType,
                           BoolExpr* initFormula,
                           std::vector<FrameClauses>& frames,
                           size_t lastLevel) {
  for (size_t level = 1; level < lastLevel; ++level) {
    for (const auto& cube : frames[level].blockedCubes) {
      if (cubeAlreadyBlocked(frames[level + 1], cube)) {
        continue;
      }
      if (canPropagateBlockedCube(problem, solverType, initFormula, frames, level, cube)) {
        frames[level + 1].blockedCubes.push_back(cube);
      }
    }
  }
}

bool framesConverged(const FrameClauses& lhs, const FrameClauses& rhs) {
  if (lhs.blockedCubes.size() != rhs.blockedCubes.size()) {
    return false;
  }
  std::unordered_set<std::string> lhsKeys;
  lhsKeys.reserve(lhs.blockedCubes.size());
  for (const auto& cube : lhs.blockedCubes) {
    lhsKeys.insert(cubeKey(cube));
  }
  for (const auto& cube : rhs.blockedCubes) {
    if (lhsKeys.find(cubeKey(cube)) == lhsKeys.end()) {
      return false;
    }
  }
  return true;
}

}  // namespace

IC3Engine::IC3Engine(const KInductionProblem& problem,
                     KEPLER_FORMAL::Config::SolverType solverType)
    : problem_(problem), solverType_(solverType) {}

IC3Result IC3Engine::run(size_t maxFrames, size_t maxStateBits) const {
  const auto combinedStateSymbols = problem_.combinedStateSymbols();
  if (combinedStateSymbols.empty() || combinedStateSymbols.size() > maxStateBits) {
    return {IC3Status::Inconclusive, 0};
  }

  BoolExpr* initFormula = buildInitFormula(problem_);
  if (initFormula == nullptr) {
    return {IC3Status::Inconclusive, 0};
  }

  std::vector<FrameClauses> frames(2);
  for (size_t level = 1; level <= maxFrames; ++level) {
    while (true) {
      const auto badCube = findBadCube(problem_, solverType_, initFormula, frames, level);
      if (!badCube.has_value()) {
        break;
      }

      size_t counterexampleDepth = 0;
      if (!blockCubeRecursively(
              problem_, solverType_, initFormula, frames, *badCube, level,
              counterexampleDepth)) {
        return {IC3Status::Different, counterexampleDepth};
      }
    }

    propagateBlockedCubes(problem_, solverType_, initFormula, frames, level);
    if (framesConverged(frames[level - 1], frames[level])) {
      return {IC3Status::Equivalent, level - 1};
    }
    frames.emplace_back();
  }

  return {IC3Status::Inconclusive, maxFrames};
}

}  // namespace KEPLER_FORMAL::SEC
