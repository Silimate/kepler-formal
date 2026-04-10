// Copyright 2024-2026 keplertech.io
// SPDX-License-Identifier: GPL-3.0-only

#include "kinduction/KInductionEngine.h"

#include "kinduction/SatEncoding.h"

namespace KEPLER_FORMAL::SEC {

namespace {

void addInitialStateRelation(SATSolverWrapper& solver,
                             const FrameVariableStore& variables,
                             const KInductionProblem& problem) {
  // SEC starts from related states: frame 0 state bits of both designs must
  // match before we unroll any transitions.
  for (size_t i = 0; i < problem.stateBits.size(); ++i) {
    addLiteralEquivalence(
        solver,
        variables.getLiteral(problem.state0Symbols[i], 0),
        variables.getLiteral(problem.state1Symbols[i], 0));
  }
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
  // Tie each next-frame state literal to the corresponding transition formula
  // evaluated over the current frame.
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

}  // namespace

KInductionEngine::KInductionEngine(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType)
    : problem_(problem), solverType_(solverType) {}

KInductionResult KInductionEngine::run(size_t maxK) const {
  // Handle the purely combinational mismatch case before any unrolling.
  if (hasBaseCounterexample(0)) {
    return {KInductionStatus::Different, 0};
  }

  // If there is no state, the base check already decided the whole problem.
  if (problem_.combinedStateSymbols().empty()) {
    return {KInductionStatus::Equivalent, 0};
  }

  for (size_t k = 1; k <= maxK; ++k) {
    // Base case: search for a reachable bad frame within 0..k.
    if (hasBaseCounterexample(k)) {
      return {KInductionStatus::Different, k};
    }
    // Induction step: assume the property along a simple path of length k and
    // ask whether the last frame can still be bad.
    if (provesByInduction(k)) {
      return {KInductionStatus::Equivalent, k};
    }
  }

  return {KInductionStatus::Inconclusive, maxK};
}

bool KInductionEngine::hasBaseCounterexample(size_t k) const {
  SATSolverWrapper solver(solverType_);
  FrameVariableStore variables(solver, problem_.allSymbols, k + 1);
  addInitialStateRelation(solver, variables, problem_);
  // Multi-output flops such as Q/QN must preserve their within-design
  // complement relation at every frame, including frame 0.
  addComplementedStateRelations(
      solver, variables, problem_.complementedStatePairs0, k + 1);
  addComplementedStateRelations(
      solver, variables, problem_.complementedStatePairs1, k + 1);

  // Unroll the combined transition system for k steps.
  for (size_t frame = 0; frame < k; ++frame) {
    addTransitionRelation(solver, variables, problem_, frame);
  }

  // A base-case witness is any bad frame in the prefix 0..k.
  std::vector<int> badClause;
  badClause.reserve(k + 1);
  for (size_t frame = 0; frame <= k; ++frame) {
    FrameFormulaEncoder encoder(solver, variables.makeLeafLits(frame));
    badClause.push_back(encoder.encode(problem_.bad));
  }
  solver.addClause(badClause);

  return solver.solve();
}

bool KInductionEngine::provesByInduction(size_t k) const {
  SATSolverWrapper solver(solverType_);
  FrameVariableStore variables(solver, problem_.allSymbols, k + 1);
  addComplementedStateRelations(
      solver, variables, problem_.complementedStatePairs0, k + 1);
  addComplementedStateRelations(
      solver, variables, problem_.complementedStatePairs1, k + 1);

  // Unroll k transitions without constraining the starting state.
  for (size_t frame = 0; frame < k; ++frame) {
    addTransitionRelation(solver, variables, problem_, frame);
  }

  // Assume the SEC property on the first k frames.
  for (size_t frame = 0; frame < k; ++frame) {
    FrameFormulaEncoder encoder(solver, variables.makeLeafLits(frame));
    solver.addClause({encoder.encode(problem_.property)});
  }

  addSimplePathConstraint(
      solver, variables, problem_.combinedStateSymbols(), k + 1);

  // Try to violate the property at the successor frame. UNSAT means the
  // property is k-inductive over simple paths.
  FrameFormulaEncoder lastFrameEncoder(solver, variables.makeLeafLits(k));
  solver.addClause({lastFrameEncoder.encode(problem_.bad)});

  return !solver.solve();
}

}  // namespace KEPLER_FORMAL::SEC
