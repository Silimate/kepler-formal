// Copyright 2024-2026 keplertech.io
// SPDX-License-Identifier: GPL-3.0-only

#include "kinduction/KInductionEngine.h"

#include <stdexcept>
#include <unordered_map>

#include "kinduction/SatEncoding.h"

namespace KEPLER_FORMAL::SEC {

namespace {

enum class InitialConstraintMode {
  None,
  ObservationOnly,
  PartialInit,
  CompleteInit,
};

size_t resetBootstrapFrames(const KInductionProblem& problem) {
  // Large mapped designs such as TinyRocket often need a few asserted reset
  // cycles before every observable path has converged to a comparable
  // post-reset state. Keep the SEC horizon user-facing by subtracting this
  // bootstrap prefix back out of reported witness cycles.
  return (!problem.hasCompleteInitialState() && problem.hasResetBootstrap())
             ? problem.resetBootstrapCycles
             : 0u;
}

void addResetBootstrapConstraints(SATSolverWrapper& solver,
                                  const FrameVariableStore& variables,
                                  const KInductionProblem& problem,
                                  size_t numFrames) {
  const size_t bootstrapFrames = resetBootstrapFrames(problem);
  if (bootstrapFrames == 0) {
    return;
  }

  for (const auto& [symbol, assertedValue] : problem.resetBootstrapInputs) {
    // Keep reset asserted across the whole bootstrap prefix so the SAT problem
    // matches the same multi-cycle reset schedule used when we derive known
    // post-reset state values. Release reset only after the bootstrap window.
    for (size_t frame = 0; frame < std::min(bootstrapFrames, numFrames); ++frame) {
      solver.addClause(
          {assertedValue ? variables.getLiteral(symbol, frame)
                         : -variables.getLiteral(symbol, frame)});
    }
    for (size_t frame = bootstrapFrames; frame < numFrames; ++frame) {
      solver.addClause(
          {assertedValue ? -variables.getLiteral(symbol, frame)
                         : variables.getLiteral(symbol, frame)});
    }
  }
}

void addBootstrapStateEqualities(SATSolverWrapper& solver,
                                 const FrameVariableStore& variables,
                                 const KInductionProblem& problem,
                                 size_t frame) {
  for (const auto& [lhsSymbol, rhsSymbol] : problem.bootstrapStateEqualityPairs) {
    addLiteralEquivalence(
        solver,
        variables.getLiteral(lhsSymbol, frame),
        variables.getLiteral(rhsSymbol, frame));
  }
}

void addInitialStateEqualities(SATSolverWrapper& solver,
                               const FrameVariableStore& variables,
                               const KInductionProblem& problem) {
  for (const auto& [lhsSymbol, rhsSymbol] : problem.initialStateEqualityPairs) {
    addLiteralEquivalence(
        solver,
        variables.getLiteral(lhsSymbol, 0),
        variables.getLiteral(rhsSymbol, 0));
  }
}

void addBootstrapStateAssignments(SATSolverWrapper& solver,
                                  const FrameVariableStore& variables,
                                  const KInductionProblem& problem,
                                  size_t frame) {
  for (const auto& [symbol, value] : problem.bootstrapStateAssignments) {
    solver.addClause({value ? variables.getLiteral(symbol, frame)
                            : -variables.getLiteral(symbol, frame)});
  }
}

void addInductiveStateEqualities(SATSolverWrapper& solver,
                                 const FrameVariableStore& variables,
                                 const KInductionProblem& problem,
                                 size_t firstFrame,
                                 size_t lastFrame) {
  if (problem.inductiveStateEqualityPairs.empty() || firstFrame > lastFrame) {
    return;
  }

  for (size_t frame = firstFrame; frame <= lastFrame; ++frame) {
    for (const auto& [lhsSymbol, rhsSymbol] : problem.inductiveStateEqualityPairs) {
      addLiteralEquivalence(
          solver,
          variables.getLiteral(lhsSymbol, frame),
          variables.getLiteral(rhsSymbol, frame));
    }
  }
}

InitialConstraintMode addInitialConstraints(SATSolverWrapper& solver,
                                            const FrameVariableStore& variables,
                                            const KInductionProblem& problem) {
  if (!problem.hasSequentialState()) {
    return InitialConstraintMode::None;
  }

  const bool hasInitialStateRelation = !problem.initialStateEqualityPairs.empty();
  FrameFormulaEncoder encoder(solver, variables.makeLeafLits(0));
  if (problem.hasCompleteInitialState()) {
    // When reset/init data is available for every extracted state bit, SEC can
    // start from the real post-reset state instead of an arbitrary
    // output-equivalent observation.
    solver.addClause({encoder.encode(problem.initialCondition)});
    return InitialConstraintMode::CompleteInit;
  }

  if (problem.hasExplicitInitialState()) {
    // Partial reset coverage still helps rule out many impossible starts, but
    // frame 0 is only guaranteed meaningful when we also have a correspondence
    // relation between the two designs' starting states.
    solver.addClause({encoder.encode(problem.initialCondition)});
    if (hasInitialStateRelation) {
      return InitialConstraintMode::CompleteInit;
    }
    solver.addClause({encoder.encode(problem.property)});
    return InitialConstraintMode::PartialInit;
  }

  if (hasInitialStateRelation) {
    return InitialConstraintMode::CompleteInit;
  }

  // Without init/reset information, output-only SEC does not assume any
  // internal state correspondence between the two designs. The base case starts
  // from an output-equivalent frame 0 observation and checks whether the
  // outputs can diverge later.
  solver.addClause({encoder.encode(problem.property)});
  return InitialConstraintMode::ObservationOnly;
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

std::unordered_map<size_t, bool> buildFrameEnvironment(
    const SATSolverWrapper& solver,
    const FrameVariableStore& variables,
    const std::vector<size_t>& symbols,
    size_t frame) {
  std::unordered_map<size_t, bool> environment;
  environment.reserve(symbols.size());
  for (const auto symbol : symbols) {
    environment.emplace(
        symbol, solver.getLiteralValue(variables.getLiteral(symbol, frame)));
  }
  return environment;
}

size_t findFirstBadFrame(const SATSolverWrapper& solver,
                         const FrameVariableStore& variables,
                         const KInductionProblem& problem,
                         size_t firstBadFrame,
                         size_t maxFrame) {
  for (size_t frame = firstBadFrame; frame <= maxFrame; ++frame) {
    if (problem.bad->evaluate(
            buildFrameEnvironment(solver, variables, problem.allSymbols, frame))) {
      return frame;
    }
  }
  throw std::runtime_error("SAT model does not satisfy any bad frame");
}

std::vector<KInductionResult::FrameInputAssignments> buildInputTrace(
    const SATSolverWrapper& solver,
    const FrameVariableStore& variables,
    const KInductionProblem& problem,
    size_t firstFrame,
    size_t lastFrame,
    size_t frameOffset) {
  std::vector<KInductionResult::FrameInputAssignments> trace;
  trace.reserve(lastFrame - firstFrame + 1);
  for (size_t frame = firstFrame; frame <= lastFrame; ++frame) {
    KInductionResult::FrameInputAssignments frameAssignments;
    frameAssignments.frame = frame - frameOffset;
    frameAssignments.assignments.reserve(problem.inputSymbols.size());
    for (size_t i = 0; i < problem.inputSymbols.size(); ++i) {
      frameAssignments.assignments.push_back(
          {problem.environmentInputNames[i],
           solver.getLiteralValue(
               variables.getLiteral(problem.inputSymbols[i], frame))});
    }
    trace.push_back(std::move(frameAssignments));
  }
  return trace;
}

std::vector<KInductionResult::SignalMismatch> collectObservedOutputMismatches(
    const SATSolverWrapper& solver,
    const FrameVariableStore& variables,
    const KInductionProblem& problem,
    size_t frame) {
  const auto environment =
      buildFrameEnvironment(solver, variables, problem.allSymbols, frame);
  std::vector<KInductionResult::SignalMismatch> mismatches;
  for (size_t i = 0; i < problem.observedOutputExprs0.size(); ++i) {
    const bool value0 = problem.observedOutputExprs0[i]->evaluate(environment);
    const bool value1 = problem.observedOutputExprs1[i]->evaluate(environment);
    if (value0 != value1) {
      mismatches.push_back(
          {problem.observedOutputNames[i], value0, value1});
    }
  }
  return mismatches;
}

KInductionResult::CounterexampleWitness buildCounterexampleWitness(
    const SATSolverWrapper& solver,
    const FrameVariableStore& variables,
    const KInductionProblem& problem,
    size_t firstBadFrame,
    size_t maxFrame,
    size_t frameOffset) {
  KInductionResult::CounterexampleWitness witness;
  const size_t internalBadFrame =
      findFirstBadFrame(solver, variables, problem, firstBadFrame, maxFrame);
  witness.badFrame = internalBadFrame - frameOffset;
  witness.inputTrace = buildInputTrace(
      solver, variables, problem, frameOffset, internalBadFrame, frameOffset);
  witness.outputMismatches = collectObservedOutputMismatches(
      solver, variables, problem, internalBadFrame);
  return witness;
}

}  // namespace

KInductionEngine::KInductionEngine(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType)
    : problem_(problem), solverType_(solverType) {}

KInductionResult KInductionEngine::run(size_t maxK) const {
  // Handle the purely combinational mismatch case before any unrolling.
  if (auto witness = findBaseCounterexample(0); witness.has_value()) {
    return {KInductionStatus::Different, witness->badFrame, std::move(witness)};
  }

  // If there is no state, the base check already decided the whole problem.
  if (problem_.combinedStateSymbols().empty()) {
    return {KInductionStatus::Equivalent, 0};
  }

  // Search the whole bounded horizon for concrete counterexamples before an
  // induction proof is allowed to conclude equivalence. This keeps SEC honest
  // when a later output divergence exists even though a small-k induction step
  // happens to be too coarse to expose it yet.
  for (size_t k = 1; k <= maxK; ++k) {
    printf("Checking k=%zu...\n", k);
    if (auto witness = findBaseCounterexample(k); witness.has_value()) {
      return {KInductionStatus::Different, witness->badFrame, std::move(witness)};
    }
  // }

  // for (size_t k = 1; k <= maxK; ++k) {
    // Induction step: assume the property along a simple path of length k and
    // ask whether the last frame can still be bad.
    if (provesByInduction(k)) {
      return {KInductionStatus::Equivalent, k};
    }
  }

  return {KInductionStatus::Inconclusive, maxK};
}

std::optional<KInductionResult::CounterexampleWitness>
KInductionEngine::findBaseCounterexample(size_t k) const {
  const size_t bootstrapFrames = resetBootstrapFrames(problem_);
  const size_t internalK = k + bootstrapFrames;
  SATSolverWrapper solver(solverType_);
  FrameVariableStore variables(solver, problem_.allSymbols, internalK + 1);
  addResetBootstrapConstraints(solver, variables, problem_, internalK + 1);
  const InitialConstraintMode initialMode =
      bootstrapFrames == 0 ? addInitialConstraints(solver, variables, problem_)
                           : InitialConstraintMode::None;
  // Multi-output flops such as Q/QN must preserve their within-design
  // complement relation at every frame, including frame 0.
  addComplementedStateRelations(
      solver, variables, problem_.complementedStatePairs0, internalK + 1);
  addComplementedStateRelations(
      solver, variables, problem_.complementedStatePairs1, internalK + 1);
  addInitialStateEqualities(solver, variables, problem_);

  // Unroll the combined transition system for k steps.
  for (size_t frame = 0; frame < internalK; ++frame) {
    addTransitionRelation(solver, variables, problem_, frame);
  }
  if (bootstrapFrames != 0) {
    addBootstrapStateAssignments(solver, variables, problem_, bootstrapFrames);
    addBootstrapStateEqualities(solver, variables, problem_, bootstrapFrames);
  }

  // A fully initialized reset state makes frame 0 meaningful. Otherwise SEC
  // still needs the old "matching observation at frame 0" guard before the
  // first real bad frame.
  size_t firstBadFrame = 0;
  if (bootstrapFrames != 0) {
    firstBadFrame = bootstrapFrames;
  } else if (initialMode == InitialConstraintMode::ObservationOnly ||
      initialMode == InitialConstraintMode::PartialInit) {
    firstBadFrame = 1;
  }
  if (firstBadFrame > internalK) {
    return std::nullopt;
  }

  std::vector<int> badClause;
  badClause.reserve(internalK - firstBadFrame + 1);
  for (size_t frame = firstBadFrame; frame <= internalK; ++frame) {
    FrameFormulaEncoder encoder(solver, variables.makeLeafLits(frame));
    badClause.push_back(encoder.encode(problem_.bad));
  }
  solver.addClause(badClause);

  if (!solver.solve()) {
    return std::nullopt;
  }
  return buildCounterexampleWitness(
      solver, variables, problem_, firstBadFrame, internalK, bootstrapFrames);
}

bool KInductionEngine::provesByInduction(size_t k) const {
  const bool hasExplicitInductionInvariant = problem_.inductionProperty != nullptr;
  BoolExpr* inductionProperty =
      hasExplicitInductionInvariant ? problem_.inductionProperty
                                            : problem_.property;
  BoolExpr* inductionBad =
      problem_.inductionBad != nullptr ? problem_.inductionBad : problem_.bad;
  SATSolverWrapper solver(solverType_);
  FrameVariableStore variables(solver, problem_.allSymbols, k + 1);
  addComplementedStateRelations(
      solver, variables, problem_.complementedStatePairs0, k + 1);
  addComplementedStateRelations(
      solver, variables, problem_.complementedStatePairs1, k + 1);

  // Unroll k transitions without constraining the starting state. The base
  // case handles reset/bootstrap reachability; the induction step remains the
  // standard arbitrary-state proof over simple paths.
  for (size_t frame = 0; frame < k; ++frame) {
    addTransitionRelation(solver, variables, problem_, frame);
  }

  // Assume the SEC property on the first k frames.
  for (size_t frame = 0; frame < k; ++frame) {
    FrameFormulaEncoder encoder(solver, variables.makeLeafLits(frame));
    solver.addClause({encoder.encode(inductionProperty)});
  }
  if (!hasExplicitInductionInvariant) {
    addInductiveStateEqualities(solver, variables, problem_, 0, k - 1);
  }

  addSimplePathConstraint(
      solver, variables, problem_.combinedStateSymbols(), k + 1);

  // Try to violate the property at the successor frame. UNSAT means the
  // property is k-inductive over simple paths.
  FrameFormulaEncoder lastFrameEncoder(solver, variables.makeLeafLits(k));
  solver.addClause({lastFrameEncoder.encode(inductionBad)});

  return !solver.solve();
}

}  // namespace KEPLER_FORMAL::SEC
