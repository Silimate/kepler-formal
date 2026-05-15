// Copyright 2024-2026 keplertech.io
// SPDX-License-Identifier: GPL-3.0-only

#include "kinduction/BaseCaseSolver.h"

#include <algorithm>
#include <cstdlib>
#include <set>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <unordered_set>

#include "common/SecDiag.h"
#include "kinduction/SatEncoding.h"
#include "proof/TransitionExprResolver.h"

namespace KEPLER_FORMAL::SEC {

namespace {

enum class InitialConstraintMode {
  None,
  ObservationOnly,
  PartialInit,
  CompleteInit,
};

size_t resetBootstrapFrames(const KInductionProblem& problem) {
  return (!problem.hasCompleteInitialState() && problem.hasResetBootstrap())
             ? problem.resetBootstrapCycles
             : 0u;
}

InitialConstraintMode determineInitialConstraintMode(const KInductionProblem& problem) {
  if (!problem.hasSequentialState()) {
    return InitialConstraintMode::None;
  }

  const bool hasInitialStateRelation = !problem.initialStateEqualityPairs.empty();
  if (problem.hasCompleteInitialState()) {
    return InitialConstraintMode::CompleteInit;
  }

  if (problem.hasExplicitInitialState()) {
    return hasInitialStateRelation ? InitialConstraintMode::CompleteInit
                                   : InitialConstraintMode::PartialInit;
  }

  if (hasInitialStateRelation) {
    return InitialConstraintMode::CompleteInit;
  }

  return InitialConstraintMode::ObservationOnly;
}

struct BaseCaseCoi {
  std::vector<std::vector<size_t>> transitionTargetsByFrame;
  std::vector<size_t> solverSymbols;
  std::unordered_set<size_t> solverSymbolSet;
};

std::unordered_set<size_t> buildStateSymbolSet(const KInductionProblem& problem) {
  std::unordered_set<size_t> stateSymbols;
  stateSymbols.reserve(problem.state0Symbols.size() + problem.state1Symbols.size());
  stateSymbols.insert(problem.state0Symbols.begin(), problem.state0Symbols.end());
  stateSymbols.insert(problem.state1Symbols.begin(), problem.state1Symbols.end());
  return stateSymbols;
}

std::unordered_map<size_t, size_t> buildPrimaryByComplementSymbol(
    const KInductionProblem& problem) {
  std::unordered_map<size_t, size_t> primaryByComplement;
  primaryByComplement.reserve(
      problem.complementedStatePairs0.size() +
      problem.complementedStatePairs1.size());
  for (const auto& [primarySymbol, complementedSymbol] :
       problem.complementedStatePairs0) {
    primaryByComplement.emplace(complementedSymbol, primarySymbol);
  }
  for (const auto& [primarySymbol, complementedSymbol] :
       problem.complementedStatePairs1) {
    primaryByComplement.emplace(complementedSymbol, primarySymbol);
  }
  return primaryByComplement;
}

std::vector<size_t> sortedSymbols(const std::unordered_set<size_t>& symbols) {
  std::vector<size_t> sorted(symbols.begin(), symbols.end());
  std::sort(sorted.begin(), sorted.end());
  return sorted;
}

std::set<size_t> formulaSupportOrThrow(BoolExpr* formula, const char* context) {
  if (formula == nullptr) {
    throw std::runtime_error(
        std::string("Missing BoolExpr while encoding base SEC formula: ") +
        context);
  }
  return formula->getSupportVars();
}

void addFormulaStateSupport(BoolExpr* formula,
                            const std::unordered_set<size_t>& stateSymbols,
                            std::unordered_set<size_t>& output) {
  if (formula == nullptr) {
    return;
  }
  for (const auto symbol : formula->getSupportVars()) {
    if (stateSymbols.find(symbol) != stateSymbols.end()) {
      output.insert(symbol);
    }
  }
}

void addFormulaSupport(BoolExpr* formula, std::unordered_set<size_t>& output) {
  if (formula == nullptr) {
    return;
  }
  for (const auto symbol : formula->getSupportVars()) {
    if (symbol >= 2) {
      output.insert(symbol);
    }
  }
}

bool hasStructuredInitialAssignments(const KInductionProblem& problem) {
  return !problem.initialStateAssignments.empty();
}

bool isKInductionCoiDiagEnabled() {
  return std::getenv("KEPLER_SEC_KI_DIAG") != nullptr || isSecDiagEnabled();
}

void addEqualityAliasesForFrame(
    FrameSymbolAliases& aliasesByFrame,
    const std::vector<std::pair<size_t, size_t>>& equalityPairs,
    const std::unordered_set<size_t>& solverSymbols,
    size_t frame) {
  if (frame >= aliasesByFrame.size()) {
    return;  // LCOV_EXCL_LINE
  }
  auto& frameAliases = aliasesByFrame[frame];
  for (const auto& [lhsSymbol, rhsSymbol] : equalityPairs) {
    if (solverSymbols.find(lhsSymbol) == solverSymbols.end() ||
        solverSymbols.find(rhsSymbol) == solverSymbols.end()) {
      continue;
    }
    frameAliases.emplace_back(lhsSymbol, rhsSymbol);
  }
}

FrameSymbolAliases buildBaseCaseFrameAliases(const KInductionProblem& problem,
                                             const BaseCaseCoi& coi,
                                             size_t numFrames,
                                             size_t bootstrapFrames) {
  // Initial/bootstrap equality pairs are assumptions about a specific time
  // frame.  Encoding those assumptions as frame-local literal aliases gives the
  // SAT engine the quotient system directly, instead of asking it to rediscover
  // thousands of state correspondences through binary equivalence clauses.
  FrameSymbolAliases aliasesByFrame(numFrames);
  addEqualityAliasesForFrame(
      aliasesByFrame, problem.initialStateEqualityPairs, coi.solverSymbolSet, 0);
  if (bootstrapFrames != 0 && bootstrapFrames < numFrames) {
    addEqualityAliasesForFrame(
        aliasesByFrame,
        problem.bootstrapStateEqualityPairs,
        coi.solverSymbolSet,
        bootstrapFrames);
  }
  // Do not alias inductive strengthening facts in the concrete base query.
  // They are valid assumptions for the induction step, but BMC must search the
  // actual initialized transition system so a finite counterexample cannot be
  // hidden by an over-eager quotient.
  return aliasesByFrame;
}

std::vector<size_t> expandTransitionTargets(
    const std::unordered_set<size_t>& requestedTargets,
    const TransitionExprResolver& transitionByState,
    const std::unordered_map<size_t, size_t>& primaryByComplement) {
  std::unordered_set<size_t> expanded;
  expanded.reserve(requestedTargets.size());
  for (const auto symbol : requestedTargets) {
    if (transitionByState.contains(symbol)) {
      expanded.insert(symbol);
      continue;
    }
    if (const auto primaryIt = primaryByComplement.find(symbol);
        primaryIt != primaryByComplement.end() &&
        transitionByState.contains(primaryIt->second)) {
      expanded.insert(primaryIt->second);
    }
  }
  return sortedSymbols(expanded);
}

void closeFrameEqualityDependencies(
    const std::vector<std::pair<size_t, size_t>>& equalityPairs,
    std::unordered_set<size_t>& frameStates) {
  // Equality constraints can make a state bit relevant even if the bad cone
  // touches only its paired bit. Iterate to cover short equality chains while
  // still keeping unrelated resetless state out of the SAT problem.
  bool changed = true;
  while (changed) {
    changed = false;
    for (const auto& [lhsSymbol, rhsSymbol] : equalityPairs) {
      const bool lhsRelevant = frameStates.find(lhsSymbol) != frameStates.end();
      const bool rhsRelevant = frameStates.find(rhsSymbol) != frameStates.end();
      if (!lhsRelevant && !rhsRelevant) {
        continue;
      }
      changed |= frameStates.insert(lhsSymbol).second;
      changed |= frameStates.insert(rhsSymbol).second;
    }
  }
}

void addRelevantComplementPartners(
    const std::vector<std::pair<size_t, size_t>>& complementedStatePairs,
    std::unordered_set<size_t>& solverSymbols) {
  for (const auto& [primarySymbol, complementedSymbol] : complementedStatePairs) {
    if (solverSymbols.find(primarySymbol) != solverSymbols.end() ||
        solverSymbols.find(complementedSymbol) != solverSymbols.end()) {
      solverSymbols.insert(primarySymbol);
      solverSymbols.insert(complementedSymbol);
    }
  }
}

BaseCaseCoi buildBaseCaseCoi(const KInductionProblem& problem,
                             InitialConstraintMode initialMode,
                             size_t bootstrapFrames,
                             size_t firstBadFrame,
                             size_t internalK,
                             bool constrainPreviouslySafeFrames) {
  // Cone-of-influence reduction for the base query. The original formula is
  // still the same bounded counterexample check, but we avoid allocating and
  // constraining state bits that cannot influence any checked bad output.
  // This matters for ASIC SEC where resetless memories can create hundreds of
  // thousands of frame-0 equality pairs that are irrelevant for a given output
  // cone.
  const auto stateSymbols = buildStateSymbolSet(problem);
  const TransitionExprResolver transitionByState(problem);
  const auto primaryByComplement = buildPrimaryByComplementSymbol(problem);

  std::vector<std::unordered_set<size_t>> requiredStates(internalK + 1);
  std::unordered_set<size_t> solverSymbols;
  solverSymbols.reserve(1024);
  for (const auto& [symbol, _] : problem.resetBootstrapInputs) {
    solverSymbols.insert(symbol);
  }

  addFormulaSupport(problem.bad, solverSymbols);
  for (size_t frame = firstBadFrame; frame <= internalK; ++frame) {
    addFormulaStateSupport(problem.bad, stateSymbols, requiredStates[frame]);
  }
  if (constrainPreviouslySafeFrames) {
    // Frontier checks are issued only after all smaller frontiers were proved
    // safe. Assert those already-known property facts in the standalone SAT
    // query so Kissat gets the same pruning an incremental BMC run would have.
    addFormulaSupport(problem.property, solverSymbols);
    for (size_t frame = bootstrapFrames; frame < firstBadFrame; ++frame) {
      addFormulaStateSupport(problem.property, stateSymbols, requiredStates[frame]);
    }
  }

  if (bootstrapFrames == 0) {
    if (initialMode == InitialConstraintMode::CompleteInit ||
        initialMode == InitialConstraintMode::PartialInit) {
      if (!hasStructuredInitialAssignments(problem)) {
        // Compatibility path for hand-built unit-test problems and older
        // callers.  Production SEC builds initial state as structured unit
        // assignments, so the base query can keep the COI narrow.
        addFormulaSupport(problem.initialCondition, solverSymbols);
        addFormulaStateSupport(
            problem.initialCondition, stateSymbols, requiredStates[0]);
      }
    }
    if (initialMode == InitialConstraintMode::ObservationOnly ||
        initialMode == InitialConstraintMode::PartialInit) {
      addFormulaSupport(problem.property, solverSymbols);
      addFormulaStateSupport(problem.property, stateSymbols, requiredStates[0]);
    }
  }

  std::vector<std::vector<size_t>> transitionTargetsByFrame(internalK);
  for (size_t frame = internalK; frame > 0; --frame) {
    if (bootstrapFrames != 0 && frame == bootstrapFrames) {
      closeFrameEqualityDependencies(
          problem.bootstrapStateEqualityPairs, requiredStates[frame]);
    }
    auto targets = expandTransitionTargets(
        requiredStates[frame],
        transitionByState,
        primaryByComplement);
    transitionTargetsByFrame[frame - 1] = targets;
    for (const auto target : targets) {
      addFormulaStateSupport(
          transitionByState.at(target), stateSymbols, requiredStates[frame - 1]);
    }
  }

  closeFrameEqualityDependencies(problem.initialStateEqualityPairs, requiredStates[0]);

  for (const auto& frameStates : requiredStates) {
    solverSymbols.insert(frameStates.begin(), frameStates.end());
  }
  for (const auto& targets : transitionTargetsByFrame) {
    for (const auto target : targets) {
      solverSymbols.insert(target);
      addFormulaSupport(transitionByState.at(target), solverSymbols);
    }
  }
  addRelevantComplementPartners(problem.complementedStatePairs0, solverSymbols);
  addRelevantComplementPartners(problem.complementedStatePairs1, solverSymbols);

  BaseCaseCoi coi;
  coi.transitionTargetsByFrame = std::move(transitionTargetsByFrame);
  coi.solverSymbols = sortedSymbols(solverSymbols);
  coi.solverSymbolSet.insert(coi.solverSymbols.begin(), coi.solverSymbols.end());
  return coi;
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
                                 const std::unordered_set<size_t>& solverSymbols,
                                 size_t frame) {
  for (const auto& [lhsSymbol, rhsSymbol] : problem.bootstrapStateEqualityPairs) {
    if (solverSymbols.find(lhsSymbol) == solverSymbols.end() ||
        solverSymbols.find(rhsSymbol) == solverSymbols.end()) {
      continue;
    }
    const int lhs = variables.getLiteral(lhsSymbol, frame);
    const int rhs = variables.getLiteral(rhsSymbol, frame);
    if (lhs == rhs) {
      continue;
    }
    addLiteralEquivalence(
        solver,
        lhs,
        rhs);
  }
}

void addInitialStateEqualities(SATSolverWrapper& solver,
                               const FrameVariableStore& variables,
                               const KInductionProblem& problem,
                               const std::unordered_set<size_t>& solverSymbols) {
  for (const auto& [lhsSymbol, rhsSymbol] : problem.initialStateEqualityPairs) {
    if (solverSymbols.find(lhsSymbol) == solverSymbols.end() ||
        solverSymbols.find(rhsSymbol) == solverSymbols.end()) {
      continue;
    }
    const int lhs = variables.getLiteral(lhsSymbol, 0);
    const int rhs = variables.getLiteral(rhsSymbol, 0);
    if (lhs == rhs) {
      continue;
    }
    addLiteralEquivalence(
        solver,
        lhs,
        rhs);
  }
}

size_t addInitialStateAssignments(
    SATSolverWrapper& solver,
    const FrameVariableStore& variables,
    const KInductionProblem& problem,
    const std::unordered_set<size_t>& solverSymbols) {
  size_t encodedCount = 0;
  for (const auto& [symbol, value] : problem.initialStateAssignments) {
    if (solverSymbols.find(symbol) == solverSymbols.end()) {
      continue;
    }
    solver.addClause({value ? variables.getLiteral(symbol, 0)
                            : -variables.getLiteral(symbol, 0)});
    ++encodedCount;
  }
  return encodedCount;
}

void addBootstrapStateAssignments(SATSolverWrapper& solver,
                                  const FrameVariableStore& variables,
                                  const KInductionProblem& problem,
                                  const std::unordered_set<size_t>& solverSymbols,
                                  size_t frame) {
  for (const auto& [symbol, value] : problem.bootstrapStateAssignments) {
    if (solverSymbols.find(symbol) == solverSymbols.end()) {
      continue;
    }
    solver.addClause({value ? variables.getLiteral(symbol, frame)
                            : -variables.getLiteral(symbol, frame)});
  }
}

void addInitialConstraints(SATSolverWrapper& solver,
                           const FrameVariableStore& variables,
                           const KInductionProblem& problem,
                           const std::unordered_set<size_t>& solverSymbols,
                           InitialConstraintMode mode) {
  if (mode == InitialConstraintMode::None) {
    return;
  }

  if ((mode == InitialConstraintMode::CompleteInit ||
       mode == InitialConstraintMode::PartialInit) &&
      problem.initialCondition != nullptr) {
    if (hasStructuredInitialAssignments(problem)) {
      addInitialStateAssignments(solver, variables, problem, solverSymbols);
    } else {
      FrameFormulaEncoder encoder(
          solver,
          variables.makeLeafLits(
              0, formulaSupportOrThrow(problem.initialCondition, "initial condition")));
      solver.addClause({encoder.encode(problem.initialCondition)});
    }
  }

  if (mode == InitialConstraintMode::ObservationOnly ||
      mode == InitialConstraintMode::PartialInit) {
    FrameFormulaEncoder encoder(
        solver,
        variables.makeLeafLits(
            0, formulaSupportOrThrow(problem.property, "observation property")));
    solver.addClause({encoder.encode(problem.property)});
  }
}

size_t countTransitionTargets(
    const std::vector<std::vector<size_t>>& transitionTargetsByFrame) {
  size_t count = 0;
  for (const auto& targets : transitionTargetsByFrame) {
    count += targets.size();
  }
  return count;
}

size_t countMatchingAssignments(
    const std::vector<std::pair<size_t, bool>>& assignments,
    const std::unordered_set<size_t>& solverSymbols) {
  size_t count = 0;
  for (const auto& [symbol, _] : assignments) {
    if (solverSymbols.find(symbol) != solverSymbols.end()) {
      ++count;
    }
  }
  return count;
}

void emitBaseCaseCoiDiag(const KInductionProblem& problem,
                         const BaseCaseCoi& coi,
                         size_t k,
                         size_t firstBadFrame,
                         size_t internalK,
                         bool constrainPreviouslySafeFrames) {
  if (!isKInductionCoiDiagEnabled()) {
    return;
  }
  emitSecDiag(
      "SEC diag: k-induction base coi k=", k,
      " first_bad_frame=", firstBadFrame,
      " frames=", internalK + 1,
      " solver_symbols=", coi.solverSymbols.size(),
      " transition_targets=", countTransitionTargets(coi.transitionTargetsByFrame),
      " bad_support=", problem.bad != nullptr ? problem.bad->getSupportVars().size() : 0,
      " initial_equalities=", problem.initialStateEqualityPairs.size(),
      " inductive_equalities=", problem.inductiveStateEqualityPairs.size(),
      " initial_assignments=", problem.initialStateAssignments.size(),
      " encoded_initial_assignments=",
      countMatchingAssignments(problem.initialStateAssignments, coi.solverSymbolSet),
      " structured_initial_assignments=", hasStructuredInitialAssignments(problem),
      " safe_prefix_constraints=", constrainPreviouslySafeFrames);
}

void addComplementedStateRelations(
    SATSolverWrapper& solver,
    const FrameVariableStore& variables,
    const std::vector<std::pair<size_t, size_t>>& complementedStatePairs,
    const std::unordered_set<size_t>& solverSymbols,
    size_t numFrames) {
  for (size_t frame = 0; frame < numFrames; ++frame) {
    for (const auto& [primarySymbol, complementedSymbol] : complementedStatePairs) {
      if (solverSymbols.find(primarySymbol) == solverSymbols.end() ||
          solverSymbols.find(complementedSymbol) == solverSymbols.end()) {
        continue;
      }
      addLiteralEquivalence(
          solver,
          variables.getLiteral(complementedSymbol, frame),
          -variables.getLiteral(primarySymbol, frame));
    }
  }
}

void addTransitionRelation(SATSolverWrapper& solver,
                           const FrameVariableStore& variables,
                           const TransitionExprResolver& transitionByState,
                           const std::vector<size_t>& targets,
                           size_t frame) {
  // All transition formulas in one frame are slices of the same combinational
  // next-state network. Reusing a frame encoder lets shared BoolExpr DAG nodes
  // produce one Tseitin literal instead of being re-encoded once per state bit.
  FrameFormulaEncoder encoder(solver, variables.makeLeafLits(frame));
  for (const auto stateSymbol : targets) {
    BoolExpr* expr = transitionByState.at(stateSymbol);
    addLiteralEquivalence(
        solver,
        variables.getLiteral(stateSymbol, frame + 1),
        encoder.encode(expr));
  }
}

std::unordered_map<size_t, bool> buildFrameEnvironment(
    const SATSolverWrapper& solver,
    const FrameVariableStore& variables,
    BoolExpr* formula,
    size_t frame) {
  std::unordered_map<size_t, bool> environment;
  if (formula == nullptr) {
    return environment;
  }
  const auto support = formula->getSupportVars();
  environment.reserve(support.size());
  for (const auto symbol : support) {
    if (symbol < 2) {
      continue;
    }
    environment.emplace(
        symbol, solver.getLiteralValue(variables.getLiteral(symbol, frame)));
  }
  return environment;
}

void addFormulaValuesToEnvironment(const SATSolverWrapper& solver,
                                   const FrameVariableStore& variables,
                                   BoolExpr* formula,
                                   size_t frame,
                                   std::unordered_map<size_t, bool>& environment) {
  if (formula == nullptr) {
    return;
  }
  for (const auto symbol : formula->getSupportVars()) {
    if (symbol < 2 || environment.find(symbol) != environment.end()) {
      continue;
    }
    environment.emplace(
        symbol, solver.getLiteralValue(variables.getLiteral(symbol, frame)));
  }
}

size_t findFirstBadFrame(const SATSolverWrapper& solver,
                         const FrameVariableStore& variables,
                         const KInductionProblem& problem,
                         size_t firstBadFrame,
                         size_t maxFrame) {
  for (size_t frame = firstBadFrame; frame <= maxFrame; ++frame) {
    if (problem.bad->evaluate(
            buildFrameEnvironment(solver, variables, problem.bad, frame))) {
      return frame;
    }
  }
  throw std::runtime_error("SAT model does not satisfy any bad frame");  // LCOV_EXCL_LINE
}  // LCOV_EXCL_LINE

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
      // COI-reduced proof obligations intentionally do not allocate SAT
      // literals for environment inputs that cannot affect the checked output.
      // A counterexample witness only needs assignments for inputs present in
      // the solved cone.
      if (!variables.hasSymbol(problem.inputSymbols[i])) {
        continue;
      }
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
  std::vector<KInductionResult::SignalMismatch> mismatches;
  for (size_t i = 0; i < problem.observedOutputExprs0.size(); ++i) {
    std::unordered_map<size_t, bool> environment;
    addFormulaValuesToEnvironment(
        solver, variables, problem.observedOutputExprs0[i], frame, environment);
    addFormulaValuesToEnvironment(
        solver, variables, problem.observedOutputExprs1[i], frame, environment);
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

namespace {

std::optional<KInductionResult::CounterexampleWitness> findBaseCounterexampleImpl(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    size_t k,
    std::optional<size_t> exactPublicBadFrame) {
  const size_t bootstrapFrames = resetBootstrapFrames(problem);
  const size_t internalK = k + bootstrapFrames;
  const bool constrainPreviouslySafeFrames = exactPublicBadFrame.has_value();
  const InitialConstraintMode initialMode =
      bootstrapFrames == 0 ? determineInitialConstraintMode(problem)
                           : InitialConstraintMode::None;

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

  size_t lastBadFrame = internalK;
  if (exactPublicBadFrame.has_value()) {
    const size_t exactInternalBadFrame = *exactPublicBadFrame + bootstrapFrames;
    if (exactInternalBadFrame < firstBadFrame ||
        exactInternalBadFrame > internalK) {
      return std::nullopt;
    }
    firstBadFrame = exactInternalBadFrame;
    lastBadFrame = exactInternalBadFrame;
  }

  const BaseCaseCoi coi = buildBaseCaseCoi(
      problem,
      initialMode,
      bootstrapFrames,
      firstBadFrame,
      internalK,
      constrainPreviouslySafeFrames);
  emitBaseCaseCoiDiag(
      problem,
      coi,
      k,
      firstBadFrame,
      internalK,
      constrainPreviouslySafeFrames);
  const TransitionExprResolver transitionByState(problem);
  const FrameSymbolAliases aliasesByFrame = buildBaseCaseFrameAliases(
      problem, coi, internalK + 1, bootstrapFrames);

  SATSolverWrapper solver(solverType);
  solver.configureForSecConeProof(coi.solverSymbols.size());
  FrameVariableStore variables(
      solver, coi.solverSymbols, internalK + 1, aliasesByFrame);
  addResetBootstrapConstraints(solver, variables, problem, internalK + 1);
  addInitialConstraints(solver, variables, problem, coi.solverSymbolSet, initialMode);

  addComplementedStateRelations(
      solver, variables, problem.complementedStatePairs0, coi.solverSymbolSet,
      internalK + 1);
  addComplementedStateRelations(
      solver, variables, problem.complementedStatePairs1, coi.solverSymbolSet,
      internalK + 1);
  addInitialStateEqualities(solver, variables, problem, coi.solverSymbolSet);

  for (size_t frame = 0; frame < internalK; ++frame) {
    addTransitionRelation(
        solver, variables, transitionByState, coi.transitionTargetsByFrame[frame], frame);
  }
  if (bootstrapFrames != 0) {
    addBootstrapStateAssignments(
        solver, variables, problem, coi.solverSymbolSet, bootstrapFrames);
    addBootstrapStateEqualities(
        solver, variables, problem, coi.solverSymbolSet, bootstrapFrames);
  }

  if (constrainPreviouslySafeFrames) {
    for (size_t frame = bootstrapFrames; frame < firstBadFrame; ++frame) {
      FrameFormulaEncoder encoder(
          solver,
          variables.makeLeafLits(
              frame,
              formulaSupportOrThrow(
                  problem.property, "previously-safe property formula")));
      solver.addClause({encoder.encode(problem.property)});
    }
  }

  std::vector<int> badClause;
  badClause.reserve(lastBadFrame - firstBadFrame + 1);
  for (size_t frame = firstBadFrame; frame <= lastBadFrame; ++frame) {
    FrameFormulaEncoder encoder(
        solver,
        variables.makeLeafLits(
            frame, formulaSupportOrThrow(problem.bad, "bad-state formula")));
    badClause.push_back(encoder.encode(problem.bad));
  }
  solver.addClause(badClause);

  if (!solver.solve()) {
    return std::nullopt;
  }
  return buildCounterexampleWitness(
      solver, variables, problem, firstBadFrame, lastBadFrame, bootstrapFrames);
}

}  // namespace

std::optional<KInductionResult::CounterexampleWitness> findBaseCounterexample(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    size_t k) {
  return findBaseCounterexampleImpl(problem, solverType, k, std::nullopt);
}

std::optional<KInductionResult::CounterexampleWitness>
findBaseCounterexampleAtFrontier(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    size_t k) {
  return findBaseCounterexampleImpl(problem, solverType, k, k);
}

}  // namespace KEPLER_FORMAL::SEC
