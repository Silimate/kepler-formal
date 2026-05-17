// Copyright 2024-2026 keplertech.io
// SPDX-License-Identifier: GPL-3.0-only

#include "kinduction/BaseCaseSolver.h"

#include <algorithm>
#include <cstdlib>
#include <memory>
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

// BlackParrot PDR sampling showed the reset-frontier precheck repeatedly
// cycling through many neighboring cube supports in the same blocking wave.
// A tiny cache cleared in the middle of that wave and forced full COI/solver
// reconstruction; keep enough exact assumption solvers to cover the measured
// working set without making the cache effectively unbounded.
constexpr size_t kMaxResetFrontierCachedSolvers = 64;
constexpr size_t kMinResetFrontierCoreChecks = 64;
constexpr size_t kMaxResetFrontierCachedCoresPerFrame = 4096;

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

struct CachedResetFrontierSolver {
  BaseCaseCoi coi;
  std::unique_ptr<SATSolverWrapper> solver;
  std::unique_ptr<FrameVariableStore> variables;
  KEPLER_FORMAL::Config::SolverType solverType =
      KEPLER_FORMAL::Config::SolverType::KISSAT;
  size_t targetFrame = 0;
  bool cubeEncodedAsUnitClauses = false;
};

std::unordered_map<size_t, size_t> buildPrimaryByComplementSymbol(
    const KInductionProblem& problem);

struct EqualityIndex {
  std::unordered_map<size_t, std::vector<size_t>> partnersBySymbol;

  explicit EqualityIndex(
      const std::vector<std::pair<size_t, size_t>>& equalityPairs) {
    partnersBySymbol.reserve(equalityPairs.size() * 2);
    for (const auto& [lhsSymbol, rhsSymbol] : equalityPairs) {
      partnersBySymbol[lhsSymbol].push_back(rhsSymbol);
      partnersBySymbol[rhsSymbol].push_back(lhsSymbol);
    }
  }

  void close(std::unordered_set<size_t>& symbols) const {
    // Equality closure is queried repeatedly for very small PDR reset cubes.
    // Walking only the adjacency of already-relevant symbols avoids rescanning
    // the full ASIC equality table until the fixed point stops changing.
    std::vector<size_t> worklist(symbols.begin(), symbols.end());
    for (size_t index = 0; index < worklist.size(); ++index) {
      const auto partnersIt = partnersBySymbol.find(worklist[index]);
      if (partnersIt == partnersBySymbol.end()) {
        continue;
      }
      for (const auto partner : partnersIt->second) {
        if (symbols.insert(partner).second) {
          worklist.push_back(partner);
        }
      }
    }
  }

  std::vector<std::pair<size_t, size_t>> pairsWithin(
      const std::unordered_set<size_t>& symbols) const {
    std::vector<std::pair<size_t, size_t>> pairs;
    for (const auto lhsSymbol : symbols) {
      const auto partnersIt = partnersBySymbol.find(lhsSymbol);
      if (partnersIt == partnersBySymbol.end()) {
        continue;
      }
      for (const auto rhsSymbol : partnersIt->second) {
        if (lhsSymbol < rhsSymbol &&
            symbols.find(rhsSymbol) != symbols.end()) {
          pairs.emplace_back(lhsSymbol, rhsSymbol);
        }
      }
    }
    return pairs;
  }
};

struct ResetFrontierReachabilityContextData {
  ResetFrontierReachabilityContextData(
      const KInductionProblem& problem,
      const TransitionExprResolver& transitionByState)
      : problem(problem),
        transitionByState(transitionByState),
        bootstrapFrames(resetBootstrapFrames(problem)),
        initialMode(bootstrapFrames == 0 ? determineInitialConstraintMode(problem)
                                         : InitialConstraintMode::None),
        primaryByComplement(buildPrimaryByComplementSymbol(problem)),
        initialEqualities(problem.initialStateEqualityPairs),
        bootstrapEqualities(problem.bootstrapStateEqualityPairs) {}

  const KInductionProblem& problem;
  const TransitionExprResolver& transitionByState;
  size_t bootstrapFrames = 0;
  InitialConstraintMode initialMode = InitialConstraintMode::None;
  std::unordered_map<size_t, size_t> primaryByComplement;
  EqualityIndex initialEqualities;
  EqualityIndex bootstrapEqualities;
  // PDR asks many concrete reachability questions for the same small set of
  // state symbols while refining projected counterexamples. Cache the unrolled
  // reset/bootstrap solver by frame and cube support, and vary only the cube
  // values through SAT assumptions.
  mutable std::unordered_map<std::string, std::unique_ptr<CachedResetFrontierSolver>>
      cachedSolvers;
  // Exact reset-frontier UNSAT cores are reusable across neighboring cubes:
  // once core C is proven unreachable, every later cube containing C is also
  // unreachable. BlackParrot PDR sampling showed thousands of repeated
  // assumption solves for such neighboring cubes, so keep a small per-frame
  // cache of minimized unreachable cores before asking SAT again.
  mutable std::unordered_map<
      size_t,
      std::vector<std::vector<std::pair<size_t, bool>>>>
      unreachableCoresByTargetFrame;
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

void addTransitionStateSupport(
    const TransitionExprResolver& transitionByState,
    size_t stateSymbol,
    const std::unordered_set<size_t>& stateSymbols,
    std::unordered_set<size_t>& output) {
  // TransitionExprResolver already caches each next-state cone support.  The
  // reset-frontier checks used by PDR can issue many tiny COI queries, so
  // reusing this cache avoids repeatedly walking and allocating support sets
  // for the same ASIC-size transition formula.
  for (const auto symbol : transitionByState.support(stateSymbol)) {
    if (stateSymbols.find(symbol) != stateSymbols.end()) {
      output.insert(symbol);
    }
  }
}

void addTransitionSupport(
    const TransitionExprResolver& transitionByState,
    size_t stateSymbol,
    std::unordered_set<size_t>& output) {
  for (const auto symbol : transitionByState.support(stateSymbol)) {
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

FrameSymbolAliases buildResetFrontierFrameAliases(
    const ResetFrontierReachabilityContextData& context,
    const BaseCaseCoi& coi,
    size_t numFrames) {
  // Reset-frontier CEGAR checks are tiny but very frequent. Use the cached
  // equality indexes to emit only aliases reachable from this cube's COI
  // instead of scanning all state-equality pairs every time.
  FrameSymbolAliases aliasesByFrame(numFrames);
  if (!aliasesByFrame.empty()) {
    aliasesByFrame[0] =
        context.initialEqualities.pairsWithin(coi.solverSymbolSet);
  }
  if (context.bootstrapFrames != 0 &&
      context.bootstrapFrames < numFrames) {
    aliasesByFrame[context.bootstrapFrames] =
        context.bootstrapEqualities.pairsWithin(coi.solverSymbolSet);
  }
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
      addTransitionStateSupport(
          transitionByState, target, stateSymbols, requiredStates[frame - 1]);
    }
  }

  closeFrameEqualityDependencies(problem.initialStateEqualityPairs, requiredStates[0]);

  for (const auto& frameStates : requiredStates) {
    solverSymbols.insert(frameStates.begin(), frameStates.end());
  }
  for (const auto& targets : transitionTargetsByFrame) {
    for (const auto target : targets) {
      solverSymbols.insert(target);
      addTransitionSupport(transitionByState, target, solverSymbols);
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

BaseCaseCoi buildStateCubeReachabilityCoi(
    const ResetFrontierReachabilityContextData& context,
    size_t targetFrame,
    const std::vector<std::pair<size_t, bool>>& cube) {
  // This is the same bounded transition prefix as the normal base case, but
  // the target is a state cube rather than the SEC bad formula.  PDR calls this
  // when a level-0 obligation may be an artifact of the abstract bootstrap
  // summary: the SAT query must be exact, but only for the cube's COI.
  const auto& problem = context.problem;
  const auto& transitionByState = context.transitionByState;
  const auto& stateSymbols = transitionByState.stateSymbols();
  std::vector<std::unordered_set<size_t>> requiredStates(targetFrame + 1);
  std::unordered_set<size_t> solverSymbols;
  solverSymbols.reserve(1024);
  for (const auto& [symbol, _] : problem.resetBootstrapInputs) {
    solverSymbols.insert(symbol);
  }
  for (const auto& [symbol, _] : cube) {
    solverSymbols.insert(symbol);
    if (stateSymbols.find(symbol) != stateSymbols.end()) {
      requiredStates[targetFrame].insert(symbol);
    }
  }

  if (context.bootstrapFrames == 0 &&
      (context.initialMode == InitialConstraintMode::CompleteInit ||
       context.initialMode == InitialConstraintMode::PartialInit) &&
      !hasStructuredInitialAssignments(problem)) {
    addFormulaSupport(problem.initialCondition, solverSymbols);
    addFormulaStateSupport(
        problem.initialCondition, stateSymbols, requiredStates[0]);
  }

  std::vector<std::vector<size_t>> transitionTargetsByFrame(targetFrame);
  for (size_t frame = targetFrame; frame > 0; --frame) {
    if (context.bootstrapFrames != 0 && frame == context.bootstrapFrames) {
      context.bootstrapEqualities.close(requiredStates[frame]);
    }
    auto targets = expandTransitionTargets(
        requiredStates[frame],
        transitionByState,
        context.primaryByComplement);
    transitionTargetsByFrame[frame - 1] = targets;
    for (const auto target : targets) {
      addTransitionStateSupport(
          transitionByState, target, stateSymbols, requiredStates[frame - 1]);
    }
  }

  context.initialEqualities.close(requiredStates[0]);

  for (const auto& frameStates : requiredStates) {
    solverSymbols.insert(frameStates.begin(), frameStates.end());
  }
  for (const auto& targets : transitionTargetsByFrame) {
    for (const auto target : targets) {
      solverSymbols.insert(target);
      addTransitionSupport(transitionByState, target, solverSymbols);
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

void addBootstrapStateEqualities(
    SATSolverWrapper& solver,
    const FrameVariableStore& variables,
    const ResetFrontierReachabilityContextData& context,
    const std::unordered_set<size_t>& solverSymbols,
    size_t frame) {
  for (const auto& [lhsSymbol, rhsSymbol] :
       context.bootstrapEqualities.pairsWithin(solverSymbols)) {
    const int lhs = variables.getLiteral(lhsSymbol, frame);
    const int rhs = variables.getLiteral(rhsSymbol, frame);
    if (lhs == rhs) {
      continue;
    }
    addLiteralEquivalence(solver, lhs, rhs);
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

void addInitialStateEqualities(
    SATSolverWrapper& solver,
    const FrameVariableStore& variables,
    const ResetFrontierReachabilityContextData& context,
    const std::unordered_set<size_t>& solverSymbols) {
  for (const auto& [lhsSymbol, rhsSymbol] :
       context.initialEqualities.pairsWithin(solverSymbols)) {
    const int lhs = variables.getLiteral(lhsSymbol, 0);
    const int rhs = variables.getLiteral(rhsSymbol, 0);
    if (lhs == rhs) {
      continue;
    }
    addLiteralEquivalence(solver, lhs, rhs);
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

void addStateCubeAssumptions(SATSolverWrapper& solver,
                             const FrameVariableStore& variables,
                             const std::vector<std::pair<size_t, bool>>& cube,
                             size_t frame) {
  for (const auto& [symbol, value] : cube) {
    solver.addClause({value ? variables.getLiteral(symbol, frame)
                            : -variables.getLiteral(symbol, frame)});
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

struct ResetFrontierReachabilityContext {
  explicit ResetFrontierReachabilityContext(
      std::shared_ptr<ResetFrontierReachabilityContextData> data)
      : data(std::move(data)) {}

  std::shared_ptr<ResetFrontierReachabilityContextData> data;
};

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

bool isStateCubeReachableAtResetFrontier(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    const std::vector<std::pair<size_t, bool>>& cube,
    size_t postBootstrapSteps) {
  const TransitionExprResolver transitionByState(problem);
  return isStateCubeReachableAtResetFrontier(
      problem, solverType, transitionByState, cube, postBootstrapSteps);
}

bool isStateCubeReachableAtResetFrontier(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    const TransitionExprResolver& transitionByState,
    const std::vector<std::pair<size_t, bool>>& cube,
    size_t postBootstrapSteps) {
  const auto context =
      makeResetFrontierReachabilityContext(problem, transitionByState);
  return isStateCubeReachableAtResetFrontier(
      *context, solverType, cube, postBootstrapSteps);
}

std::shared_ptr<ResetFrontierReachabilityContext>
makeResetFrontierReachabilityContext(
    const KInductionProblem& problem,
    const TransitionExprResolver& transitionByState) {
  return std::make_shared<ResetFrontierReachabilityContext>(
      std::make_shared<ResetFrontierReachabilityContextData>(
          problem, transitionByState));
}

std::vector<size_t> sortedCubeSymbols(
    const std::vector<std::pair<size_t, bool>>& cube) {
  std::vector<size_t> symbols;
  symbols.reserve(cube.size());
  for (const auto& [symbol, value] : cube) {
    (void)value;
    symbols.push_back(symbol);
  }
  std::sort(symbols.begin(), symbols.end());
  symbols.erase(std::unique(symbols.begin(), symbols.end()), symbols.end());
  return symbols;
}

std::vector<std::pair<size_t, bool>> sortedCubeLiterals(
    std::vector<std::pair<size_t, bool>> cube) {
  std::sort(cube.begin(), cube.end());
  cube.erase(std::unique(cube.begin(), cube.end()), cube.end());
  return cube;
}

std::string resetFrontierSolverCacheKey(
    KEPLER_FORMAL::Config::SolverType solverType,
    size_t targetFrame,
    const std::vector<std::pair<size_t, bool>>& cube,
    bool includeCubeValues) {
  std::string key = std::to_string(static_cast<int>(solverType));
  key.push_back('|');
  key.append(std::to_string(targetFrame));
  if (includeCubeValues) {
    for (const auto& [symbol, value] : sortedCubeLiterals(cube)) {
      key.push_back('|');
      key.append(std::to_string(symbol));
      key.push_back('=');
      key.push_back(value ? '1' : '0');
    }
  } else {
    for (const auto symbol : sortedCubeSymbols(cube)) {
      key.push_back('|');
      key.append(std::to_string(symbol));
    }
  }
  return key;
}

std::vector<int> stateCubeAssumptionLits(
    const FrameVariableStore& variables,
    const std::vector<std::pair<size_t, bool>>& cube,
    size_t frame) {
  std::vector<int> assumptions;
  assumptions.reserve(cube.size());
  for (const auto& [symbol, value] : cube) {
    const int literal = variables.getLiteral(symbol, frame);
    assumptions.push_back(value ? literal : -literal);
  }
  return assumptions;
}

bool solverContainsCubeSymbols(const CachedResetFrontierSolver& cached,
                               const std::vector<size_t>& cubeSymbols) {
  return std::all_of(
      cubeSymbols.begin(),
      cubeSymbols.end(),
      [&](const auto symbol) {
        return cached.coi.solverSymbolSet.find(symbol) !=
               cached.coi.solverSymbolSet.end();
      });
}

std::vector<std::pair<size_t, bool>> normalizedAssignmentCube(
    std::vector<std::pair<size_t, bool>> cube) {
  std::sort(cube.begin(), cube.end());
  cube.erase(std::unique(cube.begin(), cube.end()), cube.end());
  return cube;
}

std::optional<std::vector<std::pair<size_t, bool>>>
failedAssumptionCoreFromLastResetFrontierSolve(
    CachedResetFrontierSolver& cached,
    const std::vector<std::pair<size_t, bool>>& cube,
    size_t targetFrame) {
  if (cached.cubeEncodedAsUnitClauses) {
    return std::nullopt;
  }

  std::unordered_map<int, std::pair<size_t, bool>> cubeLiteralByAssumption;
  cubeLiteralByAssumption.reserve(cube.size());
  for (const auto& [symbol, value] : cube) {
    const int literal = cached.variables->getLiteral(symbol, targetFrame);
    cubeLiteralByAssumption.emplace(
        value ? literal : -literal, std::pair{symbol, value});
  }

  std::vector<std::pair<size_t, bool>> core;
  for (const int failedAssumption : cached.solver->failedAssumptions()) {
    const auto it = cubeLiteralByAssumption.find(failedAssumption);
    if (it != cubeLiteralByAssumption.end()) {
      core.push_back(it->second);
    }
  }
  if (core.empty()) {
    return std::nullopt;
  }
  return normalizedAssignmentCube(std::move(core));
}

bool assignmentCubeContains(
    const std::vector<std::pair<size_t, bool>>& cube,
    const std::vector<std::pair<size_t, bool>>& core) {
  return std::includes(cube.begin(), cube.end(), core.begin(), core.end());
}

std::optional<std::vector<std::pair<size_t, bool>>>
findCachedResetFrontierUnreachableCore(
    const ResetFrontierReachabilityContextData& data,
    size_t targetFrame,
    const std::vector<std::pair<size_t, bool>>& cube) {
  const auto frameIt = data.unreachableCoresByTargetFrame.find(targetFrame);
  if (frameIt == data.unreachableCoresByTargetFrame.end()) {
    return std::nullopt;
  }
  for (const auto& core : frameIt->second) {
    if (assignmentCubeContains(cube, core)) {
      return core;
    }
  }
  return std::nullopt;
}

void rememberResetFrontierUnreachableCore(
    const ResetFrontierReachabilityContextData& data,
    size_t targetFrame,
    std::vector<std::pair<size_t, bool>> core) {
  core = normalizedAssignmentCube(std::move(core));
  if (core.empty()) {
    return;
  }

  auto& cores = data.unreachableCoresByTargetFrame[targetFrame];
  for (const auto& existing : cores) {
    if (assignmentCubeContains(core, existing)) {
      return;
    }
  }
  cores.erase(
      std::remove_if(
          cores.begin(),
          cores.end(),
          [&](const auto& existing) {
            return assignmentCubeContains(existing, core);
          }),
      cores.end());
  if (cores.size() >= kMaxResetFrontierCachedCoresPerFrame) {
    cores.erase(cores.begin());
  }
  cores.push_back(std::move(core));
}

std::optional<std::vector<std::pair<size_t, bool>>>
extractUnreachableCoreFromCachedResetFrontierSolver(
    CachedResetFrontierSolver& cached,
    const std::vector<std::pair<size_t, bool>>& cube,
    size_t targetFrame) {
  if (cached.cubeEncodedAsUnitClauses) {
    return cached.solver->solve() ? std::nullopt : std::optional{cube};
  }

  std::vector<int> assumptions;
  assumptions.reserve(cube.size());
  std::unordered_map<int, std::pair<size_t, bool>> cubeLiteralByAssumption;
  cubeLiteralByAssumption.reserve(cube.size());
  for (const auto& [symbol, value] : cube) {
    const int literal = cached.variables->getLiteral(symbol, targetFrame);
    const int assumption = value ? literal : -literal;
    assumptions.push_back(assumption);
    cubeLiteralByAssumption.emplace(assumption, std::pair{symbol, value});
  }

  if (cached.solver->solveWithAssumptions(assumptions)) {
    return std::nullopt;
  }

  std::vector<std::pair<size_t, bool>> core;
  for (const int failedAssumption : cached.solver->failedAssumptions()) {
    const auto it = cubeLiteralByAssumption.find(failedAssumption);
    if (it != cubeLiteralByAssumption.end()) {
      core.push_back(it->second);
    }
  }
  if (core.empty()) {
    // Some solver backends / conflict shapes do not expose a mapped failed
    // assumption core. Start from the full cube and still run exact deletion
    // minimization below; every accepted drop is checked by SAT.
    core = cube;
  }
  core = normalizedAssignmentCube(std::move(core));
  auto coreIsReachable =
      [&](const std::vector<std::pair<size_t, bool>>& candidate) {
        return cached.solver->solveWithAssumptions(
            stateCubeAssumptionLits(*cached.variables, candidate, targetFrame));
      };

  // Glucose reports a valid conflict subset, not a guaranteed-minimal one.
  // Minimize it exactly with the same cached reset-frontier solver; the result
  // becomes a stronger PDR F[0] refinement and a reusable cache entry for later
  // neighboring cubes.
  size_t checks = 0;
  const size_t maxChecks =
      std::max(kMinResetFrontierCoreChecks, core.size() * 2);
  for (size_t chunkSize = std::max<size_t>(1, core.size() / 2);
       chunkSize > 0 && checks < maxChecks;) {
    for (size_t index = 0; index < core.size() && checks < maxChecks;) {
      const size_t erasedCount = std::min(chunkSize, core.size() - index);
      if (erasedCount == 0 || erasedCount == core.size()) {
        break;
      }
      std::vector<std::pair<size_t, bool>> reduced = core;
      reduced.erase(
          reduced.begin() + static_cast<std::ptrdiff_t>(index),
          reduced.begin() +
              static_cast<std::ptrdiff_t>(index + erasedCount));
      ++checks;
      if (!coreIsReachable(reduced)) {
        core = std::move(reduced);
        continue;
      }
      index += erasedCount;
    }
    if (chunkSize == 1) {
      break;
    }
    chunkSize = std::max<size_t>(1, chunkSize / 2);
  }
  return core;
}

std::unique_ptr<CachedResetFrontierSolver> buildResetFrontierSolver(
    const ResetFrontierReachabilityContextData& data,
    KEPLER_FORMAL::Config::SolverType solverType,
    const std::vector<std::pair<size_t, bool>>& cube,
    size_t targetFrame,
    bool encodeCubeAsUnitClauses) {
  auto cached = std::make_unique<CachedResetFrontierSolver>();
  cached->solverType = solverType;
  cached->targetFrame = targetFrame;
  cached->coi = buildStateCubeReachabilityCoi(data, targetFrame, cube);
  const FrameSymbolAliases aliasesByFrame =
      buildResetFrontierFrameAliases(data, cached->coi, targetFrame + 1);

  const auto& problem = data.problem;
  cached->solver = std::make_unique<SATSolverWrapper>(solverType);
  cached->solver->configureForSecPdrQuery(cached->coi.solverSymbols.size());
  cached->variables = std::make_unique<FrameVariableStore>(
      *cached->solver,
      cached->coi.solverSymbols,
      targetFrame + 1,
      aliasesByFrame);
  addResetBootstrapConstraints(
      *cached->solver, *cached->variables, problem, targetFrame + 1);
  addInitialConstraints(
      *cached->solver,
      *cached->variables,
      problem,
      cached->coi.solverSymbolSet,
      data.initialMode);
  addComplementedStateRelations(
      *cached->solver,
      *cached->variables,
      problem.complementedStatePairs0,
      cached->coi.solverSymbolSet,
      targetFrame + 1);
  addComplementedStateRelations(
      *cached->solver,
      *cached->variables,
      problem.complementedStatePairs1,
      cached->coi.solverSymbolSet,
      targetFrame + 1);
  addInitialStateEqualities(
      *cached->solver, *cached->variables, data, cached->coi.solverSymbolSet);

  for (size_t frame = 0; frame < targetFrame; ++frame) {
    addTransitionRelation(
        *cached->solver,
        *cached->variables,
        data.transitionByState,
        cached->coi.transitionTargetsByFrame[frame],
        frame);
  }
  if (data.bootstrapFrames != 0) {
    addBootstrapStateAssignments(
        *cached->solver,
        *cached->variables,
        problem,
        cached->coi.solverSymbolSet,
        data.bootstrapFrames);
    addBootstrapStateEqualities(
        *cached->solver,
        *cached->variables,
        data,
        cached->coi.solverSymbolSet,
        data.bootstrapFrames);
  }

  cached->cubeEncodedAsUnitClauses = encodeCubeAsUnitClauses;
  if (cached->cubeEncodedAsUnitClauses) {
    for (const auto& [symbol, value] : cube) {
      const int literal = cached->variables->getLiteral(symbol, targetFrame);
      cached->solver->addClause({value ? literal : -literal});
    }
  }
  return cached;
}

CachedResetFrontierSolver& getCachedResetFrontierSolver(
    const ResetFrontierReachabilityContextData& data,
    KEPLER_FORMAL::Config::SolverType solverType,
    const std::vector<std::pair<size_t, bool>>& cube,
    size_t targetFrame) {
  (void)solverType;
  // Reset-frontier checks are dominated by repeated neighboring cube queries.
  // Use the assumption-capable solver here even when the main SEC run selected
  // Kissat: otherwise every cube value has to be encoded as unit clauses in a
  // separate cached solver, which BlackParrot sampling showed growing to
  // multi-GB retained solver caches before PDR made progress.
  const bool encodeCubeAsUnitClauses = false;
  const auto cachedSolverType = KEPLER_FORMAL::Config::SolverType::GLUCOSE;
  const std::string key =
      resetFrontierSolverCacheKey(
          cachedSolverType, targetFrame, cube, encodeCubeAsUnitClauses);
  if (const auto it = data.cachedSolvers.find(key);
      it != data.cachedSolvers.end()) {
    return *it->second;
  }

  const auto cubeSymbols = sortedCubeSymbols(cube);
  for (const auto& [_, cached] : data.cachedSolvers) {
    if (cached->solverType == cachedSolverType &&
        cached->targetFrame == targetFrame &&
        cached->cubeEncodedAsUnitClauses == encodeCubeAsUnitClauses &&
        solverContainsCubeSymbols(*cached, cubeSymbols)) {
      // A solver built for a wider reset-frontier COI is still an exact query
      // for a smaller cube: the extra transition / init clauses constrain
      // unrelated existential variables, while the requested cube values are
      // supplied as assumptions.
      if (isKInductionCoiDiagEnabled()) {
        emitSecDiag(
            "SEC diag: reset frontier solver superset cache hit ",
            "target_frame=",
            targetFrame,
            " cube_literals=",
            cube.size(),
            " solver_symbols=",
            cached->coi.solverSymbols.size());
      }
      return *cached;
    }
  }

  if (data.cachedSolvers.size() >= kMaxResetFrontierCachedSolvers) {
    data.cachedSolvers.clear();
  }

  auto cached = buildResetFrontierSolver(
      data, cachedSolverType, cube, targetFrame, encodeCubeAsUnitClauses);
  auto [it, inserted] = data.cachedSolvers.emplace(key, std::move(cached));
  (void)inserted;
  return *it->second;
}

bool isStateCubeReachableAtResetFrontier(
    const ResetFrontierReachabilityContext& context,
    KEPLER_FORMAL::Config::SolverType solverType,
    const std::vector<std::pair<size_t, bool>>& cube,
    size_t postBootstrapSteps) {
  if (cube.empty()) {
    return true;
  }

  const auto& data = *context.data;
  const size_t targetFrame = data.bootstrapFrames + postBootstrapSteps;
  const auto normalizedCube = normalizedAssignmentCube(cube);
  if (const auto cachedCore =
          findCachedResetFrontierUnreachableCore(data, targetFrame, normalizedCube);
      cachedCore.has_value()) {
    if (isKInductionCoiDiagEnabled()) {
      emitSecDiag(
          "SEC diag: reset frontier cached unreachable core hit ",
          "post_bootstrap_steps=",
          postBootstrapSteps,
          " core_literals=",
          cachedCore->size(),
          " cube_literals=",
          normalizedCube.size());
    }
    return false;
  }
  CachedResetFrontierSolver& cached =
      getCachedResetFrontierSolver(data, solverType, normalizedCube, targetFrame);

  if (isKInductionCoiDiagEnabled()) {
    emitSecDiag(
        "SEC diag: reset frontier cube coi post_bootstrap_steps=",
        postBootstrapSteps,
        " frames=",
        targetFrame + 1,
        " solver_symbols=",
        cached.coi.solverSymbols.size(),
        " transition_targets=",
        countTransitionTargets(cached.coi.transitionTargetsByFrame),
        " cube_literals=",
        normalizedCube.size());
  }

  const bool reachable =
      cached.cubeEncodedAsUnitClauses
          ? cached.solver->solve()
          : cached.solver->solveWithAssumptions(
                stateCubeAssumptionLits(
                    *cached.variables, normalizedCube, targetFrame));
  if (!reachable) {
    if (postBootstrapSteps == 0) {
      if (const auto core = extractUnreachableCoreFromCachedResetFrontierSolver(
              cached, normalizedCube, targetFrame);
          core.has_value()) {
        rememberResetFrontierUnreachableCore(data, targetFrame, *core);
      } else {
        rememberResetFrontierUnreachableCore(
            data, targetFrame, normalizedCube);
      }
    } else if (const auto core =
                   failedAssumptionCoreFromLastResetFrontierSolve(
                       cached, normalizedCube, targetFrame);
               core.has_value()) {
      // Post-bootstrap prechecks are on the hot PDR path.  Reuse the
      // assumption core already produced by this UNSAT query, but avoid the
      // extra minimization SAT calls reserved for the exact reset frontier.
      rememberResetFrontierUnreachableCore(data, targetFrame, *core);
    }
  }
  return reachable;
}

bool isStateCubeReachableAtResetFrontierOneShot(
    const ResetFrontierReachabilityContext& context,
    KEPLER_FORMAL::Config::SolverType solverType,
    const std::vector<std::pair<size_t, bool>>& cube,
    size_t postBootstrapSteps) {
  if (cube.empty()) {
    return true;
  }

  const auto& data = *context.data;
  const size_t targetFrame = data.bootstrapFrames + postBootstrapSteps;
  const auto normalizedCube = normalizedAssignmentCube(cube);
  if (findCachedResetFrontierUnreachableCore(
          data, targetFrame, normalizedCube)
          .has_value()) {
    return false;
  }
  auto solver = buildResetFrontierSolver(
      data,
      solverType,
      normalizedCube,
      targetFrame,
      /*encodeCubeAsUnitClauses=*/true);

  if (isKInductionCoiDiagEnabled()) {
    emitSecDiag(
        "SEC diag: reset frontier one-shot cube coi post_bootstrap_steps=",
        postBootstrapSteps,
        " frames=",
        targetFrame + 1,
        " solver_symbols=",
        solver->coi.solverSymbols.size(),
        " transition_targets=",
        countTransitionTargets(solver->coi.transitionTargetsByFrame),
        " cube_literals=",
        normalizedCube.size());
  }

  const bool reachable = solver->solver->solve();
  if (!reachable && postBootstrapSteps == 0) {
    rememberResetFrontierUnreachableCore(data, targetFrame, normalizedCube);
  }
  return reachable;
}

std::optional<std::vector<std::pair<size_t, bool>>>
findResetFrontierUnreachableCubeCore(
    const ResetFrontierReachabilityContext& context,
    KEPLER_FORMAL::Config::SolverType solverType,
    const std::vector<std::pair<size_t, bool>>& cube,
    size_t postBootstrapSteps) {
  if (cube.empty()) {
    return std::nullopt;
  }

  const auto& data = *context.data;
  const size_t targetFrame = data.bootstrapFrames + postBootstrapSteps;
  const auto normalizedCube = normalizedAssignmentCube(cube);
  if (const auto cachedCore =
          findCachedResetFrontierUnreachableCore(data, targetFrame, normalizedCube);
      cachedCore.has_value()) {
    return cachedCore;
  }
  CachedResetFrontierSolver& cached =
      getCachedResetFrontierSolver(data, solverType, normalizedCube, targetFrame);
  const auto core = extractUnreachableCoreFromCachedResetFrontierSolver(
      cached, normalizedCube, targetFrame);
  if (core.has_value()) {
    rememberResetFrontierUnreachableCore(data, targetFrame, *core);
  }
  return core;
}

}  // namespace KEPLER_FORMAL::SEC
