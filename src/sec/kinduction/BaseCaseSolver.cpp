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
constexpr size_t kMaxPreviousResetFrontierBlockersPerQuery = 64;
// The relaxed post-bootstrap query is only a shortcut before the exact
// reset-frontier solver. Sampling AES PDR showed this shortcut can become the
// wall when it fails to shrink the COI, so keep it local and resource-bounded.
constexpr size_t kMaxRelaxedResetFrontierPrecheckSymbols = 256;
constexpr size_t kMaxRelaxedResetFrontierPrecheckTransitionTargets = 128;
constexpr unsigned kRelaxedResetFrontierPrecheckConflictLimit = 10000;
// BlackParrot PDR samples showed the full reset-frontier fallback exploding to
// hundreds of thousands of symbols while the reset-summary query stayed much
// smaller (about 90k symbols / 88k transition targets at the slow frontier).
// Let that exact UNSAT precheck run before opening the full prefix.
constexpr size_t kMaxResetSummaryPrecheckSymbols = 200000;
constexpr size_t kMaxResetSummaryPrecheckTransitionTargets = 200000;
// This summary query is the cheap alternative to the full reset-frontier
// fallback. BlackParrot PDR samples showed 65k-symbol summary proofs giving up
// after the old tiny cap, then falling into 600k+ symbol exact assumption
// assumption solves. Spend the bounded effort here where the COI is smaller.
constexpr unsigned kResetSummaryPrecheckConflictLimit = 5000;
constexpr unsigned kResetSummaryFrontierProofConflictLimit = 2000;
constexpr unsigned kResetSummarySingletonProofConflictLimit = 1000;
constexpr long long kResetFrontierCachedAssumptionConflictLimit = 10000;
constexpr long long kResetFrontierBatchProofPropagationLimit = 250000;
constexpr size_t kMaxResetSummaryFrontierBlockers = 256;
constexpr size_t kMaxResetSummaryRefinements = 4;
constexpr size_t kMaxResetSummaryFrontierCubeLiterals = 100000;
constexpr size_t kMaxResetSummaryFrontierProofCubeLiterals = 8192;
constexpr size_t kMaxResetSummaryFrontierProofSymbols = 20000;
constexpr size_t kMaxResetSummaryFrontierProofTransitionTargets = 20000;
constexpr size_t kMaxResetSummaryBulkSingletonBlockers = 128;
constexpr size_t kMaxResetSummaryCachedCois = 64;
// PDR often proves all but one concrete reset frame through cheap cached cores
// before asking the exact bounded fallback. In that sparse case a prefix query
// that targets every frame widens the COI unnecessarily; use exact per-step
// solvers while only a couple of frames remain.
constexpr size_t kMaxSparseResetFrontierPerStepChecks = 2;
// Transition node counts are only reserve hints for FrameFormulaEncoder.
// BlackParrot reset-frontier sampling showed exact counting across ~86k
// transition targets dominating the whole query before any CNF was emitted.
// Keep exact hints for local cones and skip the prepass for ASIC-sized groups;
// the encoder still grows its cache geometrically while emitting the same CNF.
constexpr size_t kMaxExactTransitionNodeCountHintTargets = 512;

bool resetFrontierAssumptionSolvesDisabled() {
  return std::getenv("KEPLER_SEC_PDR_DISABLE_RESET_FRONTIER_ASSUMPTIONS") !=
         nullptr;
}

SATSolverWrapper::SolveStatus solveResetFrontierUnitClauseQuery(
    SATSolverWrapper& solver,
    KEPLER_FORMAL::Config::SolverType solverType,
    int64_t conflictLimit) {
  if (solverType == KEPLER_FORMAL::Config::SolverType::KISSAT &&
      conflictLimit >= 0) {
    return solver.solveWithKissatResourceLimits(
        static_cast<unsigned>(conflictLimit));
  }
  return solver.solveStatus();
}

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
  std::vector<std::vector<size_t>> requiredStateSymbolsByFrame;
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

struct CachedResetSummaryCoi {
  BaseCaseCoi coi;
  size_t transitionTargets = 0;
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
      const TransitionExprResolver& transitionByState,
      BoolExpr* frameInvariant = nullptr)
      : problem(problem),
        transitionByState(transitionByState),
        frameInvariant(frameInvariant),
        frameInvariantSupport(frameInvariant != nullptr
                                  ? frameInvariant->getSupportVars()
                                  : std::set<size_t>{}),
        bootstrapFrames(resetBootstrapFrames(problem)),
        initialMode(bootstrapFrames == 0 ? determineInitialConstraintMode(problem)
                                         : InitialConstraintMode::None),
        primaryByComplement(buildPrimaryByComplementSymbol(problem)),
        initialEqualities(problem.initialStateEqualityPairs),
        bootstrapEqualities(problem.bootstrapStateEqualityPairs) {}

  const KInductionProblem& problem;
  const TransitionExprResolver& transitionByState;
  // Optional caller-validated invariant for frames at and after the concrete
  // startup frontier. PDR proves this separately before using it here; the
  // reset-frontier BMC only consumes it as an extra exact reachable-state fact.
  BoolExpr* frameInvariant = nullptr;
  std::set<size_t> frameInvariantSupport;
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
  // Shared-prefix reset-frontier queries check one cube against every concrete
  // post-bootstrap frame up to a depth. The COI depends only on the cube
  // symbols and max frame, so cache that exact solver separately from the
  // single-frontier cache and vary literal values through assumptions.
  mutable std::unordered_map<std::string, std::unique_ptr<CachedResetFrontierSolver>>
      cachedPrefixSolvers;
  // Exact reset-frontier UNSAT cores are reusable across neighboring cubes:
  // once core C is proven unreachable, every later cube containing C is also
  // unreachable. BlackParrot PDR sampling showed thousands of repeated
  // assumption solves for such neighboring cubes, so keep a small per-frame
  // cache of minimized unreachable cores before asking SAT again.
  mutable std::unordered_map<
      size_t,
      std::vector<std::vector<std::pair<size_t, bool>>>>
      unreachableCoresByTargetFrame;
  // The reset-summary precheck is often asked about neighboring cubes that
  // share the same support at the same post-bootstrap depth. Its COI is
  // support-only, so cache it separately from SAT solvers and vary values later.
  mutable std::unordered_map<std::string, CachedResetSummaryCoi>
      cachedResetSummaryCois;
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

std::vector<std::vector<size_t>> sortedFrameStates(
    const std::vector<std::unordered_set<size_t>>& requiredStates) {
  std::vector<std::vector<size_t>> sorted;
  sorted.reserve(requiredStates.size());
  for (const auto& frameStates : requiredStates) {
    sorted.push_back(sortedSymbols(frameStates));
  }
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

FrameSymbolAliases buildResetSummaryFrameAliases(
    const ResetFrontierReachabilityContextData& context,
    const BaseCaseCoi& coi,
    size_t numFrames) {
  FrameSymbolAliases aliasesByFrame(numFrames);
  if (!aliasesByFrame.empty()) {
    aliasesByFrame[0] =
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
                             bool constrainPreviouslySafeFrames,
                             bool closeStartupEqualityDependencies) {
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
    if (closeStartupEqualityDependencies &&
        bootstrapFrames != 0 &&
        frame == bootstrapFrames) {
      closeFrameEqualityDependencies(
          problem.bootstrapStateEqualityPairs, requiredStates[frame]);
    }
    auto targets = expandTransitionTargets(
        requiredStates[frame],
        transitionByState,
        primaryByComplement);
    transitionTargetsByFrame[frame - 1] = targets;
    transitionByState.collectSupportForTargets(
        targets, stateSymbols, requiredStates[frame - 1], solverSymbols);
  }

  if (closeStartupEqualityDependencies) {
    closeFrameEqualityDependencies(
        problem.initialStateEqualityPairs, requiredStates[0]);
  }

  for (const auto& frameStates : requiredStates) {
    solverSymbols.insert(frameStates.begin(), frameStates.end());
  }
  for (const auto& targets : transitionTargetsByFrame) {
    for (const auto target : targets) {
      solverSymbols.insert(target);
    }
  }
  addRelevantComplementPartners(problem.complementedStatePairs0, solverSymbols);
  addRelevantComplementPartners(problem.complementedStatePairs1, solverSymbols);

  BaseCaseCoi coi;
  coi.transitionTargetsByFrame = std::move(transitionTargetsByFrame);
  coi.requiredStateSymbolsByFrame = sortedFrameStates(requiredStates);
  coi.solverSymbols = sortedSymbols(solverSymbols);
  coi.solverSymbolSet.insert(coi.solverSymbols.begin(), coi.solverSymbols.end());
  return coi;
}

BaseCaseCoi buildStateCubeReachabilityCoiForTargetFrames(
    const ResetFrontierReachabilityContextData& context,
    size_t targetFrame,
    const std::vector<std::pair<size_t, bool>>& cube,
    const std::vector<size_t>& targetFrames,
    bool closeStartupEqualityDependencies) {
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
      for (const auto target : targetFrames) {
        if (target <= targetFrame) {
          requiredStates[target].insert(symbol);
        }
      }
    }
  }
  if (context.frameInvariant != nullptr) {
    // The caller has already proved this invariant on the PDR startup frontier
    // and through one post-reset transition. Encode it only from that concrete
    // frontier onward; pre-reset frames may intentionally violate it while
    // reset is still asserting.
    addFormulaSupport(context.frameInvariant, solverSymbols);
    for (size_t frame = context.bootstrapFrames; frame <= targetFrame; ++frame) {
      addFormulaStateSupport(
          context.frameInvariant, stateSymbols, requiredStates[frame]);
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
    if (closeStartupEqualityDependencies &&
        context.bootstrapFrames != 0 && frame == context.bootstrapFrames) {
      context.bootstrapEqualities.close(requiredStates[frame]);
    }
    auto targets = expandTransitionTargets(
        requiredStates[frame],
        transitionByState,
        context.primaryByComplement);
    transitionTargetsByFrame[frame - 1] = targets;
    transitionByState.collectSupportForTargets(
        targets, stateSymbols, requiredStates[frame - 1], solverSymbols);
  }

  if (closeStartupEqualityDependencies) {
    context.initialEqualities.close(requiredStates[0]);
  }

  for (const auto& frameStates : requiredStates) {
    solverSymbols.insert(frameStates.begin(), frameStates.end());
  }
  for (const auto& targets : transitionTargetsByFrame) {
    for (const auto target : targets) {
      solverSymbols.insert(target);
    }
  }
  addRelevantComplementPartners(problem.complementedStatePairs0, solverSymbols);
  addRelevantComplementPartners(problem.complementedStatePairs1, solverSymbols);

  BaseCaseCoi coi;
  coi.transitionTargetsByFrame = std::move(transitionTargetsByFrame);
  coi.requiredStateSymbolsByFrame = sortedFrameStates(requiredStates);
  coi.solverSymbols = sortedSymbols(solverSymbols);
  coi.solverSymbolSet.insert(coi.solverSymbols.begin(), coi.solverSymbols.end());
  return coi;
}

BaseCaseCoi buildStateCubeReachabilityCoi(
    const ResetFrontierReachabilityContextData& context,
    size_t targetFrame,
    const std::vector<std::pair<size_t, bool>>& cube,
    bool closeStartupEqualityDependencies) {
  return buildStateCubeReachabilityCoiForTargetFrames(
      context,
      targetFrame,
      cube,
      std::vector<size_t>{targetFrame},
      closeStartupEqualityDependencies);
}

BaseCaseCoi buildStateCubePrefixReachabilityCoi(
    const ResetFrontierReachabilityContextData& context,
    size_t maxTargetFrame,
    const std::vector<std::pair<size_t, bool>>& cube,
    bool closeStartupEqualityDependencies) {
  std::vector<size_t> targetFrames;
  targetFrames.reserve(maxTargetFrame + 1 - context.bootstrapFrames);
  for (size_t frame = context.bootstrapFrames; frame <= maxTargetFrame; ++frame) {
    targetFrames.push_back(frame);
  }
  return buildStateCubeReachabilityCoiForTargetFrames(
      context,
      maxTargetFrame,
      cube,
      targetFrames,
      closeStartupEqualityDependencies);
}

BaseCaseCoi buildResetSummaryCubeReachabilityCoi(
    const ResetFrontierReachabilityContextData& context,
    size_t postBootstrapSteps,
    const std::vector<std::pair<size_t, bool>>& cube) {
  const auto& problem = context.problem;
  const auto& transitionByState = context.transitionByState;
  const auto& stateSymbols = transitionByState.stateSymbols();
  std::vector<std::unordered_set<size_t>> requiredStates(postBootstrapSteps + 1);
  std::unordered_set<size_t> solverSymbols;
  solverSymbols.reserve(1024);
  for (const auto& [symbol, _] : problem.resetBootstrapInputs) {
    solverSymbols.insert(symbol);
  }
  for (const auto& [symbol, _] : cube) {
    solverSymbols.insert(symbol);
    if (stateSymbols.find(symbol) != stateSymbols.end()) {
      requiredStates[postBootstrapSteps].insert(symbol);
    }
  }
  if (context.frameInvariant != nullptr) {
    addFormulaSupport(context.frameInvariant, solverSymbols);
    for (size_t frame = 0; frame <= postBootstrapSteps; ++frame) {
      addFormulaStateSupport(
          context.frameInvariant, stateSymbols, requiredStates[frame]);
    }
  }

  std::vector<std::vector<size_t>> transitionTargetsByFrame(postBootstrapSteps);
  for (size_t frame = postBootstrapSteps; frame > 0; --frame) {
    auto targets = expandTransitionTargets(
        requiredStates[frame],
        transitionByState,
        context.primaryByComplement);
    transitionTargetsByFrame[frame - 1] = targets;
    transitionByState.collectSupportForTargets(
        targets, stateSymbols, requiredStates[frame - 1], solverSymbols);
  }

  context.bootstrapEqualities.close(requiredStates[0]);

  for (const auto& frameStates : requiredStates) {
    solverSymbols.insert(frameStates.begin(), frameStates.end());
  }
  for (const auto& targets : transitionTargetsByFrame) {
    for (const auto target : targets) {
      solverSymbols.insert(target);
    }
  }
  addRelevantComplementPartners(problem.complementedStatePairs0, solverSymbols);
  addRelevantComplementPartners(problem.complementedStatePairs1, solverSymbols);

  BaseCaseCoi coi;
  coi.transitionTargetsByFrame = std::move(transitionTargetsByFrame);
  coi.requiredStateSymbolsByFrame = sortedFrameStates(requiredStates);
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

void addResetFrontierFrameInvariantConstraints(
    SATSolverWrapper& solver,
    const FrameVariableStore& variables,
    const ResetFrontierReachabilityContextData& context,
    size_t targetFrame) {
  if (context.frameInvariant == nullptr) {
    return;
  }
  for (size_t frame = context.bootstrapFrames; frame <= targetFrame; ++frame) {
    FrameFormulaEncoder encoder(
        solver, variables.makeLeafLits(frame, context.frameInvariantSupport));
    solver.addClause({encoder.encode(context.frameInvariant)});
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

void addBlockedStateCubeClause(SATSolverWrapper& solver,
                               const FrameVariableStore& variables,
                               const std::vector<std::pair<size_t, bool>>& cube,
                               size_t frame) {
  std::vector<int> clause;
  clause.reserve(cube.size());
  for (const auto& [symbol, value] : cube) {
    const int literal = variables.getLiteral(symbol, frame);
    clause.push_back(value ? -literal : literal);
  }
  solver.addClause(clause);
}

void addTransitionRelation(SATSolverWrapper& solver,
                           const FrameVariableStore& variables,
                           const TransitionExprResolver& transitionByState,
                           const std::vector<size_t>& targets,
                           size_t frame) {
  // All transition formulas in one frame are slices of the same combinational
  // next-state network. Reusing a frame encoder lets shared BoolExpr DAG nodes
  // produce one Tseitin literal instead of being re-encoded once per state bit.
  struct EncodingGroup {
    const std::unordered_map<size_t, size_t>* symbolMap = nullptr;
    std::vector<size_t> stateSymbols;
  };
  std::vector<EncodingGroup> groups;
  groups.reserve(3);
  for (const auto stateSymbol : targets) {
    const TransitionExprView view = transitionByState.expressionView(stateSymbol);
    auto groupIt = std::find_if(
        groups.begin(),
        groups.end(),
        [&](const EncodingGroup& group) {
          return group.symbolMap == view.symbolMap;
        });
    if (groupIt == groups.end()) {
      groups.push_back(EncodingGroup{view.symbolMap, {stateSymbol}});
    } else {
      groupIt->stateSymbols.push_back(stateSymbol);
    }
  }

  for (const auto& group : groups) {
    size_t expectedNodes = 0;
    if (group.stateSymbols.size() <= kMaxExactTransitionNodeCountHintTargets) {
      for (const auto stateSymbol : group.stateSymbols) {
        expectedNodes += transitionByState.nodeCount(stateSymbol);
      }
    }
    FrameFormulaEncoder encoder(
        solver,
        variables.makeLeafLits(frame),
        group.symbolMap,
        false,
        expectedNodes);
    for (const auto stateSymbol : group.stateSymbols) {
      const TransitionExprView view =
          transitionByState.expressionView(stateSymbol);
      addLiteralEquivalence(
          solver,
          variables.getLiteral(stateSymbol, frame + 1),
          encoder.encode(view.expr));
    }
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

enum class BaseCaseSolverProfile {
  SecConeProof,
  PdrValidation,
  PdrValidationProofOnly,
};

std::optional<KInductionResult::CounterexampleWitness> findBaseCounterexampleImpl(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    size_t k,
    std::optional<size_t> exactPublicBadFrame,
    bool localizeMultiOutputFrontier = true,
    BaseCaseSolverProfile solverProfile = BaseCaseSolverProfile::SecConeProof);

KInductionProblem makeSingleObservedOutputProblem(
    const KInductionProblem& problem,
    size_t outputIndex) {
  KInductionProblem single = problem;
  single.observedOutputs =
      outputIndex < problem.observedOutputs.size()
          ? std::vector<SignalKey>{problem.observedOutputs[outputIndex]}
          : std::vector<SignalKey>{};
  single.observedOutputNames =
      outputIndex < problem.observedOutputNames.size()
          ? std::vector<std::string>{problem.observedOutputNames[outputIndex]}
          : std::vector<std::string>{};
  single.observedOutputExprs0 = {problem.observedOutputExprs0[outputIndex]};
  single.observedOutputExprs1 = {problem.observedOutputExprs1[outputIndex]};

  BoolExpr* outputBad = BoolExpr::simplify(
      BoolExpr::Xor(
          single.observedOutputExprs0.front(),
          single.observedOutputExprs1.front()));
  single.bad = outputBad;
  single.property = BoolExpr::Not(outputBad);
  single.inductionBad = outputBad;
  single.inductionProperty = single.property;
  return single;
}

std::optional<KInductionResult::CounterexampleWitness>
findPerOutputBaseCounterexampleAtFrontier(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    size_t k,
    std::optional<size_t> exactPublicBadFrame) {
  if (!exactPublicBadFrame.has_value() ||
      problem.observedOutputExprs0.size() <= 1 ||
      problem.observedOutputExprs0.size() != problem.observedOutputExprs1.size()) {
    return std::nullopt;
  }

  // Exact SEC validation asks whether any observed output is bad at one frame.
  // Solving the whole batch OR can force the SAT solver to reason across
  // unrelated output cones.  Match PDR's bad-cube search and validate each
  // output independently; the disjunction is SAT iff one per-output query is.
  for (size_t output = 0; output < problem.observedOutputExprs0.size(); ++output) {
    KInductionProblem single =
        makeSingleObservedOutputProblem(problem, output);
    if (auto witness = findBaseCounterexampleImpl(
            single, solverType, k, exactPublicBadFrame);
        witness.has_value()) {
      return witness;
    }
  }
  return std::nullopt;
}

std::optional<KInductionResult::CounterexampleWitness> findBaseCounterexampleImpl(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    size_t k,
    std::optional<size_t> exactPublicBadFrame,
    bool localizeMultiOutputFrontier,
    BaseCaseSolverProfile solverProfile) {
  if (localizeMultiOutputFrontier &&
      exactPublicBadFrame.has_value() &&
      problem.observedOutputExprs0.size() > 1 &&
      problem.observedOutputExprs0.size() == problem.observedOutputExprs1.size()) {
    return findPerOutputBaseCounterexampleAtFrontier(
        problem, solverType, k, exactPublicBadFrame);
  }

  const size_t bootstrapFrames = resetBootstrapFrames(problem);
  const size_t internalK = k + bootstrapFrames;
  const bool constrainPreviouslySafeFrames =
      exactPublicBadFrame.has_value() &&
      solverProfile != BaseCaseSolverProfile::PdrValidation &&
      solverProfile != BaseCaseSolverProfile::PdrValidationProofOnly;
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
      constrainPreviouslySafeFrames,
      solverProfile != BaseCaseSolverProfile::PdrValidationProofOnly);
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
  if (solverProfile == BaseCaseSolverProfile::PdrValidation ||
      solverProfile == BaseCaseSolverProfile::PdrValidationProofOnly) {
    // PDR calls this helper as a short-lived exact CEGAR validation. It asks
    // only whether bad is reachable at this frontier: older public bad frames
    // were checked or learned by earlier PDR refinements, and re-encoding them
    // as a safe-prefix constraint made AES spend minutes inside SAT search.
    // Use the PDR query profile here as well: samples on the regress PDR flow
    // showed these medium-sized validation BMCs spending their time in Kissat's
    // standalone preprocessing/probing, while PDR only needs a quick SAT/UNSAT
    // answer to decide which learned bad-formula clauses to add.
    solver.configureForSecPdrQuery(coi.solverSymbols.size());
  } else {
    solver.configureForSecConeProof(coi.solverSymbols.size());
  }
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

bool hasBaseCounterexampleAtFrontier(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    size_t k) {
  return findBaseCounterexampleImpl(
      problem,
      solverType,
      k,
      k,
      /*localizeMultiOutputFrontier=*/false,
      BaseCaseSolverProfile::PdrValidation)
      .has_value();
}

bool provesNoBaseCounterexampleAtFrontier(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    size_t k) {
  return !findBaseCounterexampleImpl(
              problem,
              solverType,
              k,
              k,
              /*localizeMultiOutputFrontier=*/false,
              BaseCaseSolverProfile::PdrValidationProofOnly)
              .has_value();
}

bool provesNoBaseCounterexampleAtFrontierWithSecConeProof(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    size_t k) {
  return !findBaseCounterexampleImpl(
              problem,
              solverType,
              k,
              k,
              /*localizeMultiOutputFrontier=*/false,
              BaseCaseSolverProfile::SecConeProof)
              .has_value();
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
    const TransitionExprResolver& transitionByState,
    BoolExpr* frameInvariant) {
  return std::make_shared<ResetFrontierReachabilityContext>(
      std::make_shared<ResetFrontierReachabilityContextData>(
          problem, transitionByState, frameInvariant));
}

void rememberResetFrontierUnreachableCore(
    const ResetFrontierReachabilityContextData& data,
    size_t targetFrame,
    std::vector<std::pair<size_t, bool>> core);

void rememberResetFrontierUnreachableCube(
    const ResetFrontierReachabilityContext& context,
    const std::vector<std::pair<size_t, bool>>& cube,
    size_t postBootstrapSteps) {
  if (cube.empty()) {
    return;
  }

  const auto& data = *context.data;
  const size_t targetFrame = data.bootstrapFrames + postBootstrapSteps;
  rememberResetFrontierUnreachableCore(data, targetFrame, cube);
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

const CachedResetSummaryCoi& getCachedResetSummaryCubeReachabilityCoi(
    const ResetFrontierReachabilityContextData& data,
    size_t postBootstrapSteps,
    const std::vector<std::pair<size_t, bool>>& cube) {
  const std::string key =
      resetFrontierSolverCacheKey(
          KEPLER_FORMAL::Config::SolverType::KISSAT,
          postBootstrapSteps,
          cube,
          /*includeCubeValues=*/false);
  if (const auto it = data.cachedResetSummaryCois.find(key);
      it != data.cachedResetSummaryCois.end()) {
    return it->second;
  }

  if (data.cachedResetSummaryCois.size() >= kMaxResetSummaryCachedCois) {
    data.cachedResetSummaryCois.clear();
  }

  CachedResetSummaryCoi cached;
  cached.coi =
      buildResetSummaryCubeReachabilityCoi(data, postBootstrapSteps, cube);
  cached.transitionTargets =
      countTransitionTargets(cached.coi.transitionTargetsByFrame);
  auto [it, _] =
      data.cachedResetSummaryCois.emplace(key, std::move(cached));
  return it->second;
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

class ParityUnionFind {
 public:
  void addEquality(size_t lhs, size_t rhs) { unite(lhs, rhs, false); }

  void addComplement(size_t lhs, size_t rhs) { unite(lhs, rhs, true); }

  std::optional<bool> xorRelation(size_t lhs, size_t rhs) {
    if (parent_.find(lhs) == parent_.end() ||
        parent_.find(rhs) == parent_.end()) {
      return std::nullopt;
    }
    const auto lhsRoot = find(lhs);
    const auto rhsRoot = find(rhs);
    if (lhsRoot.first != rhsRoot.first) {
      return std::nullopt;
    }
    return lhsRoot.second ^ rhsRoot.second;
  }

  std::pair<size_t, bool> findWithParity(size_t symbol) {
    return find(symbol);
  }

 private:
  void ensure(size_t symbol) {
    if (parent_.find(symbol) == parent_.end()) {
      parent_.emplace(symbol, symbol);
      parityToParent_.emplace(symbol, false);
    }
  }

  std::pair<size_t, bool> find(size_t symbol) {
    ensure(symbol);
    const auto parent = parent_[symbol];
    const auto parity = parityToParent_[symbol];
    if (parent == symbol) {
      return {symbol, false};
    }
    const auto root = find(parent);
    parent_[symbol] = root.first;
    parityToParent_[symbol] = parity ^ root.second;
    return {parent_[symbol], parityToParent_[symbol]};
  }

  void unite(size_t lhs, size_t rhs, bool inverted) {
    const auto lhsRoot = find(lhs);
    const auto rhsRoot = find(rhs);
    if (lhsRoot.first == rhsRoot.first) {
      return;
    }
    parent_[lhsRoot.first] = rhsRoot.first;
    // value(lhs) xor value(rhs) must equal `inverted`.
    parityToParent_[lhsRoot.first] =
        lhsRoot.second ^ rhsRoot.second ^ inverted;
  }

  std::unordered_map<size_t, size_t> parent_;
  std::unordered_map<size_t, bool> parityToParent_;
};

std::optional<std::vector<std::pair<size_t, bool>>>
knownResetFrontierConflictCore(
    const ResetFrontierReachabilityContextData& data,
    const std::vector<std::pair<size_t, bool>>& cube,
    size_t postBootstrapSteps) {
  if (cube.empty() || postBootstrapSteps != 0) {
    return std::nullopt;
  }

  const bool usesBootstrapFrontier = data.bootstrapFrames != 0;
  const auto& assignments = usesBootstrapFrontier
                                ? data.problem.bootstrapStateAssignments
                                : data.problem.initialStateAssignments;
  const auto& equalities = usesBootstrapFrontier
                               ? data.problem.bootstrapStateEqualityPairs
                               : data.problem.initialStateEqualityPairs;
  if (assignments.empty() && equalities.empty() &&
      data.problem.complementedStatePairs0.empty() &&
      data.problem.complementedStatePairs1.empty()) {
    return std::nullopt;
  }

  ParityUnionFind relations;
  for (const auto& [lhsSymbol, rhsSymbol] : equalities) {
    relations.addEquality(lhsSymbol, rhsSymbol);
  }
  for (const auto& [primarySymbol, complementedSymbol] :
       data.problem.complementedStatePairs0) {
    relations.addComplement(primarySymbol, complementedSymbol);
  }
  for (const auto& [primarySymbol, complementedSymbol] :
       data.problem.complementedStatePairs1) {
    relations.addComplement(primarySymbol, complementedSymbol);
  }

  std::unordered_map<size_t, bool> rootAssignments;
  rootAssignments.reserve(assignments.size());
  for (const auto& [symbol, value] : assignments) {
    const auto [root, parity] = relations.findWithParity(symbol);
    const bool rootValue = value ^ parity;
    if (const auto it = rootAssignments.find(root);
        it != rootAssignments.end() && it->second != rootValue) {
      continue;
    }
    rootAssignments.emplace(root, rootValue);
  }

  std::unordered_map<size_t, std::pair<bool, std::pair<size_t, bool>>>
      cubeValueByRoot;
  cubeValueByRoot.reserve(cube.size());
  for (const auto& literal : cube) {
    const auto [root, parity] = relations.findWithParity(literal.first);
    const auto assignment = rootAssignments.find(root);
    const bool rootValue = literal.second ^ parity;
    if (assignment != rootAssignments.end() &&
        assignment->second != rootValue) {
      return std::vector<std::pair<size_t, bool>>{literal};
    }
    if (const auto it = cubeValueByRoot.find(root);
        it != cubeValueByRoot.end()) {
      if (it->second.first != rootValue) {
        return normalizedAssignmentCube({it->second.second, literal});
      }
      continue;
    }
    cubeValueByRoot.emplace(root, std::pair{rootValue, literal});
  }

  return std::nullopt;
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

bool cubeSymbolsAreInSolverCoi(
    const BaseCaseCoi& coi,
    const std::vector<std::pair<size_t, bool>>& cube) {
  return std::all_of(
      cube.begin(),
      cube.end(),
      [&](const auto& literal) {
        return coi.solverSymbolSet.find(literal.first) !=
               coi.solverSymbolSet.end();
      });
}

size_t addPreviousResetFrontierBlockers(
    SATSolverWrapper& solver,
    const FrameVariableStore& variables,
    const ResetFrontierReachabilityContextData& data,
    const BaseCaseCoi& coi,
    const std::vector<std::pair<size_t, bool>>& cube,
    size_t targetFrame) {
  size_t added = 0;
  for (size_t frame = 0;
       frame < targetFrame &&
       added < kMaxPreviousResetFrontierBlockersPerQuery;
       ++frame) {
    const auto coresIt = data.unreachableCoresByTargetFrame.find(frame);
    if (coresIt == data.unreachableCoresByTargetFrame.end()) {
      continue;
    }
    for (const auto& core : coresIt->second) {
      if (!assignmentCubeContains(cube, core) ||
          !cubeSymbolsAreInSolverCoi(coi, core)) {
        continue;
      }
      // The cached core was already proved unreachable at this concrete
      // reset/bootstrap frame. Reusing it as a safe-prefix clause is redundant
      // with the exact prefix semantics, but it gives the next post-bootstrap
      // query the same learned fact without rebuilding the previous SAT proof.
      addBlockedStateCubeClause(solver, variables, core, frame);
      ++added;
      break;
    }
  }
  return added;
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

  // The assumption solver reports a valid conflict subset, not a guaranteed-minimal one.
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
    bool encodeCubeAsUnitClauses,
    bool closeStartupEqualityDependencies = true) {
  auto cached = std::make_unique<CachedResetFrontierSolver>();
  cached->solverType = solverType;
  cached->targetFrame = targetFrame;
  cached->coi = buildStateCubeReachabilityCoi(
      data, targetFrame, cube, closeStartupEqualityDependencies);
  const FrameSymbolAliases aliasesByFrame =
      buildResetFrontierFrameAliases(data, cached->coi, targetFrame + 1);

  const auto& problem = data.problem;
  cached->solver = std::make_unique<SATSolverWrapper>(solverType);
  // Reset-frontier checks run inside PDR's blocking loop. Sampled AES runs
  // showed the one-shot query spending its time in Kissat probing/sweeping
  // before any refinement could be learned, so use the same CDCL-oriented
  // profile regardless of whether the cube is encoded as clauses or
  // assumptions.
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
  addResetFrontierFrameInvariantConstraints(
      *cached->solver, *cached->variables, data, targetFrame);

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
  const size_t previousBlockers = addPreviousResetFrontierBlockers(
      *cached->solver,
      *cached->variables,
      data,
      cached->coi,
      cube,
      targetFrame);
  if (previousBlockers != 0 && isKInductionCoiDiagEnabled()) {
    emitSecDiag(
        "SEC diag: reset frontier previous unreachable blockers=",
        previousBlockers,
        " target_frame=",
        targetFrame);
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

std::unique_ptr<CachedResetFrontierSolver> buildResetFrontierSolverForCoi(
    const ResetFrontierReachabilityContextData& data,
    KEPLER_FORMAL::Config::SolverType solverType,
    BaseCaseCoi coi,
    const std::vector<std::pair<size_t, bool>>& cube,
    size_t targetFrame) {
  auto cached = std::make_unique<CachedResetFrontierSolver>();
  cached->solverType = solverType;
  cached->targetFrame = targetFrame;
  cached->coi = std::move(coi);
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
  addResetFrontierFrameInvariantConstraints(
      *cached->solver, *cached->variables, data, targetFrame);

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
  const size_t previousBlockers = addPreviousResetFrontierBlockers(
      *cached->solver,
      *cached->variables,
      data,
      cached->coi,
      cube,
      targetFrame);
  if (previousBlockers != 0 && isKInductionCoiDiagEnabled()) {
    emitSecDiag(
        "SEC diag: reset frontier previous unreachable blockers=",
        previousBlockers,
        " target_frame=",
        targetFrame);
  }

  cached->cubeEncodedAsUnitClauses = false;
  return cached;
}

CachedResetFrontierSolver& getCachedResetFrontierPrefixSolver(
    const ResetFrontierReachabilityContextData& data,
    KEPLER_FORMAL::Config::SolverType solverType,
    const std::vector<std::pair<size_t, bool>>& cube,
    size_t maxTargetFrame) {
  (void)solverType;
  const auto cachedSolverType = KEPLER_FORMAL::Config::SolverType::CADICAL;
  const std::string key =
      resetFrontierSolverCacheKey(
          cachedSolverType,
          maxTargetFrame,
          cube,
          /*includeCubeValues=*/false);
  if (const auto it = data.cachedPrefixSolvers.find(key);
      it != data.cachedPrefixSolvers.end()) {
    return *it->second;
  }

  const auto cubeSymbols = sortedCubeSymbols(cube);
  for (const auto& [_, cached] : data.cachedPrefixSolvers) {
    if (cached->solverType == cachedSolverType &&
        cached->targetFrame == maxTargetFrame &&
        !cached->cubeEncodedAsUnitClauses &&
        solverContainsCubeSymbols(*cached, cubeSymbols)) {
      if (isKInductionCoiDiagEnabled()) {
        emitSecDiag(
            "SEC diag: reset frontier prefix solver superset cache hit ",
            "target_frame=",
            maxTargetFrame,
            " cube_literals=",
            cube.size(),
            " solver_symbols=",
            cached->coi.solverSymbols.size());
      }
      return *cached;
    }
  }

  if (data.cachedPrefixSolvers.size() >= kMaxResetFrontierCachedSolvers) {
    data.cachedPrefixSolvers.clear();
  }

  auto cached = buildResetFrontierSolverForCoi(
      data,
      cachedSolverType,
      buildStateCubePrefixReachabilityCoi(
          data,
          maxTargetFrame,
          cube,
          /*closeStartupEqualityDependencies=*/true),
      cube,
      maxTargetFrame);
  auto [it, inserted] =
      data.cachedPrefixSolvers.emplace(key, std::move(cached));
  (void)inserted;
  return *it->second;
}

std::optional<std::vector<std::pair<size_t, bool>>>
extractResetSummaryFrontierCube(
    const ResetFrontierReachabilityContextData& data,
    const SATSolverWrapper& solver,
    const FrameVariableStore& variables,
    const BaseCaseCoi& coi) {
  std::vector<std::pair<size_t, bool>> cube;
  if (coi.requiredStateSymbolsByFrame.empty()) {
    return std::nullopt;  // LCOV_EXCL_LINE
  }
  for (const auto symbol : coi.requiredStateSymbolsByFrame.front()) {
    cube.emplace_back(
        symbol, solver.getLiteralValue(variables.getLiteral(symbol, 0)));
    if (cube.size() > kMaxResetSummaryFrontierCubeLiterals) {
      return std::nullopt;
    }
  }
  return normalizedAssignmentCube(std::move(cube));
}

CachedResetFrontierSolver& getCachedResetFrontierSolver(
    const ResetFrontierReachabilityContextData& data,
    KEPLER_FORMAL::Config::SolverType solverType,
    const std::vector<std::pair<size_t, bool>>& cube,
    size_t targetFrame);

std::optional<std::vector<std::pair<size_t, bool>>>
proveResetSummaryFrontierCubeUnreachable(
    const ResetFrontierReachabilityContextData& data,
    const std::vector<std::pair<size_t, bool>>& cube) {
  const auto normalizedCube = normalizedAssignmentCube(cube);
  if (normalizedCube.empty()) {
    return std::nullopt;
  }

  if (const auto knownCore = knownResetFrontierConflictCore(
          data, normalizedCube, /*postBootstrapSteps=*/0);
      knownCore.has_value()) {
    rememberResetFrontierUnreachableCore(
        data, data.bootstrapFrames, *knownCore);
    return knownCore;
  }
  if (const auto cachedCore = findCachedResetFrontierUnreachableCore(
          data, data.bootstrapFrames, normalizedCube);
      cachedCore.has_value()) {
    return cachedCore;
  }
  if (normalizedCube.size() > kMaxResetSummaryFrontierProofCubeLiterals) {
    if (isKInductionCoiDiagEnabled()) {
      emitSecDiag(
          "SEC diag: reset summary frontier proof skipped reason=cube_cap ",
          "frontier_cube=",
          normalizedCube.size(),
          " max_literals=",
          kMaxResetSummaryFrontierProofCubeLiterals);
    }
    return std::nullopt;
  }

  const BaseCaseCoi frontierCoi =
      buildStateCubeReachabilityCoi(
          data,
          data.bootstrapFrames,
          normalizedCube,
          /*closeStartupEqualityDependencies=*/true);
  const size_t frontierTransitionTargets =
      countTransitionTargets(frontierCoi.transitionTargetsByFrame);
  if (frontierCoi.solverSymbols.size() >
          kMaxResetSummaryFrontierProofSymbols ||
      frontierTransitionTargets >
          kMaxResetSummaryFrontierProofTransitionTargets) {
    if (isKInductionCoiDiagEnabled()) {
      emitSecDiag(
          "SEC diag: reset summary frontier proof skipped reason=coi_cap ",
          "frontier_cube=",
          normalizedCube.size(),
          " solver_symbols=",
          frontierCoi.solverSymbols.size(),
          " transition_targets=",
          frontierTransitionTargets);
    }
    return std::nullopt;
  }

  // Summary CEGAR can ask many neighboring frontier questions with the same
  // symbol support. Reuse the exact reset-frontier solver and vary only the
  // assumptions; rebuilding it dominated BlackParrot PDR samples.
  CachedResetFrontierSolver& solver = getCachedResetFrontierSolver(
      data,
      KEPLER_FORMAL::Config::SolverType::CADICAL,
      normalizedCube,
      data.bootstrapFrames);
  const auto assumptions = stateCubeAssumptionLits(
      *solver.variables, normalizedCube, data.bootstrapFrames);
  const auto status = solver.solver->solveWithAssumptionsStatus(
      assumptions, kResetSummaryFrontierProofConflictLimit);
  if (status == SATSolverWrapper::SolveStatus::Sat) {
    return std::nullopt;
  }
  if (status == SATSolverWrapper::SolveStatus::Unknown) {
    if (isKInductionCoiDiagEnabled()) {
      emitSecDiag(
          "SEC diag: reset summary frontier proof resource_limit ",
          "frontier_cube=",
          normalizedCube.size(),
          " solver_symbols=",
          solver.coi.solverSymbols.size(),
          " transition_targets=",
          frontierTransitionTargets);
    }
    return std::nullopt;
  }

  auto core = failedAssumptionCoreFromLastResetFrontierSolve(
      solver, normalizedCube, data.bootstrapFrames);
  if (!core.has_value()) {
    core = normalizedCube;
  }
  rememberResetFrontierUnreachableCore(data, data.bootstrapFrames, *core);
  return core;
}

std::vector<std::vector<std::pair<size_t, bool>>>
collectResetSummarySingletonFrontierBlockers(
    const ResetFrontierReachabilityContextData& data,
    const std::vector<std::pair<size_t, bool>>& cube,
    const std::vector<std::vector<std::pair<size_t, bool>>>& existingBlockers,
    size_t maxNewBlockers) {
  std::vector<std::vector<std::pair<size_t, bool>>> blockers;
  if (maxNewBlockers == 0) {
    return blockers;
  }

  CachedResetFrontierSolver& solver = getCachedResetFrontierSolver(
      data,
      KEPLER_FORMAL::Config::SolverType::CADICAL,
      cube,
      data.bootstrapFrames);
  for (const auto& literal : cube) {
    if (blockers.size() >= maxNewBlockers) {
      break;
    }

    std::vector<std::pair<size_t, bool>> singleton{literal};
    if (std::any_of(
            existingBlockers.begin(),
            existingBlockers.end(),
            [&](const auto& existing) {
              return assignmentCubeContains(singleton, existing);
            }) ||
        std::any_of(
            blockers.begin(),
            blockers.end(),
            [&](const auto& existing) {
              return assignmentCubeContains(singleton, existing);
            })) {
      continue;
    }

    const auto status = solver.solver->solveWithAssumptionsStatus(
        stateCubeAssumptionLits(
            *solver.variables, singleton, data.bootstrapFrames),
        kResetSummarySingletonProofConflictLimit);
    if (status != SATSolverWrapper::SolveStatus::Unsat) {
      continue;
    }

    rememberResetFrontierUnreachableCore(
        data, data.bootstrapFrames, singleton);
    blockers.push_back(std::move(singleton));
  }
  return blockers;
}

bool resetSummaryPrecheckProvesUnreachable(
    const ResetFrontierReachabilityContextData& data,
    KEPLER_FORMAL::Config::SolverType solverType,
    const std::vector<std::pair<size_t, bool>>& cube,
    size_t postBootstrapSteps) {
  if (resetFrontierAssumptionSolvesDisabled()) {
    return false;
  }
  if (data.bootstrapFrames == 0 || postBootstrapSteps == 0) {
    return false;
  }
  if (solverType != KEPLER_FORMAL::Config::SolverType::KISSAT) {
    return false;
  }

  const auto& cachedCoi =
      getCachedResetSummaryCubeReachabilityCoi(data, postBootstrapSteps, cube);
  const BaseCaseCoi& coi = cachedCoi.coi;
  const size_t transitionTargets = cachedCoi.transitionTargets;
  if (isKInductionCoiDiagEnabled()) {
    emitSecDiag(
        "SEC diag: reset summary one-shot cube coi "
        "post_bootstrap_steps=",
        postBootstrapSteps,
        " frames=",
        postBootstrapSteps + 1,
        " solver_symbols=",
        coi.solverSymbols.size(),
        " transition_targets=",
        transitionTargets,
        " cube_literals=",
        cube.size(),
        " frame_invariant_symbols=",
        data.frameInvariantSupport.size());
  }

  if (coi.solverSymbols.size() > kMaxResetSummaryPrecheckSymbols ||
      transitionTargets > kMaxResetSummaryPrecheckTransitionTargets) {
    if (isKInductionCoiDiagEnabled()) {
      emitSecDiag(
          "SEC diag: reset summary one-shot precheck skipped "
          "reason=coi_cap post_bootstrap_steps=",
          postBootstrapSteps,
          " solver_symbols=",
          coi.solverSymbols.size(),
          " transition_targets=",
          transitionTargets);
    }
    return false;
  }

  const auto& problem = data.problem;
  std::vector<std::vector<std::pair<size_t, bool>>> frontierBlockers;
  auto appendFrontierBlocker =
      [&](const std::vector<std::pair<size_t, bool>>& blocker) {
        if (frontierBlockers.size() >= kMaxResetSummaryFrontierBlockers) {
          return false;
        }
        if (std::any_of(
                frontierBlockers.begin(),
                frontierBlockers.end(),
                [&](const auto& existing) {
                  return assignmentCubeContains(blocker, existing);
                })) {
          return false;
        }
        frontierBlockers.push_back(blocker);
        return true;
      };
  if (const auto coresIt =
          data.unreachableCoresByTargetFrame.find(data.bootstrapFrames);
      coresIt != data.unreachableCoresByTargetFrame.end()) {
    for (const auto& core : coresIt->second) {
      if (frontierBlockers.size() >= kMaxResetSummaryFrontierBlockers) {
        break;
      }
      if (!cubeSymbolsAreInSolverCoi(coi, core)) {
        continue;
      }
      appendFrontierBlocker(core);
    }
    if (!frontierBlockers.empty() && isKInductionCoiDiagEnabled()) {
      emitSecDiag(
          "SEC diag: reset summary frontier blockers=",
          frontierBlockers.size(),
          " post_bootstrap_steps=",
          postBootstrapSteps);
    }
  }

  for (size_t refinement = 0; refinement <= kMaxResetSummaryRefinements;
       ++refinement) {
    SATSolverWrapper solver(solverType);
    solver.configureForSecPdrQuery(coi.solverSymbols.size());
    const FrameSymbolAliases aliasesByFrame =
        buildResetSummaryFrameAliases(data, coi, postBootstrapSteps + 1);
    FrameVariableStore variables(
        solver, coi.solverSymbols, postBootstrapSteps + 1, aliasesByFrame);

    for (const auto& [symbol, assertedValue] : problem.resetBootstrapInputs) {
      for (size_t frame = 0; frame <= postBootstrapSteps; ++frame) {
        solver.addClause(
            {assertedValue ? -variables.getLiteral(symbol, frame)
                           : variables.getLiteral(symbol, frame)});
      }
    }
    addComplementedStateRelations(
        solver,
        variables,
        problem.complementedStatePairs0,
        coi.solverSymbolSet,
        postBootstrapSteps + 1);
    addComplementedStateRelations(
        solver,
        variables,
        problem.complementedStatePairs1,
        coi.solverSymbolSet,
        postBootstrapSteps + 1);
    addBootstrapStateAssignments(
        solver, variables, problem, coi.solverSymbolSet, 0);
    addBootstrapStateEqualities(
        solver, variables, data, coi.solverSymbolSet, 0);
    for (const auto& blocker : frontierBlockers) {
      // Summary frame 0 is the already-validated concrete reset/bootstrap
      // frontier.  Any exact blocker learned there is a safe constraint for
      // this weaker summary query and can make it prove UNSAT without opening
      // the full post-reset SAT unroll again.
      addBlockedStateCubeClause(solver, variables, blocker, 0);
    }
    if (data.frameInvariant != nullptr) {
      for (size_t frame = 0; frame <= postBootstrapSteps; ++frame) {
        FrameFormulaEncoder encoder(
            solver, variables.makeLeafLits(frame, data.frameInvariantSupport));
        solver.addClause({encoder.encode(data.frameInvariant)});
      }
    }

    for (size_t frame = 0; frame < postBootstrapSteps; ++frame) {
      addTransitionRelation(
          solver,
          variables,
          data.transitionByState,
          coi.transitionTargetsByFrame[frame],
          frame);
    }
    for (const auto& [symbol, value] : cube) {
      const int literal = variables.getLiteral(symbol, postBootstrapSteps);
      solver.addClause({value ? literal : -literal});
    }

    const SATSolverWrapper::SolveStatus status =
        solver.solveWithKissatResourceLimits(
            kResetSummaryPrecheckConflictLimit);
    if (status == SATSolverWrapper::SolveStatus::Unsat) {
      if (refinement != 0 && isKInductionCoiDiagEnabled()) {
        emitSecDiag(
            "SEC diag: reset summary CEGAR proved unreachable "
            "post_bootstrap_steps=",
            postBootstrapSteps,
            " refinements=",
            refinement,
            " frontier_blockers=",
            frontierBlockers.size());
      }
      return true;
    }
    if (status == SATSolverWrapper::SolveStatus::Unknown) {
      if (isKInductionCoiDiagEnabled()) {
        emitSecDiag(
            "SEC diag: reset summary one-shot precheck resource_limit "
            "post_bootstrap_steps=",
            postBootstrapSteps,
            " solver_symbols=",
            coi.solverSymbols.size(),
            " transition_targets=",
            transitionTargets);
      }
      return false;
    }
    if (refinement == kMaxResetSummaryRefinements ||
        frontierBlockers.size() >= kMaxResetSummaryFrontierBlockers) {
      return false;
    }

    const auto frontierCube =
        extractResetSummaryFrontierCube(data, solver, variables, coi);
    if (!frontierCube.has_value()) {
      if (isKInductionCoiDiagEnabled()) {
        emitSecDiag(
            "SEC diag: reset summary refinement skipped reason=frontier_cap "
            "post_bootstrap_steps=",
            postBootstrapSteps,
            " max_literals=",
            kMaxResetSummaryFrontierCubeLiterals);
      }
      return false;
    }
    const auto blocker =
        proveResetSummaryFrontierCubeUnreachable(data, *frontierCube);
    if (!blocker.has_value()) {
      return false;
    }
    size_t addedBlockers = appendFrontierBlocker(*blocker) ? 1 : 0;
    if (blocker->size() == 1 &&
        frontierBlockers.size() < kMaxResetSummaryFrontierBlockers) {
      const size_t remainingBlockers =
          kMaxResetSummaryFrontierBlockers - frontierBlockers.size();
      const auto singletonBlockers =
          collectResetSummarySingletonFrontierBlockers(
              data,
              *frontierCube,
              frontierBlockers,
              std::min(
                  kMaxResetSummaryBulkSingletonBlockers,
                  remainingBlockers));
      for (const auto& singleton : singletonBlockers) {
        if (appendFrontierBlocker(singleton)) {
          ++addedBlockers;
        }
      }
    }
    if (isKInductionCoiDiagEnabled()) {
      emitSecDiag(
          "SEC diag: reset summary learned frontier blocker ",
          "post_bootstrap_steps=",
          postBootstrapSteps,
          " refinement=",
          refinement + 1,
          " frontier_cube=",
          frontierCube->size(),
          " blocker=",
          blocker->size(),
          " added=",
          addedBlockers);
    }
  }
  return false;  // LCOV_EXCL_LINE
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
  const auto cachedSolverType = KEPLER_FORMAL::Config::SolverType::CADICAL;
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

void primeResetFrontierReachabilitySolver(
    const ResetFrontierReachabilityContext& context,
    KEPLER_FORMAL::Config::SolverType solverType,
    const std::vector<std::pair<size_t, bool>>& cube,
    size_t postBootstrapSteps) {
  if (cube.empty()) {
    return;
  }

  const auto& data = *context.data;
  const size_t targetFrame = data.bootstrapFrames + postBootstrapSteps;
  const auto normalizedCube = normalizedAssignmentCube(cube);
  (void)getCachedResetFrontierSolver(
      data, solverType, normalizedCube, targetFrame);
}

bool isStateCubeReachableAtResetFrontier(
    const ResetFrontierReachabilityContext& context,
    KEPLER_FORMAL::Config::SolverType solverType,
    const std::vector<std::pair<size_t, bool>>& cube,
    size_t postBootstrapSteps,
    bool usePostBootstrapPrechecks,
    int64_t startupConflictLimit,
    int64_t startupPropagationLimit) {
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
  if (const auto knownCore = knownResetFrontierConflictCore(
          data, normalizedCube, postBootstrapSteps);
      knownCore.has_value()) {
    rememberResetFrontierUnreachableCore(data, targetFrame, *knownCore);
    if (isKInductionCoiDiagEnabled()) {
      emitSecDiag(
          "SEC diag: reset frontier known facts exclude cube ",
          "post_bootstrap_steps=",
          postBootstrapSteps,
          " core_literals=",
          knownCore->size(),
          " cube_literals=",
          normalizedCube.size());
    }
    return false;
  }
  if (postBootstrapSteps != 0 && usePostBootstrapPrechecks) {
    // Cached-assumption validation is PDR's hot reset-frontier path. Before
    // constructing the exact assumption solver, try the same weakened
    // startup-equality COI used by one-shot validation. The relaxed query only
    // drops equality closure, so UNSAT remains a sound proof; SAT simply falls
    // through to the exact cached solver below. This is deliberately bounded:
    // if the relaxed COI is still broad, or Kissat cannot decide it quickly,
    // the shortcut is abandoned rather than becoming the PDR wall itself.
    auto relaxedSolver = buildResetFrontierSolver(
        data,
        solverType,
        normalizedCube,
        targetFrame,
        /*encodeCubeAsUnitClauses=*/true,
        /*closeStartupEqualityDependencies=*/false);
    const size_t relaxedTransitionTargets =
        countTransitionTargets(relaxedSolver->coi.transitionTargetsByFrame);

    if (isKInductionCoiDiagEnabled()) {
      emitSecDiag(
          "SEC diag: reset frontier relaxed cached cube coi "
          "post_bootstrap_steps=",
          postBootstrapSteps,
          " frames=",
          targetFrame + 1,
          " solver_symbols=",
          relaxedSolver->coi.solverSymbols.size(),
          " transition_targets=",
          relaxedTransitionTargets,
          " cube_literals=",
          normalizedCube.size(),
          " frame_invariant_symbols=",
          data.frameInvariantSupport.size());
    }

    const bool relaxedCoiIsLocal =
        relaxedSolver->coi.solverSymbols.size() <=
            kMaxRelaxedResetFrontierPrecheckSymbols &&
        relaxedTransitionTargets <=
            kMaxRelaxedResetFrontierPrecheckTransitionTargets;
    if (relaxedCoiIsLocal) {
      bool relaxedUnsat = false;
      if (solverType == KEPLER_FORMAL::Config::SolverType::KISSAT) {
        const auto status =
            relaxedSolver->solver->solveWithKissatResourceLimits(
                kRelaxedResetFrontierPrecheckConflictLimit);
        relaxedUnsat = status == SATSolverWrapper::SolveStatus::Unsat;
        if (status == SATSolverWrapper::SolveStatus::Unknown &&
            isKInductionCoiDiagEnabled()) {
          emitSecDiag(
              "SEC diag: reset frontier relaxed cached precheck "
              "resource_limit post_bootstrap_steps=",
              postBootstrapSteps,
              " solver_symbols=",
              relaxedSolver->coi.solverSymbols.size(),
              " transition_targets=",
              relaxedTransitionTargets);
        }
      } else {
        relaxedUnsat = !relaxedSolver->solver->solve();
      }
      if (relaxedUnsat) {
        rememberResetFrontierUnreachableCore(data, targetFrame, normalizedCube);
        return false;
      }
    } else if (isKInductionCoiDiagEnabled()) {
      emitSecDiag(
          "SEC diag: reset frontier relaxed cached precheck skipped "
          "reason=coi_cap post_bootstrap_steps=",
          postBootstrapSteps,
          " solver_symbols=",
          relaxedSolver->coi.solverSymbols.size(),
          " transition_targets=",
          relaxedTransitionTargets);
    }

    if (resetSummaryPrecheckProvesUnreachable(
            data, solverType, normalizedCube, postBootstrapSteps)) {
      rememberResetFrontierUnreachableCore(data, targetFrame, normalizedCube);
      return false;
    }
  }
  if (resetFrontierAssumptionSolvesDisabled()) {
    auto unitSolver = buildResetFrontierSolver(
        data,
        solverType,
        normalizedCube,
        targetFrame,
        /*encodeCubeAsUnitClauses=*/true);
    const int64_t conflictLimit =
        postBootstrapSteps == 0 && startupConflictLimit >= 0
            ? startupConflictLimit
            : static_cast<int64_t>(kResetFrontierCachedAssumptionConflictLimit);
    const auto status = solveResetFrontierUnitClauseQuery(
        *unitSolver->solver, solverType, conflictLimit);
    if (status == SATSolverWrapper::SolveStatus::Unknown) {
      if (isKInductionCoiDiagEnabled()) {
        emitSecDiag(
            "SEC diag: reset frontier unit-clause proof resource_limit ",
            "post_bootstrap_steps=",
            postBootstrapSteps,
            " solver_symbols=",
            unitSolver->coi.solverSymbols.size(),
            " transition_targets=",
            countTransitionTargets(unitSolver->coi.transitionTargetsByFrame),
            " cube_literals=",
            normalizedCube.size());
      }
      return true;
    }
    const bool reachable = status == SATSolverWrapper::SolveStatus::Sat;
    if (!reachable) {
      rememberResetFrontierUnreachableCore(data, targetFrame, normalizedCube);
    }
    return reachable;
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
        normalizedCube.size(),
        " frame_invariant_symbols=",
        data.frameInvariantSupport.size());
  }

  SATSolverWrapper::SolveStatus status = SATSolverWrapper::SolveStatus::Unknown;
  if (cached.cubeEncodedAsUnitClauses) {
    status = cached.solver->solveStatus();
  } else {
    const auto assumptions =
        stateCubeAssumptionLits(*cached.variables, normalizedCube, targetFrame);
    if (postBootstrapSteps == 0) {
      status =
          startupConflictLimit >= 0 || startupPropagationLimit >= 0
              ? cached.solver->solveWithAssumptionsStatus(
                    assumptions, startupConflictLimit, startupPropagationLimit)
              : cached.solver->solveWithAssumptionsStatus(assumptions);
    } else {
      status = cached.solver->solveWithAssumptionsStatus(
          assumptions, kResetFrontierCachedAssumptionConflictLimit);
    }
  }
  if (status == SATSolverWrapper::SolveStatus::Unknown) {
    if (isKInductionCoiDiagEnabled()) {
      emitSecDiag(
          "SEC diag: reset frontier cached assumption proof resource_limit ",
          "post_bootstrap_steps=",
          postBootstrapSteps,
          " solver_symbols=",
          cached.coi.solverSymbols.size(),
          " transition_targets=",
          countTransitionTargets(cached.coi.transitionTargetsByFrame),
          " cube_literals=",
          normalizedCube.size());
    }
    return true;
  }

  const bool reachable = status == SATSolverWrapper::SolveStatus::Sat;
  if (!reachable) {
    if (postBootstrapSteps == 0) {
      // The solve above already produced a failed-assumption core.  Reuse it
      // directly instead of launching a second exact minimization loop: AES
      // PDR samples showed wide F[0] reset cubes spending their runtime inside
      // that duplicate assumption search, while the failed core is already a
      // sound reset-frontier blocker and still reusable for neighboring cubes.
      if (const auto core = failedAssumptionCoreFromLastResetFrontierSolve(
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
    size_t postBootstrapSteps,
    bool usePostBootstrapPrechecks) {
  if (cube.empty()) {
    return true;
  }

  const auto& data = *context.data;
  const size_t targetFrame = data.bootstrapFrames + postBootstrapSteps;
  const auto normalizedCube = normalizedAssignmentCube(cube);
  if (const auto knownCore = knownResetFrontierConflictCore(
          data, normalizedCube, postBootstrapSteps);
      knownCore.has_value()) {
    rememberResetFrontierUnreachableCore(data, targetFrame, *knownCore);
    return false;
  }
  if (findCachedResetFrontierUnreachableCore(
          data, targetFrame, normalizedCube)
          .has_value()) {
    return false;
  }
  if (postBootstrapSteps != 0 && usePostBootstrapPrechecks) {
    // First try a weakened COI that does not close the startup equality
    // components.  This is safe only as an UNSAT precheck: removing equality
    // constraints can create spurious SAT witnesses, but if the relaxed query
    // is already UNSAT then the exact reset-frontier query is UNSAT too.  AES
    // PDR sampling showed the exact post-reset one-shot query expanding a
    // two-literal root cube through a 900+ symbol equality/transition closure;
    // this precheck lets local transition/bootstrap contradictions prove out
    // before opening that wider solver. Keep it bounded so a broad relaxed COI
    // falls through instead of replacing the exact query with another wall.
    auto relaxedSolver = buildResetFrontierSolver(
        data,
        solverType,
        normalizedCube,
        targetFrame,
        /*encodeCubeAsUnitClauses=*/true,
        /*closeStartupEqualityDependencies=*/false);
    const size_t relaxedTransitionTargets =
        countTransitionTargets(relaxedSolver->coi.transitionTargetsByFrame);

    if (isKInductionCoiDiagEnabled()) {
      emitSecDiag(
          "SEC diag: reset frontier relaxed one-shot cube coi "
          "post_bootstrap_steps=",
          postBootstrapSteps,
          " frames=",
          targetFrame + 1,
          " solver_symbols=",
          relaxedSolver->coi.solverSymbols.size(),
          " transition_targets=",
          relaxedTransitionTargets,
          " cube_literals=",
          normalizedCube.size(),
          " frame_invariant_symbols=",
          data.frameInvariantSupport.size());
    }

    const bool relaxedCoiIsLocal =
        relaxedSolver->coi.solverSymbols.size() <=
            kMaxRelaxedResetFrontierPrecheckSymbols &&
        relaxedTransitionTargets <=
            kMaxRelaxedResetFrontierPrecheckTransitionTargets;
    if (relaxedCoiIsLocal) {
      bool relaxedUnsat = false;
      if (solverType == KEPLER_FORMAL::Config::SolverType::KISSAT) {
        const auto status =
            relaxedSolver->solver->solveWithKissatResourceLimits(
                kRelaxedResetFrontierPrecheckConflictLimit);
        relaxedUnsat = status == SATSolverWrapper::SolveStatus::Unsat;
        if (status == SATSolverWrapper::SolveStatus::Unknown &&
            isKInductionCoiDiagEnabled()) {
          emitSecDiag(
              "SEC diag: reset frontier relaxed one-shot precheck "
              "resource_limit post_bootstrap_steps=",
              postBootstrapSteps,
              " solver_symbols=",
              relaxedSolver->coi.solverSymbols.size(),
              " transition_targets=",
              relaxedTransitionTargets);
        }
      } else {
        relaxedUnsat = !relaxedSolver->solver->solve();
      }
      if (relaxedUnsat) {
        rememberResetFrontierUnreachableCore(data, targetFrame, normalizedCube);
        return false;
      }
    } else if (isKInductionCoiDiagEnabled()) {
      emitSecDiag(
          "SEC diag: reset frontier relaxed one-shot precheck skipped "
          "reason=coi_cap post_bootstrap_steps=",
          postBootstrapSteps,
          " solver_symbols=",
          relaxedSolver->coi.solverSymbols.size(),
          " transition_targets=",
          relaxedTransitionTargets);
    }

    if (resetSummaryPrecheckProvesUnreachable(
            data, solverType, normalizedCube, postBootstrapSteps)) {
      rememberResetFrontierUnreachableCore(data, targetFrame, normalizedCube);
      return false;
    }
  }
  if (resetFrontierAssumptionSolvesDisabled()) {
    auto solver = buildResetFrontierSolver(
        data,
        solverType,
        normalizedCube,
        targetFrame,
        /*encodeCubeAsUnitClauses=*/true);
    const int64_t conflictLimit =
        postBootstrapSteps == 0
            ? -1
            : static_cast<int64_t>(kResetFrontierCachedAssumptionConflictLimit);
    const auto status = solveResetFrontierUnitClauseQuery(
        *solver->solver, solverType, conflictLimit);
    if (status == SATSolverWrapper::SolveStatus::Unknown) {
      if (isKInductionCoiDiagEnabled()) {
        emitSecDiag(
            "SEC diag: reset frontier one-shot unit-clause resource_limit ",
            "post_bootstrap_steps=",
            postBootstrapSteps,
            " solver_symbols=",
            solver->coi.solverSymbols.size(),
            " transition_targets=",
            countTransitionTargets(solver->coi.transitionTargetsByFrame),
            " cube_literals=",
            normalizedCube.size());
      }
      return true;
    }
    const bool reachable = status == SATSolverWrapper::SolveStatus::Sat;
    if (!reachable) {
      rememberResetFrontierUnreachableCore(data, targetFrame, normalizedCube);
    }
    return reachable;
  }

  const auto assumptionSolverType =
      solverType == KEPLER_FORMAL::Config::SolverType::KISSAT
          ? KEPLER_FORMAL::Config::SolverType::CADICAL
          : solverType;
  auto solver = buildResetFrontierSolver(
      data,
      assumptionSolverType,
      normalizedCube,
      targetFrame,
      /*encodeCubeAsUnitClauses=*/false);

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
        normalizedCube.size(),
        " frame_invariant_symbols=",
        data.frameInvariantSupport.size());
  }

  const auto assumptions =
      stateCubeAssumptionLits(*solver->variables, normalizedCube, targetFrame);
  const bool reachable = solver->solver->solveWithAssumptions(assumptions);
  if (!reachable) {
    // Keep the one-shot COI/build profile, but query the cube through
    // assumptions so an UNSAT proof exposes a reusable core. BlackParrot
    // samples showed full-cube caching missing many neighboring root cubes.
    if (const auto core = failedAssumptionCoreFromLastResetFrontierSolve(
            *solver, normalizedCube, targetFrame);
        core.has_value()) {
      rememberResetFrontierUnreachableCore(data, targetFrame, *core);
    } else {
      rememberResetFrontierUnreachableCore(data, targetFrame, normalizedCube);
    }
  }
  return reachable;
}

bool isStateCubeReachableWithinResetFrontier(
    const ResetFrontierReachabilityContext& context,
    KEPLER_FORMAL::Config::SolverType solverType,
    const std::vector<std::pair<size_t, bool>>& cube,
    size_t maxPostBootstrapSteps) {
  if (cube.empty()) {
    return true;
  }

  const auto& data = *context.data;
  const auto normalizedCube = normalizedAssignmentCube(cube);
  std::vector<size_t> uncheckedSteps;
  uncheckedSteps.reserve(maxPostBootstrapSteps + 1);
  for (size_t step = 0; step <= maxPostBootstrapSteps; ++step) {
    const size_t targetFrame = data.bootstrapFrames + step;
    if (const auto knownCore =
            knownResetFrontierConflictCore(data, normalizedCube, step);
        knownCore.has_value()) {
      rememberResetFrontierUnreachableCore(data, targetFrame, *knownCore);
      continue;
    }
    if (findCachedResetFrontierUnreachableCore(
            data, targetFrame, normalizedCube)
            .has_value()) {
      continue;
    }
    uncheckedSteps.push_back(step);
  }
  if (uncheckedSteps.empty()) {
    return false;
  }

  std::vector<size_t> remainingSteps;
  remainingSteps.reserve(uncheckedSteps.size());
  for (const auto step : uncheckedSteps) {
    if (step != 0 &&
        resetSummaryPrecheckProvesUnreachable(
            data, solverType, normalizedCube, step)) {
      rememberResetFrontierUnreachableCore(
          data, data.bootstrapFrames + step, normalizedCube);
      continue;
    }
    remainingSteps.push_back(step);
  }
  if (remainingSteps.empty()) {
    return false;
  }
  if (resetFrontierAssumptionSolvesDisabled() ||
      remainingSteps.size() <= kMaxSparseResetFrontierPerStepChecks) {
    for (const auto step : remainingSteps) {
      if (isStateCubeReachableAtResetFrontier(
              context,
              solverType,
              normalizedCube,
              step,
              /*usePostBootstrapPrechecks=*/false)) {
        return true;
      }
    }
    return false;
  }

  const size_t maxTargetFrame =
      data.bootstrapFrames + maxPostBootstrapSteps;
  CachedResetFrontierSolver& solver = getCachedResetFrontierPrefixSolver(
      data, solverType, normalizedCube, maxTargetFrame);

  if (isKInductionCoiDiagEnabled()) {
    emitSecDiag(
        "SEC diag: reset frontier prefix cube coi max_post_bootstrap_steps=",
        maxPostBootstrapSteps,
        " frames=",
        maxTargetFrame + 1,
        " solver_symbols=",
        solver.coi.solverSymbols.size(),
        " transition_targets=",
        countTransitionTargets(solver.coi.transitionTargetsByFrame),
        " cube_literals=",
        normalizedCube.size(),
        " unchecked_steps=",
        remainingSteps.size(),
        " frame_invariant_symbols=",
        data.frameInvariantSupport.size());
  }

  for (const auto step : remainingSteps) {
    const size_t targetFrame = data.bootstrapFrames + step;
    const auto assumptions =
        stateCubeAssumptionLits(*solver.variables, normalizedCube, targetFrame);
    const auto status =
        step == 0
            ? solver.solver->solveWithAssumptionsStatus(assumptions)
            : solver.solver->solveWithAssumptionsStatus(
                  assumptions, kResetFrontierCachedAssumptionConflictLimit);
    if (status == SATSolverWrapper::SolveStatus::Unknown) {
      if (isKInductionCoiDiagEnabled()) {
        emitSecDiag(
            "SEC diag: reset frontier prefix assumption proof resource_limit ",
            "post_bootstrap_steps=",
            step,
            " max_post_bootstrap_steps=",
            maxPostBootstrapSteps,
            " solver_symbols=",
            solver.coi.solverSymbols.size(),
            " transition_targets=",
            countTransitionTargets(solver.coi.transitionTargetsByFrame),
            " cube_literals=",
            normalizedCube.size());
      }
      return true;
    }
    if (status == SATSolverWrapper::SolveStatus::Sat) {
      return true;
    }
    if (const auto core = failedAssumptionCoreFromLastResetFrontierSolve(
            solver, normalizedCube, targetFrame);
        core.has_value()) {
      rememberResetFrontierUnreachableCore(data, targetFrame, *core);
    } else {
      rememberResetFrontierUnreachableCore(data, targetFrame, normalizedCube);
    }
  }
  return false;
}

std::vector<std::pair<size_t, bool>> supportCubeForAssignmentCubes(
    const std::vector<std::vector<std::pair<size_t, bool>>>& cubes) {
  std::unordered_map<size_t, bool> valueBySymbol;
  for (const auto& cube : cubes) {
    for (const auto& [symbol, value] : cube) {
      valueBySymbol.emplace(symbol, value);
    }
  }

  std::vector<std::pair<size_t, bool>> supportCube;
  supportCube.reserve(valueBySymbol.size());
  for (const auto& [symbol, value] : valueBySymbol) {
    supportCube.emplace_back(symbol, value);
  }
  return normalizedAssignmentCube(std::move(supportCube));
}

bool anyStateCubeReachableWithinResetFrontier(
    const ResetFrontierReachabilityContext& context,
    KEPLER_FORMAL::Config::SolverType solverType,
    const std::vector<std::vector<std::pair<size_t, bool>>>& cubes,
    size_t maxPostBootstrapSteps) {
  std::vector<std::vector<std::pair<size_t, bool>>> normalizedCubes;
  normalizedCubes.reserve(cubes.size());
  for (auto cube : cubes) {
    cube = normalizedAssignmentCube(std::move(cube));
    if (cube.empty()) {
      return true;
    }
    normalizedCubes.push_back(std::move(cube));
  }
  if (normalizedCubes.empty()) {
    return false;
  }

  const auto& data = *context.data;
  const size_t maxTargetFrame = data.bootstrapFrames + maxPostBootstrapSteps;
  const std::vector<std::pair<size_t, bool>> supportCube =
      supportCubeForAssignmentCubes(normalizedCubes);
  if (supportCube.empty()) {
    return true;
  }

  CachedResetFrontierSolver& solver = getCachedResetFrontierPrefixSolver(
      data, solverType, supportCube, maxTargetFrame);

  if (isKInductionCoiDiagEnabled()) {
    emitSecDiag(
        "SEC diag: reset frontier batch cube coi max_post_bootstrap_steps=",
        maxPostBootstrapSteps,
        " frames=",
        maxTargetFrame + 1,
        " solver_symbols=",
        solver.coi.solverSymbols.size(),
        " transition_targets=",
        countTransitionTargets(solver.coi.transitionTargetsByFrame),
        " cubes=",
        normalizedCubes.size(),
        " support_literals=",
        supportCube.size(),
        " frame_invariant_symbols=",
        data.frameInvariantSupport.size());
  }

  for (size_t step = 0; step <= maxPostBootstrapSteps; ++step) {
    const size_t targetFrame = data.bootstrapFrames + step;
    for (const auto& cube : normalizedCubes) {
      if (const auto knownCore =
              knownResetFrontierConflictCore(data, cube, step);
          knownCore.has_value()) {
        rememberResetFrontierUnreachableCore(data, targetFrame, *knownCore);
        continue;
      }
      if (findCachedResetFrontierUnreachableCore(data, targetFrame, cube)
              .has_value()) {
        continue;
      }
      const auto assumptions =
          stateCubeAssumptionLits(*solver.variables, cube, targetFrame);
      const auto status =
          step == 0
              ? solver.solver->solveWithAssumptionsStatus(assumptions)
              : solver.solver->solveWithAssumptionsStatus(
                    assumptions,
                    kResetFrontierCachedAssumptionConflictLimit,
                    kResetFrontierBatchProofPropagationLimit);
      if (status == SATSolverWrapper::SolveStatus::Sat) {
        return true;
      }
      if (status == SATSolverWrapper::SolveStatus::Unknown) {
        if (isKInductionCoiDiagEnabled()) {
          emitSecDiag(
              "SEC diag: reset frontier batch assumption proof resource_limit ",
              "post_bootstrap_steps=",
              step,
              " max_post_bootstrap_steps=",
              maxPostBootstrapSteps,
              " solver_symbols=",
              solver.coi.solverSymbols.size(),
              " transition_targets=",
              countTransitionTargets(solver.coi.transitionTargetsByFrame),
              " cubes=",
              normalizedCubes.size());
        }
        return true;
      }
      if (const auto core = failedAssumptionCoreFromLastResetFrontierSolve(
              solver, cube, targetFrame);
          core.has_value()) {
        rememberResetFrontierUnreachableCore(data, targetFrame, *core);
      } else {
        rememberResetFrontierUnreachableCore(data, targetFrame, cube);
      }
    }
  }
  return false;
}

bool anyStateCubeReachableAtResetFrontier(
    const ResetFrontierReachabilityContext& context,
    KEPLER_FORMAL::Config::SolverType solverType,
    const std::vector<std::vector<std::pair<size_t, bool>>>& cubes,
    size_t postBootstrapSteps,
    long long conflictLimit,
    long long propagationLimit) {
  std::vector<std::vector<std::pair<size_t, bool>>> normalizedCubes;
  normalizedCubes.reserve(cubes.size());
  for (auto cube : cubes) {
    cube = normalizedAssignmentCube(std::move(cube));
    if (cube.empty()) {
      return true;
    }
    normalizedCubes.push_back(std::move(cube));
  }
  if (normalizedCubes.empty()) {
    return false;
  }

  const auto& data = *context.data;
  const size_t targetFrame = data.bootstrapFrames + postBootstrapSteps;
  const std::vector<std::pair<size_t, bool>> supportCube =
      supportCubeForAssignmentCubes(normalizedCubes);
  if (supportCube.empty()) {
    return true;
  }

  CachedResetFrontierSolver& solver = getCachedResetFrontierSolver(
      data, solverType, supportCube, targetFrame);

  if (isKInductionCoiDiagEnabled()) {
    emitSecDiag(
        "SEC diag: reset frontier target batch cube coi "
        "post_bootstrap_steps=",
        postBootstrapSteps,
        " frames=",
        targetFrame + 1,
        " solver_symbols=",
        solver.coi.solverSymbols.size(),
        " transition_targets=",
        countTransitionTargets(solver.coi.transitionTargetsByFrame),
        " cubes=",
        normalizedCubes.size(),
        " support_literals=",
        supportCube.size(),
        " frame_invariant_symbols=",
        data.frameInvariantSupport.size());
  }

  for (const auto& cube : normalizedCubes) {
    if (const auto knownCore =
            knownResetFrontierConflictCore(data, cube, postBootstrapSteps);
        knownCore.has_value()) {
      rememberResetFrontierUnreachableCore(data, targetFrame, *knownCore);
      continue;
    }
    if (findCachedResetFrontierUnreachableCore(data, targetFrame, cube)
            .has_value()) {
      continue;
    }
    const auto assumptions =
        stateCubeAssumptionLits(*solver.variables, cube, targetFrame);
    const auto status =
        solver.solver->solveWithAssumptionsStatus(
            assumptions, conflictLimit, propagationLimit);
    if (status == SATSolverWrapper::SolveStatus::Sat) {
      return true;
    }
    if (status == SATSolverWrapper::SolveStatus::Unknown) {
      if (isKInductionCoiDiagEnabled()) {
        emitSecDiag(
            "SEC diag: reset frontier target batch assumption proof "
            "resource_limit post_bootstrap_steps=",
            postBootstrapSteps,
            " solver_symbols=",
            solver.coi.solverSymbols.size(),
            " transition_targets=",
            countTransitionTargets(solver.coi.transitionTargetsByFrame),
            " cubes=",
            normalizedCubes.size());
      }
      return true;
    }
    if (const auto core = failedAssumptionCoreFromLastResetFrontierSolve(
            solver, cube, targetFrame);
        core.has_value()) {
      rememberResetFrontierUnreachableCore(data, targetFrame, *core);
    } else {
      rememberResetFrontierUnreachableCore(data, targetFrame, cube);
    }
  }
  return false;
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
  if (const auto knownCore = knownResetFrontierConflictCore(
          data, normalizedCube, postBootstrapSteps);
      knownCore.has_value()) {
    rememberResetFrontierUnreachableCore(data, targetFrame, *knownCore);
    return knownCore;
  }
  if (const auto cachedCore =
          findCachedResetFrontierUnreachableCore(data, targetFrame, normalizedCube);
      cachedCore.has_value()) {
    return cachedCore;
  }
  if (resetFrontierAssumptionSolvesDisabled()) {
    return std::nullopt;
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
