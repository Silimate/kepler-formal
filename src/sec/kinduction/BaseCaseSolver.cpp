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
#include <vector>

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

void mixHashValue(size_t& seed, size_t value) {
  seed ^= value + 0x9e3779b97f4a7c15ULL + (seed << 6) + (seed >> 2);
}

struct ResetFrontierSolverCacheKey {
  KEPLER_FORMAL::Config::SolverType solverType =
      KEPLER_FORMAL::Config::SolverType::KISSAT;
  size_t targetFrame = 0;
  bool includeCubeValues = false;
  std::vector<size_t> cubeSymbols;
  std::vector<std::pair<size_t, bool>> cubeLiterals;

  bool operator==(const ResetFrontierSolverCacheKey& other) const {
    return solverType == other.solverType &&
           targetFrame == other.targetFrame &&
           includeCubeValues == other.includeCubeValues &&
           cubeSymbols == other.cubeSymbols &&
           cubeLiterals == other.cubeLiterals;
  }
};

struct ResetFrontierSolverCacheKeyHash {
  size_t operator()(const ResetFrontierSolverCacheKey& key) const {
    size_t seed = std::hash<int>()(static_cast<int>(key.solverType));
    mixHashValue(seed, std::hash<size_t>()(key.targetFrame));
    mixHashValue(seed, std::hash<bool>()(key.includeCubeValues));
    for (const size_t symbol : key.cubeSymbols) {
      mixHashValue(seed, std::hash<size_t>()(symbol));
    }
    for (const auto& [symbol, value] : key.cubeLiterals) {
      mixHashValue(seed, std::hash<size_t>()(symbol));
      mixHashValue(seed, std::hash<bool>()(value));
    }
    return seed;
  }
};

bool resetFrontierAssumptionSolvesDisabled() {
  return std::getenv("KEPLER_SEC_PDR_DISABLE_RESET_FRONTIER_ASSUMPTIONS") !=
         nullptr;
}

SATSolverWrapper::SolveStatus solveResetFrontierUnitClauseQuery(  // LCOV_EXCL_LINE
    SATSolverWrapper& solver,
    KEPLER_FORMAL::Config::SolverType solverType,
    int64_t conflictLimit) {
  if (solverType == KEPLER_FORMAL::Config::SolverType::KISSAT &&  // LCOV_EXCL_LINE
      conflictLimit >= 0) {  // LCOV_EXCL_LINE
    return solver.solveWithKissatResourceLimits(  // LCOV_EXCL_LINE
        static_cast<unsigned>(conflictLimit));  // LCOV_EXCL_LINE
  }
  return solver.solveStatus();  // LCOV_EXCL_LINE
}  // LCOV_EXCL_LINE

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
  mutable std::unordered_map<
      ResetFrontierSolverCacheKey,
      std::unique_ptr<CachedResetFrontierSolver>,
      ResetFrontierSolverCacheKeyHash>
      cachedSolvers;
  // Shared-prefix reset-frontier queries check one cube against every concrete
  // post-bootstrap frame up to a depth. The COI depends only on the cube
  // symbols and max frame, so cache that exact solver separately from the
  // single-frontier cache and vary literal values through assumptions.
  mutable std::unordered_map<
      ResetFrontierSolverCacheKey,
      std::unique_ptr<CachedResetFrontierSolver>,
      ResetFrontierSolverCacheKeyHash>
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
  mutable std::unordered_map<
      ResetFrontierSolverCacheKey,
      CachedResetSummaryCoi,
      ResetFrontierSolverCacheKeyHash>
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
    throw std::runtime_error(  // LCOV_EXCL_LINE
        std::string("Missing BoolExpr while encoding base SEC formula: ") +  // LCOV_EXCL_LINE
        context);  // LCOV_EXCL_LINE
  }
  return formula->getSupportVars();
}  // LCOV_EXCL_LINE

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
    if (const auto primaryIt = primaryByComplement.find(symbol);  // LCOV_EXCL_LINE
        primaryIt != primaryByComplement.end() &&  // LCOV_EXCL_LINE
        transitionByState.contains(primaryIt->second)) {  // LCOV_EXCL_LINE
      expanded.insert(primaryIt->second);  // LCOV_EXCL_LINE
    }  // LCOV_EXCL_LINE
  }
  return sortedSymbols(expanded);
}

void closeFrameEqualityDependencies(
    const std::vector<std::pair<size_t, size_t>>& equalityPairs,
    std::unordered_set<size_t>& frameStates) {
  // Equality constraints can make a state bit relevant even if the bad cone
  // touches only its paired bit. Use the adjacency index so ASIC-sized startup
  // relations do not repeatedly rescan hundreds of thousands of unrelated
  // candidates while closing a small output COI.
  EqualityIndex(equalityPairs).close(frameStates);
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
}  // LCOV_EXCL_LINE

BaseCaseCoi buildStateCubePrefixReachabilityCoi(  // LCOV_EXCL_LINE
    const ResetFrontierReachabilityContextData& context,
    size_t maxTargetFrame,
    const std::vector<std::pair<size_t, bool>>& cube,
    bool closeStartupEqualityDependencies) {
  std::vector<size_t> targetFrames;  // LCOV_EXCL_LINE
  targetFrames.reserve(maxTargetFrame + 1 - context.bootstrapFrames);  // LCOV_EXCL_LINE
  for (size_t frame = context.bootstrapFrames; frame <= maxTargetFrame; ++frame) {  // LCOV_EXCL_LINE
    targetFrames.push_back(frame);  // LCOV_EXCL_LINE
  }  // LCOV_EXCL_LINE
  return buildStateCubeReachabilityCoiForTargetFrames(  // LCOV_EXCL_LINE
      context,  // LCOV_EXCL_LINE
      maxTargetFrame,  // LCOV_EXCL_LINE
      cube,  // LCOV_EXCL_LINE
      targetFrames,
      closeStartupEqualityDependencies);  // LCOV_EXCL_LINE
}  // LCOV_EXCL_LINE

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
    addFormulaSupport(context.frameInvariant, solverSymbols);  // LCOV_EXCL_LINE
    for (size_t frame = 0; frame <= postBootstrapSteps; ++frame) {  // LCOV_EXCL_LINE
      addFormulaStateSupport(  // LCOV_EXCL_LINE
          context.frameInvariant, stateSymbols, requiredStates[frame]);  // LCOV_EXCL_LINE
    }  // LCOV_EXCL_LINE
  }  // LCOV_EXCL_LINE

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
    addLiteralEquivalence(  // LCOV_EXCL_LINE
        solver,  // LCOV_EXCL_LINE
        lhs,  // LCOV_EXCL_LINE
        rhs);  // LCOV_EXCL_LINE
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
    const int lhs = variables.getLiteral(lhsSymbol, frame);  // LCOV_EXCL_LINE
    const int rhs = variables.getLiteral(rhsSymbol, frame);  // LCOV_EXCL_LINE
    if (lhs == rhs) {  // LCOV_EXCL_LINE
      continue;  // LCOV_EXCL_LINE
    }
    addLiteralEquivalence(solver, lhs, rhs);  // LCOV_EXCL_LINE
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
    addLiteralEquivalence(  // LCOV_EXCL_LINE
        solver,  // LCOV_EXCL_LINE
        lhs,  // LCOV_EXCL_LINE
        rhs);  // LCOV_EXCL_LINE
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
    addLiteralEquivalence(solver, lhs, rhs);  // LCOV_EXCL_LINE
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
    return environment;  // LCOV_EXCL_LINE
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
    return;  // LCOV_EXCL_LINE
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

KInductionProblem makeSingleObservedOutputProblem(  // LCOV_EXCL_LINE
    const KInductionProblem& problem,
    size_t outputIndex) {
  KInductionProblem single = problem;  // LCOV_EXCL_LINE
  single.observedOutputs =  // LCOV_EXCL_LINE
      outputIndex < problem.observedOutputs.size()  // LCOV_EXCL_LINE
          ? std::vector<SignalKey>{problem.observedOutputs[outputIndex]}  // LCOV_EXCL_LINE
          : std::vector<SignalKey>{};  // LCOV_EXCL_LINE
  single.observedOutputNames =  // LCOV_EXCL_LINE
      outputIndex < problem.observedOutputNames.size()  // LCOV_EXCL_LINE
          ? std::vector<std::string>{problem.observedOutputNames[outputIndex]}  // LCOV_EXCL_LINE
          : std::vector<std::string>{};  // LCOV_EXCL_LINE
  single.observedOutputExprs0 = {problem.observedOutputExprs0[outputIndex]};  // LCOV_EXCL_LINE
  single.observedOutputExprs1 = {problem.observedOutputExprs1[outputIndex]};  // LCOV_EXCL_LINE

  BoolExpr* outputBad = BoolExpr::simplify(  // LCOV_EXCL_LINE
      BoolExpr::Xor(  // LCOV_EXCL_LINE
          single.observedOutputExprs0.front(),  // LCOV_EXCL_LINE
          single.observedOutputExprs1.front()));  // LCOV_EXCL_LINE
  single.bad = outputBad;  // LCOV_EXCL_LINE
  single.property = BoolExpr::Not(outputBad);  // LCOV_EXCL_LINE
  single.inductionBad = outputBad;  // LCOV_EXCL_LINE
  single.inductionProperty = single.property;  // LCOV_EXCL_LINE
  return single;  // LCOV_EXCL_LINE
}  // LCOV_EXCL_LINE

std::optional<KInductionResult::CounterexampleWitness>
findPerOutputBaseCounterexampleAtFrontier(  // LCOV_EXCL_LINE
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    size_t k,
    std::optional<size_t> exactPublicBadFrame) {
  if (!exactPublicBadFrame.has_value() ||  // LCOV_EXCL_LINE
      problem.observedOutputExprs0.size() <= 1 ||  // LCOV_EXCL_LINE
      problem.observedOutputExprs0.size() != problem.observedOutputExprs1.size()) {  // LCOV_EXCL_LINE
    return std::nullopt;  // LCOV_EXCL_LINE
  }

  // Exact SEC validation asks whether any observed output is bad at one frame.
  // Solving the whole batch OR can force the SAT solver to reason across
  // unrelated output cones.  Match PDR's bad-cube search and validate each
  // output independently; the disjunction is SAT iff one per-output query is.
  for (size_t output = 0; output < problem.observedOutputExprs0.size(); ++output) {  // LCOV_EXCL_LINE
    KInductionProblem single =
        makeSingleObservedOutputProblem(problem, output);  // LCOV_EXCL_LINE
    if (auto witness = findBaseCounterexampleImpl(  // LCOV_EXCL_LINE
            single, solverType, k, exactPublicBadFrame);  // LCOV_EXCL_LINE
        witness.has_value()) {  // LCOV_EXCL_LINE
      return witness;  // LCOV_EXCL_LINE
    }
  }  // LCOV_EXCL_LINE
  return std::nullopt;  // LCOV_EXCL_LINE
}  // LCOV_EXCL_LINE

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
      problem.observedOutputExprs0.size() == problem.observedOutputExprs1.size()) {  // LCOV_EXCL_LINE
    return findPerOutputBaseCounterexampleAtFrontier(  // LCOV_EXCL_LINE
        problem, solverType, k, exactPublicBadFrame);  // LCOV_EXCL_LINE
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
      return std::nullopt;  // LCOV_EXCL_LINE
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

bool isStateCubeReachableAtResetFrontier(  // LCOV_EXCL_LINE
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    const std::vector<std::pair<size_t, bool>>& cube,
    size_t postBootstrapSteps) {
  const TransitionExprResolver transitionByState(problem);  // LCOV_EXCL_LINE
  return isStateCubeReachableAtResetFrontier(  // LCOV_EXCL_LINE
      problem, solverType, transitionByState, cube, postBootstrapSteps);  // LCOV_EXCL_LINE
}  // LCOV_EXCL_LINE

bool isStateCubeReachableAtResetFrontier(  // LCOV_EXCL_LINE
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    const TransitionExprResolver& transitionByState,
    const std::vector<std::pair<size_t, bool>>& cube,
    size_t postBootstrapSteps) {
  const auto context =
      makeResetFrontierReachabilityContext(problem, transitionByState);  // LCOV_EXCL_LINE
  return isStateCubeReachableAtResetFrontier(  // LCOV_EXCL_LINE
      *context, solverType, cube, postBootstrapSteps);  // LCOV_EXCL_LINE
}  // LCOV_EXCL_LINE

std::shared_ptr<ResetFrontierReachabilityContext>
makeResetFrontierReachabilityContext(
    const KInductionProblem& problem,
    const TransitionExprResolver& transitionByState,
    BoolExpr* frameInvariant) {
  return std::make_shared<ResetFrontierReachabilityContext>(
      std::make_shared<ResetFrontierReachabilityContextData>(
          problem, transitionByState, frameInvariant));
}  // LCOV_EXCL_LINE

void rememberResetFrontierUnreachableCore(
    const ResetFrontierReachabilityContextData& data,
    size_t targetFrame,
    std::vector<std::pair<size_t, bool>> core);

void rememberResetFrontierUnreachableCube(
    const ResetFrontierReachabilityContext& context,
    const std::vector<std::pair<size_t, bool>>& cube,
    size_t postBootstrapSteps) {
  if (cube.empty()) {
    return;  // LCOV_EXCL_LINE
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

std::vector<std::pair<size_t, bool>> sortedCubeLiterals(  // LCOV_EXCL_LINE
    std::vector<std::pair<size_t, bool>> cube) {
  std::sort(cube.begin(), cube.end());  // LCOV_EXCL_LINE
  cube.erase(std::unique(cube.begin(), cube.end()), cube.end());  // LCOV_EXCL_LINE
  return cube;  // LCOV_EXCL_LINE
}

ResetFrontierSolverCacheKey resetFrontierSolverCacheKey(
    KEPLER_FORMAL::Config::SolverType solverType,
    size_t targetFrame,
    const std::vector<std::pair<size_t, bool>>& cube,
    bool includeCubeValues) {
  ResetFrontierSolverCacheKey key;
  key.solverType = solverType;
  key.targetFrame = targetFrame;
  key.includeCubeValues = includeCubeValues;
  if (includeCubeValues) {
    key.cubeLiterals = sortedCubeLiterals(cube);  // LCOV_EXCL_LINE
  } else {  // LCOV_EXCL_LINE
    key.cubeSymbols = sortedCubeSymbols(cube);
  }
  return key;
}

const CachedResetSummaryCoi& getCachedResetSummaryCubeReachabilityCoi(
    const ResetFrontierReachabilityContextData& data,
    size_t postBootstrapSteps,
    const std::vector<std::pair<size_t, bool>>& cube) {
  const ResetFrontierSolverCacheKey key =
      resetFrontierSolverCacheKey(
          KEPLER_FORMAL::Config::SolverType::KISSAT,
          postBootstrapSteps,
          cube,
          /*includeCubeValues=*/false);
  if (const auto it = data.cachedResetSummaryCois.find(key);
      it != data.cachedResetSummaryCois.end()) {
    return it->second;  // LCOV_EXCL_LINE
  }

  if (data.cachedResetSummaryCois.size() >= kMaxResetSummaryCachedCois) {
    data.cachedResetSummaryCois.clear();  // LCOV_EXCL_LINE
  }  // LCOV_EXCL_LINE

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

  void addComplement(size_t lhs, size_t rhs) { unite(lhs, rhs, true); }  // LCOV_EXCL_LINE

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
      return;  // LCOV_EXCL_LINE
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
    relations.addComplement(primarySymbol, complementedSymbol);  // LCOV_EXCL_LINE
  }
  for (const auto& [primarySymbol, complementedSymbol] :
       data.problem.complementedStatePairs1) {
    relations.addComplement(primarySymbol, complementedSymbol);  // LCOV_EXCL_LINE
  }

  std::unordered_map<size_t, bool> rootAssignments;
  rootAssignments.reserve(assignments.size());
  for (const auto& [symbol, value] : assignments) {
    const auto [root, parity] = relations.findWithParity(symbol);
    const bool rootValue = value ^ parity;
    if (const auto it = rootAssignments.find(root);
        it != rootAssignments.end() && it->second != rootValue) {
      continue;  // LCOV_EXCL_LINE
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
      continue;  // LCOV_EXCL_LINE
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
    return std::nullopt;  // LCOV_EXCL_LINE
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
    return std::nullopt;  // LCOV_EXCL_LINE
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
    return;  // LCOV_EXCL_LINE
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
    cores.erase(cores.begin());  // LCOV_EXCL_LINE
  }  // LCOV_EXCL_LINE
  cores.push_back(std::move(core));
}

std::optional<std::vector<std::pair<size_t, bool>>>
extractUnreachableCoreFromCachedResetFrontierSolver(  // LCOV_EXCL_LINE
    CachedResetFrontierSolver& cached,
    const std::vector<std::pair<size_t, bool>>& cube,
    size_t targetFrame) {
  if (cached.cubeEncodedAsUnitClauses) {  // LCOV_EXCL_LINE
    return cached.solver->solve() ? std::nullopt : std::optional{cube};  // LCOV_EXCL_LINE
  }

  std::vector<int> assumptions;  // LCOV_EXCL_LINE
  assumptions.reserve(cube.size());  // LCOV_EXCL_LINE
  std::unordered_map<int, std::pair<size_t, bool>> cubeLiteralByAssumption;  // LCOV_EXCL_LINE
  cubeLiteralByAssumption.reserve(cube.size());  // LCOV_EXCL_LINE
  for (const auto& [symbol, value] : cube) {  // LCOV_EXCL_LINE
    const int literal = cached.variables->getLiteral(symbol, targetFrame);  // LCOV_EXCL_LINE
    const int assumption = value ? literal : -literal;  // LCOV_EXCL_LINE
    assumptions.push_back(assumption);  // LCOV_EXCL_LINE
    cubeLiteralByAssumption.emplace(assumption, std::pair{symbol, value});  // LCOV_EXCL_LINE
  }

  if (cached.solver->solveWithAssumptions(assumptions)) {  // LCOV_EXCL_LINE
    return std::nullopt;  // LCOV_EXCL_LINE
  }

  std::vector<std::pair<size_t, bool>> core;  // LCOV_EXCL_LINE
  for (const int failedAssumption : cached.solver->failedAssumptions()) {  // LCOV_EXCL_LINE
    const auto it = cubeLiteralByAssumption.find(failedAssumption);  // LCOV_EXCL_LINE
    if (it != cubeLiteralByAssumption.end()) {  // LCOV_EXCL_LINE
      core.push_back(it->second);  // LCOV_EXCL_LINE
    }  // LCOV_EXCL_LINE
  }
  if (core.empty()) {  // LCOV_EXCL_LINE
    // Some solver backends / conflict shapes do not expose a mapped failed
    // assumption core. Start from the full cube and still run exact deletion
    // minimization below; every accepted drop is checked by SAT.
    core = cube;  // LCOV_EXCL_LINE
  }  // LCOV_EXCL_LINE
  core = normalizedAssignmentCube(std::move(core));  // LCOV_EXCL_LINE
  auto coreIsReachable =
      [&](const std::vector<std::pair<size_t, bool>>& candidate) {  // LCOV_EXCL_LINE
        return cached.solver->solveWithAssumptions(  // LCOV_EXCL_LINE
            stateCubeAssumptionLits(*cached.variables, candidate, targetFrame));  // LCOV_EXCL_LINE
      };  // LCOV_EXCL_LINE

  // The assumption solver reports a valid conflict subset, not a guaranteed-minimal one.
  // Minimize it exactly with the same cached reset-frontier solver; the result
  // becomes a stronger PDR F[0] refinement and a reusable cache entry for later
  // neighboring cubes.
  size_t checks = 0;  // LCOV_EXCL_LINE
  const size_t maxChecks =  // LCOV_EXCL_LINE
      std::max(kMinResetFrontierCoreChecks, core.size() * 2);  // LCOV_EXCL_LINE
  for (size_t chunkSize = std::max<size_t>(1, core.size() / 2);  // LCOV_EXCL_LINE
       chunkSize > 0 && checks < maxChecks;) {  // LCOV_EXCL_LINE
    for (size_t index = 0; index < core.size() && checks < maxChecks;) {  // LCOV_EXCL_LINE
      const size_t erasedCount = std::min(chunkSize, core.size() - index);  // LCOV_EXCL_LINE
      if (erasedCount == 0 || erasedCount == core.size()) {  // LCOV_EXCL_LINE
        break;  // LCOV_EXCL_LINE
      }
      std::vector<std::pair<size_t, bool>> reduced = core;  // LCOV_EXCL_LINE
      reduced.erase(  // LCOV_EXCL_LINE
          reduced.begin() + static_cast<std::ptrdiff_t>(index),  // LCOV_EXCL_LINE
          reduced.begin() +  // LCOV_EXCL_LINE
              static_cast<std::ptrdiff_t>(index + erasedCount));  // LCOV_EXCL_LINE
      ++checks;  // LCOV_EXCL_LINE
      if (!coreIsReachable(reduced)) {  // LCOV_EXCL_LINE
        core = std::move(reduced);  // LCOV_EXCL_LINE
        continue;  // LCOV_EXCL_LINE
      }
      index += erasedCount;  // LCOV_EXCL_LINE
    }  // LCOV_EXCL_LINE
    if (chunkSize == 1) {  // LCOV_EXCL_LINE
      break;  // LCOV_EXCL_LINE
    }
    chunkSize = std::max<size_t>(1, chunkSize / 2);  // LCOV_EXCL_LINE
  }
  return core;  // LCOV_EXCL_LINE
}  // LCOV_EXCL_LINE

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

std::unique_ptr<CachedResetFrontierSolver> buildResetFrontierSolverForCoi(  // LCOV_EXCL_LINE
    const ResetFrontierReachabilityContextData& data,
    KEPLER_FORMAL::Config::SolverType solverType,
    BaseCaseCoi coi,
    const std::vector<std::pair<size_t, bool>>& cube,
    size_t targetFrame) {
  auto cached = std::make_unique<CachedResetFrontierSolver>();  // LCOV_EXCL_LINE
  cached->solverType = solverType;  // LCOV_EXCL_LINE
  cached->targetFrame = targetFrame;  // LCOV_EXCL_LINE
  cached->coi = std::move(coi);  // LCOV_EXCL_LINE
  const FrameSymbolAliases aliasesByFrame =
      buildResetFrontierFrameAliases(data, cached->coi, targetFrame + 1);  // LCOV_EXCL_LINE

  const auto& problem = data.problem;  // LCOV_EXCL_LINE
  cached->solver = std::make_unique<SATSolverWrapper>(solverType);  // LCOV_EXCL_LINE
  cached->solver->configureForSecPdrQuery(cached->coi.solverSymbols.size());  // LCOV_EXCL_LINE
  cached->variables = std::make_unique<FrameVariableStore>(  // LCOV_EXCL_LINE
      *cached->solver,  // LCOV_EXCL_LINE
      cached->coi.solverSymbols,  // LCOV_EXCL_LINE
      targetFrame + 1,  // LCOV_EXCL_LINE
      aliasesByFrame);
  addResetBootstrapConstraints(  // LCOV_EXCL_LINE
      *cached->solver, *cached->variables, problem, targetFrame + 1);  // LCOV_EXCL_LINE
  addInitialConstraints(  // LCOV_EXCL_LINE
      *cached->solver,  // LCOV_EXCL_LINE
      *cached->variables,  // LCOV_EXCL_LINE
      problem,  // LCOV_EXCL_LINE
      cached->coi.solverSymbolSet,  // LCOV_EXCL_LINE
      data.initialMode);  // LCOV_EXCL_LINE
  addComplementedStateRelations(  // LCOV_EXCL_LINE
      *cached->solver,  // LCOV_EXCL_LINE
      *cached->variables,  // LCOV_EXCL_LINE
      problem.complementedStatePairs0,  // LCOV_EXCL_LINE
      cached->coi.solverSymbolSet,  // LCOV_EXCL_LINE
      targetFrame + 1);  // LCOV_EXCL_LINE
  addComplementedStateRelations(  // LCOV_EXCL_LINE
      *cached->solver,  // LCOV_EXCL_LINE
      *cached->variables,  // LCOV_EXCL_LINE
      problem.complementedStatePairs1,  // LCOV_EXCL_LINE
      cached->coi.solverSymbolSet,  // LCOV_EXCL_LINE
      targetFrame + 1);  // LCOV_EXCL_LINE
  addInitialStateEqualities(  // LCOV_EXCL_LINE
      *cached->solver, *cached->variables, data, cached->coi.solverSymbolSet);  // LCOV_EXCL_LINE
  addResetFrontierFrameInvariantConstraints(  // LCOV_EXCL_LINE
      *cached->solver, *cached->variables, data, targetFrame);  // LCOV_EXCL_LINE

  for (size_t frame = 0; frame < targetFrame; ++frame) {  // LCOV_EXCL_LINE
    addTransitionRelation(  // LCOV_EXCL_LINE
        *cached->solver,  // LCOV_EXCL_LINE
        *cached->variables,  // LCOV_EXCL_LINE
        data.transitionByState,  // LCOV_EXCL_LINE
        cached->coi.transitionTargetsByFrame[frame],  // LCOV_EXCL_LINE
        frame);  // LCOV_EXCL_LINE
  }  // LCOV_EXCL_LINE
  if (data.bootstrapFrames != 0) {  // LCOV_EXCL_LINE
    addBootstrapStateAssignments(  // LCOV_EXCL_LINE
        *cached->solver,  // LCOV_EXCL_LINE
        *cached->variables,  // LCOV_EXCL_LINE
        problem,  // LCOV_EXCL_LINE
        cached->coi.solverSymbolSet,  // LCOV_EXCL_LINE
        data.bootstrapFrames);  // LCOV_EXCL_LINE
    addBootstrapStateEqualities(  // LCOV_EXCL_LINE
        *cached->solver,  // LCOV_EXCL_LINE
        *cached->variables,  // LCOV_EXCL_LINE
        data,  // LCOV_EXCL_LINE
        cached->coi.solverSymbolSet,  // LCOV_EXCL_LINE
        data.bootstrapFrames);  // LCOV_EXCL_LINE
  }  // LCOV_EXCL_LINE
  const size_t previousBlockers = addPreviousResetFrontierBlockers(  // LCOV_EXCL_LINE
      *cached->solver,  // LCOV_EXCL_LINE
      *cached->variables,  // LCOV_EXCL_LINE
      data,  // LCOV_EXCL_LINE
      cached->coi,  // LCOV_EXCL_LINE
      cube,  // LCOV_EXCL_LINE
      targetFrame);  // LCOV_EXCL_LINE
  if (previousBlockers != 0 && isKInductionCoiDiagEnabled()) {  // LCOV_EXCL_LINE
    emitSecDiag(  // LCOV_EXCL_LINE
        "SEC diag: reset frontier previous unreachable blockers=",
        previousBlockers,
        " target_frame=",
        targetFrame);
  }  // LCOV_EXCL_LINE

  cached->cubeEncodedAsUnitClauses = false;  // LCOV_EXCL_LINE
  return cached;  // LCOV_EXCL_LINE
}  // LCOV_EXCL_LINE

CachedResetFrontierSolver& getCachedResetFrontierPrefixSolver(  // LCOV_EXCL_LINE
    const ResetFrontierReachabilityContextData& data,
    KEPLER_FORMAL::Config::SolverType solverType,
    const std::vector<std::pair<size_t, bool>>& cube,
    size_t maxTargetFrame) {
  const auto cachedSolverType =  // LCOV_EXCL_LINE
      SATSolverWrapper::assumptionSolverTypeFor(solverType);  // LCOV_EXCL_LINE
  const ResetFrontierSolverCacheKey key =
      resetFrontierSolverCacheKey(  // LCOV_EXCL_LINE
          cachedSolverType,  // LCOV_EXCL_LINE
          maxTargetFrame,  // LCOV_EXCL_LINE
          cube,  // LCOV_EXCL_LINE
          /*includeCubeValues=*/false);
  if (const auto it = data.cachedPrefixSolvers.find(key);  // LCOV_EXCL_LINE
      it != data.cachedPrefixSolvers.end()) {  // LCOV_EXCL_LINE
    return *it->second;  // LCOV_EXCL_LINE
  }

  const auto cubeSymbols = sortedCubeSymbols(cube);  // LCOV_EXCL_LINE
  for (const auto& [_, cached] : data.cachedPrefixSolvers) {  // LCOV_EXCL_LINE
    if (cached->solverType == cachedSolverType &&  // LCOV_EXCL_LINE
        cached->targetFrame == maxTargetFrame &&  // LCOV_EXCL_LINE
        !cached->cubeEncodedAsUnitClauses &&  // LCOV_EXCL_LINE
        solverContainsCubeSymbols(*cached, cubeSymbols)) {  // LCOV_EXCL_LINE
      if (isKInductionCoiDiagEnabled()) {  // LCOV_EXCL_LINE
        emitSecDiag(  // LCOV_EXCL_LINE
            "SEC diag: reset frontier prefix solver superset cache hit ",
            "target_frame=",
            maxTargetFrame,
            " cube_literals=",
            cube.size(),  // LCOV_EXCL_LINE
            " solver_symbols=",
            cached->coi.solverSymbols.size());  // LCOV_EXCL_LINE
      }  // LCOV_EXCL_LINE
      return *cached;  // LCOV_EXCL_LINE
    }
  }

  if (data.cachedPrefixSolvers.size() >= kMaxResetFrontierCachedSolvers) {  // LCOV_EXCL_LINE
    data.cachedPrefixSolvers.clear();  // LCOV_EXCL_LINE
  }  // LCOV_EXCL_LINE

  auto cached = buildResetFrontierSolverForCoi(  // LCOV_EXCL_LINE
      data,  // LCOV_EXCL_LINE
      cachedSolverType,  // LCOV_EXCL_LINE
      buildStateCubePrefixReachabilityCoi(  // LCOV_EXCL_LINE
          data,  // LCOV_EXCL_LINE
          maxTargetFrame,  // LCOV_EXCL_LINE
          cube,  // LCOV_EXCL_LINE
          /*closeStartupEqualityDependencies=*/true),
      cube,  // LCOV_EXCL_LINE
      maxTargetFrame);  // LCOV_EXCL_LINE
  auto [it, inserted] =  // LCOV_EXCL_LINE
      data.cachedPrefixSolvers.emplace(key, std::move(cached));  // LCOV_EXCL_LINE
  (void)inserted;  // LCOV_EXCL_LINE
  return *it->second;  // LCOV_EXCL_LINE
}  // LCOV_EXCL_LINE

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
      return std::nullopt;  // LCOV_EXCL_LINE
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
    return std::nullopt;  // LCOV_EXCL_LINE
  }

  if (const auto knownCore = knownResetFrontierConflictCore(
          data, normalizedCube, /*postBootstrapSteps=*/0);
      knownCore.has_value()) {
    rememberResetFrontierUnreachableCore(  // LCOV_EXCL_LINE
        data, data.bootstrapFrames, *knownCore);  // LCOV_EXCL_LINE
    return knownCore;  // LCOV_EXCL_LINE
  }
  if (const auto cachedCore = findCachedResetFrontierUnreachableCore(
          data, data.bootstrapFrames, normalizedCube);
      cachedCore.has_value()) {
    return cachedCore;  // LCOV_EXCL_LINE
  }
  if (normalizedCube.size() > kMaxResetSummaryFrontierProofCubeLiterals) {
    if (isKInductionCoiDiagEnabled()) {  // LCOV_EXCL_LINE
      emitSecDiag(  // LCOV_EXCL_LINE
          "SEC diag: reset summary frontier proof skipped reason=cube_cap ",
          "frontier_cube=",
          normalizedCube.size(),  // LCOV_EXCL_LINE
          " max_literals=",
          kMaxResetSummaryFrontierProofCubeLiterals);
    }  // LCOV_EXCL_LINE
    return std::nullopt;  // LCOV_EXCL_LINE
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
    if (isKInductionCoiDiagEnabled()) {  // LCOV_EXCL_LINE
      emitSecDiag(  // LCOV_EXCL_LINE
          "SEC diag: reset summary frontier proof skipped reason=coi_cap ",
          "frontier_cube=",
          normalizedCube.size(),  // LCOV_EXCL_LINE
          " solver_symbols=",
          frontierCoi.solverSymbols.size(),  // LCOV_EXCL_LINE
          " transition_targets=",
          frontierTransitionTargets);
    }  // LCOV_EXCL_LINE
    return std::nullopt;  // LCOV_EXCL_LINE
  }

  // Summary CEGAR can ask many neighboring frontier questions with the same
  // symbol support. Reuse the exact reset-frontier solver and vary only the
  // assumptions; rebuilding it dominated BlackParrot PDR samples.
  CachedResetFrontierSolver& solver = getCachedResetFrontierSolver(
      data,
      SATSolverWrapper::assumptionSolverTypeFor(
          KEPLER_FORMAL::Config::getSolverType()),
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
    if (isKInductionCoiDiagEnabled()) {  // LCOV_EXCL_LINE
      emitSecDiag(  // LCOV_EXCL_LINE
          "SEC diag: reset summary frontier proof resource_limit ",
          "frontier_cube=",
          normalizedCube.size(),  // LCOV_EXCL_LINE
          " solver_symbols=",
          solver.coi.solverSymbols.size(),  // LCOV_EXCL_LINE
          " transition_targets=",
          frontierTransitionTargets);
    }  // LCOV_EXCL_LINE
    return std::nullopt;  // LCOV_EXCL_LINE
  }

  auto core = failedAssumptionCoreFromLastResetFrontierSolve(
      solver, normalizedCube, data.bootstrapFrames);
  if (!core.has_value()) {
    core = normalizedCube;  // LCOV_EXCL_LINE
  }  // LCOV_EXCL_LINE
  rememberResetFrontierUnreachableCore(data, data.bootstrapFrames, *core);
  return core;
}

std::vector<std::vector<std::pair<size_t, bool>>>
collectResetSummarySingletonFrontierBlockers(  // LCOV_EXCL_LINE
    const ResetFrontierReachabilityContextData& data,
    const std::vector<std::pair<size_t, bool>>& cube,
    const std::vector<std::vector<std::pair<size_t, bool>>>& existingBlockers,
    size_t maxNewBlockers) {
  std::vector<std::vector<std::pair<size_t, bool>>> blockers;  // LCOV_EXCL_LINE
  if (maxNewBlockers == 0) {  // LCOV_EXCL_LINE
    return blockers;  // LCOV_EXCL_LINE
  }

  CachedResetFrontierSolver& solver = getCachedResetFrontierSolver(  // LCOV_EXCL_LINE
      data,  // LCOV_EXCL_LINE
      SATSolverWrapper::assumptionSolverTypeFor(  // LCOV_EXCL_LINE
          KEPLER_FORMAL::Config::getSolverType()),  // LCOV_EXCL_LINE
      cube,  // LCOV_EXCL_LINE
      data.bootstrapFrames);  // LCOV_EXCL_LINE
  for (const auto& literal : cube) {  // LCOV_EXCL_LINE
    if (blockers.size() >= maxNewBlockers) {  // LCOV_EXCL_LINE
      break;  // LCOV_EXCL_LINE
    }

    std::vector<std::pair<size_t, bool>> singleton{literal};  // LCOV_EXCL_LINE
    if (std::any_of(  // LCOV_EXCL_LINE
            existingBlockers.begin(),  // LCOV_EXCL_LINE
            existingBlockers.end(),  // LCOV_EXCL_LINE
            [&](const auto& existing) {  // LCOV_EXCL_LINE
              return assignmentCubeContains(singleton, existing);  // LCOV_EXCL_LINE
            }) ||  // LCOV_EXCL_LINE
        std::any_of(  // LCOV_EXCL_LINE
            blockers.begin(),  // LCOV_EXCL_LINE
            blockers.end(),  // LCOV_EXCL_LINE
            [&](const auto& existing) {  // LCOV_EXCL_LINE
              return assignmentCubeContains(singleton, existing);  // LCOV_EXCL_LINE
            })) {
      continue;  // LCOV_EXCL_LINE
    }

    const auto status = solver.solver->solveWithAssumptionsStatus(  // LCOV_EXCL_LINE
        stateCubeAssumptionLits(  // LCOV_EXCL_LINE
            *solver.variables, singleton, data.bootstrapFrames),  // LCOV_EXCL_LINE
        kResetSummarySingletonProofConflictLimit);
    if (status != SATSolverWrapper::SolveStatus::Unsat) {  // LCOV_EXCL_LINE
      continue;  // LCOV_EXCL_LINE
    }

    rememberResetFrontierUnreachableCore(  // LCOV_EXCL_LINE
        data, data.bootstrapFrames, singleton);  // LCOV_EXCL_LINE
    blockers.push_back(std::move(singleton));  // LCOV_EXCL_LINE
  }  // LCOV_EXCL_LINE
  return blockers;  // LCOV_EXCL_LINE
}  // LCOV_EXCL_LINE

bool resetSummaryPrecheckProvesUnreachable(
    const ResetFrontierReachabilityContextData& data,
    KEPLER_FORMAL::Config::SolverType solverType,
    const std::vector<std::pair<size_t, bool>>& cube,
    size_t postBootstrapSteps) {
  if (resetFrontierAssumptionSolvesDisabled()) {
    return false;  // LCOV_EXCL_LINE
  }
  if (data.bootstrapFrames == 0 || postBootstrapSteps == 0) {
    return false;
  }
  if (solverType != KEPLER_FORMAL::Config::SolverType::KISSAT) {
    return false;  // LCOV_EXCL_LINE
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
    if (isKInductionCoiDiagEnabled()) {  // LCOV_EXCL_LINE
      emitSecDiag(  // LCOV_EXCL_LINE
          "SEC diag: reset summary one-shot precheck skipped "
          "reason=coi_cap post_bootstrap_steps=",
          postBootstrapSteps,
          " solver_symbols=",
          coi.solverSymbols.size(),  // LCOV_EXCL_LINE
          " transition_targets=",
          transitionTargets);
    }  // LCOV_EXCL_LINE
    return false;  // LCOV_EXCL_LINE
  }

  const auto& problem = data.problem;
  std::vector<std::vector<std::pair<size_t, bool>>> frontierBlockers;
  auto appendFrontierBlocker =
      [&](const std::vector<std::pair<size_t, bool>>& blocker) {
        if (frontierBlockers.size() >= kMaxResetSummaryFrontierBlockers) {
          return false;  // LCOV_EXCL_LINE
        }
        if (std::any_of(
                frontierBlockers.begin(),
                frontierBlockers.end(),
                [&](const auto& existing) {
                  return assignmentCubeContains(blocker, existing);
                })) {
          return false;  // LCOV_EXCL_LINE
        }
        frontierBlockers.push_back(blocker);
        return true;
      };
  if (const auto coresIt =
          data.unreachableCoresByTargetFrame.find(data.bootstrapFrames);
      coresIt != data.unreachableCoresByTargetFrame.end()) {
    for (const auto& core : coresIt->second) {
      if (frontierBlockers.size() >= kMaxResetSummaryFrontierBlockers) {
        break;  // LCOV_EXCL_LINE
      }
      if (!cubeSymbolsAreInSolverCoi(coi, core)) {
        continue;  // LCOV_EXCL_LINE
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
                           : variables.getLiteral(symbol, frame)});  // LCOV_EXCL_LINE
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
      for (size_t frame = 0; frame <= postBootstrapSteps; ++frame) {  // LCOV_EXCL_LINE
        FrameFormulaEncoder encoder(  // LCOV_EXCL_LINE
            solver, variables.makeLeafLits(frame, data.frameInvariantSupport));  // LCOV_EXCL_LINE
        solver.addClause({encoder.encode(data.frameInvariant)});  // LCOV_EXCL_LINE
      }  // LCOV_EXCL_LINE
    }  // LCOV_EXCL_LINE

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
        emitSecDiag(  // LCOV_EXCL_LINE
            "SEC diag: reset summary CEGAR proved unreachable "
            "post_bootstrap_steps=",
            postBootstrapSteps,
            " refinements=",
            refinement,
            " frontier_blockers=",
            frontierBlockers.size());  // LCOV_EXCL_LINE
      }  // LCOV_EXCL_LINE
      return true;
    }
    if (status == SATSolverWrapper::SolveStatus::Unknown) {
      if (isKInductionCoiDiagEnabled()) {  // LCOV_EXCL_LINE
        emitSecDiag(  // LCOV_EXCL_LINE
            "SEC diag: reset summary one-shot precheck resource_limit "
            "post_bootstrap_steps=",
            postBootstrapSteps,
            " solver_symbols=",
            coi.solverSymbols.size(),  // LCOV_EXCL_LINE
            " transition_targets=",
            transitionTargets);
      }  // LCOV_EXCL_LINE
      return false;  // LCOV_EXCL_LINE
    }
    if (refinement == kMaxResetSummaryRefinements ||
        frontierBlockers.size() >= kMaxResetSummaryFrontierBlockers) {
      return false;
    }

    const auto frontierCube =
        extractResetSummaryFrontierCube(data, solver, variables, coi);
    if (!frontierCube.has_value()) {
      if (isKInductionCoiDiagEnabled()) {  // LCOV_EXCL_LINE
        emitSecDiag(  // LCOV_EXCL_LINE
            "SEC diag: reset summary refinement skipped reason=frontier_cap "
            "post_bootstrap_steps=",
            postBootstrapSteps,
            " max_literals=",
            kMaxResetSummaryFrontierCubeLiterals);
      }  // LCOV_EXCL_LINE
      return false;  // LCOV_EXCL_LINE
    }
    const auto blocker =
        proveResetSummaryFrontierCubeUnreachable(data, *frontierCube);
    if (!blocker.has_value()) {
      return false;
    }
    size_t addedBlockers = appendFrontierBlocker(*blocker) ? 1 : 0;
    if (blocker->size() == 1 &&
        frontierBlockers.size() < kMaxResetSummaryFrontierBlockers) {  // LCOV_EXCL_LINE
      const size_t remainingBlockers =  // LCOV_EXCL_LINE
          kMaxResetSummaryFrontierBlockers - frontierBlockers.size();  // LCOV_EXCL_LINE
      const auto singletonBlockers =
          collectResetSummarySingletonFrontierBlockers(  // LCOV_EXCL_LINE
              data,  // LCOV_EXCL_LINE
              *frontierCube,  // LCOV_EXCL_LINE
              frontierBlockers,
              std::min(  // LCOV_EXCL_LINE
                  kMaxResetSummaryBulkSingletonBlockers,
                  remainingBlockers));
      for (const auto& singleton : singletonBlockers) {  // LCOV_EXCL_LINE
        if (appendFrontierBlocker(singleton)) {  // LCOV_EXCL_LINE
          ++addedBlockers;  // LCOV_EXCL_LINE
        }  // LCOV_EXCL_LINE
      }
    }  // LCOV_EXCL_LINE
    if (isKInductionCoiDiagEnabled()) {
      emitSecDiag(  // LCOV_EXCL_LINE
          "SEC diag: reset summary learned frontier blocker ",
          "post_bootstrap_steps=",
          postBootstrapSteps,
          " refinement=",
          refinement + 1,  // LCOV_EXCL_LINE
          " frontier_cube=",
          frontierCube->size(),  // LCOV_EXCL_LINE
          " blocker=",
          blocker->size(),  // LCOV_EXCL_LINE
          " added=",
          addedBlockers);
    }  // LCOV_EXCL_LINE
  }
  return false;  // LCOV_EXCL_LINE
}

CachedResetFrontierSolver& getCachedResetFrontierSolver(
    const ResetFrontierReachabilityContextData& data,
    KEPLER_FORMAL::Config::SolverType solverType,
    const std::vector<std::pair<size_t, bool>>& cube,
    size_t targetFrame) {
  // Reset-frontier checks are dominated by repeated neighboring cube queries.
  // Use the assumption-capable solver here even when the main SEC run selected
  // Kissat: otherwise every cube value has to be encoded as unit clauses in a
  // separate cached solver, which BlackParrot sampling showed growing to
  // multi-GB retained solver caches before PDR made progress.
  const bool encodeCubeAsUnitClauses = false;
  const auto cachedSolverType =
      SATSolverWrapper::assumptionSolverTypeFor(solverType);
  const ResetFrontierSolverCacheKey key =
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
    data.cachedSolvers.clear();  // LCOV_EXCL_LINE
  }  // LCOV_EXCL_LINE

  auto cached = buildResetFrontierSolver(
      data, cachedSolverType, cube, targetFrame, encodeCubeAsUnitClauses);
  auto [it, inserted] = data.cachedSolvers.emplace(key, std::move(cached));
  (void)inserted;
  return *it->second;
}

void primeResetFrontierReachabilitySolver(  // LCOV_EXCL_LINE
    const ResetFrontierReachabilityContext& context,
    KEPLER_FORMAL::Config::SolverType solverType,
    const std::vector<std::pair<size_t, bool>>& cube,
    size_t postBootstrapSteps) {
  if (cube.empty()) {  // LCOV_EXCL_LINE
    return;  // LCOV_EXCL_LINE
  }

  const auto& data = *context.data;  // LCOV_EXCL_LINE
  const size_t targetFrame = data.bootstrapFrames + postBootstrapSteps;  // LCOV_EXCL_LINE
  const auto normalizedCube = normalizedAssignmentCube(cube);  // LCOV_EXCL_LINE
  (void)getCachedResetFrontierSolver(  // LCOV_EXCL_LINE
      data, solverType, normalizedCube, targetFrame);  // LCOV_EXCL_LINE
}  // LCOV_EXCL_LINE

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
            isKInductionCoiDiagEnabled()) {  // LCOV_EXCL_LINE
          emitSecDiag(  // LCOV_EXCL_LINE
              "SEC diag: reset frontier relaxed cached precheck "
              "resource_limit post_bootstrap_steps=",
              postBootstrapSteps,
              " solver_symbols=",
              relaxedSolver->coi.solverSymbols.size(),  // LCOV_EXCL_LINE
              " transition_targets=",
              relaxedTransitionTargets);
        }  // LCOV_EXCL_LINE
      } else {
        relaxedUnsat = !relaxedSolver->solver->solve();  // LCOV_EXCL_LINE
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
      rememberResetFrontierUnreachableCore(data, targetFrame, normalizedCube);  // LCOV_EXCL_LINE
      return false;  // LCOV_EXCL_LINE
    }
  }
  if (resetFrontierAssumptionSolvesDisabled()) {
    auto unitSolver = buildResetFrontierSolver(  // LCOV_EXCL_LINE
        data,  // LCOV_EXCL_LINE
        solverType,  // LCOV_EXCL_LINE
        normalizedCube,
        targetFrame,  // LCOV_EXCL_LINE
        /*encodeCubeAsUnitClauses=*/true);
    const int64_t conflictLimit =  // LCOV_EXCL_LINE
        postBootstrapSteps == 0 && startupConflictLimit >= 0  // LCOV_EXCL_LINE
            ? startupConflictLimit  // LCOV_EXCL_LINE
            : static_cast<int64_t>(kResetFrontierCachedAssumptionConflictLimit);
    const auto status = solveResetFrontierUnitClauseQuery(  // LCOV_EXCL_LINE
        *unitSolver->solver, solverType, conflictLimit);  // LCOV_EXCL_LINE
    if (status == SATSolverWrapper::SolveStatus::Unknown) {  // LCOV_EXCL_LINE
      if (isKInductionCoiDiagEnabled()) {  // LCOV_EXCL_LINE
        emitSecDiag(  // LCOV_EXCL_LINE
            "SEC diag: reset frontier unit-clause proof resource_limit ",
            "post_bootstrap_steps=",
            postBootstrapSteps,
            " solver_symbols=",
            unitSolver->coi.solverSymbols.size(),  // LCOV_EXCL_LINE
            " transition_targets=",
            countTransitionTargets(unitSolver->coi.transitionTargetsByFrame),  // LCOV_EXCL_LINE
            " cube_literals=",
            normalizedCube.size());  // LCOV_EXCL_LINE
      }  // LCOV_EXCL_LINE
      return true;  // LCOV_EXCL_LINE
    }
    const bool reachable = status == SATSolverWrapper::SolveStatus::Sat;  // LCOV_EXCL_LINE
    if (!reachable) {  // LCOV_EXCL_LINE
      rememberResetFrontierUnreachableCore(data, targetFrame, normalizedCube);  // LCOV_EXCL_LINE
    }  // LCOV_EXCL_LINE
    return reachable;  // LCOV_EXCL_LINE
  }  // LCOV_EXCL_LINE

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
    status = cached.solver->solveStatus();  // LCOV_EXCL_LINE
  } else {  // LCOV_EXCL_LINE
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
    if (isKInductionCoiDiagEnabled()) {  // LCOV_EXCL_LINE
      emitSecDiag(  // LCOV_EXCL_LINE
          "SEC diag: reset frontier cached assumption proof resource_limit ",
          "post_bootstrap_steps=",
          postBootstrapSteps,
          " solver_symbols=",
          cached.coi.solverSymbols.size(),  // LCOV_EXCL_LINE
          " transition_targets=",
          countTransitionTargets(cached.coi.transitionTargetsByFrame),  // LCOV_EXCL_LINE
          " cube_literals=",
          normalizedCube.size());  // LCOV_EXCL_LINE
    }  // LCOV_EXCL_LINE
    return true;  // LCOV_EXCL_LINE
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
        rememberResetFrontierUnreachableCore(  // LCOV_EXCL_LINE
            data, targetFrame, normalizedCube);  // LCOV_EXCL_LINE
      }
    } else if (const auto core =
                   failedAssumptionCoreFromLastResetFrontierSolve(  // LCOV_EXCL_LINE
                       cached, normalizedCube, targetFrame);  // LCOV_EXCL_LINE
               core.has_value()) {  // LCOV_EXCL_LINE
      // Post-bootstrap prechecks are on the hot PDR path.  Reuse the
      // assumption core already produced by this UNSAT query, but avoid the
      // extra minimization SAT calls reserved for the exact reset frontier.
      rememberResetFrontierUnreachableCore(data, targetFrame, *core);  // LCOV_EXCL_LINE
    }  // LCOV_EXCL_LINE
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
    return true;  // LCOV_EXCL_LINE
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
    return false;  // LCOV_EXCL_LINE
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
            isKInductionCoiDiagEnabled()) {  // LCOV_EXCL_LINE
          emitSecDiag(  // LCOV_EXCL_LINE
              "SEC diag: reset frontier relaxed one-shot precheck "
              "resource_limit post_bootstrap_steps=",
              postBootstrapSteps,
              " solver_symbols=",
              relaxedSolver->coi.solverSymbols.size(),  // LCOV_EXCL_LINE
              " transition_targets=",
              relaxedTransitionTargets);
        }  // LCOV_EXCL_LINE
      } else {
        relaxedUnsat = !relaxedSolver->solver->solve();  // LCOV_EXCL_LINE
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
    auto solver = buildResetFrontierSolver(  // LCOV_EXCL_LINE
        data,  // LCOV_EXCL_LINE
        solverType,  // LCOV_EXCL_LINE
        normalizedCube,
        targetFrame,  // LCOV_EXCL_LINE
        /*encodeCubeAsUnitClauses=*/true);
    const int64_t conflictLimit =  // LCOV_EXCL_LINE
        postBootstrapSteps == 0  // LCOV_EXCL_LINE
            ? -1
            : static_cast<int64_t>(kResetFrontierCachedAssumptionConflictLimit);
    const auto status = solveResetFrontierUnitClauseQuery(  // LCOV_EXCL_LINE
        *solver->solver, solverType, conflictLimit);  // LCOV_EXCL_LINE
    if (status == SATSolverWrapper::SolveStatus::Unknown) {  // LCOV_EXCL_LINE
      if (isKInductionCoiDiagEnabled()) {  // LCOV_EXCL_LINE
        emitSecDiag(  // LCOV_EXCL_LINE
            "SEC diag: reset frontier one-shot unit-clause resource_limit ",
            "post_bootstrap_steps=",
            postBootstrapSteps,
            " solver_symbols=",
            solver->coi.solverSymbols.size(),  // LCOV_EXCL_LINE
            " transition_targets=",
            countTransitionTargets(solver->coi.transitionTargetsByFrame),  // LCOV_EXCL_LINE
            " cube_literals=",
            normalizedCube.size());  // LCOV_EXCL_LINE
      }  // LCOV_EXCL_LINE
      return true;  // LCOV_EXCL_LINE
    }
    const bool reachable = status == SATSolverWrapper::SolveStatus::Sat;  // LCOV_EXCL_LINE
    if (!reachable) {  // LCOV_EXCL_LINE
      rememberResetFrontierUnreachableCore(data, targetFrame, normalizedCube);  // LCOV_EXCL_LINE
    }  // LCOV_EXCL_LINE
    return reachable;  // LCOV_EXCL_LINE
  }  // LCOV_EXCL_LINE

  const auto assumptionSolverType =
      SATSolverWrapper::assumptionSolverTypeFor(solverType);
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
      rememberResetFrontierUnreachableCore(data, targetFrame, normalizedCube);  // LCOV_EXCL_LINE
    }
  }
  return reachable;
}

bool isStateCubeReachableWithinResetFrontier(  // LCOV_EXCL_LINE
    const ResetFrontierReachabilityContext& context,
    KEPLER_FORMAL::Config::SolverType solverType,
    const std::vector<std::pair<size_t, bool>>& cube,
    size_t maxPostBootstrapSteps) {
  if (cube.empty()) {  // LCOV_EXCL_LINE
    return true;  // LCOV_EXCL_LINE
  }

  const auto& data = *context.data;  // LCOV_EXCL_LINE
  const auto normalizedCube = normalizedAssignmentCube(cube);  // LCOV_EXCL_LINE
  std::vector<size_t> uncheckedSteps;  // LCOV_EXCL_LINE
  uncheckedSteps.reserve(maxPostBootstrapSteps + 1);  // LCOV_EXCL_LINE
  for (size_t step = 0; step <= maxPostBootstrapSteps; ++step) {  // LCOV_EXCL_LINE
    const size_t targetFrame = data.bootstrapFrames + step;  // LCOV_EXCL_LINE
    if (const auto knownCore =  // LCOV_EXCL_LINE
            knownResetFrontierConflictCore(data, normalizedCube, step);  // LCOV_EXCL_LINE
        knownCore.has_value()) {  // LCOV_EXCL_LINE
      rememberResetFrontierUnreachableCore(data, targetFrame, *knownCore);  // LCOV_EXCL_LINE
      continue;  // LCOV_EXCL_LINE
    }
    if (findCachedResetFrontierUnreachableCore(  // LCOV_EXCL_LINE
            data, targetFrame, normalizedCube)  // LCOV_EXCL_LINE
            .has_value()) {  // LCOV_EXCL_LINE
      continue;  // LCOV_EXCL_LINE
    }
    uncheckedSteps.push_back(step);  // LCOV_EXCL_LINE
  }  // LCOV_EXCL_LINE
  if (uncheckedSteps.empty()) {  // LCOV_EXCL_LINE
    return false;  // LCOV_EXCL_LINE
  }

  std::vector<size_t> remainingSteps;  // LCOV_EXCL_LINE
  remainingSteps.reserve(uncheckedSteps.size());  // LCOV_EXCL_LINE
  for (const auto step : uncheckedSteps) {  // LCOV_EXCL_LINE
    if (step != 0 &&  // LCOV_EXCL_LINE
        resetSummaryPrecheckProvesUnreachable(  // LCOV_EXCL_LINE
            data, solverType, normalizedCube, step)) {  // LCOV_EXCL_LINE
      rememberResetFrontierUnreachableCore(  // LCOV_EXCL_LINE
          data, data.bootstrapFrames + step, normalizedCube);  // LCOV_EXCL_LINE
      continue;  // LCOV_EXCL_LINE
    }
    remainingSteps.push_back(step);  // LCOV_EXCL_LINE
  }
  if (remainingSteps.empty()) {  // LCOV_EXCL_LINE
    return false;  // LCOV_EXCL_LINE
  }
  if (resetFrontierAssumptionSolvesDisabled() ||  // LCOV_EXCL_LINE
      remainingSteps.size() <= kMaxSparseResetFrontierPerStepChecks) {  // LCOV_EXCL_LINE
    for (const auto step : remainingSteps) {  // LCOV_EXCL_LINE
      if (isStateCubeReachableAtResetFrontier(  // LCOV_EXCL_LINE
              context,  // LCOV_EXCL_LINE
              solverType,  // LCOV_EXCL_LINE
              normalizedCube,
              step,  // LCOV_EXCL_LINE
              /*usePostBootstrapPrechecks=*/false)) {
        return true;  // LCOV_EXCL_LINE
      }
    }
    return false;  // LCOV_EXCL_LINE
  }

  const size_t maxTargetFrame =  // LCOV_EXCL_LINE
      data.bootstrapFrames + maxPostBootstrapSteps;  // LCOV_EXCL_LINE
  CachedResetFrontierSolver& solver = getCachedResetFrontierPrefixSolver(  // LCOV_EXCL_LINE
      data, solverType, normalizedCube, maxTargetFrame);  // LCOV_EXCL_LINE

  if (isKInductionCoiDiagEnabled()) {  // LCOV_EXCL_LINE
    emitSecDiag(  // LCOV_EXCL_LINE
        "SEC diag: reset frontier prefix cube coi max_post_bootstrap_steps=",
        maxPostBootstrapSteps,
        " frames=",
        maxTargetFrame + 1,  // LCOV_EXCL_LINE
        " solver_symbols=",
        solver.coi.solverSymbols.size(),  // LCOV_EXCL_LINE
        " transition_targets=",
        countTransitionTargets(solver.coi.transitionTargetsByFrame),  // LCOV_EXCL_LINE
        " cube_literals=",
        normalizedCube.size(),  // LCOV_EXCL_LINE
        " unchecked_steps=",
        remainingSteps.size(),  // LCOV_EXCL_LINE
        " frame_invariant_symbols=",
        data.frameInvariantSupport.size());  // LCOV_EXCL_LINE
  }  // LCOV_EXCL_LINE

  for (const auto step : remainingSteps) {  // LCOV_EXCL_LINE
    const size_t targetFrame = data.bootstrapFrames + step;  // LCOV_EXCL_LINE
    const auto assumptions =
        stateCubeAssumptionLits(*solver.variables, normalizedCube, targetFrame);  // LCOV_EXCL_LINE
    const auto status =  // LCOV_EXCL_LINE
        step == 0  // LCOV_EXCL_LINE
            ? solver.solver->solveWithAssumptionsStatus(assumptions)  // LCOV_EXCL_LINE
            : solver.solver->solveWithAssumptionsStatus(  // LCOV_EXCL_LINE
                  assumptions, kResetFrontierCachedAssumptionConflictLimit);
    if (status == SATSolverWrapper::SolveStatus::Unknown) {  // LCOV_EXCL_LINE
      if (isKInductionCoiDiagEnabled()) {  // LCOV_EXCL_LINE
        emitSecDiag(  // LCOV_EXCL_LINE
            "SEC diag: reset frontier prefix assumption proof resource_limit ",
            "post_bootstrap_steps=",
            step,
            " max_post_bootstrap_steps=",
            maxPostBootstrapSteps,
            " solver_symbols=",
            solver.coi.solverSymbols.size(),  // LCOV_EXCL_LINE
            " transition_targets=",
            countTransitionTargets(solver.coi.transitionTargetsByFrame),  // LCOV_EXCL_LINE
            " cube_literals=",
            normalizedCube.size());  // LCOV_EXCL_LINE
      }  // LCOV_EXCL_LINE
      return true;  // LCOV_EXCL_LINE
    }
    if (status == SATSolverWrapper::SolveStatus::Sat) {  // LCOV_EXCL_LINE
      return true;  // LCOV_EXCL_LINE
    }
    if (const auto core = failedAssumptionCoreFromLastResetFrontierSolve(  // LCOV_EXCL_LINE
            solver, normalizedCube, targetFrame);  // LCOV_EXCL_LINE
        core.has_value()) {  // LCOV_EXCL_LINE
      rememberResetFrontierUnreachableCore(data, targetFrame, *core);  // LCOV_EXCL_LINE
    } else {  // LCOV_EXCL_LINE
      rememberResetFrontierUnreachableCore(data, targetFrame, normalizedCube);  // LCOV_EXCL_LINE
    }
  }  // LCOV_EXCL_LINE
  return false;  // LCOV_EXCL_LINE
}  // LCOV_EXCL_LINE

std::vector<std::pair<size_t, bool>> supportCubeForAssignmentCubes(  // LCOV_EXCL_LINE
    const std::vector<std::vector<std::pair<size_t, bool>>>& cubes) {
  std::unordered_map<size_t, bool> valueBySymbol;  // LCOV_EXCL_LINE
  for (const auto& cube : cubes) {  // LCOV_EXCL_LINE
    for (const auto& [symbol, value] : cube) {  // LCOV_EXCL_LINE
      valueBySymbol.emplace(symbol, value);  // LCOV_EXCL_LINE
    }
  }

  std::vector<std::pair<size_t, bool>> supportCube;  // LCOV_EXCL_LINE
  supportCube.reserve(valueBySymbol.size());  // LCOV_EXCL_LINE
  for (const auto& [symbol, value] : valueBySymbol) {  // LCOV_EXCL_LINE
    supportCube.emplace_back(symbol, value);  // LCOV_EXCL_LINE
  }
  return normalizedAssignmentCube(std::move(supportCube));  // LCOV_EXCL_LINE
}  // LCOV_EXCL_LINE

bool anyStateCubeReachableWithinResetFrontier(  // LCOV_EXCL_LINE
    const ResetFrontierReachabilityContext& context,
    KEPLER_FORMAL::Config::SolverType solverType,
    const std::vector<std::vector<std::pair<size_t, bool>>>& cubes,
    size_t maxPostBootstrapSteps) {
  std::vector<std::vector<std::pair<size_t, bool>>> normalizedCubes;  // LCOV_EXCL_LINE
  normalizedCubes.reserve(cubes.size());  // LCOV_EXCL_LINE
  for (auto cube : cubes) {  // LCOV_EXCL_LINE
    cube = normalizedAssignmentCube(std::move(cube));  // LCOV_EXCL_LINE
    if (cube.empty()) {  // LCOV_EXCL_LINE
      return true;  // LCOV_EXCL_LINE
    }
    normalizedCubes.push_back(std::move(cube));  // LCOV_EXCL_LINE
  }  // LCOV_EXCL_LINE
  if (normalizedCubes.empty()) {  // LCOV_EXCL_LINE
    return false;  // LCOV_EXCL_LINE
  }

  const auto& data = *context.data;  // LCOV_EXCL_LINE
  const size_t maxTargetFrame = data.bootstrapFrames + maxPostBootstrapSteps;  // LCOV_EXCL_LINE
  const std::vector<std::pair<size_t, bool>> supportCube =
      supportCubeForAssignmentCubes(normalizedCubes);  // LCOV_EXCL_LINE
  if (supportCube.empty()) {  // LCOV_EXCL_LINE
    return true;  // LCOV_EXCL_LINE
  }

  CachedResetFrontierSolver& solver = getCachedResetFrontierPrefixSolver(  // LCOV_EXCL_LINE
      data, solverType, supportCube, maxTargetFrame);  // LCOV_EXCL_LINE

  if (isKInductionCoiDiagEnabled()) {  // LCOV_EXCL_LINE
    emitSecDiag(  // LCOV_EXCL_LINE
        "SEC diag: reset frontier batch cube coi max_post_bootstrap_steps=",
        maxPostBootstrapSteps,
        " frames=",
        maxTargetFrame + 1,  // LCOV_EXCL_LINE
        " solver_symbols=",
        solver.coi.solverSymbols.size(),  // LCOV_EXCL_LINE
        " transition_targets=",
        countTransitionTargets(solver.coi.transitionTargetsByFrame),  // LCOV_EXCL_LINE
        " cubes=",
        normalizedCubes.size(),  // LCOV_EXCL_LINE
        " support_literals=",
        supportCube.size(),  // LCOV_EXCL_LINE
        " frame_invariant_symbols=",
        data.frameInvariantSupport.size());  // LCOV_EXCL_LINE
  }  // LCOV_EXCL_LINE

  for (size_t step = 0; step <= maxPostBootstrapSteps; ++step) {  // LCOV_EXCL_LINE
    const size_t targetFrame = data.bootstrapFrames + step;  // LCOV_EXCL_LINE
    for (const auto& cube : normalizedCubes) {  // LCOV_EXCL_LINE
      if (const auto knownCore =  // LCOV_EXCL_LINE
              knownResetFrontierConflictCore(data, cube, step);  // LCOV_EXCL_LINE
          knownCore.has_value()) {  // LCOV_EXCL_LINE
        rememberResetFrontierUnreachableCore(data, targetFrame, *knownCore);  // LCOV_EXCL_LINE
        continue;  // LCOV_EXCL_LINE
      }
      if (findCachedResetFrontierUnreachableCore(data, targetFrame, cube)  // LCOV_EXCL_LINE
              .has_value()) {  // LCOV_EXCL_LINE
        continue;  // LCOV_EXCL_LINE
      }
      const auto assumptions =
          stateCubeAssumptionLits(*solver.variables, cube, targetFrame);  // LCOV_EXCL_LINE
      const auto status =  // LCOV_EXCL_LINE
          step == 0  // LCOV_EXCL_LINE
              ? solver.solver->solveWithAssumptionsStatus(assumptions)  // LCOV_EXCL_LINE
              : solver.solver->solveWithAssumptionsStatus(  // LCOV_EXCL_LINE
                    assumptions,
                    kResetFrontierCachedAssumptionConflictLimit,
                    kResetFrontierBatchProofPropagationLimit);
      if (status == SATSolverWrapper::SolveStatus::Sat) {  // LCOV_EXCL_LINE
        return true;  // LCOV_EXCL_LINE
      }
      if (status == SATSolverWrapper::SolveStatus::Unknown) {  // LCOV_EXCL_LINE
        if (isKInductionCoiDiagEnabled()) {  // LCOV_EXCL_LINE
          emitSecDiag(  // LCOV_EXCL_LINE
              "SEC diag: reset frontier batch assumption proof resource_limit ",
              "post_bootstrap_steps=",
              step,
              " max_post_bootstrap_steps=",
              maxPostBootstrapSteps,
              " solver_symbols=",
              solver.coi.solverSymbols.size(),  // LCOV_EXCL_LINE
              " transition_targets=",
              countTransitionTargets(solver.coi.transitionTargetsByFrame),  // LCOV_EXCL_LINE
              " cubes=",
              normalizedCubes.size());  // LCOV_EXCL_LINE
        }  // LCOV_EXCL_LINE
        return true;  // LCOV_EXCL_LINE
      }
      if (const auto core = failedAssumptionCoreFromLastResetFrontierSolve(  // LCOV_EXCL_LINE
              solver, cube, targetFrame);  // LCOV_EXCL_LINE
          core.has_value()) {  // LCOV_EXCL_LINE
        rememberResetFrontierUnreachableCore(data, targetFrame, *core);  // LCOV_EXCL_LINE
      } else {  // LCOV_EXCL_LINE
        rememberResetFrontierUnreachableCore(data, targetFrame, cube);  // LCOV_EXCL_LINE
      }
    }  // LCOV_EXCL_LINE
  }  // LCOV_EXCL_LINE
  return false;  // LCOV_EXCL_LINE
}  // LCOV_EXCL_LINE

bool anyStateCubeReachableAtResetFrontier(  // LCOV_EXCL_LINE
    const ResetFrontierReachabilityContext& context,
    KEPLER_FORMAL::Config::SolverType solverType,
    const std::vector<std::vector<std::pair<size_t, bool>>>& cubes,
    size_t postBootstrapSteps,
    long long conflictLimit,
    long long propagationLimit) {
  std::vector<std::vector<std::pair<size_t, bool>>> normalizedCubes;  // LCOV_EXCL_LINE
  normalizedCubes.reserve(cubes.size());  // LCOV_EXCL_LINE
  for (auto cube : cubes) {  // LCOV_EXCL_LINE
    cube = normalizedAssignmentCube(std::move(cube));  // LCOV_EXCL_LINE
    if (cube.empty()) {  // LCOV_EXCL_LINE
      return true;  // LCOV_EXCL_LINE
    }
    normalizedCubes.push_back(std::move(cube));  // LCOV_EXCL_LINE
  }  // LCOV_EXCL_LINE
  if (normalizedCubes.empty()) {  // LCOV_EXCL_LINE
    return false;  // LCOV_EXCL_LINE
  }

  const auto& data = *context.data;  // LCOV_EXCL_LINE
  const size_t targetFrame = data.bootstrapFrames + postBootstrapSteps;  // LCOV_EXCL_LINE
  const std::vector<std::pair<size_t, bool>> supportCube =
      supportCubeForAssignmentCubes(normalizedCubes);  // LCOV_EXCL_LINE
  if (supportCube.empty()) {  // LCOV_EXCL_LINE
    return true;  // LCOV_EXCL_LINE
  }

  CachedResetFrontierSolver& solver = getCachedResetFrontierSolver(  // LCOV_EXCL_LINE
      data, solverType, supportCube, targetFrame);  // LCOV_EXCL_LINE

  if (isKInductionCoiDiagEnabled()) {  // LCOV_EXCL_LINE
    emitSecDiag(  // LCOV_EXCL_LINE
        "SEC diag: reset frontier target batch cube coi "
        "post_bootstrap_steps=",
        postBootstrapSteps,
        " frames=",
        targetFrame + 1,  // LCOV_EXCL_LINE
        " solver_symbols=",
        solver.coi.solverSymbols.size(),  // LCOV_EXCL_LINE
        " transition_targets=",
        countTransitionTargets(solver.coi.transitionTargetsByFrame),  // LCOV_EXCL_LINE
        " cubes=",
        normalizedCubes.size(),  // LCOV_EXCL_LINE
        " support_literals=",
        supportCube.size(),  // LCOV_EXCL_LINE
        " frame_invariant_symbols=",
        data.frameInvariantSupport.size());  // LCOV_EXCL_LINE
  }  // LCOV_EXCL_LINE

  for (const auto& cube : normalizedCubes) {  // LCOV_EXCL_LINE
    if (const auto knownCore =  // LCOV_EXCL_LINE
            knownResetFrontierConflictCore(data, cube, postBootstrapSteps);  // LCOV_EXCL_LINE
        knownCore.has_value()) {  // LCOV_EXCL_LINE
      rememberResetFrontierUnreachableCore(data, targetFrame, *knownCore);  // LCOV_EXCL_LINE
      continue;  // LCOV_EXCL_LINE
    }
    if (findCachedResetFrontierUnreachableCore(data, targetFrame, cube)  // LCOV_EXCL_LINE
            .has_value()) {  // LCOV_EXCL_LINE
      continue;  // LCOV_EXCL_LINE
    }
    const auto assumptions =
        stateCubeAssumptionLits(*solver.variables, cube, targetFrame);  // LCOV_EXCL_LINE
    const auto status =  // LCOV_EXCL_LINE
        solver.solver->solveWithAssumptionsStatus(  // LCOV_EXCL_LINE
            assumptions, conflictLimit, propagationLimit);  // LCOV_EXCL_LINE
    if (status == SATSolverWrapper::SolveStatus::Sat) {  // LCOV_EXCL_LINE
      return true;  // LCOV_EXCL_LINE
    }
    if (status == SATSolverWrapper::SolveStatus::Unknown) {  // LCOV_EXCL_LINE
      if (isKInductionCoiDiagEnabled()) {  // LCOV_EXCL_LINE
        emitSecDiag(  // LCOV_EXCL_LINE
            "SEC diag: reset frontier target batch assumption proof "
            "resource_limit post_bootstrap_steps=",
            postBootstrapSteps,
            " solver_symbols=",
            solver.coi.solverSymbols.size(),  // LCOV_EXCL_LINE
            " transition_targets=",
            countTransitionTargets(solver.coi.transitionTargetsByFrame),  // LCOV_EXCL_LINE
            " cubes=",
            normalizedCubes.size());  // LCOV_EXCL_LINE
      }  // LCOV_EXCL_LINE
      return true;  // LCOV_EXCL_LINE
    }
    if (const auto core = failedAssumptionCoreFromLastResetFrontierSolve(  // LCOV_EXCL_LINE
            solver, cube, targetFrame);  // LCOV_EXCL_LINE
        core.has_value()) {  // LCOV_EXCL_LINE
      rememberResetFrontierUnreachableCore(data, targetFrame, *core);  // LCOV_EXCL_LINE
    } else {  // LCOV_EXCL_LINE
      rememberResetFrontierUnreachableCore(data, targetFrame, cube);  // LCOV_EXCL_LINE
    }
  }  // LCOV_EXCL_LINE
  return false;  // LCOV_EXCL_LINE
}  // LCOV_EXCL_LINE

std::optional<std::vector<std::pair<size_t, bool>>>
findResetFrontierUnreachableCubeCore(
    const ResetFrontierReachabilityContext& context,
    KEPLER_FORMAL::Config::SolverType solverType,
    const std::vector<std::pair<size_t, bool>>& cube,
    size_t postBootstrapSteps) {
  if (cube.empty()) {
    return std::nullopt;  // LCOV_EXCL_LINE
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
  if (resetFrontierAssumptionSolvesDisabled()) {  // LCOV_EXCL_LINE
    return std::nullopt;  // LCOV_EXCL_LINE
  }
  CachedResetFrontierSolver& cached =  // LCOV_EXCL_LINE
      getCachedResetFrontierSolver(data, solverType, normalizedCube, targetFrame);  // LCOV_EXCL_LINE
  const auto core = extractUnreachableCoreFromCachedResetFrontierSolver(  // LCOV_EXCL_LINE
      cached, normalizedCube, targetFrame);  // LCOV_EXCL_LINE
  if (core.has_value()) {  // LCOV_EXCL_LINE
    rememberResetFrontierUnreachableCore(data, targetFrame, *core);  // LCOV_EXCL_LINE
  }  // LCOV_EXCL_LINE
  return core;  // LCOV_EXCL_LINE
}

}  // namespace KEPLER_FORMAL::SEC
