// Copyright 2024-2026 keplertech.io
// SPDX-License-Identifier: GPL-3.0-only

#include "pdr/PDREngine.h"

#include <algorithm>
#include <cstdlib>
#include <memory>
#include <optional>
#include <set>
#include <sstream>
#include <stdexcept>
#include <unordered_map>
#include <string_view>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/BoolExprUtils.h"
#include "common/ProofProblemDebug.h"
#include "common/SecDiag.h"
#include "kinduction/BaseCaseSolver.h"
#include "proof/ProofEngineShared.h"
#include "proof/TransitionExprResolver.h"
#include "kinduction/SatEncoding.h"

namespace KEPLER_FORMAL::SEC {

// Overall PDR algorithm:
// 1. Build Init from the SEC startup constraints and reuse any already
//    validated strengthening invariant when it is sound to do so.
// 2. Maintain frames F[0], F[1], ... where each frame stores clauses known to
//    hold for all states reachable within that many steps.
// 3. At each level, ask whether a bad state still survives the current frame.
// 4. If so, recursively search for predecessors until either Init is reached
//    (real counterexample) or the bad cube is blocked by a learned clause.
// 5. Generalize learned blocking clauses, add them to all earlier frames, and
//    then propagate them forward when the transition relation preserves them.
// 6. Stop once two adjacent frames converge, when a real bug is found, or when
//    the requested frame budget is exhausted.

namespace {

// The init-intersection fast path runs inside literal-dropping generalization.
// On ASICs the complemented-state table can be enormous while each cube is
// tiny, so scanning the full table per literal costs more than the SAT queries
// it was meant to avoid. Above this limit we skip only the cheap contradiction
// shortcut and conservatively treat the cube as init-intersecting below.
constexpr size_t kMaxComplementPairsForCheapInitCheck = 1024;
// Reset-constant evaluation is only a shortcut before the exact reset-image
// SAT check. Bound the recursive evaluator so an ASIC memory cone cannot spend
// minutes proving that the shortcut is inconclusive.
constexpr size_t kMaxResetConstantEvaluatorStates = 1024;
constexpr size_t kMaxResetConstantEvaluatorExprs = 8192;
// The first bad obligation controls how much abstraction PDR is allowed to use.
// A tiny structural justification can be too weak on large SEC cones and may
// produce an abstract counterexample that concrete BMC later rejects. Prefer a
// full state-support cube when the bad cone is bounded, but keep the structural
// fallback for very large datapaths so one output cannot materialize the whole
// ASIC into every predecessor query.
constexpr size_t kMaxPreciseBadCubeSupportNodes = 16384;
// After exact BMC rejects an abstract final-stage PDR counterexample, a small
// state-only bad predicate can be turned into frame clauses directly. Keep the
// enumeration deliberately small: this is for one-output ASIC cones such as
// BlackParrot's six-state-bit bad predicates, not arbitrary datapath CNF.
constexpr size_t kMaxValidatedBadFormulaCnfSupport = 8;
// Batched SEC bad predicates are an OR of per-output mismatches. Each output
// may have a small state-only bad cone even when the union across the batch is
// too wide to enumerate. Cap the total learned clauses so the batched
// refinement stays a local PDR repair instead of becoming a broad CNF dump.
constexpr size_t kMaxValidatedBadFormulaClauses = 4096;
// The DAG walk budget above prevents pathological formula traversal, while
// this state-symbol budget keeps a "bounded" cone from still producing a giant
// target cube. PDR can safely use the structural justification fallback for
// larger cones and any reported counterexample is still concrete-BMC checked.
// A SAT predecessor assignment can mention every state bit in a large target
// transition cone. Carrying that entire model forward makes the next PDR query
// encode hundreds of unrelated next-state functions. The engine therefore has
// a configurable projection limit: above it, keep the SAT query exact but carry
// forward only a bounded set of state literals from the satisfying model.
// Learned clauses are still checked by real predecessor queries before being
// added.
constexpr size_t kMinPredecessorJustificationVisits = 4096;
constexpr size_t kPredecessorJustificationVisitMultiplier = 64;
// Literal-dropping only improves clause strength; it is not required for
// soundness.  ASIC predecessor cubes can still contain hundreds of literals,
// and learning them almost verbatim makes PDR rediscover nearby cubes.  Use a
// bounded chunk-dropping pass: each proposed stronger clause is validated by
// the same predecessor SAT query, but we first try removing large literal
// blocks instead of spending one query per literal.
// Sampling on large SEC regressions showed clause generalization itself
// dominating runtime: many blocked cubes are not "huge", but they are already
// large enough that each extra predecessor SAT check costs far more than the
// slightly smaller learned clause saves later. Switch to the cheap-seed-only
// path earlier so medium ASIC cubes do not trigger a long literal-dropping
// search.
constexpr size_t kLargeBlockedCubeGeneralizationThreshold = 64;
// BlackParrot exact-PDR sampling showed a pathological loop where a 116-literal
// predecessor cube was repeatedly reduced to different 32-literal cheap seeds,
// each cheaply UNSAT at F[0] but too narrow to cover neighboring predecessors.
// Start with a smaller validated seed so those exact UNSAT probes learn broader
// frame clauses before PDR falls back to more expensive literal dropping.
constexpr size_t kLargeBlockedCubeSeedSize = 8;
constexpr size_t kMaxSmallBlockedCubeGeneralizationChecks = 8;
constexpr size_t kMaxLargeBlockedCubeGeneralizationChecks = 16;
// If a blocked cube's transition cone has only a tiny current-state/input
// surface, a few extra literal-dropping checks can pay for themselves. Keep the
// cap modest anyway: local BlackParrot samples showed this "cheap" path
// becoming the dominant runtime once the larger predecessor-core explosion was
// fixed.
constexpr size_t kCheapBlockedCubeTransitionSupportLimit = 8;
constexpr size_t kMaxCheapBlockedCubeGeneralizationChecks = 32;
constexpr size_t kMaxGeneralizedBlockedCubeTransitionSupport = 32;
// Clause generalization is optional. A sampled BlackParrot SEC/PDR run showed
// the final exact stage repeatedly trying to shrink already-blocked 116-literal
// cubes with broad transition support; almost every predecessor core collapsed
// to a tiny cube that still had a predecessor, so the engine spent its runtime
// rebuilding SAT queries without learning a useful stronger clause. For very
// large broad-support cubes, learn the proven cube verbatim and let later frame
// propagation decide whether more precision is actually needed.
constexpr size_t kVeryLargeBlockedCubeGeneralizationBypassThreshold = 96;
// Glucose's final conflict can be too coarse to use directly as a target-cube
// core in the PDR predecessor oracle. When that happens, stay inside the same
// already-built target-context solver and shrink the full target assumption set
// by deletion. These checks reuse the solver; unlike ordinary cube
// generalization they do not rebuild transition/frame CNF per trial.
constexpr size_t kMaxPredecessorCoreContextMinimizationChecks = 32;
// BlackParrot sampling later found the same predecessor-core need below the
// "large cube" threshold: level-zero blockers around 37-49 literals with
// thousands of transition-support symbols were learned verbatim and then
// rediscovered one valuation at a time.  Try the core oracle for medium cubes
// only when their transition surface is already too broad for bounded
// literal-dropping to be worthwhile.
constexpr size_t kMinMediumCubePredecessorCoreTargetSize = 16;
// Projected predecessor queries are allowed to ignore some learned frame
// clauses: that only weakens the SAT query, which can create extra obligations
// but cannot justify an unsound blocked cube. Large ASIC SEC runs can learn
// thousands of local frame clauses, and materializing all of them per query
// turns each predecessor check back into a near-global proof.
// Later steady-state samples on BlackParrot showed projected predecessor
// queries spending a large fraction of time just re-materializing learned
// frame clauses.  Projected PDR is allowed to under-approximate those clauses:
// skipping some only weakens the query and can at worst create extra
// obligations. Keep the per-query learned-frame surface small enough that the
// predecessor SAT work dominates again instead of clause streaming.
// BlackParrot measurements showed that a 128-clause cap was too aggressive:
// the query became cheaper to encode, but PDR then spent minutes solving
// tens of thousands of predecessors already blocked by omitted frame clauses.
// Keep projection bounded, but let a local ASIC cone see enough of its learned
// frame that the CEGAR refinement loop remains the exception rather than the
// steady state.
constexpr size_t kDefaultMaxProjectedFrameClausesPerQuery = 1024;
constexpr size_t kDefaultMaxProjectedFrameLiteralsPerQuery = 8192;
// Projected-frame CEGAR is useful for a few missing learned clauses, but
// BlackParrot sampling showed it can otherwise spend thousands of SAT queries
// adding local blockers for the same obligation before falling back to exact
// frames anyway. Cap the local repair loop and retry that obligation with the
// complete learned frame once projection is clearly too weak.
constexpr size_t kDefaultMaxProjectedFrameRefinementsBeforeExactRetry = 16;
// F[0] reset-frontier refinement is different from ordinary predecessor
// generalization: every dropped literal is guarded by an exact reset-image SAT
// query, and weak F[0] clauses can otherwise make PDR enumerate thousands of
// abstract reset states one cube at a time. Keep the pass bounded, but allow
// enough drops to minimize the small projected cubes PDR normally learns at
// level zero.
// Reset-frontier literal dropping is exact, but each trial can require a
// multi-frame reset-image SAT query.  BlackParrot sampling showed this pass
// dominating runtime and memory once reset bootstrap was correctly enabled, so
// keep only a small amount of safe weakening and let normal PDR blocking handle
// the rest.
constexpr size_t kMaxResetFrontierGeneralizationAttempts = 2;
// A projected predecessor path can reach Init even when the original bad cube
// is not reachable in the concrete bounded transition system.  When that
// happens, spend a small exact-SAT budget generalizing the unreachable root
// cube before learning the refinement; this blocks whole neighborhoods of
// spurious roots instead of rediscovering them one valuation at a time.
// The exact post-reset predecessor precheck is valuable when one concrete
// reset-image query can replace many abstract F[0] predecessor/refinement
// loops. BlackParrot sampling showed 42-support targets exploding when skipped,
// while much wider cones should still fall back to local F[0] CEGAR.
constexpr size_t kMaxExactResetPrecheckTransitionSupport = 64;
constexpr size_t kDefaultPdrStatsInterval = 1000;
constexpr size_t kInitialPdrStatsQueries = 20;
// PDR can use inferred state correspondences as an ordinary frame invariant,
// but ASIC retiming/optimization can make a few inferred pairs non-inductive
// while many others are still valid and very useful.  Mine a validated subset
// once per PDR run instead of forcing the blocking loop to rediscover thousands
// of those equality clauses one cube at a time.
constexpr size_t kMaxStateEqualitySubsetPairs = 2048;
constexpr size_t kMaxStateEqualitySubsetIterations = 256;

// Cubes represent a concrete bad/predecessor state, while clauses are the
// blocked generalization of such a state stored in a PDR frame.
struct CubeLiteral {
  size_t symbol = 0;
  bool value = false;

  bool operator==(const CubeLiteral& other) const {
    return symbol == other.symbol && value == other.value;
  }
};

struct ClauseLiteral {
  size_t symbol = 0;
  bool positive = false;

  bool operator==(const ClauseLiteral& other) const {
    return symbol == other.symbol && positive == other.positive;
  }
};

using StateCube = std::vector<CubeLiteral>;
using StateClause = std::vector<ClauseLiteral>;

struct FrameClauses {
  // F[i] stores clauses known to hold for all states reachable within i steps.
  std::vector<StateClause> clauses;
  // Lazily maps a state symbol to the learned clauses mentioning it. PDR asks
  // many local SAT queries against the same frame, so this cache lets each
  // query pull only the clauses touching its cone instead of rescanning the
  // entire learned frame history.
  mutable bool clauseIndexDirty = true;
  mutable std::unordered_map<size_t, std::vector<size_t>> clauseIndicesBySymbol;
  // Scratch epoch marks used while emitting relevant clauses into one SAT
  // query.  This avoids materializing and sorting a giant candidate-index list
  // when many query symbols touch overlapping learned clauses.
  mutable uint64_t clauseEmitEpoch = 1;
  mutable std::vector<uint64_t> clauseEmitEpochByIndex;
};

uint64_t nextClauseEmitEpoch(const FrameClauses& frameClauses);

struct ComplementPartnerIndex {
  std::unordered_map<size_t, std::vector<size_t>> partnersBySymbol;

  explicit ComplementPartnerIndex(const KInductionProblem& problem) {
    partnersBySymbol.reserve(
        2 * (problem.complementedStatePairs0.size() +
             problem.complementedStatePairs1.size()));
    addPairs(problem.complementedStatePairs0);
    addPairs(problem.complementedStatePairs1);
  }

 private:
  void addPairs(const std::vector<std::pair<size_t, size_t>>& pairs) {
    for (const auto& [primarySymbol, complementedSymbol] : pairs) {
      partnersBySymbol[primarySymbol].push_back(complementedSymbol);
      partnersBySymbol[complementedSymbol].push_back(primarySymbol);
    }
  }
};

struct ProofObligation {
  // "cube is bad at level" requests either a predecessor or a blocking clause.
  StateCube cube;
  size_t level = 0;
  size_t badFrame = 0;
  // The original frontier cube this obligation is trying to block.  Projected
  // predecessor cubes are useful for fast blocking, but if such a projection
  // reaches Init we validate the root cube against the concrete bounded
  // transition prefix before reporting a counterexample.
  StateCube rootCube;
};

struct JustificationBudget {
  size_t remainingVisits = 0;
  size_t maxAssignments = 0;
  bool exhausted = false;
};

struct SymbolPair {
  size_t first = 0;
  size_t second = 0;

  bool operator==(const SymbolPair& other) const {
    return first == other.first && second == other.second;
  }
};

struct SymbolPairHash {
  size_t operator()(const SymbolPair& pair) const {
    // Splitmix-style mixing keeps pair lookup cheap and avoids repeatedly
    // scanning thousands of extracted startup equalities during PDR seeding.
    size_t seed = pair.first + 0x9e3779b97f4a7c15ULL;
    seed ^= pair.second + 0x9e3779b97f4a7c15ULL + (seed << 6) + (seed >> 2);
    return seed;
  }
};

struct InitFactIndex {
  std::unordered_map<size_t, bool> assignments;
  std::unordered_set<SymbolPair, SymbolPairHash> equalities;
  std::unordered_set<SymbolPair, SymbolPairHash> complements;
};

struct ResetFrontierCache {
  // PDR can revisit the same abstract F[0] cube through multiple bad
  // obligations. Cache the exact reset-image answer so we do not rebuild the
  // same reset-prefix SAT query more than once per engine run.
  std::unordered_map<std::string, bool> outsideByCubeKey;
  // The exact reset-frontier query also needs immutable per-problem indexes
  // for equality aliases and complemented-state lookup. Build them once per
  // blocking wave instead of rescanning ASIC-size equality tables per cube.
  std::shared_ptr<ResetFrontierReachabilityContext> reachabilityContext;
};

enum class ConcreteCubeReachabilityMode {
  CachedAssumptions,
  OneShotUnitClauses,
};

class PdrQueryBudgetExceeded : public std::runtime_error {
 public:
  PdrQueryBudgetExceeded()
      : std::runtime_error("PDR predecessor query budget exceeded") {}
};

void consumePdrPredecessorQueryBudget(size_t* remainingQueries) {
  if (remainingQueries == nullptr) {
    return;
  }
  if (*remainingQueries == 0) {
    throw PdrQueryBudgetExceeded();
  }
  --(*remainingQueries);
}

bool pdrStatsEnabled() {
  return std::getenv("KEPLER_SEC_PDR_STATS") != nullptr;
}

std::string_view concreteCubeReachabilityModeName(
    ConcreteCubeReachabilityMode mode) {
  switch (mode) {
    case ConcreteCubeReachabilityMode::CachedAssumptions:
      return "cached_assumptions";
    case ConcreteCubeReachabilityMode::OneShotUnitClauses:
      return "one_shot_unit_clauses";
  }
  return "unknown";  // LCOV_EXCL_LINE
}

size_t pdrStatsInterval() {
  const char* intervalText = std::getenv("KEPLER_SEC_PDR_STATS_INTERVAL");
  if (intervalText == nullptr || *intervalText == '\0') {
    return kDefaultPdrStatsInterval;
  }

  const auto interval = std::strtoull(intervalText, nullptr, 10);
  return interval == 0 ? 1 : static_cast<size_t>(interval);
}

size_t envSizeLimitOrDefault(const char* name, size_t defaultValue) {
  const char* valueText = std::getenv(name);
  if (valueText == nullptr || *valueText == '\0') {
    return defaultValue;
  }
  const auto value = std::strtoull(valueText, nullptr, 10);
  return value == 0 ? defaultValue : static_cast<size_t>(value);
}

size_t maxProjectedFrameClausesPerQuery() {
  return envSizeLimitOrDefault(
      "KEPLER_SEC_PDR_PROJECTED_FRAME_CLAUSE_LIMIT",
      kDefaultMaxProjectedFrameClausesPerQuery);
}

size_t maxProjectedFrameLiteralsPerQuery() {
  return envSizeLimitOrDefault(
      "KEPLER_SEC_PDR_PROJECTED_FRAME_LITERAL_LIMIT",
      kDefaultMaxProjectedFrameLiteralsPerQuery);
}

size_t maxProjectedFrameRefinementsBeforeExactRetry() {
  return envSizeLimitOrDefault(
      "KEPLER_SEC_PDR_PROJECTED_FRAME_REFINEMENT_LIMIT",
      kDefaultMaxProjectedFrameRefinementsBeforeExactRetry);
}

size_t nextPdrPredecessorQueryNumber() {
  // The stats path is intentionally process-local and diagnostic-only. PDR is
  // currently run serially per SEC output slice, so a simple counter gives a
  // stable view of where a long proof is spending time without touching the
  // proof algorithm or adding synchronization overhead to normal runs.
  static size_t queryNumber = 0;
  return ++queryNumber;
}

size_t nextPdrProjectedBlockedRetryNumber() {
  static size_t retryNumber = 0;
  return ++retryNumber;
}

bool shouldEmitPdrStats(size_t queryNumber) {
  if (!pdrStatsEnabled()) {
    return false;
  }
  return queryNumber <= kInitialPdrStatsQueries ||
         queryNumber % pdrStatsInterval() == 0;
}

void addComplementedStateRelations(
    SATSolverWrapper& solver,
    const FrameVariableStore& variables,
    const std::vector<std::pair<size_t, size_t>>& complementedStatePairs,
    size_t numFrames);

void addTransitionRelation(SATSolverWrapper& solver,
                           const FrameVariableStore& variables,
                           const KInductionProblem& problem,
                           size_t frame);

void addCubeAssumptions(SATSolverWrapper& solver,
                        const FrameVariableStore& variables,
                        const StateCube& cube,
                        size_t frame);

void addFormulaSymbols(BoolExpr* formula, std::unordered_set<size_t>& symbols);

void addFormulaStateSupport(BoolExpr* formula,
                            const std::unordered_set<size_t>& stateSymbols,
                            std::unordered_set<size_t>& output);

bool predecessorSourceFrameIsKnownSafe(size_t level);

void normalizeCube(StateCube& cube);

std::optional<std::set<size_t>> boundedSupportVars(BoolExpr* formula,
                                                   size_t maxVisitedNodes);

void addRelevantComplementedStatePartners(
    const ComplementPartnerIndex& complementPartners,
    std::unordered_set<size_t>& symbols);

std::unordered_map<size_t, BoolExpr*> buildTransitionExprByStateSymbol(
    const KInductionProblem& problem) {
  std::unordered_map<size_t, BoolExpr*> transitionExprByStateSymbol;
  transitionExprByStateSymbol.reserve(
      problem.transitions0.size() + problem.transitions1.size());
  for (const auto& [stateSymbol, expr] : problem.transitions0) {
    transitionExprByStateSymbol.emplace(stateSymbol, expr);
  }
  for (const auto& [stateSymbol, expr] : problem.transitions1) {
    transitionExprByStateSymbol.emplace(stateSymbol, expr);
  }
  return transitionExprByStateSymbol;
}

bool cubeOutsideConcreteResetFrontier(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    const TransitionExprResolver& transitionByState,
    const StateCube& cube,
    size_t postBootstrapSteps,
    ResetFrontierCache& cache,
    bool useResetConstantShortcut = true);

bool cubeReachableWithinConcreteFrames(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    const TransitionExprResolver& transitionByState,
    const StateCube& cube,
    size_t maxPostBootstrapSteps,
    ResetFrontierCache& cache,
    ConcreteCubeReachabilityMode mode =
        ConcreteCubeReachabilityMode::CachedAssumptions);

std::unordered_map<size_t, size_t> buildComplementPrimaryByStateSymbol(
    const KInductionProblem& problem) {
  std::unordered_map<size_t, size_t> primaryByComplement;
  primaryByComplement.reserve(
      problem.complementedStatePairs0.size() +
      problem.complementedStatePairs1.size());
  for (const auto& [primarySymbol, complementedSymbol] :
       problem.complementedStatePairs0) {
    primaryByComplement.emplace(complementedSymbol, primarySymbol);  // LCOV_EXCL_LINE
  }
  for (const auto& [primarySymbol, complementedSymbol] :
       problem.complementedStatePairs1) {
    primaryByComplement.emplace(complementedSymbol, primarySymbol);
  }
  return primaryByComplement;
}

std::vector<size_t> sortUniqueSymbols(std::unordered_set<size_t> symbols) {
  std::vector<size_t> ordered(symbols.begin(), symbols.end());
  std::sort(ordered.begin(), ordered.end());
  ordered.erase(std::unique(ordered.begin(), ordered.end()), ordered.end());
  return ordered;
}

std::optional<std::vector<size_t>> collectBoundedStateSupportSymbols(
    BoolExpr* formula,
    size_t maxVisitedNodes,
    size_t maxStateSymbols,
    const std::unordered_set<size_t>& stateSymbolSet) {
  if (formula == nullptr) {
    return {};  // LCOV_EXCL_LINE
  }

  const auto support = boundedSupportVars(formula, maxVisitedNodes);
  if (!support.has_value()) {
    return std::nullopt;
  }

  std::unordered_set<size_t> stateSupport;
  for (const auto symbol : *support) {
    if (stateSymbolSet.find(symbol) != stateSymbolSet.end()) {
      stateSupport.insert(symbol);
      if (stateSupport.size() > maxStateSymbols) {
        return std::nullopt;
      }
    }
  }
  return sortUniqueSymbols(std::move(stateSupport));
}

std::vector<size_t> expandTransitionTargets(
    const KInductionProblem& problem,
    const std::vector<size_t>& requestedTargets,
    const std::unordered_map<size_t, BoolExpr*>& transitionExprByStateSymbol) {
  const auto primaryByComplement = buildComplementPrimaryByStateSymbol(problem);
  std::unordered_set<size_t> targets;
  targets.reserve(requestedTargets.size());

  for (const auto symbol : requestedTargets) {
    if (transitionExprByStateSymbol.find(symbol) !=
        transitionExprByStateSymbol.end()) {
      targets.insert(symbol);
      continue;
    }

    // Complemented flop outputs are constrained through the primary flop. If a
    // cube talks only about the complemented bit, encode the primary transition
    // and let the complemented-state relation connect the two next-frame bits.
    if (const auto primaryIt = primaryByComplement.find(symbol);  // LCOV_EXCL_LINE
        primaryIt != primaryByComplement.end() &&  // LCOV_EXCL_LINE
        transitionExprByStateSymbol.find(primaryIt->second) !=  // LCOV_EXCL_LINE
            transitionExprByStateSymbol.end()) {  // LCOV_EXCL_LINE
      targets.insert(primaryIt->second);  // LCOV_EXCL_LINE
    }  // LCOV_EXCL_LINE
  }

  return sortUniqueSymbols(std::move(targets));
}

std::vector<size_t> expandTransitionTargets(
    const KInductionProblem& problem,
    const std::vector<size_t>& requestedTargets,
    const TransitionExprResolver& transitionByState) {
  const auto& primaryByComplement = transitionByState.primaryByComplement();
  std::unordered_set<size_t> targets;
  targets.reserve(requestedTargets.size());

  for (const auto symbol : requestedTargets) {
    if (transitionByState.contains(symbol)) {
      targets.insert(symbol);
      continue;
    }
    if (const auto primaryIt = primaryByComplement.find(symbol);
        primaryIt != primaryByComplement.end() &&
        transitionByState.contains(primaryIt->second)) {
      targets.insert(primaryIt->second);
    }
  }

  return sortUniqueSymbols(std::move(targets));
}

std::vector<size_t> collectTransitionSupportSymbols(
    const TransitionExprResolver& transitionByState,
    const std::vector<size_t>& encodedTargets) {
  std::unordered_set<size_t> supportSymbols;
  for (const auto stateSymbol : encodedTargets) {
    const auto& support = transitionByState.support(stateSymbol);
    supportSymbols.insert(support.begin(), support.end());
  }
  return sortUniqueSymbols(std::move(supportSymbols));
}

size_t estimateTransitionEncodingNodes(
    const TransitionExprResolver& transitionByState,
    const std::vector<size_t>& encodedTargets) {
  size_t estimate = 0;
  for (const auto stateSymbol : encodedTargets) {
    estimate += transitionByState.nodeCount(stateSymbol);
  }
  return estimate;
}

std::vector<size_t> cubeStateSymbols(const StateCube& cube) {
  std::unordered_set<size_t> symbols;
  symbols.reserve(cube.size());
  for (const auto& literal : cube) {
    symbols.insert(literal.symbol);
  }
  return sortUniqueSymbols(std::move(symbols));
}

std::vector<size_t> boundedPrefixSymbols(const std::vector<size_t>& symbols,
                                         size_t limit) {
  if (limit == 0 || symbols.size() <= limit) {
    return symbols;
  }
  return std::vector<size_t>(symbols.begin(), symbols.begin() + limit);
}

StateCube boundedPrefixCube(const StateCube& cube, size_t limit) {
  if (limit == 0 || cube.size() <= limit) {
    return cube;
  }
  return StateCube(cube.begin(), cube.begin() + limit);
}

size_t transitionLiteralCost(const TransitionExprResolver& transitionByState,
                             size_t symbol) {
  size_t transitionSymbol = symbol;
  if (!transitionByState.contains(transitionSymbol)) {
    const auto primaryIt = transitionByState.primaryByComplement().find(symbol);
    if (primaryIt == transitionByState.primaryByComplement().end() ||
        !transitionByState.contains(primaryIt->second)) {
      return 0;
    }
    transitionSymbol = primaryIt->second;
  }
  // Support width is the dominant SAT-query cost; node count breaks ties among
  // cones with similar state/input footprints.
  return transitionByState.support(transitionSymbol).size() * 4 +
         transitionByState.nodeCount(transitionSymbol);
}

size_t blockedCubeTransitionSupportSize(
    const KInductionProblem& problem,
    const TransitionExprResolver& transitionByState,
    const StateCube& cube) {
  const std::vector<size_t> targetSymbols = cubeStateSymbols(cube);
  const std::vector<size_t> encodedTargets =
      expandTransitionTargets(problem, targetSymbols, transitionByState);
  return collectTransitionSupportSymbols(transitionByState, encodedTargets).size();
}

StateCube boundedCheapTransitionCube(
    const StateCube& cube,
    size_t limit,
    const TransitionExprResolver& transitionByState) {
  if (limit == 0 || cube.size() <= limit) {
    return cube;
  }

  StateCube selected = cube;
  std::stable_sort(
      selected.begin(),
      selected.end(),
      [&](const CubeLiteral& lhs, const CubeLiteral& rhs) {
        const size_t lhsCost = transitionLiteralCost(transitionByState, lhs.symbol);
        const size_t rhsCost = transitionLiteralCost(transitionByState, rhs.symbol);
        if (lhsCost != rhsCost) {
          return lhsCost < rhsCost;
        }
        return lhs.symbol < rhs.symbol;
      });
  selected.resize(limit);
  normalizeCube(selected);
  return selected;
}

std::vector<std::pair<size_t, bool>> cubeAssignments(const StateCube& cube) {
  std::vector<std::pair<size_t, bool>> assignments;
  assignments.reserve(cube.size());
  for (const auto& literal : cube) {
    assignments.emplace_back(literal.symbol, literal.value);
  }
  return assignments;
}

StateCube cubeFromAssignments(
    const std::vector<std::pair<size_t, bool>>& assignments) {
  StateCube cube;
  cube.reserve(assignments.size());
  for (const auto& [symbol, value] : assignments) {
    cube.push_back({symbol, value});
  }
  normalizeCube(cube);
  return cube;
}

std::string resetFrontierCacheKey(const StateCube& cube,
                                  size_t postBootstrapSteps) {
  // The cube is normalized before it enters the PDR queue, so a compact textual
  // key is deterministic and avoids adding a custom vector hasher just for this
  // CEGAR memo table.
  std::string key = std::to_string(postBootstrapSteps);
  key.push_back('|');
  for (const auto& literal : cube) {
    key += std::to_string(literal.symbol);
    key.push_back(literal.value ? '1' : '0');
    key.push_back(';');
  }
  return key;
}

std::string stateClauseKey(const StateClause& clause) {
  // Learned-frame clauses are normalized before storage. A compact textual key
  // is enough here and keeps the local projected-frame CEGAR loop independent
  // from any lossy hash/fingerprint collision behavior.
  std::string key;
  for (const auto& literal : clause) {
    key += std::to_string(literal.symbol);
    key.push_back(literal.positive ? '1' : '0');
    key.push_back(';');
  }
  return key;
}

uint64_t cubeFingerprint(const StateCube& cube) {
  uint64_t hash = 1469598103934665603ULL;
  for (const auto& literal : cube) {
    hash ^= static_cast<uint64_t>(literal.symbol) + 0x9e3779b97f4a7c15ULL;
    hash *= 1099511628211ULL;
    hash ^= literal.value ? 0xa5a5a5a5a5a5a5a5ULL : 0x5a5a5a5a5a5a5a5aULL;
    hash *= 1099511628211ULL;
  }
  return hash;
}

std::optional<std::set<size_t>> boundedSupportVars(BoolExpr* formula,
                                                   size_t maxVisitedNodes) {
  if (formula == nullptr) {
    return std::set<size_t>{};  // LCOV_EXCL_LINE
  }

  std::set<size_t> support;
  std::unordered_set<const BoolExpr*> visited;
  std::vector<const BoolExpr*> stack{formula};
  while (!stack.empty()) {
    const BoolExpr* node = stack.back();
    stack.pop_back();
    if (!visited.insert(node).second) {
      continue;
    }
    if (visited.size() > maxVisitedNodes) {
      return std::nullopt;
    }

    if (node->getOp() == Op::VAR) {
      support.insert(node->getId());
      continue;
    }
    if (node->getRight() != nullptr) {
      stack.push_back(node->getRight());
    }
    if (node->getLeft() != nullptr) {
      stack.push_back(node->getLeft());
    }
  }
  return support;
}

class ResetConstantEvaluator {
 public:
  ResetConstantEvaluator(const KInductionProblem& problem,
                         const TransitionExprResolver& transitionByState)
      : problem_(problem),
        transitionByState_(transitionByState),
        exprMemoByStep_(problem.resetBootstrapCycles + 1) {
    resetInputs_.reserve(problem.resetBootstrapInputs.size());
    for (const auto& [symbol, value] : problem.resetBootstrapInputs) {
      resetInputs_.emplace(symbol, value);
    }
    initialStates_.reserve(problem.initialStateAssignments.size());
    for (const auto& [symbol, value] : problem.initialStateAssignments) {
      initialStates_.emplace(symbol, value);
    }
    bootstrapStates_.reserve(problem.bootstrapStateAssignments.size());
    for (const auto& [symbol, value] : problem.bootstrapStateAssignments) {
      bootstrapStates_.emplace(symbol, value);
    }
  }

  std::optional<bool> stateValue(size_t symbol, size_t step) {
    if (budgetExhausted_) {
      return std::nullopt;  // LCOV_EXCL_LINE
    }
    if (step == problem_.resetBootstrapCycles) {
      if (const auto it = bootstrapStates_.find(symbol);
          it != bootstrapStates_.end()) {
        return it->second;
      }
    }

    const SymbolPair key{symbol, step};
    if (const auto it = stateMemo_.find(key); it != stateMemo_.end()) {
      return it->second;
    }
    if (++stateEvaluations_ > kMaxResetConstantEvaluatorStates) {
      budgetExhausted_ = true;
      return std::nullopt;  // LCOV_EXCL_LINE
    }

    std::optional<bool> value;
    if (step == 0) {
      if (const auto it = initialStates_.find(symbol);
          it != initialStates_.end()) {
        value = it->second;
      }
    } else if (transitionByState_.contains(symbol)) {
      // A state bit at reset step N is obtained by evaluating its transition
      // expression in reset step N-1. This recursively follows only the cube's
      // required reset cone and short-circuits through reset mux constants.
      value = exprValue(transitionByState_.at(symbol), step - 1);
    }

    stateMemo_.emplace(key, value);
    return value;
  }

  bool budgetExhausted() const { return budgetExhausted_; }

 private:
  std::optional<bool> exprValue(BoolExpr* expr, size_t step) {
    if (budgetExhausted_ || expr == nullptr || step >= exprMemoByStep_.size()) {
      return std::nullopt;  // LCOV_EXCL_LINE
    }

    auto& memo = exprMemoByStep_[step];
    if (const auto it = memo.find(expr); it != memo.end()) {
      return it->second;
    }
    if (++exprEvaluations_ > kMaxResetConstantEvaluatorExprs) {
      budgetExhausted_ = true;
      return std::nullopt;  // LCOV_EXCL_LINE
    }

    std::optional<bool> value;
    switch (expr->getOp()) {
      case Op::VAR:
        if (expr->getId() < 2) {
          value = expr->getId() == 1;
        } else if (const auto resetIt = resetInputs_.find(expr->getId());
                   resetIt != resetInputs_.end()) {
          value = resetIt->second;
        } else {
          const auto& stateSymbols = transitionByState_.stateSymbols();
          if (stateSymbols.find(expr->getId()) != stateSymbols.end()) {
            value = stateValue(expr->getId(), step);
          }
        }
        break;
      case Op::NOT:
        if (const auto operand = exprValue(expr->getLeft(), step);
            operand.has_value()) {
          value = !*operand;
        }
        break;
      case Op::AND: {
        const auto lhs = exprValue(expr->getLeft(), step);
        if (lhs.has_value() && !*lhs) {
          value = false;
          break;
        }
        const auto rhs = exprValue(expr->getRight(), step);
        if (rhs.has_value() && !*rhs) {
          value = false;
        } else if (lhs.has_value() && rhs.has_value()) {
          value = *lhs && *rhs;
        }
        break;
      }
      case Op::OR: {
        const auto lhs = exprValue(expr->getLeft(), step);
        if (lhs.has_value() && *lhs) {
          value = true;
          break;
        }
        const auto rhs = exprValue(expr->getRight(), step);
        if (rhs.has_value() && *rhs) {
          value = true;
        } else if (lhs.has_value() && rhs.has_value()) {
          value = *lhs || *rhs;
        }
        break;
      }
      case Op::XOR: {
        const auto lhs = exprValue(expr->getLeft(), step);
        const auto rhs = exprValue(expr->getRight(), step);
        if (lhs.has_value() && rhs.has_value()) {
          value = *lhs != *rhs;
        }
        break;
      }
      case Op::NONE:
      default:
        break;  // LCOV_EXCL_LINE
    }

    memo.emplace(expr, value);
    return value;
  }

  const KInductionProblem& problem_;
  const TransitionExprResolver& transitionByState_;
  std::unordered_map<size_t, bool> resetInputs_;
  std::unordered_map<size_t, bool> initialStates_;
  std::unordered_map<size_t, bool> bootstrapStates_;
  std::unordered_map<SymbolPair, std::optional<bool>, SymbolPairHash> stateMemo_;
  std::vector<std::unordered_map<BoolExpr*, std::optional<bool>>> exprMemoByStep_;
  size_t stateEvaluations_ = 0;
  size_t exprEvaluations_ = 0;
  bool budgetExhausted_ = false;
};

bool cubeContradictsResetSpecializedConstants(
    const KInductionProblem& problem,
    const TransitionExprResolver& transitionByState,
    const StateCube& cube) {
  if (problem.resetBootstrapCycles == 0) {
    return false;  // LCOV_EXCL_LINE
  }

  ResetConstantEvaluator evaluator(problem, transitionByState);
  for (const auto& literal : cube) {
    const auto resetValue =
        evaluator.stateValue(literal.symbol, problem.resetBootstrapCycles);
    if (resetValue.has_value() && *resetValue != literal.value) {
      return true;
    }
    if (evaluator.budgetExhausted()) {
      return false;  // LCOV_EXCL_LINE
    }
  }
  return false;
}

void addFormulaSymbols(BoolExpr* formula, std::unordered_set<size_t>& symbols) {
  if (formula == nullptr) {
    return;  // LCOV_EXCL_LINE
  }
  for (const auto symbol : formula->getSupportVars()) {
    if (symbol >= 2) {
      symbols.insert(symbol);
    }
  }
}

void addFormulaStateSupport(BoolExpr* formula,
                            const std::unordered_set<size_t>& stateSymbols,
                            std::unordered_set<size_t>& output) {
  if (formula == nullptr) {
    return;  // LCOV_EXCL_LINE
  }
  for (const auto symbol : formula->getSupportVars()) {
    if (stateSymbols.find(symbol) != stateSymbols.end()) {
      output.insert(symbol);
    }
  }
}

void addRelevantComplementedStatePartners(
    const ComplementPartnerIndex& complementPartners,
    std::unordered_set<size_t>& symbols) {
  std::vector<size_t> worklist(symbols.begin(), symbols.end());
  for (size_t cursor = 0; cursor < worklist.size(); ++cursor) {
    const auto partnerIt =
        complementPartners.partnersBySymbol.find(worklist[cursor]);
    if (partnerIt == complementPartners.partnersBySymbol.end()) {
      continue;
    }
    for (const auto partnerSymbol : partnerIt->second) {
      if (symbols.insert(partnerSymbol).second) {
        worklist.push_back(partnerSymbol);
      }
    }
  }
}

void addRelevantComplementedStatePartners(
    const std::vector<std::pair<size_t, size_t>>& complementedStatePairs,
    std::unordered_set<size_t>& symbols) {
  for (const auto& [primarySymbol, complementedSymbol] : complementedStatePairs) {
    if (symbols.find(primarySymbol) != symbols.end() ||
        symbols.find(complementedSymbol) != symbols.end()) {
      symbols.insert(primarySymbol);
      symbols.insert(complementedSymbol);
    }
  }
}

bool hasStructuredInitFacts(const KInductionProblem& problem) {
  if (problem.resetBootstrapCycles != 0) {
    return !problem.bootstrapStateAssignments.empty() ||
           !problem.bootstrapStateEqualityPairs.empty();
  }
  return !problem.initialStateAssignments.empty() ||
         !problem.initialStateEqualityPairs.empty();
}

void addRelevantInitConstraintSymbols(const KInductionProblem& problem,
                                      std::unordered_set<size_t>& symbols) {
  const bool usesBootstrapFrontier = problem.resetBootstrapCycles != 0;
  const auto& assignments = usesBootstrapFrontier
                                ? problem.bootstrapStateAssignments
                                : problem.initialStateAssignments;
  const auto& equalities = usesBootstrapFrontier
                               ? problem.bootstrapStateEqualityPairs
                               : problem.initialStateEqualityPairs;

  for (const auto& [symbol, /*value*/ _] : assignments) {
    if (symbols.find(symbol) != symbols.end()) {
      symbols.insert(symbol);
    }
  }
  for (const auto& [lhsSymbol, rhsSymbol] : equalities) {
    const bool touchesQuery =
        symbols.find(lhsSymbol) != symbols.end() ||
        symbols.find(rhsSymbol) != symbols.end();
    if (!touchesQuery) {
      continue;
    }
    symbols.insert(lhsSymbol);
    symbols.insert(rhsSymbol);
  }
}

void addCubeSymbols(const StateCube& cube, std::unordered_set<size_t>& symbols) {
  for (const auto& literal : cube) {
    symbols.insert(literal.symbol);
  }
}

void addClauseSymbols(const StateClause& clause, std::unordered_set<size_t>& symbols) {
  for (const auto& literal : clause) {
    symbols.insert(literal.symbol);
  }
}

void ensureFrameClauseIndex(const FrameClauses& frame) {
  if (!frame.clauseIndexDirty) {
    return;
  }

  frame.clauseIndicesBySymbol.clear();
  for (size_t clauseIndex = 0; clauseIndex < frame.clauses.size(); ++clauseIndex) {
    for (const auto& literal : frame.clauses[clauseIndex]) {
      frame.clauseIndicesBySymbol[literal.symbol].push_back(clauseIndex);
    }
  }
  frame.clauseIndexDirty = false;
}

void addAllFrameClauseSymbols(const FrameClauses& frame,
                              std::unordered_set<size_t>& symbols) {
  for (const auto& clause : frame.clauses) {
    addClauseSymbols(clause, symbols);
  }
}

void addRelevantFrameClauseSymbols(const KInductionProblem& problem,
                                   const FrameClauses& frame,
                                   std::unordered_set<size_t>& symbols) {
  // Learned frame clauses are independent constraints.  Clauses outside the
  // current query cone may be omitted soundly, but once a relevant clause pulls
  // in a new symbol, clauses on that symbol can also be needed to avoid
  // repeatedly rediscovering states that are already blocked by the small
  // learned frame.  Close this relation to a bounded fixed point: exact for
  // small local frames, still capped for very large ASIC frames.
  (void)problem;
  ensureFrameClauseIndex(frame);
  const uint64_t emitEpoch = nextClauseEmitEpoch(frame);
  std::vector<size_t> worklist(symbols.begin(), symbols.end());
  size_t includedClauses = 0;
  size_t includedLiterals = 0;
  const size_t maxProjectedFrameClauses = maxProjectedFrameClausesPerQuery();
  const size_t maxProjectedFrameLiterals = maxProjectedFrameLiteralsPerQuery();
  for (size_t cursor = 0; cursor < worklist.size(); ++cursor) {
    const auto symbol = worklist[cursor];
    const auto indexIt = frame.clauseIndicesBySymbol.find(symbol);
    if (indexIt == frame.clauseIndicesBySymbol.end()) {
      continue;
    }
    for (const auto clauseIndex : indexIt->second) {
      if (includedClauses >= maxProjectedFrameClauses ||
          includedLiterals >= maxProjectedFrameLiterals) {
        return;
      }
      if (frame.clauseEmitEpochByIndex[clauseIndex] == emitEpoch) {
        continue;
      }
      const auto& clause = frame.clauses[clauseIndex];
      if (clause.size() > maxProjectedFrameLiterals) {
        continue;
      }
      if (includedLiterals + clause.size() > maxProjectedFrameLiterals &&
          includedClauses != 0) {
        continue;
      }
      frame.clauseEmitEpochByIndex[clauseIndex] = emitEpoch;
      ++includedClauses;
      includedLiterals += clause.size();
      for (const auto& literal : clause) {
        if (symbols.insert(literal.symbol).second) {
          worklist.push_back(literal.symbol);
        }
      }
    }
  }
}

void addFrameConstraintSymbols(const KInductionProblem& problem,
                               BoolExpr* initFormula,
                               BoolExpr* frameInvariant,
                               const std::vector<FrameClauses>& frames,
                               size_t level,
                               bool exactFrameClauses,
                               const ComplementPartnerIndex& complementPartners,
                               std::unordered_set<size_t>& symbols) {
  if (level == 0) {
    if (hasStructuredInitFacts(problem)) {
      // Keep Init cone-local even in the exact frame-clause retry. ASIC SEC
      // startup frontiers contain tens of thousands of equality facts, while a
      // predecessor query usually touches only a few of them. The exact retry
      // below disables learned-frame filtering, not this structured Init
      // sparsification.
      addRelevantInitConstraintSymbols(problem, symbols);
    } else {
      addFormulaSymbols(initFormula, symbols);
    }
    // Reset-bootstrap refinement clauses live in F[0]. Include their symbols
    // only when they touch the current query cone. ASIC PDR can learn many F[0]
    // CEGAR clauses; encoding all of them in every local predecessor query
    // turns unrelated output slices into a monolithic proof.
    if (exactFrameClauses) {
      addAllFrameClauseSymbols(frames[0], symbols);
    } else {
      addRelevantFrameClauseSymbols(problem, frames[0], symbols);
    }
  } else {
    addFormulaSymbols(frameInvariant, symbols);
    if (exactFrameClauses) {
      addAllFrameClauseSymbols(frames[level], symbols);
    } else {
      addRelevantFrameClauseSymbols(problem, frames[level], symbols);
    }
  }
  addRelevantComplementedStatePartners(complementPartners, symbols);
}

void addEncodedTransitionTargetSymbols(
    const KInductionProblem& problem,
    const ComplementPartnerIndex& complementPartners,
    const std::vector<size_t>& encodedTargets,
    const std::vector<size_t>& transitionSupportSymbols,
    std::unordered_set<size_t>& symbols) {
  // The predecessor query asks for one concrete transition into a target cube.
  // Its target list and support set are computed once in findPredecessorCube()
  // and threaded through these helpers; recomputing support here is expensive
  // on ASIC cones because each resolver lookup can walk a large formula DAG.
  symbols.insert(encodedTargets.begin(), encodedTargets.end());
  symbols.insert(transitionSupportSymbols.begin(), transitionSupportSymbols.end());
  addRelevantComplementedStatePartners(complementPartners, symbols);
}

std::vector<size_t> findBadQuerySymbols(const KInductionProblem& problem,
                                        BoolExpr* initFormula,
                                        BoolExpr* frameInvariant,
                                        const std::vector<FrameClauses>& frames,
                                        BoolExpr* badFormula,
                                        size_t level,
                                        const ComplementPartnerIndex& complementPartners,
                                        bool exactFrameClauses) {
  std::unordered_set<size_t> symbols;
  addFormulaSymbols(badFormula, symbols);
  addFrameConstraintSymbols(
      problem,
      initFormula,
      frameInvariant,
      frames,
      level,
      exactFrameClauses,
      complementPartners,
      symbols);
  return sortUniqueSymbols(std::move(symbols));
}

std::vector<size_t> predecessorCurrentFrameQuerySymbols(
    const KInductionProblem& problem,
    BoolExpr* initFormula,
    BoolExpr* frameInvariant,
    const std::vector<FrameClauses>& frames,
    size_t level,
    const StateCube& targetCube,
    bool excludeTargetOnCurrentFrame,
    const std::vector<size_t>& predecessorSymbols,
    const std::vector<size_t>& transitionSupportSymbols,
    const ComplementPartnerIndex& complementPartners,
    bool exactFrameClauses,
    const std::vector<StateClause>* extraFrameClauses) {
  std::unordered_set<size_t> symbols;
  symbols.reserve(
      predecessorSymbols.size() + transitionSupportSymbols.size() +
      (excludeTargetOnCurrentFrame ? targetCube.size() : 0));
  symbols.insert(predecessorSymbols.begin(), predecessorSymbols.end());
  addFrameConstraintSymbols(
      problem,
      initFormula,
      frameInvariant,
      frames,
      level,
      exactFrameClauses,
      complementPartners,
      symbols);
  if (predecessorSourceFrameIsKnownSafe(level)) {
    // The safe-frame property is encoded below, but it must not widen the
    // projected learned-frame surface. Otherwise every property-support state
    // bit can pull in large neighborhoods of unrelated frame clauses.
    addFormulaSymbols(problem.property, symbols);
  }
  for (const auto symbol : transitionSupportSymbols) {
    if (symbol >= 2) {
      symbols.insert(symbol);
    }
  }
  addRelevantComplementedStatePartners(complementPartners, symbols);
  if (excludeTargetOnCurrentFrame) {
    addCubeSymbols(targetCube, symbols);
  }
  if (extraFrameClauses != nullptr) {
    for (const auto& clause : *extraFrameClauses) {
      addClauseSymbols(clause, symbols);
    }
  }
  return sortUniqueSymbols(std::move(symbols));
}

std::vector<size_t> initIntersectionSymbols(const KInductionProblem& problem,
                                            BoolExpr* initFormula,
                                            const StateCube& cube) {
  // Init-intersection checks are issued many times during cube
  // generalization. They only need the startup formula, the candidate cube, and
  // complemented partners of those bits; allocating every SEC state/input here
  // made PDR spend most of its time constructing throwaway SAT variables.
  std::unordered_set<size_t> symbols;
  addFormulaSymbols(initFormula, symbols);
  for (const auto& literal : cube) {
    symbols.insert(literal.symbol);
  }
  addRelevantComplementedStatePartners(problem.complementedStatePairs0, symbols);
  addRelevantComplementedStatePartners(problem.complementedStatePairs1, symbols);
  return sortUniqueSymbols(std::move(symbols));
}

std::optional<bool> findCubeLiteralValue(const StateCube& cube, size_t symbol) {
  const auto it = std::lower_bound(
      cube.begin(),
      cube.end(),
      symbol,
      [](const CubeLiteral& literal, size_t requestedSymbol) {
        return literal.symbol < requestedSymbol;
      });
  if (it == cube.end() || it->symbol != symbol) {
    return std::nullopt;
  }
  return it->value;
}

bool contradictsAssignments(
    const StateCube& cube,
    const std::vector<std::pair<size_t, bool>>& initAssignments) {
  for (const auto& [symbol, value] : initAssignments) {
    if (const auto cubeValue = findCubeLiteralValue(cube, symbol);
        cubeValue.has_value() && *cubeValue != value) {
      return true;
    }
  }
  return false;
}

bool contradictsEqualities(
    const StateCube& cube,
    const std::vector<std::pair<size_t, size_t>>& equalities) {
  for (const auto& [lhsSymbol, rhsSymbol] : equalities) {
    const auto lhsValue = findCubeLiteralValue(cube, lhsSymbol);
    const auto rhsValue = findCubeLiteralValue(cube, rhsSymbol);
    if (lhsValue.has_value() && rhsValue.has_value() &&
        *lhsValue != *rhsValue) {
      return true;
    }
  }
  return false;
}

bool contradictsComplements(
    const StateCube& cube,
    const std::vector<std::pair<size_t, size_t>>& complements) {
  for (const auto& [primarySymbol, complementedSymbol] : complements) {
    const auto primaryValue = findCubeLiteralValue(cube, primarySymbol);
    const auto complementedValue = findCubeLiteralValue(cube, complementedSymbol);
    if (primaryValue.has_value() && complementedValue.has_value() &&
        *primaryValue == *complementedValue) {
      return true;
    }
  }
  return false;
}

std::optional<bool> cubeIntersectsKnownInitFacts(
    const KInductionProblem& problem,
    const StateCube& cube) {
  const bool usesBootstrapFrontier = problem.resetBootstrapCycles != 0;
  const auto& assignments = usesBootstrapFrontier
                                ? problem.bootstrapStateAssignments
                                : problem.initialStateAssignments;
  const auto& equalities = usesBootstrapFrontier
                               ? problem.bootstrapStateEqualityPairs
                               : problem.initialStateEqualityPairs;

  if (contradictsAssignments(cube, assignments) ||
      contradictsEqualities(cube, equalities)) {
    return false;
  }
  if (problem.complementedStatePairs0.size() <=
      kMaxComplementPairsForCheapInitCheck &&
      contradictsComplements(cube, problem.complementedStatePairs0)) {
    return false;
  }
  if (problem.complementedStatePairs1.size() <=
      kMaxComplementPairsForCheapInitCheck &&
      contradictsComplements(cube, problem.complementedStatePairs1)) {
    return false;
  }

  // The structured init/bootstrap facts are a cheap, explicit abstraction of
  // the startup frontier. If they do not visibly exclude this cube, be
  // conservative and keep the cube as init-intersecting instead of spending a
  // large SAT query only to drop one more literal during generalization.
  if (usesBootstrapFrontier || !assignments.empty() || !equalities.empty()) {
    return true;
  }
  return std::nullopt;
}

void addTransitionRelationForTargets(
    SATSolverWrapper& solver,
    const FrameVariableStore& variables,
    const TransitionExprResolver& transitionByState,
    size_t frame,
    const std::vector<size_t>& encodedTargets,
    const std::vector<size_t>& supportSymbols,
    bool createMissingTransitionLeaves = false,
    std::unordered_map<size_t, int>* encodedLeafLits = nullptr) {
  FrameFormulaEncoder encoder(
      solver,
      variables.makeLeafLits(frame, supportSymbols),
      createMissingTransitionLeaves,
      estimateTransitionEncodingNodes(transitionByState, encodedTargets));
  for (const auto stateSymbol : encodedTargets) {
    try {
      addLiteralEquivalence(
          solver,
          variables.getLiteral(stateSymbol, frame + 1),
          encoder.encode(transitionByState.at(stateSymbol)));
    } catch (const std::runtime_error& error) {
      throw std::runtime_error(
          "PDR transition relation encoding failed for target state symbol " +
          std::to_string(stateSymbol) + " at frame " + std::to_string(frame) +
          " with " + std::to_string(supportSymbols.size()) +
          " support symbols: " + error.what());
    }
  }
  if (encodedLeafLits != nullptr) {
    *encodedLeafLits = encoder.leafLits();
  }
}

void addTransitionConstraintsForTargetCube(
    SATSolverWrapper& solver,
    const FrameVariableStore& variables,
    const TransitionExprResolver& transitionByState,
    size_t frame,
    const StateCube& targetCube,
    const std::vector<size_t>& encodedTargets,
    const std::vector<size_t>& supportSymbols,
    std::unordered_map<size_t, int>* encodedLeafLits = nullptr) {
  FrameFormulaEncoder encoder(
      solver,
      variables.makeLeafLits(frame, supportSymbols),
      estimateTransitionEncodingNodes(transitionByState, encodedTargets));
  const auto& primaryByComplement = transitionByState.primaryByComplement();
  for (const auto& literal : targetCube) {
    size_t transitionSymbol = literal.symbol;
    bool desiredValue = literal.value;
    if (!transitionByState.contains(transitionSymbol)) {
      const auto primaryIt = primaryByComplement.find(transitionSymbol);
      if (primaryIt == primaryByComplement.end() ||
          !transitionByState.contains(primaryIt->second)) {
        continue;
      }
      transitionSymbol = primaryIt->second;
      desiredValue = !desiredValue;
    }
    // A predecessor query only asks whether the current frame can transition
    // into this target value.  Encoding a next-frame SAT variable and then
    // asserting next == target is equivalent but creates extra variables,
    // complemented-pair clauses, and two more equivalence clauses per target.
    int transitionLit = 0;
    try {
      transitionLit = encoder.encode(transitionByState.at(transitionSymbol));
    } catch (const std::runtime_error& error) {
      throw std::runtime_error(
          "PDR predecessor transition encoding failed for target state symbol " +
          std::to_string(transitionSymbol) + " at frame " +
          std::to_string(frame) + " with " +
          std::to_string(supportSymbols.size()) + " support symbols: " +
          error.what());
    }
    solver.addClause({desiredValue ? transitionLit : -transitionLit});
  }
  if (encodedLeafLits != nullptr) {
    *encodedLeafLits = encoder.leafLits();
  }
}

std::vector<std::pair<int, CubeLiteral>> addTransitionAssumptionsForTargetCube(
    SATSolverWrapper& solver,
    const FrameVariableStore& variables,
    const TransitionExprResolver& transitionByState,
    size_t frame,
    const StateCube& targetCube,
    const std::vector<size_t>& encodedTargets,
    const std::vector<size_t>& supportSymbols) {
  FrameFormulaEncoder encoder(
      solver,
      variables.makeLeafLits(frame, supportSymbols),
      estimateTransitionEncodingNodes(transitionByState, encodedTargets));
  const auto& primaryByComplement = transitionByState.primaryByComplement();
  std::vector<std::pair<int, CubeLiteral>> assumptions;
  assumptions.reserve(targetCube.size());
  for (const auto& literal : targetCube) {
    size_t transitionSymbol = literal.symbol;
    bool desiredValue = literal.value;
    if (!transitionByState.contains(transitionSymbol)) {
      const auto primaryIt = primaryByComplement.find(transitionSymbol);
      if (primaryIt == primaryByComplement.end() ||
          !transitionByState.contains(primaryIt->second)) {
        continue;
      }
      transitionSymbol = primaryIt->second;
      desiredValue = !desiredValue;
    }
    int transitionLit = 0;
    try {
      transitionLit = encoder.encode(transitionByState.at(transitionSymbol));
    } catch (const std::runtime_error& error) {
      throw std::runtime_error(
          "PDR predecessor core encoding failed for target state symbol " +
          std::to_string(transitionSymbol) + " at frame " +
          std::to_string(frame) + " with " +
          std::to_string(supportSymbols.size()) +
          " support symbols: " + error.what());
    }
    assumptions.emplace_back(
        desiredValue ? transitionLit : -transitionLit,
        literal);
  }
  return assumptions;
}

std::vector<size_t> predecessorProjectionSymbols(
    const KInductionProblem& problem,
    const TransitionExprResolver& transitionByState,
    BoolExpr* initFormula,
    BoolExpr* frameInvariant,
    const std::vector<FrameClauses>& frames,
    size_t level,
    const ComplementPartnerIndex& complementPartners,
    const std::vector<size_t>& transitionSupportSymbols) {
  // This routine runs for every predecessor query.  Reuse the resolver's
  // cached state-symbol set instead of rebuilding the large miter-state hash
  // table on each PDR obligation.
  const auto& stateSymbolSet = transitionByState.stateSymbols();

  std::unordered_set<size_t> projection;
  projection.reserve(transitionSupportSymbols.size());
  for (const auto supportSymbol : transitionSupportSymbols) {
    if (stateSymbolSet.find(supportSymbol) != stateSymbolSet.end()) {
      projection.insert(supportSymbol);
    }
  }
  if (level == 0) {
    if (hasStructuredInitFacts(problem)) {
      // Most SEC startup formulas are generated from explicit state
      // assignments/equalities.  Use those structured facts to pull in only
      // init partners relevant to the current transition cone; scanning the
      // full monolithic init BoolExpr here dominated large PDR predecessor
      // queries even though the query itself encoded only a small slice.
      addRelevantInitConstraintSymbols(problem, projection);
    } else {
      addFormulaStateSupport(initFormula, stateSymbolSet, projection);
    }
  } else {
    addRelevantFrameClauseSymbols(problem, frames[level], projection);
    addFormulaStateSupport(frameInvariant, stateSymbolSet, projection);
  }
  addRelevantComplementedStatePartners(complementPartners, projection);
  return sortUniqueSymbols(std::move(projection));
}

void addComplementedStateRelations(
    SATSolverWrapper& solver,
    const FrameVariableStore& variables,
    const std::vector<std::pair<size_t, size_t>>& complementedStatePairs,
    size_t numFrames) {
  for (size_t frame = 0; frame < numFrames; ++frame) {
    for (const auto& [primarySymbol, complementedSymbol] : complementedStatePairs) {
      if (!variables.hasSymbol(primarySymbol) ||
          !variables.hasSymbol(complementedSymbol)) {
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

void normalizeCube(StateCube& cube) {
  // Canonical ordering lets us compare cubes structurally and avoid learning
  // the same obligation more than once with a different literal order.
  std::sort(cube.begin(), cube.end(), [](const CubeLiteral& lhs, const CubeLiteral& rhs) {
    if (lhs.symbol != rhs.symbol) {
      return lhs.symbol < rhs.symbol;
    }
    return lhs.value < rhs.value;  // LCOV_EXCL_LINE
  });
  cube.erase(std::unique(cube.begin(), cube.end()), cube.end());
}

void normalizeClause(StateClause& clause) {
  // Clauses are canonicalized for the same reason: later subsumption and
  // convergence checks depend on stable ordering and deduplication.
  std::sort(
      clause.begin(), clause.end(), [](const ClauseLiteral& lhs, const ClauseLiteral& rhs) {
        if (lhs.symbol != rhs.symbol) {
          return lhs.symbol < rhs.symbol;
        }
        return lhs.positive < rhs.positive;  // LCOV_EXCL_LINE
      });
  clause.erase(std::unique(clause.begin(), clause.end()), clause.end());
}

SymbolPair canonicalPair(size_t lhs, size_t rhs) {
  if (rhs < lhs) {
    std::swap(lhs, rhs);
  }
  return SymbolPair{lhs, rhs};
}

InitFactIndex buildInitFactIndex(const KInductionProblem& problem) {
  const bool usesBootstrapFrontier = problem.resetBootstrapCycles != 0;
  const auto& assignments = usesBootstrapFrontier
                                ? problem.bootstrapStateAssignments
                                : problem.initialStateAssignments;
  const auto& equalities = usesBootstrapFrontier
                               ? problem.bootstrapStateEqualityPairs
                               : problem.initialStateEqualityPairs;

  InitFactIndex index;
  index.assignments.reserve(assignments.size());
  for (const auto& [symbol, value] : assignments) {
    index.assignments.emplace(symbol, value);
  }
  index.equalities.reserve(equalities.size());
  for (const auto& [lhsSymbol, rhsSymbol] : equalities) {
    index.equalities.insert(canonicalPair(lhsSymbol, rhsSymbol));
  }
  index.complements.reserve(
      problem.complementedStatePairs0.size() +
      problem.complementedStatePairs1.size());
  for (const auto& [primarySymbol, complementedSymbol] :
       problem.complementedStatePairs0) {
    index.complements.insert(canonicalPair(primarySymbol, complementedSymbol));
  }
  for (const auto& [primarySymbol, complementedSymbol] :
       problem.complementedStatePairs1) {
    index.complements.insert(canonicalPair(primarySymbol, complementedSymbol));
  }
  return index;
}

std::optional<StateCube> knownInitConflictCube(const InitFactIndex& facts,
                                               const StateCube& cube) {
  // PDR frequently reaches a level-0 cube that is impossible only because it
  // violates a startup equality such as "state0 == state1".  Learning the full
  // 100+ literal cube makes the engine enumerate many adjacent impossible
  // startup states.  This extractor turns the visible conflict into the
  // smallest safe cube:
  //   - one literal for an init assignment conflict;
  //   - two literals for equality/complement conflicts.
  // The learned clause is still exactly an Init consequence, but much stronger.
  for (const auto& literal : cube) {
    const auto assignment = facts.assignments.find(literal.symbol);
    if (assignment != facts.assignments.end() &&
        assignment->second != literal.value) {
      StateCube conflict{literal};
      normalizeCube(conflict);
      return conflict;
    }
  }

  for (size_t lhsIndex = 0; lhsIndex < cube.size(); ++lhsIndex) {
    for (size_t rhsIndex = lhsIndex + 1; rhsIndex < cube.size(); ++rhsIndex) {
      const auto& lhs = cube[lhsIndex];
      const auto& rhs = cube[rhsIndex];
      if (lhs.symbol == rhs.symbol) {
        continue;  // LCOV_EXCL_LINE
      }

      const SymbolPair pair = canonicalPair(lhs.symbol, rhs.symbol);
      if (lhs.value != rhs.value &&
          facts.equalities.find(pair) != facts.equalities.end()) {
        StateCube conflict{lhs, rhs};
        normalizeCube(conflict);
        return conflict;
      }
      if (lhs.value == rhs.value &&
          facts.complements.find(pair) != facts.complements.end()) {
        StateCube conflict{lhs, rhs};
        normalizeCube(conflict);
        return conflict;
      }
    }
  }

  return std::nullopt;
}

bool twoLiteralCubeIsKnownOutsideInit(const InitFactIndex& facts,
                                      size_t lhsSymbol,
                                      bool lhsValue,
                                      size_t rhsSymbol,
                                      bool rhsValue) {
  if (const auto lhsAssignment = facts.assignments.find(lhsSymbol);
      lhsAssignment != facts.assignments.end() &&
      lhsAssignment->second != lhsValue) {
    return true;
  }
  if (const auto rhsAssignment = facts.assignments.find(rhsSymbol);
      rhsAssignment != facts.assignments.end() &&
      rhsAssignment->second != rhsValue) {
    return true;
  }
  return lhsValue != rhsValue &&
         facts.equalities.find(canonicalPair(lhsSymbol, rhsSymbol)) !=
             facts.equalities.end();
}

StateClause clauseFromCube(const StateCube& cube) {
  StateClause clause;
  clause.reserve(cube.size());
  for (const auto& literal : cube) {
    clause.push_back({literal.symbol, !literal.value});
  }
  normalizeClause(clause);
  return clause;
}

StateCube cubeFromClauseNegation(const StateClause& clause) {
  StateCube cube;
  cube.reserve(clause.size());
  for (const auto& literal : clause) {
    cube.push_back({literal.symbol, !literal.positive});
  }
  normalizeCube(cube);
  return cube;
}

bool clauseSubsumes(const StateClause& lhs, const StateClause& rhs) {
  return std::includes(rhs.begin(), rhs.end(), lhs.begin(), lhs.end(),
                       [](const ClauseLiteral& a, const ClauseLiteral& b) {
                         if (a.symbol != b.symbol) {
                           return a.symbol < b.symbol;
                         }
                         return a.positive < b.positive;
                       });
}

bool frameHasSubsumingClause(const FrameClauses& frame, const StateClause& clause) {
  for (const auto& existingClause : frame.clauses) {
    if (clauseSubsumes(existingClause, clause)) {
      return true;
    }
  }
  return false;
}

std::optional<StateClause> findSubsumingFrameClause(
    const FrameClauses& frame,
    const StateClause& clause) {
  for (const auto& existingClause : frame.clauses) {
    if (clauseSubsumes(existingClause, clause)) {
      return existingClause;
    }
  }
  return std::nullopt;
}

void addClauseToFrame(FrameClauses& frame, StateClause clause) {
  normalizeClause(clause);
  if (frameHasSubsumingClause(frame, clause)) {
    return;
  }

  // Keep each frame minimal so later SAT queries do not carry redundant facts.
  frame.clauses.erase(
      std::remove_if(
          frame.clauses.begin(),
          frame.clauses.end(),
          [&](const StateClause& existingClause) {
            return clauseSubsumes(clause, existingClause);
          }),
      frame.clauses.end());
  frame.clauses.push_back(std::move(clause));
  frame.clauseIndexDirty = true;
}

void addClauseToFrames(std::vector<FrameClauses>& frames,
                       const StateClause& clause,
                       size_t maxLevel) {
  for (size_t level = 1; level <= maxLevel; ++level) {
    addClauseToFrame(frames[level], clause);
  }
}

std::optional<std::vector<StateClause>> stateOnlyBadFormulaClauses(
    BoolExpr* badFormula,
    const std::unordered_set<size_t>& stateSymbols) {
  if (badFormula == nullptr) {
    return std::nullopt;
  }

  const auto supportSet = badFormula->getSupportVars();
  if (supportSet.size() > kMaxValidatedBadFormulaCnfSupport) {
    return std::nullopt;
  }
  for (const auto symbol : supportSet) {
    if (stateSymbols.find(symbol) == stateSymbols.end()) {
      return std::nullopt;
    }
  }

  std::vector<size_t> support(supportSet.begin(), supportSet.end());
  std::vector<StateClause> clauses;
  const size_t assignmentCount = static_cast<size_t>(1) << support.size();
  clauses.reserve(assignmentCount);
  for (size_t mask = 0; mask < assignmentCount; ++mask) {
    std::unordered_map<size_t, bool> env;
    env.reserve(support.size());
    for (size_t bit = 0; bit < support.size(); ++bit) {
      env.emplace(support[bit], ((mask >> bit) & 1u) != 0u);
    }
    if (!badFormula->evaluate(env)) {
      continue;
    }

    StateClause clause;
    clause.reserve(support.size());
    for (const auto symbol : support) {
      const bool value = env.at(symbol);
      // Forbid exactly this bad assignment.
      clause.push_back({symbol, !value});
    }
    normalizeClause(clause);
    clauses.push_back(std::move(clause));
  }
  return clauses;
}

bool appendStateOnlyBadFormulaClauses(
    std::vector<StateClause>& target,
    BoolExpr* badFormula,
    const std::unordered_set<size_t>& stateSymbols) {
  const auto clauses = stateOnlyBadFormulaClauses(badFormula, stateSymbols);
  if (!clauses.has_value() || clauses->empty()) {
    return false;
  }
  if (target.size() + clauses->size() > kMaxValidatedBadFormulaClauses) {
    return false;
  }
  target.insert(target.end(), clauses->begin(), clauses->end());
  return true;
}

std::optional<std::vector<StateClause>> observedOutputBadFormulaClauses(
    const KInductionProblem& problem,
    const std::unordered_set<size_t>& stateSymbols) {
  if (problem.observedOutputExprs0.size() <= 1 ||
      problem.observedOutputExprs0.size() != problem.observedOutputExprs1.size()) {
    return std::nullopt;
  }

  std::vector<StateClause> clauses;
  for (size_t output = 0; output < problem.observedOutputExprs0.size(); ++output) {
    BoolExpr* outputBad = BoolExpr::simplify(
        BoolExpr::Xor(
            problem.observedOutputExprs0[output],
            problem.observedOutputExprs1[output]));
    // A rejected batched SEC counterexample proves the OR of output mismatches
    // unreachable at this frame. Therefore each small state-only disjunct can
    // be learned independently, while unsupported or too-wide disjuncts simply
    // remain for normal PDR search.
    appendStateOnlyBadFormulaClauses(clauses, outputBad, stateSymbols);
    if (clauses.size() >= kMaxValidatedBadFormulaClauses) {
      break;
    }
  }
  if (clauses.empty()) {
    return std::nullopt;
  }
  return clauses;
}

std::optional<bool> learnValidatedBadFormulaClauses(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    const TransitionExprResolver& transitionByState,
    std::vector<FrameClauses>& frames,
    size_t targetFrame,
    size_t& badFrame) {
  auto badClauses =
      observedOutputBadFormulaClauses(problem, transitionByState.stateSymbols());
  if (!badClauses.has_value()) {
    badClauses =
        stateOnlyBadFormulaClauses(problem.bad, transitionByState.stateSymbols());
  }
  if (!badClauses.has_value() || badClauses->empty()) {
    return std::nullopt;
  }

  if (SEC::findBaseCounterexampleAtFrontier(
          problem, solverType, targetFrame)
          .has_value()) {
    badFrame = targetFrame;
    return false;
  }

  for (const auto& clause : *badClauses) {
    addClauseToFrames(frames, clause, targetFrame);
  }
  if (pdrStatsEnabled()) {
    emitSecDiag(
        "SEC PDR stats: refined projected counterexample with validated "
        "bad-formula clauses ",
        "bad_frame=", targetFrame,
        " clauses=", badClauses->size());
  }
  return true;
}

void addStateClause(SATSolverWrapper& solver,
                    const FrameVariableStore& variables,
                    const StateClause& clause,
                    size_t frame) {
  std::vector<int> satClause;
  satClause.reserve(clause.size());
  for (const auto& literal : clause) {
    const int satLiteral = variables.getLiteral(literal.symbol, frame);
    satClause.push_back(literal.positive ? satLiteral : -satLiteral);
  }
  solver.addClause(satClause);
}

bool clauseCoveredByVariables(const FrameVariableStore& variables,
                              const StateClause& clause) {
  for (const auto& literal : clause) {
    if (!variables.hasSymbol(literal.symbol)) {
      return false;
    }
  }
  return true;
}

uint64_t nextClauseEmitEpoch(const FrameClauses& frameClauses) {
  if (frameClauses.clauseEmitEpochByIndex.size() !=
      frameClauses.clauses.size()) {
    frameClauses.clauseEmitEpochByIndex.assign(
        frameClauses.clauses.size(), 0);
  }
  ++frameClauses.clauseEmitEpoch;
  if (frameClauses.clauseEmitEpoch == 0) {
    // Practically unreachable, but keep the epoch scheme correct even after an
    // absurd number of local PDR queries.
    std::fill(
        frameClauses.clauseEmitEpochByIndex.begin(),
        frameClauses.clauseEmitEpochByIndex.end(),
        0);
    frameClauses.clauseEmitEpoch = 1;
  }
  return frameClauses.clauseEmitEpoch;
}

void addIndexedFrameClauses(SATSolverWrapper& solver,
                            const FrameVariableStore& variables,
                            const FrameClauses& frameClauses,
                            const std::vector<size_t>& querySymbols,
                            size_t frame) {
  // Frame clauses are filtered twice.  First use the lazy symbol index to pull
  // only clauses that touch the current SAT query.  Then keep the existing
  // variable-coverage guard because complemented partners and formula support
  // can make a symbol present without allocating every literal in a clause.
  //
  // This is intentionally an over-approximate PDR frame: omitting unrelated
  // clauses makes the predecessor query weaker, which can produce spurious
  // obligations but cannot justify an unsound blocking clause.
  ensureFrameClauseIndex(frameClauses);
  const uint64_t emitEpoch = nextClauseEmitEpoch(frameClauses);
  size_t emittedClauses = 0;
  size_t emittedLiterals = 0;
  const size_t maxProjectedFrameClauses = maxProjectedFrameClausesPerQuery();
  const size_t maxProjectedFrameLiterals = maxProjectedFrameLiteralsPerQuery();
  for (const auto symbol : querySymbols) {
    if (emittedClauses >= maxProjectedFrameClauses ||
        emittedLiterals >= maxProjectedFrameLiterals) {
      break;
    }
    const auto indexIt = frameClauses.clauseIndicesBySymbol.find(symbol);
    if (indexIt == frameClauses.clauseIndicesBySymbol.end()) {
      continue;
    }
    for (const auto clauseIndex : indexIt->second) {
      if (emittedClauses >= maxProjectedFrameClauses ||
          emittedLiterals >= maxProjectedFrameLiterals) {
        return;
      }
      if (frameClauses.clauseEmitEpochByIndex[clauseIndex] == emitEpoch) {
        continue;
      }
      frameClauses.clauseEmitEpochByIndex[clauseIndex] = emitEpoch;
      const auto& clause = frameClauses.clauses[clauseIndex];
      if (!clauseCoveredByVariables(variables, clause)) {
        continue;
      }
      if (clause.size() > maxProjectedFrameLiterals) {
        continue;
      }
      if (emittedLiterals + clause.size() > maxProjectedFrameLiterals &&
          emittedClauses != 0) {
        continue;
      }
      addStateClause(solver, variables, clause, frame);
      ++emittedClauses;
      emittedLiterals += clause.size();
    }
  }
}

void addAllFrameClauses(SATSolverWrapper& solver,
                        const FrameVariableStore& variables,
                        const FrameClauses& frameClauses,
                        size_t frame) {
  // Normal projected PDR intentionally emits only cone-relevant clauses.  The
  // exact retry uses the same blocking algorithm but disables projection, so it
  // should also see the complete learned frame for its already-pruned local
  // output slice.
  for (const auto& clause : frameClauses.clauses) {
    if (!clauseCoveredByVariables(variables, clause)) {
      continue;  // LCOV_EXCL_LINE
    }
    addStateClause(solver, variables, clause, frame);
  }
}

void addCubeAssumptions(SATSolverWrapper& solver,
                        const FrameVariableStore& variables,
                        const StateCube& cube,
                        size_t frame) {
  for (const auto& literal : cube) {
    solver.addClause(
        {literal.value ? variables.getLiteral(literal.symbol, frame)
                       : -variables.getLiteral(literal.symbol, frame)});
  }
}

void addNegatedCubeClause(SATSolverWrapper& solver,
                          const FrameVariableStore& variables,
                          const StateCube& cube,
                          size_t frame) {
  std::vector<int> satClause;
  satClause.reserve(cube.size());
  for (const auto& literal : cube) {
    const int satLiteral = variables.getLiteral(literal.symbol, frame);
    satClause.push_back(literal.value ? -satLiteral : satLiteral);
  }
  solver.addClause(satClause);
}

void addPostBootstrapResetInputConstraints(
    SATSolverWrapper& solver,
    const FrameVariableStore& variables,
    const KInductionProblem& problem,
    size_t frame) {
  if (problem.resetBootstrapCycles == 0) {
    return;
  }

  // PDR frames are already positioned after the concrete reset prefix. The
  // reset controls are therefore no longer free environment inputs in one-step
  // predecessor queries; they must stay at their deasserted value on every PDR
  // transition, exactly as the concrete base solver constrains them.
  for (const auto& [symbol, assertedValue] : problem.resetBootstrapInputs) {
    if (!variables.hasSymbol(symbol)) {
      continue;
    }
    solver.addClause(
        {assertedValue ? -variables.getLiteral(symbol, frame)
                       : variables.getLiteral(symbol, frame)});
  }
}

void addLiteralEqualityAtFrame(SATSolverWrapper& solver,
                               const FrameVariableStore& variables,
                               size_t lhsSymbol,
                               size_t rhsSymbol,
                               size_t frame) {
  if (!variables.hasSymbol(lhsSymbol) || !variables.hasSymbol(rhsSymbol)) {
    return;
  }
  const int lhs = variables.getLiteral(lhsSymbol, frame);
  const int rhs = variables.getLiteral(rhsSymbol, frame);
  solver.addClause({-lhs, rhs});
  solver.addClause({lhs, -rhs});
}

bool addRelevantStructuredInitConstraints(
    const KInductionProblem& problem,
    SATSolverWrapper& solver,
    const FrameVariableStore& variables,
    const std::vector<size_t>& querySymbols,
    size_t frame) {
  const bool usesBootstrapFrontier = problem.resetBootstrapCycles != 0;
  const auto& assignments = usesBootstrapFrontier
                                ? problem.bootstrapStateAssignments
                                : problem.initialStateAssignments;
  const auto& equalities = usesBootstrapFrontier
                               ? problem.bootstrapStateEqualityPairs
                               : problem.initialStateEqualityPairs;

  std::unordered_set<size_t> querySet(querySymbols.begin(), querySymbols.end());
  bool addedConstraint = false;
  for (const auto& [symbol, value] : assignments) {
    if (querySet.find(symbol) == querySet.end() ||
        !variables.hasSymbol(symbol)) {
      continue;
    }
    solver.addClause(
        {value ? variables.getLiteral(symbol, frame)
               : -variables.getLiteral(symbol, frame)});
    addedConstraint = true;
  }
  for (const auto& [lhsSymbol, rhsSymbol] : equalities) {
    const bool touchesQuery =
        querySet.find(lhsSymbol) != querySet.end() ||
        querySet.find(rhsSymbol) != querySet.end();
    if (!touchesQuery) {
      continue;
    }
    addLiteralEqualityAtFrame(solver, variables, lhsSymbol, rhsSymbol, frame);
    addedConstraint = true;
  }
  return addedConstraint;
}

void addFrameConstraints(SATSolverWrapper& solver,
                         const FrameVariableStore& variables,
                         const KInductionProblem& problem,
                         BoolExpr* initFormula,
                         BoolExpr* frameInvariant,
                         const std::vector<FrameClauses>& frames,
                         size_t level,
                         size_t frame,
                         const std::vector<size_t>& querySymbols,
                         bool exactFrameClauses) {
  if (level == 0) {
    // F[0] is Init, so the SAT query is anchored directly in the startup
    // frontier rather than in learned blocking clauses.
    const bool emittedStructuredInit = addRelevantStructuredInitConstraints(
        problem, solver, variables, querySymbols, frame);
    if (!emittedStructuredInit && initFormula != nullptr &&
        !hasStructuredInitFacts(problem)) {
      // Observation-only startups have no per-symbol structured summary, so
      // the exact init formula must remain as the F[0] fallback. When
      // structured init facts do exist, an empty relevant subset simply means
      // the local cone is unconstrained by Init; falling back to the full
      // monolithic init formula would reintroduce unrelated symbols into a
      // reduced compact-PDR query and can make the encoder reference leaves
      // that were intentionally left out of the local solver.
      FrameFormulaEncoder encoder(solver, variables.makeLeafLits(frame));
      try {
        solver.addClause({encoder.encode(initFormula)});
      } catch (const std::runtime_error& error) {
        throw std::runtime_error(
            "PDR init-frame encoding failed at frame " + std::to_string(frame) +
            ": " + error.what());
      }
    }
    // With reset-bootstrap SEC, F[0] can be a safe abstraction of the concrete
    // post-reset image. PDR may add refinement clauses here when an abstract
    // level-0 obligation is proven outside that concrete image.
    if (exactFrameClauses) {
      addAllFrameClauses(solver, variables, frames[0], frame);
    } else {
      addIndexedFrameClauses(solver, variables, frames[0], querySymbols, frame);
    }
    return;
  }

  // For higher frames, materialize the currently learned blocking clauses and
  // any validated strengthening invariant the strategy handed to PDR.
  if (exactFrameClauses) {
    addAllFrameClauses(solver, variables, frames[level], frame);
  } else {
    addIndexedFrameClauses(solver, variables, frames[level], querySymbols, frame);
  }
  if (frameInvariant != nullptr) {
    // The optional strengthening is treated exactly like a frame fact, but it
    // is validated before we allow the engine to rely on it.
    FrameFormulaEncoder encoder(solver, variables.makeLeafLits(frame));  // LCOV_EXCL_LINE
    try {  // LCOV_EXCL_LINE
      solver.addClause({encoder.encode(frameInvariant)});  // LCOV_EXCL_LINE
    } catch (const std::runtime_error& error) {  // LCOV_EXCL_LINE
      throw std::runtime_error(  // LCOV_EXCL_LINE
          "PDR frame invariant encoding failed at frame " +
          std::to_string(frame) + ": " + error.what());  // LCOV_EXCL_LINE
    }  // LCOV_EXCL_LINE
  }  // LCOV_EXCL_LINE
}

bool predecessorSourceFrameIsKnownSafe(size_t level) {
  // Predecessor queries are only issued from frames that were already checked
  // safe in an earlier PDR phase: blocking a bad cube at F[i+1] asks from F[i],
  // and propagation runs after the current frontier has been exhausted. F[0]
  // is the startup frontier and is handled separately by Init/reset facts.
  return level > 0;
}

void addSafeFramePropertyConstraint(SATSolverWrapper& solver,
                                    const FrameVariableStore& variables,
                                    const KInductionProblem& problem,
                                    size_t level,
                                    size_t frame) {
  if (!predecessorSourceFrameIsKnownSafe(level) || problem.property == nullptr) {
    return;
  }
  // Projected frame clauses intentionally omit unrelated learned clauses to
  // keep ASIC predecessor queries local. The property is the one frame fact we
  // must not let projection forget for already-safe frames; adding it is
  // logically redundant for exact PDR, but avoids fake init-reaching paths
  // that then need expensive concrete reset-frontier validation.
  FrameFormulaEncoder encoder(solver, variables.makeLeafLits(frame));  // LCOV_EXCL_LINE
  try {  // LCOV_EXCL_LINE
    solver.addClause({encoder.encode(problem.property)});  // LCOV_EXCL_LINE
  } catch (const std::runtime_error& error) {  // LCOV_EXCL_LINE
    throw std::runtime_error(  // LCOV_EXCL_LINE
        "PDR safe-frame property encoding failed at frame " +
        std::to_string(frame) + ": " + error.what());  // LCOV_EXCL_LINE
  }  // LCOV_EXCL_LINE
}

StateCube extractStateCube(const SATSolverWrapper& solver,
                           const FrameVariableStore& variables,
                           const std::vector<size_t>& stateSymbols,
                           size_t frame) {
  StateCube cube;
  cube.reserve(stateSymbols.size());
  for (const auto symbol : stateSymbols) {
    cube.push_back({symbol, solver.getLiteralValue(variables.getLiteral(symbol, frame))});
  }
  normalizeCube(cube);
  return cube;
}

void addComplementedPartnerAssignments(
    const SATSolverWrapper& solver,
    const FrameVariableStore& variables,
    const ComplementPartnerIndex& complementPartners,
    size_t frame,
    std::unordered_map<size_t, bool>& assignments) {
  // Predecessor projection cubes are intentionally tiny, while ASIC SEC
  // designs can have thousands of complemented flop pairs. Walk only the
  // partners of symbols already present in the cube instead of rescanning the
  // whole pair table for every SAT predecessor query.
  std::vector<size_t> worklist;
  worklist.reserve(assignments.size());
  for (const auto& [symbol, value] : assignments) {
    (void)value;
    worklist.push_back(symbol);
  }

  for (size_t index = 0; index < worklist.size(); ++index) {
    const size_t symbol = worklist[index];
    const auto partnersIt = complementPartners.partnersBySymbol.find(symbol);
    if (partnersIt == complementPartners.partnersBySymbol.end()) {
      continue;
    }
    if (!variables.hasSymbol(symbol)) {
      continue;  // LCOV_EXCL_LINE
    }
    for (const auto partnerSymbol : partnersIt->second) {
      if (assignments.find(partnerSymbol) != assignments.end() ||
          !variables.hasSymbol(partnerSymbol)) {
        continue;
      }
      assignments[partnerSymbol] =
          solver.getLiteralValue(variables.getLiteral(partnerSymbol, frame));
      worklist.push_back(partnerSymbol);
    }
  }
}

bool formulaModelValue(const SATSolverWrapper& solver,
                       const std::unordered_map<size_t, int>& leafLits,
                       BoolExpr* formula,
                       std::unordered_map<BoolExpr*, bool>& memo) {
  if (formula == nullptr) {
    return false;  // LCOV_EXCL_LINE
  }
  if (const auto it = memo.find(formula); it != memo.end()) {
    return it->second;
  }

  bool value = false;
  switch (formula->getOp()) {
    case Op::VAR:
      if (formula->getId() == 0) {
        value = false;
      } else if (formula->getId() == 1) {
        value = true;
      } else {
        value = solver.getLiteralValue(leafLits.at(formula->getId()));
      }
      break;
    case Op::NOT:
      value = !formulaModelValue(
          solver, leafLits, formula->getLeft(), memo);
      break;
    case Op::AND:
      value = formulaModelValue(
                  solver, leafLits, formula->getLeft(), memo) &&
              formulaModelValue(
                  solver, leafLits, formula->getRight(), memo);
      break;
    case Op::OR:
      value = formulaModelValue(
                  solver, leafLits, formula->getLeft(), memo) ||
              formulaModelValue(
                  solver, leafLits, formula->getRight(), memo);
      break;
    case Op::XOR:
      value = formulaModelValue(
                  solver, leafLits, formula->getLeft(), memo) ^
              formulaModelValue(
                  solver, leafLits, formula->getRight(), memo);
      break;
    case Op::NONE:
    default:
      value = false;  // LCOV_EXCL_LINE
      break;
  }
  memo.emplace(formula, value);
  return value;
}

void addJustifyingStateLiterals(
    const SATSolverWrapper& solver,
    const std::unordered_map<size_t, int>& leafLits,
    BoolExpr* formula,
    bool desiredValue,
    const std::unordered_set<size_t>& stateSymbols,
    std::unordered_map<BoolExpr*, bool>& valueMemo,
    std::unordered_map<size_t, bool>& assignments,
    JustificationBudget* budget = nullptr) {
  if (formula == nullptr) {
    return;  // LCOV_EXCL_LINE
  }
  if (budget != nullptr) {
    if (budget->exhausted ||
        budget->remainingVisits == 0 ||
        assignments.size() >= budget->maxAssignments) {
      budget->exhausted = true;
      return;
    }
    --budget->remainingVisits;
  }

  switch (formula->getOp()) {
    case Op::VAR:
      if (stateSymbols.find(formula->getId()) != stateSymbols.end()) {
        assignments[formula->getId()] = desiredValue;
        if (budget != nullptr && assignments.size() >= budget->maxAssignments) {
          budget->exhausted = true;
        }
      }
      return;
    case Op::NOT:
      addJustifyingStateLiterals(
          solver,
          leafLits,
          formula->getLeft(),
          !desiredValue,
          stateSymbols,
          valueMemo,
          assignments,
          budget);
      return;
    case Op::AND:
      if (desiredValue) {
        addJustifyingStateLiterals(
            solver, leafLits, formula->getLeft(), true,
            stateSymbols, valueMemo, assignments, budget);
        addJustifyingStateLiterals(
            solver, leafLits, formula->getRight(), true,
            stateSymbols, valueMemo, assignments, budget);
      } else {
        const bool leftValue = formulaModelValue(
            solver, leafLits, formula->getLeft(), valueMemo);
        addJustifyingStateLiterals(
            solver,
            leafLits,
            leftValue ? formula->getRight() : formula->getLeft(),
            false,
            stateSymbols,
            valueMemo,
            assignments,
            budget);
      }
      return;
    case Op::OR:
      if (desiredValue) {
        const bool leftValue = formulaModelValue(
            solver, leafLits, formula->getLeft(), valueMemo);
        addJustifyingStateLiterals(
            solver,
            leafLits,
            leftValue ? formula->getLeft() : formula->getRight(),
            true,
            stateSymbols,
            valueMemo,
            assignments,
            budget);
      } else {
        addJustifyingStateLiterals(
            solver, leafLits, formula->getLeft(), false,
            stateSymbols, valueMemo, assignments, budget);
        addJustifyingStateLiterals(
            solver, leafLits, formula->getRight(), false,
            stateSymbols, valueMemo, assignments, budget);
      }
      return;
    case Op::XOR: {
      const bool leftValue = formulaModelValue(
          solver, leafLits, formula->getLeft(), valueMemo);
      const bool rightValue = formulaModelValue(
          solver, leafLits, formula->getRight(), valueMemo);
      if ((leftValue ^ rightValue) == desiredValue) {
        addJustifyingStateLiterals(
            solver, leafLits, formula->getLeft(), leftValue,
            stateSymbols, valueMemo, assignments, budget);
        addJustifyingStateLiterals(
            solver, leafLits, formula->getRight(), rightValue,
            stateSymbols, valueMemo, assignments, budget);
      }
      return;
    }
    case Op::NONE:
    default:
      return;  // LCOV_EXCL_LINE
  }
}

StateCube extractBadJustificationCube(const SATSolverWrapper& solver,
                                      const FrameVariableStore& variables,
                                      BoolExpr* badFormula,
                                      const std::unordered_set<size_t>& stateSymbols,
                                      size_t maxAssignments,
                                      size_t frame) {
  std::unordered_map<BoolExpr*, bool> valueMemo;
  std::unordered_map<size_t, bool> assignments;
  const auto leafLits = variables.makeLeafLits(frame);
  JustificationBudget budget{
      std::max(
          kMinPredecessorJustificationVisits,
          maxAssignments * kPredecessorJustificationVisitMultiplier),
      maxAssignments,
      false};
  addJustifyingStateLiterals(
      solver,
      leafLits,
      badFormula,
      true,
      stateSymbols,
      valueMemo,
      assignments,
      maxAssignments == 0 ? nullptr : &budget);

  StateCube cube;
  cube.reserve(assignments.size());
  for (const auto& [symbol, value] : assignments) {
    cube.push_back({symbol, value});
  }
  normalizeCube(cube);
  return cube;
}

StateCube extractPredecessorJustificationCube(
    const SATSolverWrapper& solver,
    const FrameVariableStore& variables,
    const KInductionProblem& problem,
    const TransitionExprResolver& transitionByState,
    const StateCube& targetCube,
    const std::unordered_map<size_t, int>& transitionLeafLits,
    const ComplementPartnerIndex& complementPartners,
    size_t maxAssignments,
    size_t frame) {
  std::unordered_map<BoolExpr*, bool> valueMemo;
  std::unordered_map<size_t, bool> assignments;
  // This projection is a CEGAR-style obligation reduction. It is allowed to
  // return a subset of the satisfying predecessor model because every learned
  // clause is still guarded by a real predecessor query, and any reported
  // counterexample is concrete-BMC validated by the top SEC strategy.
  JustificationBudget budget{
      std::max(
          kMinPredecessorJustificationVisits,
          maxAssignments * kPredecessorJustificationVisitMultiplier),
      maxAssignments,
      false};
  const auto& stateSymbols = transitionByState.stateSymbols();
  const auto& primaryByComplement = transitionByState.primaryByComplement();

  for (const auto& literal : targetCube) {
    size_t transitionSymbol = literal.symbol;
    bool desiredValue = literal.value;
    if (!transitionByState.contains(transitionSymbol)) {
      const auto primaryIt = primaryByComplement.find(transitionSymbol);
      if (primaryIt == primaryByComplement.end() ||
          !transitionByState.contains(primaryIt->second)) {
        continue;
      }
      // The target names a complemented flop output. The transition relation
      // is encoded on the primary flop, and addComplementedStateRelations()
      // constrains the complemented next-state literal to be its inverse.
      transitionSymbol = primaryIt->second;
      desiredValue = !desiredValue;
    }

    addJustifyingStateLiterals(
        solver,
        transitionLeafLits,
        transitionByState.at(transitionSymbol),
        desiredValue,
        stateSymbols,
        valueMemo,
        assignments,
        &budget);
    if (budget.exhausted) {
      break;
    }
  }

  addComplementedPartnerAssignments(
      solver, variables, complementPartners, frame, assignments);

  StateCube cube;
  cube.reserve(assignments.size());
  for (const auto& [symbol, value] : assignments) {
    cube.push_back({symbol, value});
  }
  normalizeCube(cube);
  return cube;
}

StateCube extractSolvedPredecessorCube(
    const SATSolverWrapper& solver,
    const FrameVariableStore& variables,
    const KInductionProblem& problem,
    const TransitionExprResolver& transitionByState,
    const StateCube& targetCube,
    const std::vector<size_t>& predecessorSymbols,
    const std::unordered_map<size_t, int>& transitionLeafLits,
    const ComplementPartnerIndex& complementPartners,
    size_t predecessorProjectionLimit) {
  // Keep the carried obligation compact, including level-0 reset-bootstrap
  // predecessors. The predecessor SAT query remains exact for the requested
  // target, learned clauses are still validated by UNSAT predecessor or exact
  // reset-frontier checks, and reported counterexamples are validated against
  // the original root cube by the bounded concrete prefix path below. Carrying
  // the full level-0 support was measured on BlackParrot to turn one concrete
  // reset-precheck into hundreds of 600-bit reset-frontier refinement queries.
  if (predecessorProjectionLimit != 0 &&
      predecessorSymbols.size() > predecessorProjectionLimit) {
    const StateCube projectedCube = extractPredecessorJustificationCube(
        solver,
        variables,
        problem,
        transitionByState,
        targetCube,
        transitionLeafLits,
        complementPartners,
        predecessorProjectionLimit,
        0);
    if (!projectedCube.empty()) {
      return boundedPrefixCube(projectedCube, predecessorProjectionLimit);
    }
    // Some transition encodings can be satisfied without a compact structural
    // justification path. Falling back to the full SAT model can create
    // thousands of predecessor literals and make reset-bootstrap PDR enumerate
    // huge abstract cubes. Keep the CEGAR contract instead: carry a bounded
    // subset of the satisfying predecessor model, then rely on later exact
    // predecessor checks and concrete BMC validation before accepting any
    // result.
    const std::vector<size_t> boundedSymbols =
        boundedPrefixSymbols(predecessorSymbols, predecessorProjectionLimit);
    return extractStateCube(solver, variables, boundedSymbols, 0);
  }

  // Keep smaller predecessor obligations as concrete state assignments over
  // the target transition cone.  For large cones, including level-0 cubes, the
  // structural projection above prevents one SAT model from turning hundreds of
  // unrelated support flops into the next target.
  return boundedPrefixCube(
      extractStateCube(solver, variables, predecessorSymbols, 0),
      predecessorProjectionLimit);
}

std::optional<StateCube> findBadCubeForFormula(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    BoolExpr* initFormula,
    BoolExpr* frameInvariant,
    const std::vector<FrameClauses>& frames,
    BoolExpr* badFormula,
    const std::optional<std::vector<size_t>>& preciseBadStateSupport,
    size_t structuralBadProjectionLimit,
    const std::unordered_set<size_t>& stateSymbols,
    size_t level,
    const ComplementPartnerIndex& complementPartners,
    bool exactFrameClauses) {
  // Search the current frame for a concrete state that still satisfies bad
  // after all learned blocking clauses and optional strengthening are applied.
  const std::vector<size_t> solverSymbols =
      findBadQuerySymbols(
          problem,
          initFormula,
          frameInvariant,
          frames,
          badFormula,
          level,
          complementPartners,
          exactFrameClauses);
  SATSolverWrapper solver(solverType);
  // The bad-state query is not the repeated predecessor obligation that makes
  // PDR sensitive to solver startup overhead. It is a frame-level cone proof
  // over the current output slice, so Kissat's normal SEC cone profile may use
  // preprocessing/congruence when that helps collapse duplicated miter logic.
  solver.configureForSecConeProof(solverSymbols.size());
  FrameVariableStore variables(solver, solverSymbols, 1);
  addComplementedStateRelations(solver, variables, problem.complementedStatePairs0, 1);
  addComplementedStateRelations(solver, variables, problem.complementedStatePairs1, 1);
  addFrameConstraints(
      solver, variables, problem, initFormula, frameInvariant, frames, level, 0,
      solverSymbols, exactFrameClauses);
  addPostBootstrapResetInputConstraints(solver, variables, problem, 0);
  FrameFormulaEncoder encoder(solver, variables.makeLeafLits(0));
  try {
    solver.addClause({encoder.encode(badFormula)});
  } catch (const std::runtime_error& error) {
    throw std::runtime_error(
        "PDR bad-state encoding failed at level " + std::to_string(level) +
        ": " + error.what());
  }
  if (!solver.solve()) {
    return std::nullopt;
  }

  // Start with the full state support when it is bounded.  That gives PDR a
  // precise bad obligation instead of a tiny projection that can mix unrelated
  // state valuations and later look like a counterexample only in the abstract.
  if (preciseBadStateSupport.has_value() && !preciseBadStateSupport->empty()) {
    if (isSecDiagEnabled()) {
      emitSecDiag(
          "SEC diag: PDR bad cube uses precise state support: ",
          preciseBadStateSupport->size(),
          " state symbols at F",
          level);
    }
    StateCube cube = boundedPrefixCube(
        extractStateCube(solver, variables, *preciseBadStateSupport, 0),
        structuralBadProjectionLimit);
    if (pdrStatsEnabled()) {
      emitSecDiag(
          "SEC PDR stats: bad cube level=", level,
          " source=precise support=", preciseBadStateSupport->size(),
          " cube=", cube.size(),
          " hash=", cubeFingerprint(cube),
          " limit=", structuralBadProjectionLimit);
    }
    return cube;
  } else if (isSecDiagEnabled()) {
    emitSecDiag(
        "SEC diag: PDR bad cube falls back to structural justification at F",
        level,
        " after support budget ",
        kMaxPreciseBadCubeSupportNodes);
  }

  // Very large ASIC datapaths still need a compact fallback: extracting every
  // state bit in the bad cone would force every later predecessor query to
  // encode the transition for all of those latches.  The structural
  // justification keeps one satisfying branch of OR/AND style bad formulas.
  StateCube cube = boundedPrefixCube(
      extractBadJustificationCube(
          solver,
          variables,
          badFormula,
          stateSymbols,
          structuralBadProjectionLimit,
          0),
      structuralBadProjectionLimit);
  if (pdrStatsEnabled()) {
    emitSecDiag(
        "SEC PDR stats: bad cube level=", level,
        " source=structural cube=", cube.size(),
        " hash=", cubeFingerprint(cube),
        " limit=", structuralBadProjectionLimit);
  }
  return cube;
}

std::optional<StateCube> findBadCube(const KInductionProblem& problem,
                                     KEPLER_FORMAL::Config::SolverType solverType,
                                     BoolExpr* initFormula,
                                     BoolExpr* frameInvariant,
                                     const std::vector<FrameClauses>& frames,
                                     const std::optional<std::vector<size_t>>&
                                         preciseBadStateSupport,
                                     size_t preciseBadCubeStateLimit,
                                     const std::unordered_set<size_t>& stateSymbols,
                                     size_t level,
                                     const ComplementPartnerIndex& complementPartners,
                                     bool exactFrameClauses) {
  if (problem.observedOutputExprs0.size() <= 1 ||
      problem.observedOutputExprs0.size() != problem.observedOutputExprs1.size()) {
    return findBadCubeForFormula(
        problem,
        solverType,
        initFormula,
        frameInvariant,
        frames,
        problem.bad,
        preciseBadStateSupport,
        preciseBadCubeStateLimit,
        stateSymbols,
        level,
        complementPartners,
        exactFrameClauses);
  }

  // The batch bad predicate is an OR over output mismatches. Asking SAT for the
  // whole OR is logically compact, but it can be a poor search problem on ASIC
  // SEC because the solver first has to reason across unrelated output cones.
  // Query each output mismatch independently: if any bit can be bad, PDR gets
  // a real bad cube; if every bit is UNSAT, the batched bad OR is UNSAT too.
  for (size_t output = 0; output < problem.observedOutputExprs0.size(); ++output) {
    BoolExpr* outputBad = BoolExpr::simplify(
        BoolExpr::Xor(
            problem.observedOutputExprs0[output],
            problem.observedOutputExprs1[output]));
    const auto outputStateSupport = collectBoundedStateSupportSymbols(
        outputBad,
        kMaxPreciseBadCubeSupportNodes,
        preciseBadCubeStateLimit,
        stateSymbols);
    if (auto cube = findBadCubeForFormula(
            problem,
            solverType,
            initFormula,
            frameInvariant,
            frames,
            outputBad,
            outputStateSupport,
            preciseBadCubeStateLimit,
            stateSymbols,
            level,
            complementPartners,
            exactFrameClauses);
        cube.has_value()) {
      return cube;
    }
  }
  return std::nullopt;
}

std::optional<StateCube> findPredecessorCube(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    const TransitionExprResolver& transitionByState,
    BoolExpr* initFormula,
    BoolExpr* frameInvariant,
    const std::vector<FrameClauses>& frames,
    size_t level,
    const StateCube& targetCube,
    bool excludeTargetOnCurrentFrame,
    const ComplementPartnerIndex& complementPartners,
    size_t predecessorProjectionLimit,
    bool exactFrameClauses,
    ResetFrontierCache* resetFrontierCache = nullptr,
    const std::vector<StateClause>* extraFrameClauses = nullptr,
    size_t* predecessorQueryBudget = nullptr,
    bool useExactResetFrontierChecks = true) {
  // This is the one-step predecessor query at the heart of PDR: does some
  // state in F[level] transition into the target cube on the next frame?
  consumePdrPredecessorQueryBudget(predecessorQueryBudget);
  const std::vector<size_t> targetSymbols = cubeStateSymbols(targetCube);
  const std::vector<size_t> encodedTargets =
      expandTransitionTargets(problem, targetSymbols, transitionByState);
  const std::vector<size_t> transitionSupportSymbols =
      collectTransitionSupportSymbols(transitionByState, encodedTargets);
  const size_t statsQueryNumber = nextPdrPredecessorQueryNumber();
  const bool emitStatsForQuery = shouldEmitPdrStats(statsQueryNumber);

  if (useExactResetFrontierChecks &&
      level == 0 && problem.resetBootstrapCycles != 0 &&
      resetFrontierCache != nullptr &&
      transitionSupportSymbols.size() <=
          kMaxExactResetPrecheckTransitionSupport) {
    // F[0] is a compact summary of the concrete post-reset image. Asking only
    // the abstract F[0] predecessor query can enumerate thousands of fake
    // reset states one refinement clause at a time. The exact reset-frontier
    // check answers the real level-0 question first: can any concrete
    // post-reset state reach this target cube in one PDR transition?
    const bool hasConcreteResetPredecessor =
        !cubeOutsideConcreteResetFrontier(
            problem,
            solverType,
            transitionByState,
            targetCube,
            1,
            *resetFrontierCache,
            false);
    if (emitStatsForQuery) {
      emitSecDiag(
          "SEC PDR stats: predecessor #", statsQueryNumber,
          " level=", level,
          " target_cube=", targetCube.size(),
          " target_hash=", cubeFingerprint(targetCube),
          " encoded_targets=", encodedTargets.size(),
          " transition_support=", transitionSupportSymbols.size(),
          " projection_limit=", predecessorProjectionLimit,
          " exact_reset_frontier=1 result=",
          hasConcreteResetPredecessor ? "sat" : "unsat");
    }
    if (!hasConcreteResetPredecessor) {
      return std::nullopt;
    }
  } else if (
      level == 0 && problem.resetBootstrapCycles != 0 &&
      resetFrontierCache != nullptr && emitStatsForQuery) {
    emitSecDiag(
        "SEC PDR stats: predecessor #", statsQueryNumber,
        " level=", level,
        " target_cube=", targetCube.size(),
        " target_hash=", cubeFingerprint(targetCube),
        " encoded_targets=", encodedTargets.size(),
        " transition_support=", transitionSupportSymbols.size(),
        " projection_limit=", predecessorProjectionLimit,
        " exact_reset_frontier=",
        useExactResetFrontierChecks ? "skipped" : "disabled");
  }

  const std::vector<size_t> predecessorSymbols = predecessorProjectionSymbols(
      problem,
      transitionByState,
      initFormula,
      frameInvariant,
      frames,
      level,
      complementPartners,
      transitionSupportSymbols);
  const std::vector<size_t> solverSymbols = predecessorCurrentFrameQuerySymbols(
      problem,
      initFormula,
      frameInvariant,
      frames,
      level,
      targetCube,
      excludeTargetOnCurrentFrame,
      predecessorSymbols,
      transitionSupportSymbols,
      complementPartners,
      exactFrameClauses,
      extraFrameClauses);
  if (emitStatsForQuery) {
    emitSecDiag(
        "SEC PDR stats: predecessor #", statsQueryNumber,
        " level=", level,
        " target_cube=", targetCube.size(),
        " target_hash=", cubeFingerprint(targetCube),
        " encoded_targets=", encodedTargets.size(),
        " transition_support=", transitionSupportSymbols.size(),
        " predecessor_symbols=", predecessorSymbols.size(),
        " solver_symbols=", solverSymbols.size(),
        " projection_limit=", predecessorProjectionLimit,
        " frame_clauses=",
        level < frames.size() ? frames[level].clauses.size() : 0,
        " exclude_target=", excludeTargetOnCurrentFrame ? 1 : 0);
  }
  SATSolverWrapper solver(solverType);
  solver.configureForSecPdrQuery(solverSymbols.size());
  FrameVariableStore variables(solver, solverSymbols, 1);
  addComplementedStateRelations(solver, variables, problem.complementedStatePairs0, 1);
  addComplementedStateRelations(solver, variables, problem.complementedStatePairs1, 1);
  addFrameConstraints(
      solver, variables, problem, initFormula, frameInvariant, frames, level, 0,
      solverSymbols, exactFrameClauses);
  addSafeFramePropertyConstraint(solver, variables, problem, level, 0);
  if (extraFrameClauses != nullptr) {
    for (const auto& clause : *extraFrameClauses) {
      if (clauseCoveredByVariables(variables, clause)) {
        addStateClause(solver, variables, clause, 0);
      }
    }
  }
  addPostBootstrapResetInputConstraints(solver, variables, problem, 0);
  // Encode only the next-state equations needed to decide the requested target
  // cube. This keeps one local PDR obligation from materializing the entire
  // design transition relation.
  std::unordered_map<size_t, int> transitionLeafLits;
  addTransitionConstraintsForTargetCube(
      solver,
      variables,
      transitionByState,
      0,
      targetCube,
      encodedTargets,
      transitionSupportSymbols,
      &transitionLeafLits);
  if (excludeTargetOnCurrentFrame) {
    addNegatedCubeClause(solver, variables, targetCube, 0);
  }
  const bool hasPredecessor = solver.solve();
  if (emitStatsForQuery) {
    emitSecDiag(
        "SEC PDR stats: predecessor #", statsQueryNumber,
        " result=", hasPredecessor ? "sat" : "unsat");
  }
  if (!hasPredecessor) {
    return std::nullopt;
  }
  StateCube predecessor = extractSolvedPredecessorCube(
      solver,
      variables,
      problem,
      transitionByState,
      targetCube,
      predecessorSymbols,
      transitionLeafLits,
      complementPartners,
      predecessorProjectionLimit);
  if (emitStatsForQuery) {
    emitSecDiag(
        "SEC PDR stats: predecessor #", statsQueryNumber,
        " predecessor_cube=", predecessor.size(),
        " predecessor_hash=", cubeFingerprint(predecessor));
  }
  return predecessor;
}

bool cubeIntersectsInit(const KInductionProblem& problem,
                        KEPLER_FORMAL::Config::SolverType solverType,
                        BoolExpr* initFormula,
                        const StateCube& cube) {
  // A clause is only safe to learn if its negated cube stays outside Init.
  if (const auto knownResult = cubeIntersectsKnownInitFacts(problem, cube);
      knownResult.has_value()) {
    return *knownResult;
  }

  const std::vector<size_t> solverSymbols =
      initIntersectionSymbols(problem, initFormula, cube);
  SATSolverWrapper solver(solverType);
  solver.configureForSecPdrQuery(solverSymbols.size());
  FrameVariableStore variables(solver, solverSymbols, 1);
  addComplementedStateRelations(solver, variables, problem.complementedStatePairs0, 1);
  addComplementedStateRelations(solver, variables, problem.complementedStatePairs1, 1);
  FrameFormulaEncoder encoder(solver, variables.makeLeafLits(0));
  solver.addClause({encoder.encode(initFormula)});
  addCubeAssumptions(solver, variables, cube, 0);
  return solver.solve();
}

bool appendTargetLiteral(StateCube& candidate,
                         const StateCube& targetCube,
                         size_t symbol) {
  if (findCubeLiteralValue(candidate, symbol).has_value()) {
    return false;
  }
  const auto targetValue = findCubeLiteralValue(targetCube, symbol);
  if (!targetValue.has_value()) {
    return false;
  }
  candidate.push_back({symbol, *targetValue});
  normalizeCube(candidate);
  return true;
}

size_t cubeLiteralKey(const CubeLiteral& literal) {
  return (literal.symbol << 1) | (literal.value ? 1u : 0u);
}

std::vector<int> assumptionLiteralsForCube(
    const StateCube& cube,
    const std::vector<std::pair<int, CubeLiteral>>& assumptionPairs) {
  std::unordered_map<size_t, int> assumptionByLiteral;
  assumptionByLiteral.reserve(assumptionPairs.size());
  for (const auto& [assumptionLit, literal] : assumptionPairs) {
    assumptionByLiteral.emplace(cubeLiteralKey(literal), assumptionLit);
  }

  std::vector<int> assumptions;
  assumptions.reserve(cube.size());
  for (const auto& literal : cube) {
    const auto it = assumptionByLiteral.find(cubeLiteralKey(literal));
    if (it == assumptionByLiteral.end()) {
      assumptions.clear();
      return assumptions;
    }
    assumptions.push_back(it->second);
  }
  return assumptions;
}

StateCube cubeFromAssumptionLiterals(
    const std::vector<int>& assumptions,
    const std::unordered_map<int, CubeLiteral>& literalByAssumption) {
  StateCube cube;
  cube.reserve(assumptions.size());
  for (const auto assumption : assumptions) {
    const auto it = literalByAssumption.find(assumption);
    if (it == literalByAssumption.end()) {
      cube.clear();
      return cube;
    }
    cube.push_back(it->second);
  }
  normalizeCube(cube);
  return cube;
}

std::optional<StateCube> minimizeCoreInTargetContext(
    SATSolverWrapper& coreSolver,
    const std::vector<int>& assumptions,
    const std::unordered_map<int, CubeLiteral>& literalByAssumption,
    size_t* checks) {
  std::vector<int> candidate = assumptions;
  if (candidate.empty()) {
    return std::nullopt;
  }

  for (size_t chunkSize = std::max<size_t>(1, candidate.size() / 2);
       chunkSize > 0 &&
       *checks < kMaxPredecessorCoreContextMinimizationChecks;) {
    bool removedAny = false;
    for (size_t index = 0;
         index < candidate.size() &&
         *checks < kMaxPredecessorCoreContextMinimizationChecks;) {
      const size_t erasedCount =
          std::min(chunkSize, candidate.size() - index);
      if (erasedCount == 0 || erasedCount == candidate.size()) {
        break;
      }

      std::vector<int> trial = candidate;
      trial.erase(
          trial.begin() + static_cast<std::ptrdiff_t>(index),
          trial.begin() +
              static_cast<std::ptrdiff_t>(index + erasedCount));
      ++(*checks);
      if (!coreSolver.solveWithAssumptions(trial)) {
        candidate = std::move(trial);
        removedAny = true;
        continue;
      }
      index += erasedCount;
    }

    if (chunkSize == 1) {
      break;
    }
    if (!removedAny && chunkSize == 1) {
      break;
    }
    chunkSize = std::max<size_t>(1, chunkSize / 2);
  }

  StateCube minimized = cubeFromAssumptionLiterals(
      candidate, literalByAssumption);
  if (minimized.empty()) {
    return std::nullopt;
  }
  return minimized;
}

std::optional<StateCube> growCoreOutsideInit(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    BoolExpr* initFormula,
    const StateCube& core,
    const StateCube& targetCube) {
  StateCube candidate = core;
  if (!cubeIntersectsInit(problem, solverType, initFormula, candidate)) {
    return candidate;
  }

  auto tryAddSymbol = [&](size_t symbol) -> bool {
    if (!appendTargetLiteral(candidate, targetCube, symbol)) {
      return false;
    }
    return !cubeIntersectsInit(problem, solverType, initFormula, candidate);
  };

  const bool usesBootstrapFrontier = problem.resetBootstrapCycles != 0;
  const auto& assignments = usesBootstrapFrontier
                                ? problem.bootstrapStateAssignments
                                : problem.initialStateAssignments;
  const auto& equalities = usesBootstrapFrontier
                               ? problem.bootstrapStateEqualityPairs
                               : problem.initialStateEqualityPairs;

  // UNSAT cores from transition assumptions can be too small to be legal PDR
  // frame clauses because a one-bit reason may still overlap Init. Add only
  // original target literals until the cube visibly contradicts Init; the
  // predecessor UNSAT result is monotonic under this strengthening.
  for (const auto& [symbol, initValue] : assignments) {
    const auto targetValue = findCubeLiteralValue(targetCube, symbol);
    if (targetValue.has_value() && *targetValue != initValue &&
        tryAddSymbol(symbol)) {
      return candidate;
    }
  }
  for (const auto& [lhsSymbol, rhsSymbol] : equalities) {
    const auto lhsTargetValue = findCubeLiteralValue(targetCube, lhsSymbol);
    const auto rhsTargetValue = findCubeLiteralValue(targetCube, rhsSymbol);
    if (!lhsTargetValue.has_value() || !rhsTargetValue.has_value() ||
        *lhsTargetValue == *rhsTargetValue) {
      continue;
    }
    if (tryAddSymbol(lhsSymbol) || tryAddSymbol(rhsSymbol)) {
      return candidate;
    }
  }
  for (const auto& [lhsSymbol, rhsSymbol] : equalities) {
    const auto lhsCoreValue = findCubeLiteralValue(candidate, lhsSymbol);
    const auto rhsCoreValue = findCubeLiteralValue(candidate, rhsSymbol);
    const auto lhsTargetValue = findCubeLiteralValue(targetCube, lhsSymbol);
    const auto rhsTargetValue = findCubeLiteralValue(targetCube, rhsSymbol);
    if (lhsCoreValue.has_value() && rhsTargetValue.has_value() &&
        *lhsCoreValue != *rhsTargetValue && tryAddSymbol(rhsSymbol)) {
      return candidate;
    }
    if (rhsCoreValue.has_value() && lhsTargetValue.has_value() &&
        *rhsCoreValue != *lhsTargetValue && tryAddSymbol(lhsSymbol)) {
      return candidate;
    }
  }
  if (problem.complementedStatePairs0.size() <=
      kMaxComplementPairsForCheapInitCheck) {
    for (const auto& [primarySymbol, complementedSymbol] :
         problem.complementedStatePairs0) {
      const auto primaryTargetValue =
          findCubeLiteralValue(targetCube, primarySymbol);
      const auto complementedTargetValue =
          findCubeLiteralValue(targetCube, complementedSymbol);
      if (!primaryTargetValue.has_value() ||
          !complementedTargetValue.has_value() ||
          *primaryTargetValue != *complementedTargetValue) {
        continue;
      }
      if (tryAddSymbol(primarySymbol) || tryAddSymbol(complementedSymbol)) {
        return candidate;
      }
    }
    for (const auto& [primarySymbol, complementedSymbol] :
         problem.complementedStatePairs0) {
      const auto primaryCoreValue =
          findCubeLiteralValue(candidate, primarySymbol);
      const auto complementedCoreValue =
          findCubeLiteralValue(candidate, complementedSymbol);
      const auto primaryTargetValue =
          findCubeLiteralValue(targetCube, primarySymbol);
      const auto complementedTargetValue =
          findCubeLiteralValue(targetCube, complementedSymbol);
      if (primaryCoreValue.has_value() && complementedTargetValue.has_value() &&
          *primaryCoreValue == *complementedTargetValue &&
          tryAddSymbol(complementedSymbol)) {
        return candidate;
      }
      if (complementedCoreValue.has_value() && primaryTargetValue.has_value() &&
          *complementedCoreValue == *primaryTargetValue &&
          tryAddSymbol(primarySymbol)) {
        return candidate;
      }
    }
  }
  if (problem.complementedStatePairs1.size() <=
      kMaxComplementPairsForCheapInitCheck) {
    for (const auto& [primarySymbol, complementedSymbol] :
         problem.complementedStatePairs1) {
      const auto primaryTargetValue =
          findCubeLiteralValue(targetCube, primarySymbol);
      const auto complementedTargetValue =
          findCubeLiteralValue(targetCube, complementedSymbol);
      if (!primaryTargetValue.has_value() ||
          !complementedTargetValue.has_value() ||
          *primaryTargetValue != *complementedTargetValue) {
        continue;
      }
      if (tryAddSymbol(primarySymbol) || tryAddSymbol(complementedSymbol)) {
        return candidate;
      }
    }
    for (const auto& [primarySymbol, complementedSymbol] :
         problem.complementedStatePairs1) {
      const auto primaryCoreValue =
          findCubeLiteralValue(candidate, primarySymbol);
      const auto complementedCoreValue =
          findCubeLiteralValue(candidate, complementedSymbol);
      const auto primaryTargetValue =
          findCubeLiteralValue(targetCube, primarySymbol);
      const auto complementedTargetValue =
          findCubeLiteralValue(targetCube, complementedSymbol);
      if (primaryCoreValue.has_value() && complementedTargetValue.has_value() &&
          *primaryCoreValue == *complementedTargetValue &&
          tryAddSymbol(complementedSymbol)) {
        return candidate;
      }
      if (complementedCoreValue.has_value() && primaryTargetValue.has_value() &&
          *complementedCoreValue == *primaryTargetValue &&
          tryAddSymbol(primarySymbol)) {
        return candidate;
      }
    }
  }

  for (const auto& literal : targetCube) {
    if (tryAddSymbol(literal.symbol)) {
      return candidate;
    }
  }
  if (!cubeIntersectsInit(problem, solverType, initFormula, candidate)) {
    return candidate;
  }
  return std::nullopt;
}

std::optional<StateCube> findValidatedPredecessorCore(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    const TransitionExprResolver& transitionByState,
    BoolExpr* initFormula,
    BoolExpr* frameInvariant,
    const std::vector<FrameClauses>& frames,
    size_t sourceLevel,
    const StateCube& targetCube,
    ResetFrontierCache* resetFrontierCache,
    const ComplementPartnerIndex& complementPartners,
    size_t predecessorProjectionLimit,
    bool exactFrameClauses,
    bool useExactResetFrontierChecks,
    size_t* predecessorQueryBudget) {
  // For source level zero, the learned clause is placed in F1 and only needs
  // the concrete "F0 cannot transition to core'" check.  Higher levels use the
  // usual relative-induction check and may rely on excluding the candidate cube
  // from the current frame because that clause is already present there.
  const bool excludeCurrentTargetForCore = sourceLevel != 0;
  const std::vector<size_t> targetSymbols = cubeStateSymbols(targetCube);
  const std::vector<size_t> encodedTargets =
      expandTransitionTargets(problem, targetSymbols, transitionByState);
  const std::vector<size_t> transitionSupportSymbols =
      collectTransitionSupportSymbols(transitionByState, encodedTargets);
  const std::vector<size_t> predecessorSymbols = predecessorProjectionSymbols(
      problem,
      transitionByState,
      initFormula,
      frameInvariant,
      frames,
      sourceLevel,
      complementPartners,
      transitionSupportSymbols);
  const std::vector<size_t> solverSymbols = predecessorCurrentFrameQuerySymbols(
      problem,
      initFormula,
      frameInvariant,
      frames,
      sourceLevel,
      targetCube,
      excludeCurrentTargetForCore,
      predecessorSymbols,
      transitionSupportSymbols,
      complementPartners,
      exactFrameClauses,
      nullptr);

  // Glucose is used here only as an UNSAT-core oracle over the target
  // literals. Any proposed smaller cube is revalidated below with the normal
  // PDR predecessor query before it can become a learned frame clause.
  SATSolverWrapper coreSolver(KEPLER_FORMAL::Config::SolverType::GLUCOSE);
  coreSolver.configureForSecPdrQuery(solverSymbols.size());
  FrameVariableStore variables(coreSolver, solverSymbols, 1);
  addComplementedStateRelations(
      coreSolver, variables, problem.complementedStatePairs0, 1);
  addComplementedStateRelations(
      coreSolver, variables, problem.complementedStatePairs1, 1);
  addFrameConstraints(
      coreSolver,
      variables,
      problem,
      initFormula,
      frameInvariant,
      frames,
      sourceLevel,
      0,
      solverSymbols,
      exactFrameClauses);
  addSafeFramePropertyConstraint(coreSolver, variables, problem, sourceLevel, 0);
  addPostBootstrapResetInputConstraints(coreSolver, variables, problem, 0);
  if (excludeCurrentTargetForCore) {
    addNegatedCubeClause(coreSolver, variables, targetCube, 0);
  }

  const auto assumptionPairs = addTransitionAssumptionsForTargetCube(
      coreSolver,
      variables,
      transitionByState,
      0,
      targetCube,
      encodedTargets,
      transitionSupportSymbols);
  if (assumptionPairs.empty()) {
    if (pdrStatsEnabled() && targetCube.size() > kLargeBlockedCubeGeneralizationThreshold) {
      emitSecDiag(
          "SEC PDR stats: predecessor core miss reason=empty_assumptions target=",
          targetCube.size(),
          " source_level=",
          sourceLevel,
          " target_hash=",
          cubeFingerprint(targetCube));
    }
    return std::nullopt;
  }

  std::vector<int> assumptions;
  assumptions.reserve(assumptionPairs.size());
  std::unordered_map<int, CubeLiteral> literalByAssumption;
  literalByAssumption.reserve(assumptionPairs.size() * 2);
  for (const auto& [assumptionLit, cubeLiteral] : assumptionPairs) {
    assumptions.push_back(assumptionLit);
    literalByAssumption.emplace(assumptionLit, cubeLiteral);
    // Glucose reports final conflicts in solver-literal polarity. Map both
    // signs back to the requested cube literal and let exact revalidation below
    // decide whether the proposed core is usable.
    literalByAssumption.emplace(-assumptionLit, cubeLiteral);
  }

  if (coreSolver.solveWithAssumptions(assumptions)) {
    if (pdrStatsEnabled() && targetCube.size() > kLargeBlockedCubeGeneralizationThreshold) {
      emitSecDiag(
          "SEC PDR stats: predecessor core miss reason=core_query_sat target=",
          targetCube.size(),
          " source_level=",
          sourceLevel,
          " target_hash=",
          cubeFingerprint(targetCube));
    }
    return std::nullopt;
  }

  StateCube core;
  const auto failedAssumptions = coreSolver.failedAssumptions();
  for (const auto failedLit : failedAssumptions) {
    const auto it = literalByAssumption.find(failedLit);
    if (it == literalByAssumption.end()) {
      continue;
    }
    core.push_back(it->second);
  }
  normalizeCube(core);
  if (core.empty() || core.size() >= targetCube.size()) {
    if (pdrStatsEnabled() && targetCube.size() > kLargeBlockedCubeGeneralizationThreshold) {
      emitSecDiag(
          "SEC PDR stats: predecessor core miss reason=not_smaller target=",
          targetCube.size(),
          " source_level=",
          sourceLevel,
          " failed_assumptions=",
          failedAssumptions.size(),
          " mapped_core=",
          core.size(),
          " target_hash=",
          cubeFingerprint(targetCube));
    }
    return std::nullopt;
  }

  if (sourceLevel != 0) {
    // For higher frames the generalized clause is pushed into earlier learned
    // frames as well, so keep the standard IC3/PDR requirement that the reduced
    // cube excludes Init.  Source level zero is different in this implementation:
    // F0 is the already-checked startup frontier and the learned clause is only
    // placed in F1, so the exact no-predecessor query from F0 is the required
    // safety check.  BlackParrot sampling showed thousands of repeated
    // source_level=0 core misses when we unnecessarily rejected those cores for
    // overlapping Init.
    const auto initSafeCore = growCoreOutsideInit(
        problem, solverType, initFormula, core, targetCube);
    if (!initSafeCore.has_value() || initSafeCore->size() >= targetCube.size()) {
      if (pdrStatsEnabled() &&
          targetCube.size() > kLargeBlockedCubeGeneralizationThreshold) {
        emitSecDiag(
            "SEC PDR stats: predecessor core miss reason=init_intersection target=",
            targetCube.size(),
            "->",
            core.size(),
            " source_level=",
            sourceLevel,
            " target_hash=",
            cubeFingerprint(targetCube),
            " core_hash=",
            cubeFingerprint(core));
      }
      return std::nullopt;
    }
    core = *initSafeCore;
  }

  std::vector<int> coreAssumptions =
      assumptionLiteralsForCube(core, assumptionPairs);
  bool coreBlockedInTargetContext =
      coreAssumptions.size() == core.size() &&
      !coreSolver.solveWithAssumptions(coreAssumptions);
  size_t contextMinimizationChecks = 0;
  if (!coreBlockedInTargetContext &&
      targetCube.size() > kLargeBlockedCubeGeneralizationThreshold) {
    // The failed-assumption vector is only a seed. If it is not itself UNSAT,
    // minimize the full target assumption set in the same solver context. This
    // keeps the proof obligation honest: every accepted reduced cube is backed
    // by an actual UNSAT predecessor query, not by solver-conflict bookkeeping.
    if (const auto minimizedCore = minimizeCoreInTargetContext(
            coreSolver,
            assumptions,
            literalByAssumption,
            &contextMinimizationChecks);
        minimizedCore.has_value() &&
        minimizedCore->size() < targetCube.size()) {
      core = *minimizedCore;
      coreAssumptions = assumptionLiteralsForCube(core, assumptionPairs);
      coreBlockedInTargetContext =
          coreAssumptions.size() == core.size() &&
          !coreSolver.solveWithAssumptions(coreAssumptions);
    }
  }
  if (!coreBlockedInTargetContext) {
    if (pdrStatsEnabled() &&
        targetCube.size() > kLargeBlockedCubeGeneralizationThreshold) {
      emitSecDiag(
          "SEC PDR stats: predecessor core miss reason=context_core_sat target=",
          targetCube.size(),
          "->",
          core.size(),
          " source_level=",
          sourceLevel,
          " target_hash=",
          cubeFingerprint(targetCube),
          " core_hash=",
          cubeFingerprint(core),
          " context_checks=",
          contextMinimizationChecks);
    }
    return std::nullopt;
  }
  if (sourceLevel == 0) {
    // The core came from, and is rechecked in, the full target-context
    // predecessor query. This is stronger than rebuilding a narrower
    // one-literal query: all included frame clauses, reset-input constraints,
    // complemented-state relations, and target-cone transition definitions are
    // real PDR constraints. If that context cannot reach the reduced cube from
    // F0, the learned clause is safe for F1. Re-running a smaller query can
    // lose exactly the context that proved the core and was measured on
    // BlackParrot as repeated 116->1 false misses.
    if (pdrStatsEnabled()) {
      emitSecDiag(
          "SEC PDR stats: predecessor core target=",
          targetCube.size(),
          "->",
          core.size(),
          " source_level=",
          sourceLevel,
          " target_hash=",
          cubeFingerprint(targetCube),
          " core_hash=",
          cubeFingerprint(core),
          " validation=target_context",
          " context_checks=",
          contextMinimizationChecks);
    }
    return core;
  }

  if (findPredecessorCube(
          problem,
          solverType,
          transitionByState,
          initFormula,
          frameInvariant,
          frames,
          sourceLevel,
          core,
          excludeCurrentTargetForCore,
          complementPartners,
          predecessorProjectionLimit,
          exactFrameClauses,
          resetFrontierCache,
          nullptr,
          predecessorQueryBudget,
          useExactResetFrontierChecks)
          .has_value()) {
    if (pdrStatsEnabled() && targetCube.size() > kLargeBlockedCubeGeneralizationThreshold) {
      emitSecDiag(
          "SEC PDR stats: predecessor core miss reason=predecessor_exists target=",
          targetCube.size(),
          "->",
          core.size(),
          " source_level=",
          sourceLevel,
          " target_hash=",
          cubeFingerprint(targetCube),
          " core_hash=",
          cubeFingerprint(core));
    }
    return std::nullopt;
  }

  if (pdrStatsEnabled()) {
    emitSecDiag(
        "SEC PDR stats: predecessor core target=",
        targetCube.size(),
        "->",
        core.size(),
        " source_level=",
        sourceLevel,
        " target_hash=",
        cubeFingerprint(targetCube),
        " core_hash=",
        cubeFingerprint(core));
  }
  return core;
}

StateCube generalizeBlockedCube(const KInductionProblem& problem,
                                KEPLER_FORMAL::Config::SolverType solverType,
                                const TransitionExprResolver& transitionByState,
                                BoolExpr* initFormula,
                                BoolExpr* frameInvariant,
                                const std::vector<FrameClauses>& frames,
                                size_t level,
                                const StateCube& cube,
                                ResetFrontierCache* resetFrontierCache,
                                const ComplementPartnerIndex& complementPartners,
                                size_t predecessorProjectionLimit,
                                bool exactFrameClauses,
                                bool useExactResetFrontierChecks,
                                size_t* predecessorQueryBudget) {
  // Clause generalization for ordinary PDR blocking.  A candidate reduction is
  // accepted only when two proof obligations still hold:
  //   1. Init cannot already satisfy the reduced cube, so the clause is safe in
  //      every non-zero frame.
  //   2. F[level-1] cannot transition into the reduced cube, so the clause is
  //      inductive relative to the previous frame.
  //
  // The validation remains exact; the optimization is only in the search order.
  // Large output slices often produce model cubes where many adjacent literals
  // are irrelevant.  Trying to remove chunks first gives PDR compact clauses
  // without requiring an unsat-core API from the underlying SAT solver.
  size_t checks = 0;
  const size_t checkLimit =
      cube.size() > kLargeBlockedCubeGeneralizationThreshold
          ? kMaxLargeBlockedCubeGeneralizationChecks
          : kMaxSmallBlockedCubeGeneralizationChecks;
  const size_t blockedCubeSupportSize =
      blockedCubeTransitionSupportSize(problem, transitionByState, cube);
  const bool cheapTransitionSurface =
      blockedCubeSupportSize <= kCheapBlockedCubeTransitionSupportLimit;
  const size_t effectiveCheckLimit =
      cheapTransitionSurface
          ? std::max(
                checkLimit,
                std::min(
                    kMaxCheapBlockedCubeGeneralizationChecks,
                    std::max(cube.size() * 2, checkLimit)))
          : checkLimit;
  const bool shouldTryPredecessorCore =
      !cheapTransitionSurface &&
      (cube.size() > kLargeBlockedCubeGeneralizationThreshold ||
       (cube.size() >= kMinMediumCubePredecessorCoreTargetSize &&
        blockedCubeSupportSize > kMaxGeneralizedBlockedCubeTransitionSupport));
  if (shouldTryPredecessorCore) {
    // For wide blockers, ask the SAT solver for the actual predecessor UNSAT
    // reason before spending bounded chunk-dropping checks. BlackParrot samples
    // showed both wide 68/88-literal blockers and medium 37-49-literal blockers
    // with huge transition support where the conflict core was one or two
    // literals; without this step PDR learned thousands of adjacent clauses.
    if (const auto core = findValidatedPredecessorCore(
            problem,
            solverType,
            transitionByState,
            initFormula,
            frameInvariant,
            frames,
            level - 1,
            cube,
            resetFrontierCache,
            complementPartners,
            predecessorProjectionLimit,
            exactFrameClauses,
            useExactResetFrontierChecks,
            predecessorQueryBudget);
        core.has_value()) {
      return *core;
    }
  }
  if (!cheapTransitionSurface &&
      cube.size() > kVeryLargeBlockedCubeGeneralizationBypassThreshold) {
    if (level != 1) {
      // Keep the measured benefit of the assumption-core pass above:
      // BlackParrot wide level-1 blockers often collapse from ~100 state bits
      // to a few literals.  If no validated core is available at higher
      // levels, skip slower chunk-dropping probes and learn the already-proven
      // cube verbatim.
      return cube;
    }
  }
  if (!cheapTransitionSurface &&
      blockedCubeSupportSize > kMaxGeneralizedBlockedCubeTransitionSupport) {
    // Generalization is only a clause-strengthening optimization.  When the
    // target cube depends on a broad transition surface, every literal-dropping
    // probe rebuilds and solves an expensive predecessor query.  Learn the
    // already-proven blocked cube verbatim instead of spending ASIC runtime on
    // optional minimization work.
    return cube;
  }

  const bool blocksFromInitialFrame = level == 1;
  auto reductionStillBlocks = [&](const StateCube& reduced) {
    if (reduced.empty()) {
      return false;
    }
    if (!blocksFromInitialFrame &&
        cubeIntersectsInit(problem, solverType, initFormula, reduced)) {
      return false;
    }
    return !findPredecessorCube(
                problem,
                solverType,
                transitionByState,
                initFormula,
                frameInvariant,
                frames,
                level - 1,
                reduced,
                !blocksFromInitialFrame,
                complementPartners,
                predecessorProjectionLimit,
                exactFrameClauses,
                resetFrontierCache,
                nullptr,
                predecessorQueryBudget,
                useExactResetFrontierChecks)
                .has_value();
  };

  StateCube candidate = cube;
  if (cube.size() > kLargeBlockedCubeGeneralizationThreshold) {
    // Large SAT-model cubes often contain a few cheap literals that already
    // explain the blocked transition plus hundreds of unrelated support bits.
    // Try that cheap seed first so generalization does not spend its budget on
    // giant intermediate cubes whose transition cones dominate runtime.
    const StateCube cheapSeed = boundedCheapTransitionCube(
        cube, kLargeBlockedCubeSeedSize, transitionByState);
    if (cheapSeed.size() < cube.size() && checks < checkLimit) {
      ++checks;
      if (reductionStillBlocks(cheapSeed)) {
        candidate = cheapSeed;
      }
    }
    // On ASIC SEC slices, the predecessor query itself is usually the
    // expensive part. Once a large cube is known blockable, spending dozens
    // more predecessor SAT calls to shave a few extra literals often costs more
    // than the smaller clause saves later. The exception is a measured cheap
    // transition surface: then the extra checks cost little and prevent PDR
    // from enumerating thousands of adjacent trivially unreachable cubes.
    if (!cheapTransitionSurface) {
      if (pdrStatsEnabled() && candidate.size() != cube.size()) {
        emitSecDiag(
            "SEC PDR stats: generalized blocked cube level=",
            level,
            " size=",
            cube.size(),
            "->",
            candidate.size(),
            " checks=",
            checks);
      }
      return candidate;
    }
    if (pdrStatsEnabled() && candidate.size() != cube.size()) {
      emitSecDiag(
          "SEC PDR stats: generalized blocked cube level=",
          level,
          " size=",
          cube.size(),
          "->",
          candidate.size(),
          " checks=",
          checks);
    }
  }

  for (size_t chunkSize = std::max<size_t>(1, candidate.size() / 2);
       chunkSize > 0 && checks < effectiveCheckLimit;) {
    for (size_t index = 0;
         index < candidate.size() &&
         checks < effectiveCheckLimit;) {
      const size_t erasedCount =
          std::min(chunkSize, candidate.size() - index);
      if (erasedCount == 0 || erasedCount == candidate.size()) {
        break;
      }

      ++checks;
      StateCube reduced = candidate;
      reduced.erase(
          reduced.begin() + static_cast<std::ptrdiff_t>(index),
          reduced.begin() +
              static_cast<std::ptrdiff_t>(index + erasedCount));
      if (reductionStillBlocks(reduced)) {
        candidate = std::move(reduced);
        continue;
      }
      index += erasedCount;
    }

    if (chunkSize == 1) {
      break;
    }
    chunkSize = std::max<size_t>(1, chunkSize / 2);
  }

  if (pdrStatsEnabled() && candidate.size() != cube.size()) {
    emitSecDiag(
        "SEC PDR stats: generalized blocked cube level=",
        level,
        " size=",
        cube.size(),
        "->",
        candidate.size(),
        " checks=",
        checks);
  }
  return candidate;
}

bool framesConverged(const FrameClauses& lhs, const FrameClauses& rhs) {
  if (lhs.clauses.size() != rhs.clauses.size()) {
    return false;
  }
  for (const auto& clause : lhs.clauses) {
    if (!frameHasSubsumingClause(rhs, clause)) {
      return false;  // LCOV_EXCL_LINE
    }
  }
  for (const auto& clause : rhs.clauses) {
    if (!frameHasSubsumingClause(lhs, clause)) {
      return false;  // LCOV_EXCL_LINE
    }
  }
  return true;
}

bool obligationAlreadyBlocked(const std::vector<FrameClauses>& frames,
                              const ProofObligation& obligation) {
  return frameHasSubsumingClause(frames[obligation.level], clauseFromCube(obligation.cube));
}  // LCOV_EXCL_LINE

bool cubeOutsideConcreteResetFrontier(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    const TransitionExprResolver& transitionByState,
    const StateCube& cube,
    size_t postBootstrapSteps,
    ResetFrontierCache& cache,
    bool useResetConstantShortcut) {
  if (problem.resetBootstrapCycles == 0) {
    return false;
  }
  const std::string key = resetFrontierCacheKey(cube, postBootstrapSteps);
  if (const auto it = cache.outsideByCubeKey.find(key);
      it != cache.outsideByCubeKey.end()) {
    return it->second;
  }

  bool outside = false;
  const auto knownInitIntersection =
      postBootstrapSteps == 0
          ? cubeIntersectsKnownInitFacts(problem, cube)
          : std::optional<bool>{};
  if (knownInitIntersection.has_value() && !*knownInitIntersection) {
    // Structured init/bootstrap facts are exact facts about the reset frontier.
    // If they already contradict the cube, avoid rebuilding the much heavier
    // reset-prefix SAT query just to rediscover that contradiction.
    outside = true;
  } else if (postBootstrapSteps == 0 &&
      useResetConstantShortcut &&
      cubeContradictsResetSpecializedConstants(problem, transitionByState, cube)) {
    outside = true;
  } else {
    if (cache.reachabilityContext == nullptr) {
      cache.reachabilityContext =
          makeResetFrontierReachabilityContext(problem, transitionByState);
    }
    outside = !isStateCubeReachableAtResetFrontier(
        *cache.reachabilityContext,
        solverType,
        cubeAssignments(cube),
        postBootstrapSteps);
  }
  cache.outsideByCubeKey.emplace(std::move(key), outside);
  return outside;
}

bool cubeReachableAtConcreteFrame(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    const TransitionExprResolver& transitionByState,
    const StateCube& cube,
    size_t postBootstrapSteps,
    ResetFrontierCache& cache,
    ConcreteCubeReachabilityMode mode) {
  const std::string key = resetFrontierCacheKey(cube, postBootstrapSteps);
  if (const auto it = cache.outsideByCubeKey.find(key);
      it != cache.outsideByCubeKey.end()) {
    return !it->second;
  }

  if (cache.reachabilityContext == nullptr) {
    cache.reachabilityContext =
        makeResetFrontierReachabilityContext(problem, transitionByState);
  }
  const auto assignments = cubeAssignments(cube);
  const bool reachable =
      mode == ConcreteCubeReachabilityMode::OneShotUnitClauses
          ? isStateCubeReachableAtResetFrontierOneShot(
                *cache.reachabilityContext,
                solverType,
                assignments,
                postBootstrapSteps)
          : isStateCubeReachableAtResetFrontier(
                *cache.reachabilityContext,
                solverType,
                assignments,
                postBootstrapSteps);
  cache.outsideByCubeKey.emplace(key, !reachable);
  return reachable;
}

bool cubeReachableWithinConcreteFrames(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    const TransitionExprResolver& transitionByState,
    const StateCube& cube,
    size_t maxPostBootstrapSteps,
    ResetFrontierCache& cache,
    ConcreteCubeReachabilityMode mode) {
  if (pdrStatsEnabled()) {
    emitSecDiag(
        "SEC PDR stats: concrete cube reachability begin ",
        "cube=", cube.size(),
        " max_step=", maxPostBootstrapSteps,
        " mode=", concreteCubeReachabilityModeName(mode));
  }
  for (size_t step = 0; step <= maxPostBootstrapSteps; ++step) {
    const bool reachable = cubeReachableAtConcreteFrame(
            problem,
            solverType,
            transitionByState,
            cube,
            step,
            cache,
            mode);
    if (pdrStatsEnabled()) {
      emitSecDiag(
          "SEC PDR stats: concrete cube reachability step ",
          "step=", step,
          " result=", reachable ? "sat" : "unsat",
          " mode=", concreteCubeReachabilityModeName(mode));
    }
    if (reachable) {
      return true;
    }
  }
  return false;
}

StateCube generalizeResetFrontierCube(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    const TransitionExprResolver& transitionByState,
    const StateCube& cube,
    ResetFrontierCache& cache) {
  // This is an exact, reset-specific literal dropping pass. A reduced cube is
  // accepted only when the concrete reset-frontier SAT query proves that no
  // real post-reset state can satisfy it. The resulting F[0] clause is thus a
  // stronger abstraction refinement, not a heuristic shortcut.
  StateCube candidate = cube;
  if (cache.reachabilityContext == nullptr) {
    cache.reachabilityContext =
        makeResetFrontierReachabilityContext(problem, transitionByState);
  }
  if (const auto core = findResetFrontierUnreachableCubeCore(
          *cache.reachabilityContext,
          solverType,
          cubeAssignments(candidate),
          0);
      core.has_value() && core->size() < candidate.size()) {
    candidate = cubeFromAssignments(*core);
    if (pdrStatsEnabled()) {
      emitSecDiag(
          "SEC PDR stats: reset-frontier core ",
          "cube=", cube.size(),
          "->", candidate.size(),
          " hash=", cubeFingerprint(candidate));
    }
  }
  size_t index = 0;
  size_t attempts = 0;
  while (index < candidate.size() &&
         attempts < kMaxResetFrontierGeneralizationAttempts) {
    ++attempts;
    StateCube reduced = candidate;
    reduced.erase(reduced.begin() + static_cast<std::ptrdiff_t>(index));
    if (cubeOutsideConcreteResetFrontier(
            problem,
            solverType,
            transitionByState,
            reduced,
            0,
            cache)) {
      candidate = std::move(reduced);
      continue;
    }
    ++index;
  }
  return candidate;
}

StateCube generalizeInitExcludedCube(const KInductionProblem& problem,
                                     KEPLER_FORMAL::Config::SolverType solverType,
                                     BoolExpr* initFormula,
                                     const StateCube& cube) {
  // Ordinary Init can also be a relational frontier made of equality facts.
  // When a projected predecessor violates that frontier, learn a generalized
  // F[0] clause immediately instead of relying on many small seed clauses to
  // rediscover adjacent impossible cubes one at a time.
  StateCube candidate = cube;
  size_t index = 0;
  size_t attempts = 0;
  while (index < candidate.size() &&
         attempts < kMaxResetFrontierGeneralizationAttempts) {
    ++attempts;
    StateCube reduced = candidate;
    reduced.erase(reduced.begin() + static_cast<std::ptrdiff_t>(index));
    if (!cubeIntersectsInit(problem, solverType, initFormula, reduced)) {
      candidate = std::move(reduced);
      continue;
    }
    ++index;
  }
  return candidate;
}

StateCube generalizeBoundedUnreachableRootCube(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    const TransitionExprResolver& transitionByState,
    const StateCube& cube,
    size_t maxPostBootstrapSteps,
    ResetFrontierCache& cache,
    size_t maxAttempts,
    size_t& attempts) {
  // Every literal drop is checked against the concrete bounded transition
  // prefix, so the learned clause remains a real CEGAR refinement of the
  // projected PDR trace rather than a heuristic pruning trick.
  StateCube candidate = cube;
  size_t index = 0;
  attempts = 0;
  while (index < candidate.size() && attempts < maxAttempts) {
    StateCube reduced = candidate;
    reduced.erase(reduced.begin() + static_cast<std::ptrdiff_t>(index));
    ++attempts;
    if (!cubeReachableWithinConcreteFrames(
            problem,
            solverType,
            transitionByState,
            reduced,
            maxPostBootstrapSteps,
            cache,
            ConcreteCubeReachabilityMode::OneShotUnitClauses)) {
      candidate = std::move(reduced);
      continue;
    }
    ++index;
  }
  return candidate;
}

size_t popNextObligationIndex(const std::vector<ProofObligation>& queue) {
  size_t bestIndex = 0;
  for (size_t i = 1; i < queue.size(); ++i) {
    if (queue[i].level < queue[bestIndex].level ||
        (queue[i].level == queue[bestIndex].level &&
         (queue[i].cube.size() < queue[bestIndex].cube.size() ||
          (queue[i].cube.size() == queue[bestIndex].cube.size() &&
           queue[i].badFrame < queue[bestIndex].badFrame)))) {
      bestIndex = i;
    }
  }
  return bestIndex;
}

std::string proofObligationKey(const ProofObligation& obligation) {
  std::string key;
  key.reserve(32 + obligation.cube.size() * 24);
  key.append(std::to_string(obligation.level));
  key.push_back('|');
  key.append(std::to_string(obligation.badFrame));
  for (const auto& literal : obligation.cube) {
    key.push_back('|');
    key.append(std::to_string(literal.symbol));
    key.push_back('=');
    key.push_back(literal.value ? '1' : '0');
  }
  key.append("|root");
  for (const auto& literal : obligation.rootCube) {
    key.push_back('|');
    key.append(std::to_string(literal.symbol));
    key.push_back('=');
    key.push_back(literal.value ? '1' : '0');
  }
  return key;
}

void enqueueProofObligation(std::vector<ProofObligation>& queue,
                            std::unordered_set<std::string>& queuedKeys,
                            ProofObligation obligation) {
  // Large SEC output cones can reach the same normalized cube/level pair
  // through several predecessor projections before a learned frame clause
  // subsumes it. Keep only one pending copy: once that obligation is blocked
  // or reaches Init, every duplicate would repeat the same SAT work.
  const std::string key = proofObligationKey(obligation);
  if (!queuedKeys.insert(key).second) {
    return;
  }
  queue.push_back(std::move(obligation));
}

size_t predecessorProjectionLimitForObligation(size_t /*obligationLevel*/,
                                               size_t predecessorProjectionLimit) {
  // Keep predecessor cubes under the projection budget chosen by the SEC stage.
  // A previous near-init widening helped small examples, but BlackParrot
  // sampling showed it expanding level-2 targets into 100+ literal
  // predecessors that the F[0] blocking loop could not shrink usefully.
  return predecessorProjectionLimit;
}

bool blockProofObligations(const KInductionProblem& problem,
                           KEPLER_FORMAL::Config::SolverType solverType,
                           const TransitionExprResolver& transitionByState,
                           BoolExpr* initFormula,
                           BoolExpr* frameInvariant,
                           std::vector<FrameClauses>& frames,
                           const StateCube& rootCube,
                           size_t rootLevel,
                           size_t& badFrame,
                           const ComplementPartnerIndex& complementPartners,
                           size_t predecessorProjectionLimit,
                           bool exactFrameClauses,
                           bool refineProjectedCounterexamples,
                           ResetFrontierCache& resetFrontierCache,
                           size_t maxBoundedRootGeneralizationAttempts,
                           bool learnValidatedBadFormulaClausesOnReject,
                           bool useExactResetFrontierChecks,
                           size_t* predecessorQueryBudget) {
  // This is the paper's recursive blocking idea expressed as an explicit queue
  // so we do not depend on deep recursion for large obligation stacks.
  std::vector<ProofObligation> queue;
  std::unordered_set<std::string> queuedKeys;
  enqueueProofObligation(
      queue, queuedKeys, ProofObligation{rootCube, rootLevel, rootLevel, rootCube});
  const InitFactIndex initFacts = buildInitFactIndex(problem);
  auto learnBlockedObligation = [&](const ProofObligation& blockedObligation,
                                    bool exactClausesForGeneralization) {
    const StateCube generalizedCube = generalizeBlockedCube(
        problem,
        solverType,
        transitionByState,
        initFormula,
        frameInvariant,
        frames,
        blockedObligation.level,
        blockedObligation.cube,
        &resetFrontierCache,
        complementPartners,
        predecessorProjectionLimit,
        exactClausesForGeneralization,
        useExactResetFrontierChecks,
        predecessorQueryBudget);
    addClauseToFrames(
        frames, clauseFromCube(generalizedCube), blockedObligation.level);
    if (blockedObligation.level < blockedObligation.badFrame) {
      const StateCube propagatedRoot =
          blockedObligation.rootCube.empty()
              ? generalizedCube
              : blockedObligation.rootCube;
      // The pushed obligation is the generalized blocked cube, but any
      // concrete counterexample must still be validated against the original
      // bad/root cube. A generalized cube is a larger state set and may be
      // reachable even when the property cube that caused it is not.
      enqueueProofObligation(
          queue,
          queuedKeys,
          ProofObligation{
              generalizedCube,
              blockedObligation.level + 1,
              blockedObligation.badFrame,
              propagatedRoot});
    }
  };
  auto learnBlockedObligationVerbatim =
      [&](const ProofObligation& blockedObligation) {
    // The projected-frame CEGAR loop below can prove a cube blocked only after
    // adding a few missing learned-frame clauses to that local query. Those
    // clauses are real frame facts, so learning the original cube is sound; we
    // intentionally skip optional literal-dropping here because re-running
    // generalization without the same local CEGAR blockers can rediscover the
    // stale predecessor that we just eliminated.
    addClauseToFrames(
        frames, clauseFromCube(blockedObligation.cube), blockedObligation.level);
    if (blockedObligation.level < blockedObligation.badFrame) {
      enqueueProofObligation(
          queue,
          queuedKeys,
          ProofObligation{
              blockedObligation.cube,
              blockedObligation.level + 1,
              blockedObligation.badFrame,
              blockedObligation.rootCube});
    }
  };

  while (!queue.empty()) {
    const size_t obligationIndex = popNextObligationIndex(queue);
    const ProofObligation obligation = queue[obligationIndex];
    queuedKeys.erase(proofObligationKey(obligation));
    queue.erase(queue.begin() + static_cast<std::ptrdiff_t>(obligationIndex));
    const bool obligationExactFrameClauses = exactFrameClauses;

    if (obligationAlreadyBlocked(frames, obligation)) {
      continue;
    }

    if (obligation.level == 0) {
      const bool outsideConcreteResetFrontier =
          useExactResetFrontierChecks &&
          cubeOutsideConcreteResetFrontier(
              problem,
              solverType,
              transitionByState,
              obligation.cube,
              0,
              resetFrontierCache);
      if (outsideConcreteResetFrontier) {
        // For reset-bootstrap SEC, F[0] is an over-approximation of the
        // concrete post-reset image. Reaching an abstract-only level-0 cube is
        // not a counterexample; it is a refinement opportunity. Adding the
        // negated cube to F[0] is safe because either reset-specialized
        // constants or the exact reset-image query proved that no concrete
        // post-reset state satisfies the cube. Before learning it, run a
        // bounded exact generalization pass; otherwise large reset-bootstrap
        // ASICs can enumerate thousands of adjacent abstract F[0] cubes that
        // differ only in irrelevant predecessor support bits.
        const StateCube generalizedCube = generalizeResetFrontierCube(
            problem,
            solverType,
            transitionByState,
            obligation.cube,
            resetFrontierCache);
        addClauseToFrame(frames[0], clauseFromCube(generalizedCube));
        continue;
      }
      if (const auto conflictCube =
              knownInitConflictCube(initFacts, obligation.cube);
          conflictCube.has_value()) {
        // Ordinary relational Init has the same refinement opportunity as the
        // reset-frontier path.  When the cube visibly contradicts a structured
        // init fact, learn only that conflict instead of a wide SAT-model cube;
        // this keeps large ASIC output slices from rediscovering the same
        // state equality violation thousands of times.
        addClauseToFrame(frames[0], clauseFromCube(*conflictCube));
        continue;
      }
      if (!cubeIntersectsInit(problem, solverType, initFormula, obligation.cube)) {
        const StateCube generalizedCube = generalizeInitExcludedCube(
            problem,
            solverType,
            initFormula,
            obligation.cube);
        addClauseToFrame(frames[0], clauseFromCube(generalizedCube));
        continue;
      }
      if (pdrStatsEnabled()) {
        emitSecDiag(
            "SEC PDR stats: counterexample candidate reached init ",
            "bad_frame=", obligation.badFrame,
            " cube=", obligation.cube.size(),
            " root_cube=", obligation.rootCube.size());
      }
      if (!refineProjectedCounterexamples) {
        // SEC strategy runs a concrete base-case validation immediately after
        // every PDR difference. Projected retry stages therefore do not need to
        // spend another exact bounded-prefix query here; returning the
        // candidate lets the caller either accept a real witness or move to the
        // next precision stage.
        badFrame = obligation.badFrame;
        return false;
      }
      if (learnValidatedBadFormulaClausesOnReject) {
        const auto refinement = learnValidatedBadFormulaClauses(
              problem,
              solverType,
              transitionByState,
              frames,
              obligation.badFrame,
              badFrame);
        if (refinement.has_value()) {
          return *refinement;
        }
      }
      const StateCube& concreteTarget =
          obligation.rootCube.empty() ? obligation.cube : obligation.rootCube;
      if (!cubeReachableWithinConcreteFrames(
              problem,
              solverType,
              transitionByState,
              concreteTarget,
              obligation.badFrame,
              resetFrontierCache,
              ConcreteCubeReachabilityMode::OneShotUnitClauses)) {
        // Projected predecessor cubes can be reachable even when the original
        // bad/frontier cube they came from is not.  Before accepting such a
        // path as a counterexample, validate the root cube with the exact
        // bounded transition prefix.  This is a final candidate check, not a
        // stream of neighboring reset cubes, so use a one-shot unit-clause SAT
        // query and the selected SEC solver instead of a long-lived Glucose
        // assumption solver. If no concrete prefix reaches it, learn a
        // bounded-safe frame clause and keep the ordinary PDR loop going.
        size_t generalizationAttempts = 0;
        const StateCube generalizedTarget =
            generalizeBoundedUnreachableRootCube(
                problem,
                solverType,
                transitionByState,
                concreteTarget,
                obligation.badFrame,
                resetFrontierCache,
                maxBoundedRootGeneralizationAttempts,
                generalizationAttempts);
        const StateClause refinedClause = clauseFromCube(generalizedTarget);
        if (obligation.badFrame == 0) {
          addClauseToFrame(frames[0], refinedClause);
        } else {
          addClauseToFrames(frames, refinedClause, obligation.badFrame);
        }
        if (pdrStatsEnabled()) {
          emitSecDiag(
              "SEC PDR stats: refined projected counterexample ",
              "bad_frame=", obligation.badFrame,
              " root_cube=", concreteTarget.size(),
              "->", generalizedTarget.size(),
              " checks=", generalizationAttempts);
        }
        return true;
      }
      badFrame = obligation.badFrame;
      return false;
    }

    const size_t obligationProjectionLimit =
        predecessorProjectionLimitForObligation(
            obligation.level, predecessorProjectionLimit);

    if (obligation.cube.size() > kLargeBlockedCubeGeneralizationThreshold) {
      // For a large target cube, first try to block a cheap subset.  If no
      // predecessor can reach the subset, then no predecessor can reach the
      // stronger original cube either, and we avoid building a SAT query for a
      // thousand next-state functions just to learn the same small clause.
      const StateCube cheapTarget = boundedCheapTransitionCube(
          obligation.cube, kLargeBlockedCubeSeedSize, transitionByState);
      if (cheapTarget.size() < obligation.cube.size() &&
          !findPredecessorCube(
               problem,
               solverType,
               transitionByState,
               initFormula,
               frameInvariant,
               frames,
               obligation.level - 1,
               cheapTarget,
               false,
               complementPartners,
               obligationProjectionLimit,
               obligationExactFrameClauses,
               &resetFrontierCache,
               nullptr,
               predecessorQueryBudget,
               useExactResetFrontierChecks)
               .has_value()) {
        const StateCube generalizedCube = generalizeBlockedCube(
            problem,
            solverType,
            transitionByState,
            initFormula,
            frameInvariant,
            frames,
            obligation.level,
            cheapTarget,
            &resetFrontierCache,
            complementPartners,
            obligationProjectionLimit,
            obligationExactFrameClauses,
            useExactResetFrontierChecks,
            predecessorQueryBudget);
        addClauseToFrames(frames, clauseFromCube(generalizedCube), obligation.level);
        if (obligation.level < obligation.badFrame) {
          const StateCube propagatedRoot =
              obligation.rootCube.empty() ? generalizedCube : obligation.rootCube;
          enqueueProofObligation(
              queue,
              queuedKeys,
              ProofObligation{
                  generalizedCube,
                  obligation.level + 1,
                  obligation.badFrame,
                  propagatedRoot});
        }
        continue;
      }
    }

    std::vector<StateClause> projectedFrameRefinements;
    std::unordered_set<std::string> projectedFrameRefinementKeys;
    while (true) {
      const auto predecessor = findPredecessorCube(
          problem,
          solverType,
          transitionByState,
          initFormula,
          frameInvariant,
          frames,
          obligation.level - 1,
          obligation.cube,
          false,
          complementPartners,
          obligationProjectionLimit,
          obligationExactFrameClauses,
          &resetFrontierCache,
          projectedFrameRefinements.empty() ? nullptr : &projectedFrameRefinements,
          predecessorQueryBudget,
          useExactResetFrontierChecks);
      if (!predecessor.has_value()) {
        // No predecessor survives F[level-1], so the cube can be blocked at
        // every frame up to "level". If we needed local projected-frame
        // refinements, learn this exact cube directly rather than re-entering
        // generalization without the same refinement clauses.
        if (projectedFrameRefinements.empty()) {
          learnBlockedObligation(obligation, obligationExactFrameClauses);
        } else {
          learnBlockedObligationVerbatim(obligation);
        }
        break;
      }
      const StateCube queuedPredecessor =
          obligation.level == 1
              ? *predecessor
              : boundedPrefixCube(*predecessor, obligationProjectionLimit);
      ProofObligation predecessorObligation{
          queuedPredecessor,
          obligation.level - 1,
          obligation.badFrame,
          obligation.rootCube};
      const StateClause predecessorClause =
          clauseFromCube(predecessorObligation.cube);
      const auto blockingClause =
          !obligationExactFrameClauses
              ? findSubsumingFrameClause(
                    frames[predecessorObligation.level], predecessorClause)
              : std::optional<StateClause>{};
      if (blockingClause.has_value()) {
        // Projected frame encoding is sound but incomplete: it may omit the
        // learned clause that already blocks this predecessor.  Re-enqueueing
        // such a stale predecessor creates a reset-frontier loop. Refine only
        // this local SAT query with the missing learned blocker instead of
        // rebuilding the query with every clause from the full frame.
        const std::string blockingKey = stateClauseKey(*blockingClause);
        if (projectedFrameRefinementKeys.insert(blockingKey).second) {
          projectedFrameRefinements.push_back(*blockingClause);
          if (pdrStatsEnabled()) {
            const size_t retryNumber = nextPdrProjectedBlockedRetryNumber();
            if (retryNumber <= kInitialPdrStatsQueries ||
                retryNumber % pdrStatsInterval() == 0) {
              emitSecDiag(
                  "SEC PDR stats: projected-frame refinement #", retryNumber,
                  " level=", obligation.level,
                  " cube=", obligation.cube.size(),
                  " predecessor=", predecessorObligation.cube.size(),
                  " refinements=", projectedFrameRefinements.size());
            }
          }
          if (projectedFrameRefinements.size() <
              maxProjectedFrameRefinementsBeforeExactRetry()) {
            continue;
          }
          if (pdrStatsEnabled()) {
            emitSecDiag(
                "SEC PDR stats: projected-frame refinement cap reached ",
                "level=", obligation.level,
                " cube=", obligation.cube.size(),
                " predecessor=", predecessorObligation.cube.size(),
                " refinements=", projectedFrameRefinements.size());
          }
        } else if (pdrStatsEnabled()) {
          // If the same blocker was already added and the projected query still
          // returns a predecessor blocked by it, keep the algorithm
          // conservative: fall back to the exact-frame path once instead of
          // spinning forever.
          emitSecDiag(
              "SEC PDR stats: exact retry for duplicate projected blocker ",
              "level=", obligation.level,
              " cube=", obligation.cube.size(),
              " predecessor=", predecessorObligation.cube.size());
        }
        const auto exactPredecessor = findPredecessorCube(
            problem,
            solverType,
            transitionByState,
            initFormula,
            frameInvariant,
            frames,
            obligation.level - 1,
            obligation.cube,
            false,
            complementPartners,
            obligationProjectionLimit,
            true,
            &resetFrontierCache,
            nullptr,
            predecessorQueryBudget,
            useExactResetFrontierChecks);
        if (!exactPredecessor.has_value()) {
          learnBlockedObligation(obligation, true);
          break;
        }
        const StateCube exactQueuedPredecessor =
            obligation.level == 1
                ? *exactPredecessor
                : boundedPrefixCube(*exactPredecessor, obligationProjectionLimit);
        predecessorObligation = ProofObligation{
            exactQueuedPredecessor,
            obligation.level - 1,
            obligation.badFrame,
            obligation.rootCube};
      }
      enqueueProofObligation(queue, queuedKeys, obligation);
      enqueueProofObligation(queue, queuedKeys, predecessorObligation);
      break;
    }
  }

  return true;
}

std::vector<StateClause> buildSeedClauses(const KInductionProblem& problem) {
  std::vector<StateClause> seedClauses;
  // Seed the first learned frame with state equalities that are already
  // guaranteed by Init/bootstrap, so PDR starts from facts that are known
  // reachable-state invariants instead of rediscovering them from scratch.
  //
  // This deliberately uses only structured init/bootstrap facts. Running an
  // exact SAT init-intersection query for every possible equality seed is too
  // expensive on ASIC regressions and is not needed for soundness: if a seed is
  // not cheaply known to hold on the startup frontier, we simply do not seed it.
  const InitFactIndex initFacts = buildInitFactIndex(problem);
  for (const auto& [lhsSymbol, rhsSymbol] : problem.inductiveStateEqualityPairs) {
    StateClause clause0 = {{lhsSymbol, false}, {rhsSymbol, true}};
    StateClause clause1 = {{lhsSymbol, true}, {rhsSymbol, false}};
    normalizeClause(clause0);
    normalizeClause(clause1);

    // Promote already-anchored state equalities into initial frame facts when
    // they are guaranteed by Init/bootstrap instead of guessed from structure.
    if (twoLiteralCubeIsKnownOutsideInit(
            initFacts, lhsSymbol, true, rhsSymbol, false)) {
      seedClauses.push_back(clause0);
    }
    if (twoLiteralCubeIsKnownOutsideInit(
            initFacts, lhsSymbol, false, rhsSymbol, true)) {
      seedClauses.push_back(clause1);
    }
  }
  return seedClauses;
}

BoolExpr* buildStateEqualityInvariant(
    const std::vector<std::pair<size_t, size_t>>& equalityPairs) {
  if (equalityPairs.empty()) {
    return nullptr;
  }

  BoolExpr* invariant = BoolExpr::createTrue();
  for (const auto& [lhsSymbol, rhsSymbol] : equalityPairs) {
    invariant = BoolExpr::And(
        invariant,
        makeEqualityExpr(BoolExpr::Var(lhsSymbol), BoolExpr::Var(rhsSymbol)));
  }
  invariant = BoolExpr::simplify(invariant);
  return invariant == BoolExpr::createTrue() ? nullptr : invariant;
}

BoolExpr* buildStateEqualityInvariant(const KInductionProblem& problem) {
  return buildStateEqualityInvariant(problem.inductiveStateEqualityPairs);
}

BoolExpr* buildStateAndOutputInvariant(
    const KInductionProblem& problem,
    const std::vector<std::pair<size_t, size_t>>& equalityPairs) {
  BoolExpr* invariant = buildStateEqualityInvariant(equalityPairs);
  if (invariant == nullptr) {
    invariant = BoolExpr::createTrue();
  }
  for (size_t output = 0;
       output < problem.observedOutputExprs0.size() &&
       output < problem.observedOutputExprs1.size();
       ++output) {
    invariant = BoolExpr::And(
        invariant,
        makeEqualityExpr(
            problem.observedOutputExprs0[output],
            problem.observedOutputExprs1[output]));
  }
  invariant = BoolExpr::simplify(invariant);
  return invariant == BoolExpr::createTrue() ? nullptr : invariant;
}

std::vector<size_t> stateEqualitySymbols(
    const std::vector<std::pair<size_t, size_t>>& equalityPairs) {
  std::unordered_set<size_t> symbols;
  symbols.reserve(equalityPairs.size() * 2);
  for (const auto& [lhsSymbol, rhsSymbol] : equalityPairs) {
    symbols.insert(lhsSymbol);
    symbols.insert(rhsSymbol);
  }
  return sortUniqueSymbols(std::move(symbols));
}

bool equalityPairViolatedAtFrame(const SATSolverWrapper& solver,
                                 const FrameVariableStore& variables,
                                 const std::pair<size_t, size_t>& pair,
                                 size_t frame) {
  if (!variables.hasSymbol(pair.first) || !variables.hasSymbol(pair.second)) {
    return false;  // LCOV_EXCL_LINE
  }
  return solver.getLiteralValue(variables.getLiteral(pair.first, frame)) !=
         solver.getLiteralValue(variables.getLiteral(pair.second, frame));
}

std::optional<std::vector<std::pair<size_t, size_t>>>
pruneStateEqualitySubsetByInductiveCounterexample(
    const KInductionProblem& problem,
    const TransitionExprResolver& transitionByState,
    const std::vector<std::pair<size_t, size_t>>& equalityPairs,
    BoolExpr* invariant,
    KEPLER_FORMAL::Config::SolverType solverType) {
  const std::vector<size_t> invariantSymbols = stateEqualitySymbols(equalityPairs);
  const std::vector<size_t> encodedTargets =
      expandTransitionTargets(problem, invariantSymbols, transitionByState);
  const std::vector<size_t> transitionSupportSymbols =
      collectTransitionSupportSymbols(transitionByState, encodedTargets);

  std::unordered_set<size_t> querySymbols(
      invariantSymbols.begin(), invariantSymbols.end());
  querySymbols.insert(encodedTargets.begin(), encodedTargets.end());
  querySymbols.insert(
      transitionSupportSymbols.begin(), transitionSupportSymbols.end());
  addRelevantComplementedStatePartners(problem.complementedStatePairs0, querySymbols);
  addRelevantComplementedStatePartners(problem.complementedStatePairs1, querySymbols);

  SATSolverWrapper solver(solverType);
  const auto solverSymbols = sortUniqueSymbols(std::move(querySymbols));
  FrameVariableStore variables(solver, solverSymbols, 2);
  addComplementedStateRelations(solver, variables, problem.complementedStatePairs0, 2);
  addComplementedStateRelations(solver, variables, problem.complementedStatePairs1, 2);
  addPostBootstrapResetInputConstraints(solver, variables, problem, 0);
  addTransitionRelationForTargets(
      solver,
      variables,
      transitionByState,
      0,
      encodedTargets,
      transitionSupportSymbols);

  FrameFormulaEncoder currentEncoder(
      solver, variables.makeLeafLits(0, invariantSymbols));
  FrameFormulaEncoder nextEncoder(
      solver, variables.makeLeafLits(1, invariantSymbols));
  solver.addClause({currentEncoder.encode(invariant)});
  solver.addClause({nextEncoder.encode(BoolExpr::Not(invariant))});
  if (!solver.solve()) {
    return std::nullopt;
  }

  std::vector<std::pair<size_t, size_t>> keptPairs;
  keptPairs.reserve(equalityPairs.size());
  for (const auto& pair : equalityPairs) {
    if (!equalityPairViolatedAtFrame(solver, variables, pair, 1)) {
      keptPairs.push_back(pair);
    }
  }
  if (keptPairs.size() == equalityPairs.size()) {
    return std::vector<std::pair<size_t, size_t>>{};
  }
  return keptPairs;
}

BoolExpr* selectInductiveStateEqualitySubsetInvariant(
    const KInductionProblem& problem,
    BoolExpr* initFormula,
    KEPLER_FORMAL::Config::SolverType solverType,
    std::vector<std::pair<size_t, size_t>>* selectedPairs = nullptr) {
  if (problem.inductiveStateEqualityPairs.empty() ||
      problem.inductiveStateEqualityPairs.size() > kMaxStateEqualitySubsetPairs) {
    return nullptr;
  }

  std::vector<std::pair<size_t, size_t>> equalityPairs =
      problem.inductiveStateEqualityPairs;
  BoolExpr* invariant = buildStateEqualityInvariant(equalityPairs);
  if (invariant == nullptr ||
      !initialFrontierImplies(initFormula, invariant, solverType)) {
    return nullptr;
  }

  TransitionExprResolver transitionByState(problem);
  for (size_t iteration = 0;
       iteration < kMaxStateEqualitySubsetIterations && !equalityPairs.empty();
       ++iteration) {
    invariant = buildStateEqualityInvariant(equalityPairs);
    auto prunedPairs = pruneStateEqualitySubsetByInductiveCounterexample(
        problem, transitionByState, equalityPairs, invariant, solverType);
    if (!prunedPairs.has_value()) {
      if (pdrStatsEnabled()) {
        emitSecDiag(
            "SEC PDR stats: frame invariant state_equality_subset support=",
            invariant->getSupportVars().size(),
            " pairs=", equalityPairs.size(),
            " iterations=", iteration + 1,
            " init=pass inductive=pass");
      }
      if (selectedPairs != nullptr) {
        *selectedPairs = equalityPairs;
      }
      return invariant;
    }
    if (prunedPairs->empty()) {
      break;
    }
    equalityPairs = std::move(*prunedPairs);
  }

  if (pdrStatsEnabled()) {
    emitSecDiag(
        "SEC PDR stats: frame invariant state_equality_subset unavailable ",
        "remaining_pairs=", equalityPairs.size(),
        " iterations=", kMaxStateEqualitySubsetIterations);
  }
  return nullptr;
}

BoolExpr* selectPdrFrameInvariant(const KInductionProblem& problem,
                                  BoolExpr* initFormula,
                                  KEPLER_FORMAL::Config::SolverType solverType) {
  // PDR can use already inferred SEC facts as a strengthening invariant, but
  // only after validating the same two proof obligations that make any frame
  // invariant sound:
  //   1. the startup/reset frontier implies it, and
  //   2. one transition step preserves it.
  //
  // This is not a separate "fast proof" path. The invariant is fed back into
  // the ordinary bad-cube and predecessor queries below, so PDR still performs
  // the frame/blocking/convergence algorithm. It simply avoids relearning the
  // same state-equality facts one clause at a time on large SEC designs.
  if (initFormula == nullptr) {
    return nullptr;
  }

  FormulaSupportCache invariantSupportCache;
  auto validateCandidate = [&](const char* label, BoolExpr* candidate) -> BoolExpr* {
    if (candidate == nullptr) {
      if (pdrStatsEnabled()) {
        emitSecDiag("SEC PDR stats: frame invariant ", label, " unavailable");
      }
      return nullptr;
    }

    const bool initImpliesCandidate =
        initialFrontierImplies(initFormula, candidate, solverType);
    const bool inductive =
        initImpliesCandidate &&
        isInductiveInvariant(
            problem, candidate, solverType, invariantSupportCache);
    if (pdrStatsEnabled()) {
      emitSecDiag(
          "SEC PDR stats: frame invariant ", label,
          " support=", candidate->getSupportVars().size(),
          " init=", initImpliesCandidate ? "pass" : "fail",
          " inductive=", inductive ? "pass" : "fail");
    }
    if (!initImpliesCandidate || !inductive) {
      return nullptr;
    }
    return candidate;
  };

  auto selectSharedStrengthening = [&]() -> BoolExpr* {
    // The shared SEC strengthening can be stronger than a pruned equality
    // subset.  It still has to pass the same init and one-step inductiveness
    // checks before PDR may use it as a frame fact.
    BoolExpr* sharedStrengthening =
        selectValidatedStrengtheningInvariant(problem, initFormula, solverType);
    return validateCandidate("shared_strengthening", sharedStrengthening);
  };

  if (BoolExpr* stateInvariant =
          validateCandidate("state_equalities", buildStateEqualityInvariant(problem))) {
    if (isSecDiagEnabled()) {
      emitSecDiag(
          "SEC diag: PDR using validated state-equality frame invariant with ",
          problem.inductiveStateEqualityPairs.size(),
          " equality pairs");
    }
    return stateInvariant;
  }

  std::vector<std::pair<size_t, size_t>> stateSubsetPairs;
  if (BoolExpr* stateSubsetInvariant =
          selectInductiveStateEqualitySubsetInvariant(
              problem, initFormula, solverType, &stateSubsetPairs)) {
    // A state-only subset may be inductive but too weak to exclude the output
    // mismatch, causing PDR to rediscover the output equality as thousands of
    // tiny blocking clauses.  Strengthen that subset with the current output
    // equality only when the combined formula is itself proved valid on Init
    // and inductive across one transition.  The result is still just a PDR
    // frame fact; it is not an external fast proof path.
    if (BoolExpr* outputStrengthenedInvariant =
            validateCandidate(
                "state_equality_subset_outputs",
                buildStateAndOutputInvariant(problem, stateSubsetPairs))) {
      if (isSecDiagEnabled()) {
        emitSecDiag(
            "SEC diag: PDR using validated state/output subset frame invariant");
      }
      return outputStrengthenedInvariant;
    }

    if (BoolExpr* strengthenedInvariant = selectSharedStrengthening()) {
      if (isSecDiagEnabled()) {
        emitSecDiag(
            "SEC diag: PDR using validated SEC strengthening frame invariant");
      }
      return strengthenedInvariant;
    }

    if (isSecDiagEnabled()) {
      emitSecDiag(
          "SEC diag: PDR using validated state-equality subset frame invariant");
    }
    return stateSubsetInvariant;
  }

  // Some SEC proofs need the full extracted strengthening lemma, not just the
  // raw state-equality core. This is still used as a PDR frame constraint only
  // after the same inductiveness check succeeds.
  if (BoolExpr* strengthenedInvariant = selectSharedStrengthening()) {
    if (isSecDiagEnabled()) {
      emitSecDiag(
          "SEC diag: PDR using validated SEC strengthening frame invariant");
    }
    return strengthenedInvariant;
  }
  return nullptr;
}

void propagateClauses(const KInductionProblem& problem,
                      KEPLER_FORMAL::Config::SolverType solverType,
                      const TransitionExprResolver& transitionByState,
                      BoolExpr* initFormula,
                      BoolExpr* frameInvariant,
                      std::vector<FrameClauses>& frames,
                      size_t maxLevel,
                      const ComplementPartnerIndex& complementPartners,
                      size_t predecessorProjectionLimit,
                      bool exactFrameClauses,
                      size_t* predecessorQueryBudget) {
  // Standard PDR propagation: if F[i] /\ T implies a clause on the next frame,
  // move that clause forward into F[i+1].
  for (size_t level = 1; level <= maxLevel; ++level) {
    const auto snapshot = frames[level].clauses;
    for (const auto& clause : snapshot) {
      // Only propagate clauses that are not already known to hold on the next frame,
      // otherwise we would be doing redundant work and risking over-blocking by
      // adding the same clause again after generalization.
      if (frameHasSubsumingClause(frames[level + 1], clause)) {
        continue;
      }
      const StateCube violatingCube = cubeFromClauseNegation(clause);
      // A clause is only safe to propagate if it does not block a real bad path, so check
      // whether any predecessor of the negated cube survives in the current frame. If not, the
      // clause can be added to the next frame without risking over-blocking.
      if (!findPredecessorCube(
               problem,
               solverType,
               transitionByState,
               initFormula,
               frameInvariant,
               frames,
               level,
               violatingCube,
               false,
               complementPartners,
               predecessorProjectionLimit,
               exactFrameClauses,
               nullptr,
               nullptr,
               predecessorQueryBudget)
               .has_value()) {
        addClauseToFrame(frames[level + 1], clause);
      }
    }
  }
}

bool isSecPdrTraceEnabled() {
  return std::getenv("KEPLER_SEC_PDR_TRACE") != nullptr;
}

std::string formatSymbolForPdrTrace(size_t symbol) {
  if (symbol == 0) {
    return "FALSE";  // LCOV_EXCL_LINE
  }
  if (symbol == 1) {
    return "TRUE";  // LCOV_EXCL_LINE
  }
  return "x" + std::to_string(symbol);
}

std::string formatCubeForPdrTrace(const StateCube& cube) {
  std::ostringstream oss;
  oss << "{";
  for (size_t i = 0; i < cube.size(); ++i) {
    if (i != 0) {
      oss << ", ";
    }
    oss << formatSymbolForPdrTrace(cube[i].symbol) << "=" << (cube[i].value ? "1" : "0");
  }
  oss << "}";
  return oss.str();
}

std::string formatClauseForPdrTrace(const StateClause& clause) {
  std::ostringstream oss;
  oss << "(";
  for (size_t i = 0; i < clause.size(); ++i) {
    if (i != 0) {
      oss << " OR ";
    }
    if (!clause[i].positive) {
      oss << "!";
    }
    oss << formatSymbolForPdrTrace(clause[i].symbol);
  }
  oss << ")";
  return oss.str();
}

std::string formatFramesForPdrTrace(const std::vector<FrameClauses>& frames) {
  std::ostringstream oss;
  for (size_t level = 0; level < frames.size(); ++level) {
    oss << "  F[" << level << "]: ";
    if (level == 0) {
      oss << "Init";
    }
    oss << "\n";
    if (frames[level].clauses.empty()) {
      oss << "    <empty>\n";
      continue;
    }
    for (const auto& clause : frames[level].clauses) {
      oss << "    " << formatClauseForPdrTrace(clause) << "\n";
    }
  }
  return oss.str();
}

void emitPdrTrace(std::string_view label, const std::string& body) {
  if (!isSecPdrTraceEnabled()) {
    return;
  }
  emitSecDiag("SEC PDR trace: ", label, "\n", body);
}

void emitPdrTraceProblem(const KInductionProblem& problem) {
  if (!isSecPdrTraceEnabled()) {
    return;
  }
  // Full formula formatting recursively walks every transition/property DAG.
  // That is useful for small debug tests, but on ASIC-size SEC problems it can
  // allocate gigabytes before PDR starts.  Keep the expensive string build
  // strictly behind the explicit PDR trace flag.
  emitSecDiag("SEC PDR trace: problem\n", formatKInductionProblemForDebug(problem));
}

void emitPdrTraceFrames(std::string_view label,
                        const std::vector<FrameClauses>& frames) {
  if (!isSecPdrTraceEnabled()) {
    return;
  }
  emitSecDiag("SEC PDR trace: ", label, "\n", formatFramesForPdrTrace(frames));
}

std::optional<PDRResult> checkResetBootstrapFrameZero(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    bool& resetBootstrapFrameCheckedSafe) {
  if (problem.resetBootstrapCycles == 0 || resetBootstrapFrameCheckedSafe) {
    return std::nullopt;
  }

  // A reset-bootstrap frontier may be summarized by only the state facts the
  // extractor could prove cheaply. Before PDR treats that summary as F[0], run
  // the concrete one-shot reset BMC used by the other SEC engines. If it finds
  // a real bad post-reset state, report it; otherwise PDR is allowed to add the
  // checked property as a safe F[0] fact below.
  if (auto witness = findBaseCounterexample(problem, solverType, 0);
      witness.has_value()) {
    return PDRResult{PDRStatus::Different, witness->badFrame};
  }
  resetBootstrapFrameCheckedSafe = true;
  return std::nullopt;
}

BoolExpr* buildPdrInitFormula(const KInductionProblem& problem,
                              bool resetBootstrapFrameCheckedSafe) {
  BoolExpr* initFormula = buildProofInitFormula(problem);
  if (problem.resetBootstrapCycles == 0 ||
      !resetBootstrapFrameCheckedSafe ||
      problem.property == nullptr) {
    return initFormula;
  }

  // The bootstrap summary is an abstraction of the reset-unrolled frontier, not
  // necessarily the exact set of post-reset states. Once concrete BMC proved no
  // k=0 SEC mismatch, the SEC property itself is a valid F[0] fact. PDR is run
  // on output batches for wide SEC problems, so this guard stays local to the
  // current property slice instead of materializing the full design property in
  // every SAT query.
  return BoolExpr::simplify(
      BoolExpr::And(
          initFormula != nullptr ? initFormula : BoolExpr::createTrue(),
          problem.property));
}

}  // namespace

PDREngine::PDREngine(const KInductionProblem& problem,
                     KEPLER_FORMAL::Config::SolverType solverType,
                     size_t predecessorProjectionLimit,
                     size_t preciseBadCubeStateLimit,
                     bool useExactFrameClauses,
                     size_t maxPredecessorQueries,
                     bool refineProjectedCounterexamples,
                     size_t maxBoundedRootGeneralizationAttempts,
                     bool learnValidatedBadFormulaClauses,
                     bool useExactResetFrontierChecks)
    : problem_(problem),
      solverType_(solverType),
      predecessorProjectionLimit_(predecessorProjectionLimit),
      useExactFrameClauses_(useExactFrameClauses ||
                            predecessorProjectionLimit == 0),
      preciseBadCubeStateLimit_(preciseBadCubeStateLimit),
      maxPredecessorQueries_(maxPredecessorQueries),
      refineProjectedCounterexamples_(refineProjectedCounterexamples),
      maxBoundedRootGeneralizationAttempts_(
          maxBoundedRootGeneralizationAttempts),
      learnValidatedBadFormulaClauses_(learnValidatedBadFormulaClauses),
      useExactResetFrontierChecks_(useExactResetFrontierChecks) {}

PDRResult PDREngine::run(size_t maxFrames,
                         bool resetBootstrapFrameCheckedSafe) const {
  // Build the SEC startup frontier once so every frame query shares the same
  // interpretation of reset/bootstrap and frame-0 equality constraints.
  emitPdrTraceProblem(problem_);
  if (const auto resetProof = checkResetBootstrapFrameZero(
          problem_, solverType_, resetBootstrapFrameCheckedSafe);
      resetProof.has_value()) {
    return *resetProof;
  }

  BoolExpr* initFormula =
      buildPdrInitFormula(problem_, resetBootstrapFrameCheckedSafe);
  if (initFormula == nullptr) {
    return {PDRStatus::Inconclusive, 0};
  }

  // PDR still establishes convergence through its own frame/blocking loop, but
  // it may use validated state-correspondence equalities as a frame invariant.
  // Those equalities come from the shared SEC extraction/reset analysis and are
  // checked for init coverage and transition preservation before use.
  BoolExpr* frameInvariant =
      selectPdrFrameInvariant(problem_, initFormula, solverType_);
  const bool exactFrameClauses = useExactFrameClauses_;

  TransitionExprResolver transitionByState(problem_);
  ComplementPartnerIndex complementPartners(problem_);
  // The bad predicate is the same for every frame query. Cache its state
  // support once so repeated PDR bad-cube checks do not rebuild the large
  // combined miter state set on every loop iteration.
  const auto preciseBadStateSupport = collectBoundedStateSupportSymbols(
      problem_.bad,
      kMaxPreciseBadCubeSupportNodes,
      preciseBadCubeStateLimit_,
      transitionByState.stateSymbols());
  ResetFrontierCache resetFrontierCache;
  size_t remainingPredecessorQueries = maxPredecessorQueries_;
  size_t* predecessorQueryBudget =
      maxPredecessorQueries_ == 0 ? nullptr : &remainingPredecessorQueries;
  std::vector<FrameClauses> frames(1);
  emitPdrTraceFrames("initial_frames", frames);

  // Before growing any frame sequence, check whether Init itself already
  // contains a bad state.
  if (!(problem_.resetBootstrapCycles != 0 && resetBootstrapFrameCheckedSafe)) {
    if (auto badCube = findBadCube(
            problem_,
            solverType_,
            initFormula,
            frameInvariant,
            frames,
            preciseBadStateSupport,
            preciseBadCubeStateLimit_,
            transitionByState.stateSymbols(),
            0,
            complementPartners,
            exactFrameClauses);
        badCube.has_value()) {
      emitPdrTrace("bad_cube@F0", formatCubeForPdrTrace(*badCube));
      return {PDRStatus::Different, 0};
    }
  }

  if (maxFrames == 0) {
    return {PDRStatus::Inconclusive, 0};
  }

  const auto seedClauses = buildSeedClauses(problem_);
  frames.emplace_back(FrameClauses{seedClauses});
  emitPdrTraceFrames("seeded_frames", frames);
  try {
  for (size_t level = 1; level <= maxFrames; ++level) {
    // Phase 1: exhaust the proof obligations created by bad states that still
    // survive in the current frontier.
    while (true) {
      const auto badCube =
          findBadCube(
              problem_,
              solverType_,
              initFormula,
              frameInvariant,
              frames,
              preciseBadStateSupport,
              preciseBadCubeStateLimit_,
              transitionByState.stateSymbols(),
              level,
              complementPartners,
              exactFrameClauses);
      if (!badCube.has_value()) {
        break;
      }
      emitPdrTrace(("bad_cube@F" + std::to_string(level)).c_str(),
                   formatCubeForPdrTrace(*badCube));
      size_t badFrame = level;
      if (!blockProofObligations(
              problem_,
              solverType_,
              transitionByState,
              initFormula,
              frameInvariant,
              frames,
              *badCube,
              level,
              badFrame,
              complementPartners,
              predecessorProjectionLimit_,
              exactFrameClauses,
              refineProjectedCounterexamples_,
              resetFrontierCache,
              maxBoundedRootGeneralizationAttempts_,
              learnValidatedBadFormulaClauses_,
              useExactResetFrontierChecks_,
              predecessorQueryBudget)) {
        emitPdrTraceFrames("frames_before_counterexample", frames);
        return {PDRStatus::Different, badFrame};
      }
      emitPdrTraceFrames("frames_after_blocking", frames);
    }

    // Phase 2: create the next frame, seed it with already-known startup
    // facts
    frames.emplace_back(FrameClauses{seedClauses});
    // and then try to push learned clauses forward.
    // We push in order to reach covergence and the condition is that that 
    // the clause is not preventing an actual bad path
    propagateClauses(
        problem_,
        solverType_,
        transitionByState,
        initFormula,
        frameInvariant,
        frames,
        level,
        complementPartners,
        predecessorProjectionLimit_,
        exactFrameClauses,
        predecessorQueryBudget);
    emitPdrTraceFrames(("frames_after_propagation@F" + std::to_string(level)).c_str(),
                       frames);

    // Phase 3: convergence means F[i] == F[i+1], so the frame has become an
    // inductive invariant and the SEC property is proved.
    for (size_t convergenceLevel = 1; convergenceLevel <= level; ++convergenceLevel) {
      if (framesConverged(frames[convergenceLevel], frames[convergenceLevel + 1])) {
        emitPdrTraceFrames(
            ("frames_converged@F" + std::to_string(convergenceLevel)).c_str(), frames);
        return {PDRStatus::Equivalent, convergenceLevel};
      }
    }
  }
  } catch (const PdrQueryBudgetExceeded&) {
    if (pdrStatsEnabled()) {
      emitSecDiag(
          "SEC PDR stats: predecessor query budget exhausted limit=",
          maxPredecessorQueries_);
    }
    return {PDRStatus::Inconclusive, maxFrames};
  }

  return {PDRStatus::Inconclusive, maxFrames};  // LCOV_EXCL_LINE
}

}  // namespace KEPLER_FORMAL::SEC
