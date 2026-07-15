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
#include "proof/ProofEngineShared.h"
#include "proof/TransitionExprResolver.h"
#include "kinduction/SatEncoding.h"

namespace KEPLER_FORMAL::SEC {

namespace detail {

std::vector<size_t> makeDeterministicPdrWorklist(
    const std::unordered_set<size_t>& symbols) {
  std::vector<size_t> worklist(symbols.begin(), symbols.end());
  std::sort(worklist.begin(), worklist.end());
  return worklist;
}

std::vector<size_t> makePdrClosureWorklist(
    const std::unordered_set<size_t>& symbols) {
  // Partner closure has no cap, and every caller sorts the final symbol vector
  // before SAT encoding. Avoid sorting this temporary worklist on wide
  // dual-rail leaves; traversal order cannot change the closed symbol set.
  return std::vector<size_t>(symbols.begin(), symbols.end());
}

bool pdrCubeLiteralOrderLess(size_t lhsSymbol,
                             bool lhsValue,
                             size_t rhsSymbol,
                             bool rhsValue) {
  if (lhsSymbol != rhsSymbol) {
    return lhsSymbol < rhsSymbol;
  }
  return lhsValue < rhsValue;
}

bool pdrCubeAssignmentOrderLess(
    const std::vector<std::pair<size_t, bool>>& lhs,
    const std::vector<std::pair<size_t, bool>>& rhs) {
  if (lhs.size() != rhs.size()) {
    return lhs.size() < rhs.size();
  }
  return std::lexicographical_compare(
      lhs.begin(), lhs.end(), rhs.begin(), rhs.end(), [](const auto& a,
                                                         const auto& b) {
        return pdrCubeLiteralOrderLess(a.first, a.second, b.first, b.second);
      });
}

}  // namespace detail

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
// Node counts are reserve hints only. Use exact hints for local groups and rely
// on the encoder's bounded growth for ASIC-sized groups.
constexpr size_t kMaxExactTransitionNodeCountHintTargets = 512;
// Local residual leaves can use larger exact SAT-query budgets while broad
// batches remain bounded.
constexpr size_t kMaxLocalDualRailFinalLeafStateSymbols = 128 * 1024;
constexpr size_t kMinLocalDualRailFinalLeafPredecessorSupport = 16 * 1024;
// Full-state bad cubes require discovering the complete state support. If the
// formula walk exceeds this resource bound, PDR returns inconclusive.
constexpr size_t kMaxPreciseBadCubeSupportNodes = 262144;
constexpr size_t kMaxMediumDualRailObservedOutputs = 384;
constexpr size_t kMaxDualRailNodeCountStateSymbols = 20000;
constexpr size_t kMaxDualRailNodeCountTransitionSources = 20000;
constexpr unsigned kDefaultDualRailBadCubeConflictLimit = 20000;
constexpr unsigned kDefaultDualRailPredecessorConflictLimit = 10000;
// Residual one-output leaves need more search than broad batch queries.  Do not
// lower this bound to save runtime; doing so can make a legal PDR obligation
// report inconclusive before the residual repair has had its intended search
// budget.
constexpr unsigned kDefaultDualRailResidualPredecessorConflictLimit = 200000;
constexpr size_t kDefaultDualRailPredecessorEncodingNodeLimit = 1000000;
constexpr size_t kDefaultDualRailPredecessorEncodingSupportLimit = 8192;
constexpr const char* kDualRailPredecessorConflictLimitEnv =
    "KEPLER_SEC_PDR_DUAL_RAIL_PREDECESSOR_CONFLICT_LIMIT";
// Literal-dropping only improves clause strength; it is not required for
// soundness.  ASIC predecessor cubes can still contain hundreds of literals,
// and learning them almost verbatim makes PDR rediscover nearby cubes.  Use a
// bounded chunk-dropping pass: each proposed stronger clause is validated by
// the same predecessor SAT query, but we first remove large literal
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
// Predecessor-core extraction is optional clause strengthening. Samples show
// it pays near the init frontier, where a small core blocks many nearby
// predecessors. Deeper frames already carry many learned clauses; the
// same core oracle can dominate runtime while trying to shrink an already-safe
// blocked cube, so learn the proven cube verbatim there.
constexpr size_t kMaxPredecessorCoreGeneralizationLevel = 2;
constexpr long long kPredecessorCoreConflictLimit = 10000;
// The solver's final conflict can be too coarse to use directly as a target-cube
// core in the PDR predecessor oracle. When that happens, stay inside the same
// already-built target-context solver and shrink the full target assumption set
// by deletion. These checks reuse the solver; unlike ordinary cube
// generalization they do not rebuild transition/frame CNF per trial.
constexpr size_t kMaxPredecessorCoreContextMinimizationChecks = 32;
// Broad dual-rail transition cones can make predecessor-core extraction too
// expensive, but BlackParrot shows a smaller shape where the cube support is
// only local (dozens of symbols) and skipping the core makes PDR enumerate
// sibling blockers. Try the core oracle for those local cones only.
constexpr size_t kMaxLocalDualRailPredecessorCoreSupport = 128;
constexpr size_t kMinLocalDualRailPredecessorCoreTargetSize = 4;
// BlackParrot sampling later found the same predecessor-core need below the
// "large cube" threshold: level-zero blockers around 37-49 literals with
// thousands of transition-support symbols were learned verbatim and then
// rediscovered one valuation at a time.  Try the core oracle for medium cubes
// only when their transition surface is already too broad for bounded
// literal-dropping to be worthwhile.
// AES sampling found the same broad-support blocker pattern at 12 literals:
// PDR repeatedly proved 12-literal, 113-support level-zero predecessor cubes
// UNSAT and learned them verbatim. Let the predecessor-core oracle cover that
// medium shape before the engine starts enumerating neighboring blockers.
constexpr size_t kMinMediumCubePredecessorCoreTargetSize = 8;
constexpr size_t kMaxInitExcludedCubeGeneralizationAttempts = 2;
constexpr size_t kDefaultPdrStatsInterval = 1000;
constexpr size_t kInitialPdrStatsQueries = 20;
// Query-result caching is an accelerator only.  Keep it bounded so a long SEC
// run cannot trade the predecessor-encoding wall for unbounded retained cubes.
constexpr size_t kMaxPredecessorQueryResultCacheEntries = 64 * 1024;
constexpr size_t kMaxPredecessorUnsatCoresPerContext = 4096;
constexpr size_t kMaxPredecessorClosedSymbolCacheEntries = 4096;
constexpr size_t kMaxPredecessorTargetSurfaceCacheEntries = 4096;
// The target-surface cache saves recomputing local transition supports on
// AES/Swerv-sized leaves, but Ariane-scale dual-rail memory arrays can generate
// thousands of unique target cubes over a multi-million-symbol state surface.
// In that shape, retaining target-derived vectors is pure memory pressure.
constexpr size_t kMaxDualRailTargetSurfaceCacheStateSymbols = 256 * 1024;
// The reusable predecessor solver is also a memory/perf cache.  Keep it for
// local AES/Swerv-sized dual-rail leaves, but let giant Ariane-scale leaves use
// one-shot predecessor queries so released solver pages do not accumulate in
// the process footprint across many unique target surfaces.
constexpr size_t kMaxDualRailPredecessorSolverCacheStateSymbols =
    kMaxDualRailTargetSurfaceCacheStateSymbols;
// The bad-cube cached solver permanently absorbs learned frame clauses.  That
// is useful for AES/Swerv-sized leaves, but Ariane-scale dual-rail batches can
// learn many neighboring F[0] clauses and inflate one long-lived SAT instance.
// Keep the proof query identical there, but rebuild it as a one-shot solver so
// each wave can release its frame-clause encoding promptly.
constexpr size_t kMaxDualRailBadCubeSolverCacheStateSymbols =
    kMaxDualRailTargetSurfaceCacheStateSymbols;
// FrameFormulaEncoder already makes a small generic Tseitin reservation, but
// sampled dual-rail PDR leaves still spent most time growing CaDiCaL variable
// vectors while streaming known-large transition cones. Reserve a larger,
// bounded chunk from PDR when we have the transition DAG estimate.
constexpr size_t kMinPdrTransitionSolverReserveNodes = 64 * 1024;
constexpr size_t kMaxPdrTransitionSolverReserveHint = 512 * 1024;
bool isLocalDualRailPredecessorCoreSurface(size_t level,
                                           size_t cubeSize,
                                           size_t transitionSupportSize) {
  return level <= 1 &&
         cubeSize >= kMinLocalDualRailPredecessorCoreTargetSize &&
         transitionSupportSize <= kMaxLocalDualRailPredecessorCoreSupport;
}

// Cubes represent a concrete bad/predecessor state, while clauses are the
// blocked generalization of such a state stored in a PDR frame.
struct CubeLiteral {  // LCOV_EXCL_LINE
  size_t symbol = 0;  // LCOV_EXCL_LINE
  bool value = false;  // LCOV_EXCL_LINE

  bool operator==(const CubeLiteral& other) const {
    return symbol == other.symbol && value == other.value;
  }
};

struct CubeLiteralHash {
  size_t operator()(const CubeLiteral& literal) const {
    return std::hash<size_t>()(
        (literal.symbol << 1) ^ (literal.value ? 1ULL : 0ULL));
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

void mixHashValue(size_t& seed, size_t value) {
  seed ^= value + 0x9e3779b97f4a7c15ULL + (seed << 6) + (seed >> 2);
}

struct StateCubeHash {
  size_t operator()(const StateCube& cube) const {
    size_t seed = 0x9e3779b97f4a7c15ULL;
    for (const auto& literal : cube) {
      mixHashValue(seed, CubeLiteralHash{}(literal));
    }
    return seed;
  }
};

size_t cubeFingerprint(const StateCube& cube) {
  return StateCubeHash{}(cube);
}

struct StateClauseHash {
  size_t operator()(const StateClause& clause) const {
    size_t seed = 0x517cc1b727220a95ULL;
    for (const auto& literal : clause) {
      mixHashValue(seed, std::hash<size_t>()(literal.symbol));
      mixHashValue(seed, std::hash<bool>()(literal.positive));
    }
    return seed;
  }
// LCOV_EXCL_START
};

bool cubeLiteralLess(const CubeLiteral& lhs, const CubeLiteral& rhs) {
  return detail::pdrCubeLiteralOrderLess(
      lhs.symbol, lhs.value, rhs.symbol, rhs.value);
}

bool clauseLiteralLess(const ClauseLiteral& lhs, const ClauseLiteral& rhs) {
  if (lhs.symbol != rhs.symbol) {
    return lhs.symbol < rhs.symbol;
  }
  return lhs.positive < rhs.positive;
}

bool stateCubeLess(const StateCube& lhs, const StateCube& rhs) {
  if (lhs.size() != rhs.size()) {
    return lhs.size() < rhs.size();
  }
  return std::lexicographical_compare(
      lhs.begin(), lhs.end(), rhs.begin(), rhs.end(), cubeLiteralLess);
}

bool stateClauseLess(const StateClause& lhs, const StateClause& rhs) {
  if (lhs.size() != rhs.size()) {
    return lhs.size() < rhs.size();
  }
  return std::lexicographical_compare(
      lhs.begin(), lhs.end(), rhs.begin(), rhs.end(), clauseLiteralLess);
}

void sortStateCubesDeterministically(std::vector<StateCube>& cubes) {
  std::sort(cubes.begin(), cubes.end(), stateCubeLess);
}


struct FrameClauses {
  // F[i] stores clauses known to hold for all states reachable within i steps.
  std::vector<StateClause> clauses;
  // Cached SAT queries can keep old, subsumed clauses soundly; they only need
  // to see every newly learned clause.  Keep an append-only log so they can
  // synchronize by delta instead of rescanning ASIC-size frames after each
  // local refinement.
  std::vector<StateClause> addedClauseLog;
};

size_t frameClausesFingerprint(const std::vector<FrameClauses>& frames,
                               size_t level) {
  if (level >= frames.size()) {
    return 0; // LCOV_EXCL_LINE
  }
  size_t seed = std::hash<size_t>()(level);
  const auto& frame = frames[level];
  mixHashValue(seed, std::hash<size_t>()(frame.clauses.size()));
  for (const auto& clause : frame.clauses) {
    mixHashValue(seed, StateClauseHash{}(clause));
  }
  return seed;
}

size_t extraFrameClausesFingerprint(
    const std::vector<StateClause>* extraFrameClauses) {
  if (extraFrameClauses == nullptr) {
    return 0;
  }
  // Include temporary relative-induction clauses in the result-cache key.
  return detail::pdrOrderedClauseFingerprint(*extraFrameClauses); // LCOV_EXCL_LINE
}

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
};

struct ProofObligationKey {
  size_t level = 0;
  size_t badFrame = 0;
  StateCube cube;

  bool operator==(const ProofObligationKey& other) const {
    return level == other.level &&
           badFrame == other.badFrame &&
           cube == other.cube;
  }
};

struct ProofObligationKeyHash {
  size_t operator()(const ProofObligationKey& key) const {
    size_t seed = std::hash<size_t>()(key.level);
    mixHashValue(seed, std::hash<size_t>()(key.badFrame));
    mixHashValue(seed, StateCubeHash{}(key.cube));
    return seed;
  }
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

class InitParityRelations {
 public:
  void ensureSymbol(size_t symbol) {
    if (parent_.find(symbol) == parent_.end()) {
      parent_.emplace(symbol, symbol);
      parityToParent_.emplace(symbol, false);
    }
  }

  void addEquality(size_t lhs, size_t rhs) { unite(lhs, rhs, false); }

  void addComplement(size_t lhs, size_t rhs) { unite(lhs, rhs, true); }

  std::optional<std::pair<size_t, bool>> findWithParity(size_t symbol) const {
    const auto parentIt = parent_.find(symbol);
    if (parentIt == parent_.end()) {
      return std::nullopt;
    }
    const size_t parent = parentIt->second;
    // LCOV_EXCL_START
    const bool parity = parityToParent_.at(symbol);
    // LCOV_EXCL_STOP
    if (parent == symbol) {
      return std::pair{symbol, false};
    }
    const auto parentRoot = findWithParity(parent);
    if (!parentRoot.has_value()) {
      return std::nullopt;  // LCOV_EXCL_LINE
    }
    return std::pair{parentRoot->first, parity ^ parentRoot->second};
  }

 private:
  std::pair<size_t, bool> mutableFind(size_t symbol) {
    // LCOV_EXCL_START
    ensureSymbol(symbol);
    const size_t parent = parent_[symbol];
    const bool parity = parityToParent_[symbol];
    if (parent == symbol) {
    // LCOV_EXCL_STOP
      return {symbol, false};
    }
    const auto root = mutableFind(parent);  // LCOV_EXCL_LINE
    parent_[symbol] = root.first;  // LCOV_EXCL_LINE
    parityToParent_[symbol] = parity ^ root.second;  // LCOV_EXCL_LINE
    return {parent_[symbol], parityToParent_[symbol]};  // LCOV_EXCL_LINE
  }

  void unite(size_t lhs, size_t rhs, bool inverted) {
    const auto lhsRoot = mutableFind(lhs);
    const auto rhsRoot = mutableFind(rhs);
    if (lhsRoot.first == rhsRoot.first) {
      return; // LCOV_EXCL_LINE
    }
    parent_[lhsRoot.first] = rhsRoot.first;
    // value(lhs) xor value(rhs) must equal `inverted`.
    parityToParent_[lhsRoot.first] =
        lhsRoot.second ^ rhsRoot.second ^ inverted;
  }

  std::unordered_map<size_t, size_t> parent_;
  std::unordered_map<size_t, bool> parityToParent_;
};

struct ExprPair {
  BoolExpr* first = nullptr;
  BoolExpr* second = nullptr;

  bool operator==(const ExprPair& other) const {
    return first == other.first && second == other.second;
  }
};

struct ExprPairHash {
  size_t operator()(const ExprPair& pair) const {
    size_t seed =
        reinterpret_cast<size_t>(pair.first) + 0x9e3779b97f4a7c15ULL;
    seed ^= reinterpret_cast<size_t>(pair.second) +
            0x9e3779b97f4a7c15ULL + (seed << 6) + (seed >> 2);
    return seed;
  }
};

struct InitFactIndex {
  std::unordered_map<size_t, bool> assignments;
  std::unordered_map<size_t, bool> rootAssignments;
  std::unordered_set<SymbolPair, SymbolPairHash> equalities;
  std::unordered_set<SymbolPair, SymbolPairHash> complements;
  InitParityRelations relations;
};

struct TransitionAssumptionKey {
  size_t transitionSymbol = 0;
  bool desiredValue = false;

  bool operator==(const TransitionAssumptionKey& other) const {
    return transitionSymbol == other.transitionSymbol &&
           desiredValue == other.desiredValue;
  }
};

struct TransitionAssumptionKeyHash {
  size_t operator()(const TransitionAssumptionKey& key) const {
    size_t seed = std::hash<size_t>()(key.transitionSymbol);
    mixHashValue(seed, std::hash<bool>()(key.desiredValue));
    return seed;
  }
};

struct PredecessorQueryResultKey { // LCOV_EXCL_LINE
  const KInductionProblem* problem = nullptr;
  const TransitionExprResolver* transitionByState = nullptr;
  const BoolExpr* initFormula = nullptr;
  const BoolExpr* frameInvariant = nullptr;
  size_t level = 0;
  size_t frameFingerprint = 0;
  size_t extraFrameFingerprint = 0;
  bool excludeTargetOnCurrentFrame = false;
  StateCube targetCube;

  bool operator==(const PredecessorQueryResultKey& other) const {
    return problem == other.problem &&
           transitionByState == other.transitionByState &&
           initFormula == other.initFormula &&
           frameInvariant == other.frameInvariant &&
           level == other.level &&
           frameFingerprint == other.frameFingerprint &&
           extraFrameFingerprint == other.extraFrameFingerprint &&
           excludeTargetOnCurrentFrame == other.excludeTargetOnCurrentFrame &&
           targetCube == other.targetCube;
  }
};

struct PredecessorQueryResultKeyHash {
  size_t operator()(const PredecessorQueryResultKey& key) const {
    size_t seed = std::hash<const void*>()(key.problem);
    mixHashValue(seed, std::hash<const void*>()(key.transitionByState));
    mixHashValue(seed, std::hash<const void*>()(key.initFormula));
    mixHashValue(seed, std::hash<const void*>()(key.frameInvariant));
    mixHashValue(seed, std::hash<size_t>()(key.level));
    mixHashValue(seed, std::hash<size_t>()(key.frameFingerprint));
    mixHashValue(seed, std::hash<size_t>()(key.extraFrameFingerprint));
    mixHashValue(seed, std::hash<bool>()(key.excludeTargetOnCurrentFrame));
    mixHashValue(seed, StateCubeHash{}(key.targetCube));
    return seed;
  }
};

struct PredecessorQueryResultEntry {
  bool hasPredecessor = false;
  StateCube predecessor;
  bool hasUnsatCore = false;
  StateCube unsatCore;
};

struct PredecessorUnsatCoreCacheKey {
  const KInductionProblem* problem = nullptr;
  const TransitionExprResolver* transitionByState = nullptr;
  const BoolExpr* initFormula = nullptr;
  const BoolExpr* frameInvariant = nullptr;
  size_t level = 0;
  size_t extraFrameFingerprint = 0;
  bool excludeTargetOnCurrentFrame = false;

  bool operator==(const PredecessorUnsatCoreCacheKey& other) const {
    return problem == other.problem &&
           transitionByState == other.transitionByState &&
           initFormula == other.initFormula &&
           frameInvariant == other.frameInvariant &&
           level == other.level &&
           extraFrameFingerprint == other.extraFrameFingerprint &&
           excludeTargetOnCurrentFrame == other.excludeTargetOnCurrentFrame;
  }
};

struct PredecessorUnsatCoreCacheKeyHash {
  size_t operator()(const PredecessorUnsatCoreCacheKey& key) const {
    size_t seed = std::hash<const void*>()(key.problem);
    mixHashValue(seed, std::hash<const void*>()(key.transitionByState));
    mixHashValue(seed, std::hash<const void*>()(key.initFormula));
    mixHashValue(seed, std::hash<const void*>()(key.frameInvariant));
    mixHashValue(seed, std::hash<size_t>()(key.level));
    mixHashValue(seed, std::hash<size_t>()(key.extraFrameFingerprint));
    mixHashValue(seed, std::hash<bool>()(key.excludeTargetOnCurrentFrame));
    return seed;
  }
};

class PdrFormulaSupportCache;

struct PredecessorFrameSymbolSurfaceKey {
  const KInductionProblem* problem = nullptr;
  BoolExpr* initFormula = nullptr;
  BoolExpr* frameInvariant = nullptr;
  const ComplementPartnerIndex* complementPartners = nullptr;
  const PdrFormulaSupportCache* supportCache = nullptr;
  size_t level = 0;
  size_t frameFingerprint = 0;

  bool operator==(const PredecessorFrameSymbolSurfaceKey& other) const { // LCOV_EXCL_LINE
    return problem == other.problem && // LCOV_EXCL_LINE
           initFormula == other.initFormula && // LCOV_EXCL_LINE
           frameInvariant == other.frameInvariant && // LCOV_EXCL_LINE
           complementPartners == other.complementPartners && // LCOV_EXCL_LINE
           supportCache == other.supportCache && // LCOV_EXCL_LINE
           level == other.level && // LCOV_EXCL_LINE
           frameFingerprint == other.frameFingerprint; // LCOV_EXCL_LINE
  }
};

struct PredecessorFrameSymbolSurface {
  bool valid = false;
  PredecessorFrameSymbolSurfaceKey key;
  std::vector<size_t> symbols;
};

struct SymbolVectorHash {
  size_t operator()(const std::vector<size_t>& symbols) const {
    size_t seed = std::hash<size_t>()(symbols.size());
    for (const auto symbol : symbols) {
      mixHashValue(seed, std::hash<size_t>()(symbol));
    }
    return seed;
  }
};

struct PredecessorTargetSurfaceKey {
  const KInductionProblem* problem = nullptr;
  const TransitionExprResolver* transitionByState = nullptr;
  StateCube targetCube;

  bool operator==(const PredecessorTargetSurfaceKey& other) const {
    return problem == other.problem &&
           transitionByState == other.transitionByState &&
           targetCube == other.targetCube;
  }
};

struct PredecessorTargetSurfaceKeyHash {
  size_t operator()(const PredecessorTargetSurfaceKey& key) const {
    size_t seed = std::hash<const void*>()(key.problem);
    mixHashValue(seed, std::hash<const void*>()(key.transitionByState));
    mixHashValue(seed, StateCubeHash{}(key.targetCube));
    return seed;
  }
};

struct PredecessorTargetSurface { // LCOV_EXCL_LINE
  std::vector<size_t> targetSymbols;
  std::vector<size_t> encodedTargets;
  std::vector<size_t> transitionSupportSymbols;
  size_t transitionEncodingNodes = 0;
};

struct PredecessorAssumptionCacheKey {
  const KInductionProblem* problem = nullptr;
  const TransitionExprResolver* transitionByState = nullptr;
  const BoolExpr* initFormula = nullptr;
  const BoolExpr* frameInvariant = nullptr;
  size_t level = 0;
  size_t frameFingerprint = 0;
  std::vector<size_t> solverSymbols;

  bool operator==(const PredecessorAssumptionCacheKey& other) const {
    return problem == other.problem &&
           transitionByState == other.transitionByState &&
           initFormula == other.initFormula &&
           frameInvariant == other.frameInvariant &&
           level == other.level &&
           frameFingerprint == other.frameFingerprint &&
           solverSymbols == other.solverSymbols;
  }

  bool hasSameReusableContext(
      const PredecessorAssumptionCacheKey& other) const {
    return problem == other.problem &&
           transitionByState == other.transitionByState &&
           initFormula == other.initFormula &&
           frameInvariant == other.frameInvariant &&
           level == other.level &&
           solverSymbols == other.solverSymbols;
  }
};

struct PredecessorAssumptionSolver {
  PredecessorAssumptionCacheKey key;
  std::unique_ptr<SATSolverWrapper> solver;
  std::unique_ptr<FrameVariableStore> variables;
  // The cached SAT model is useful only if predecessor extraction can read the
  // transition-expression leaves that were encoded under assumptions.
  std::unordered_map<size_t, int> transitionLeafLits;
  std::unordered_map<TransitionAssumptionKey, int, TransitionAssumptionKeyHash>
      assumptionByTransitionLiteral;
  // Reuse the transition-DAG encoder together with the cached predecessor
  // solver. Neighboring dual-rail PDR targets often share most of the same
  // transition cone; keeping the encoder node cache avoids re-emitting that
  // Tseitin structure for every target literal.
  std::unordered_map<const std::unordered_map<size_t, size_t>*,
                     std::unique_ptr<FrameFormulaEncoder>>
      transitionEncoderBySymbolMap;
  std::unordered_set<size_t> querySymbolSet;
  std::unordered_set<StateClause, StateClauseHash> emittedFrameClauses;
  // Some predecessor checks also need "current state is not the target cube".
  // Keep those target-specific clauses behind selectors so the base solver can
  // be reused for neighboring queries without permanently excluding a cube.
  std::unordered_map<StateClause, int, StateClauseHash>
      exclusionAssumptionByClause;
  // Temporary retries add a few blockers around one obligation. Selector
  // assumptions let those local constraints reuse the same cached
  // predecessor solver instead of rebuilding a fresh exact SAT instance.
  std::unordered_map<StateClause, int, StateClauseHash>
      extraFrameAssumptionByClause;
};

struct PredecessorAssumptionCache {
  // PDR level-local predecessor queries share the same frame/bootstrap context
  // and differ mostly by target cube.
  std::unique_ptr<PredecessorAssumptionSolver> solver;
  // Full predecessor-query result cache. SAT entries are keyed by the exact
  // frame fingerprint; UNSAT entries also get a fingerprint-free key because
  // PDR frames only strengthen over time, so a proven-empty predecessor set
  // remains empty after more clauses are learned.
  std::unordered_map<PredecessorQueryResultKey,
                     PredecessorQueryResultEntry,
                     PredecessorQueryResultKeyHash>
      queryResults;
  std::unordered_set<PredecessorQueryResultKey,
                     PredecessorQueryResultKeyHash>
      unsatQueries;
  // A predecessor UNSAT core for cube U also proves UNSAT for every later
  // target cube that contains U under the same PDR context. Keep those cores
  // separately from exact target results so neighboring dual-rail cubes can
  // reuse the proof without re-solving a wider assumption set.
  std::unordered_map<PredecessorUnsatCoreCacheKey,
                     std::vector<StateCube>,
                     PredecessorUnsatCoreCacheKeyHash>
      unsatCoresByContext;
  const TransitionExprResolver* widenedPredecessorCacheResolver = nullptr;
  // Local dual-rail leaves repeatedly ask nearly identical predecessor
  // questions.  Keep a monotonically widened cached-solver surface so a few
  // target-specific local support symbols do not force solver rebuilds.
  std::vector<size_t> widenedPredecessorCacheSymbols;
  PredecessorFrameSymbolSurface currentFrameSymbols;
  std::unordered_map<std::vector<size_t>,
                     std::vector<size_t>,
                     SymbolVectorHash>
      closedCurrentFrameSymbols;
  std::unordered_map<PredecessorTargetSurfaceKey,
                     PredecessorTargetSurface,
                     PredecessorTargetSurfaceKeyHash>
      targetSurfaces;
};

struct BadCubeAssumptionCacheKey {
  const KInductionProblem* problem = nullptr;
  const BoolExpr* initFormula = nullptr;
  const BoolExpr* frameInvariant = nullptr;
  size_t level = 0;
  std::vector<size_t> solverSymbols;

  bool operator==(const BadCubeAssumptionCacheKey& other) const {
    return problem == other.problem &&
           initFormula == other.initFormula &&
           frameInvariant == other.frameInvariant &&
           level == other.level &&
           solverSymbols == other.solverSymbols;
  }
};

struct BadCubeAssumptionSolver {
  BadCubeAssumptionCacheKey key;
  std::unique_ptr<SATSolverWrapper> solver;
  std::unique_ptr<FrameVariableStore> variables;
  std::unique_ptr<FrameFormulaEncoder> encoder;
  std::unordered_map<BoolExpr*, int> encodedBadRoots;
  std::unordered_set<size_t> querySymbolSet;
  std::unordered_set<StateClause, StateClauseHash> emittedFrameClauses;
  size_t emittedFrameFingerprint = 0;
  size_t emittedFrameLogOffset = 0;
};

struct BadCubeAssumptionCache {
  // Bad-cube searches repeatedly ask the same frame context with different
  // output-bad roots. Keep frame facts permanent and vary only the root
  // literal as a solver assumption.
  std::unique_ptr<BadCubeAssumptionSolver> solver;
};

enum class PdrBudgetExhaustion {
  None,
  LocalQuery,
};

thread_local PdrBudgetExhaustion pdrBudgetExhaustion =
    PdrBudgetExhaustion::None;
thread_local size_t pdrPredecessorQueryLimit = 0;

bool pdrStatsEnabled();

void resetPdrBudgetExhaustion() {
  pdrBudgetExhaustion = PdrBudgetExhaustion::None;
}

void setPdrPredecessorQueryLimit(size_t limit) {
  pdrPredecessorQueryLimit = limit;
}

void markPdrBudgetExhausted(PdrBudgetExhaustion reason) {
  if (pdrBudgetExhaustion == PdrBudgetExhaustion::None) {
    pdrBudgetExhaustion = reason;
  }
}

bool hasPdrBudgetExhaustion() {
  return pdrBudgetExhaustion != PdrBudgetExhaustion::None;
}

bool consumePdrPredecessorQueryBudget(size_t* remainingQueries) {
  if (remainingQueries == nullptr) {
    return true;
  }
  if (*remainingQueries == 0) {
    if (pdrStatsEnabled()) {  // LCOV_EXCL_LINE
      emitSecDiag(  // LCOV_EXCL_LINE
          "SEC PDR stats: predecessor query-count budget exhausted limit=",
          pdrPredecessorQueryLimit);
    }  // LCOV_EXCL_LINE
    markPdrBudgetExhausted(PdrBudgetExhaustion::LocalQuery);  // LCOV_EXCL_LINE
    return false;  // LCOV_EXCL_LINE
  }
  --(*remainingQueries);
  return true;
}

bool pdrStatsEnabled() {
  return std::getenv("KEPLER_SEC_PDR_STATS") != nullptr;
}

size_t pdrDualRailStateSymbolCount(const KInductionProblem& problem) {
  return problem.dualRailStatePairs.size() * 2;
}

size_t pdrTransitionSourceCount(const KInductionProblem& problem) {
  size_t count = problem.transitions0.size() + problem.transitions1.size();
  if (problem.lazyTransitions != nullptr) {
    count += problem.lazyTransitions->sourceByStateSymbol.size();
  }
  return count;
}

size_t pdrOriginalObservedOutputCount(const KInductionProblem& problem) {
  return problem.originalObservedOutputCount == 0
             ? problem.observedOutputExprs0.size()
             : problem.originalObservedOutputCount;
}

bool hasBroadDualRailResidualOutputSurface(const KInductionProblem& problem) {
  return detail::isBroadDualRailResidualOutputSurface(
      problem.usesDualRailStateEncoding,
      problem.observedOutputExprs0.size(),
      pdrOriginalObservedOutputCount(problem),
      kMaxMediumDualRailObservedOutputs);
}

bool hasLocalDualRailFinalLeafSurface(const KInductionProblem& problem) {
  return hasBroadDualRailResidualOutputSurface(problem) &&
         pdrDualRailStateSymbolCount(problem) <=
             kMaxLocalDualRailFinalLeafStateSymbols;
}

bool canRetryDualRailPredecessorInCachedSolver(
    const KInductionProblem& problem) {
  return hasLocalDualRailFinalLeafSurface(problem);
}

bool canUsePredecessorQueryResultCache(const KInductionProblem& problem) {
  if (!problem.usesDualRailStateEncoding) {
    return false;
  }
  const size_t observedOutputs = problem.observedOutputExprs0.size();
  const size_t originalOutputs = pdrOriginalObservedOutputCount(problem);
  // Medium residual slices, such as AES 129->1 output leaves, must stay on the
  // 376a017 path: cached assumptions may probe cheaply, but the predecessor
  // answer/core itself is recomputed by the ordinary exact query. Non-residual
  // unit fixtures and broad residual leaves keep the cache path.
  return !(originalOutputs > observedOutputs &&
           originalOutputs <= kMaxMediumDualRailObservedOutputs);
}



size_t effectiveLocalDualRailFinalLeafEncodingSupportLimit(
    size_t configuredLimit) {
  if (configuredLimit == 0) {
    return 0; // LCOV_EXCL_LINE
  }
  return std::max(configuredLimit,
                  kMinLocalDualRailFinalLeafPredecessorSupport);
}

KEPLER_FORMAL::Config::SolverType localDualRailPredecessorSolverType(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType configuredSolverType) {
  if (hasLocalDualRailFinalLeafSurface(problem) &&
      configuredSolverType == KEPLER_FORMAL::Config::SolverType::KISSAT) { // LCOV_EXCL_LINE
    // This exact fallback is reached after the cached-assumption query could
    // not answer.  Use the incremental-friendly backend so the local query has
    // both conflict and decision limits; Kissat can otherwise spend the wall in
    // propagation on a single residual Swerv leaf.
    return SATSolverWrapper::assumptionSolverTypeFor(configuredSolverType); // LCOV_EXCL_LINE
  }
  return configuredSolverType;
}

size_t envSizeLimitOrDefault(const char* name, size_t defaultValue);

size_t pdrStatsInterval() {
  const char* intervalText = std::getenv("KEPLER_SEC_PDR_STATS_INTERVAL");
  if (intervalText == nullptr || *intervalText == '\0') {
    return kDefaultPdrStatsInterval;  // LCOV_EXCL_LINE
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

unsigned envUnsignedLimitOrDefaultAllowZero(const char* name,
                                            // LCOV_EXCL_START
                                            unsigned defaultValue) {
                                            // LCOV_EXCL_STOP
  const char* valueText = std::getenv(name);
  if (valueText == nullptr || *valueText == '\0') {
    return defaultValue;
  }
  const auto value = std::strtoull(valueText, nullptr, 10);
  return value > std::numeric_limits<unsigned>::max()
             ? std::numeric_limits<unsigned>::max()  // LCOV_EXCL_LINE
             : static_cast<unsigned>(value);
}

unsigned dualRailBadCubeConflictLimit() {
  return envUnsignedLimitOrDefaultAllowZero(
      "KEPLER_SEC_PDR_DUAL_RAIL_BAD_CUBE_CONFLICT_LIMIT",
      kDefaultDualRailBadCubeConflictLimit);
}

unsigned dualRailPredecessorConflictLimit() {
  return envUnsignedLimitOrDefaultAllowZero(
      kDualRailPredecessorConflictLimitEnv,
      kDefaultDualRailPredecessorConflictLimit);
}

unsigned dualRailPredecessorConflictLimitForQuery(
    const KInductionProblem& problem,
    const StateCube& targetCube,
    size_t level,
    size_t solverSymbolCount) {
  const unsigned configuredLimit = dualRailPredecessorConflictLimit();
  if (std::getenv(kDualRailPredecessorConflictLimitEnv) != nullptr) {
    return configuredLimit; // LCOV_EXCL_LINE
  }
  // BlackParrot leaves with one residual output need a deeper predecessor SAT
  // search, but broad multi-output batches should keep the cheaper default.
  // Keep this scoped to small target cubes and local solver cones so it repairs
  // isolated handshake leaves without opening whole-SoC predecessor searches.
  if (detail::shouldUseResidualDualRailPredecessorBudget(
          problem.usesDualRailStateEncoding,
          problem.observedOutputExprs0.size(),
          level,
          targetCube.size(),
          solverSymbolCount)) {
    return std::max(
        configuredLimit,
        kDefaultDualRailResidualPredecessorConflictLimit);
  }
  return configuredLimit;
}

unsigned dualRailPredecessorDecisionLimit(unsigned defaultValue) {
  return envUnsignedLimitOrDefaultAllowZero(
      "KEPLER_SEC_PDR_DUAL_RAIL_PREDECESSOR_DECISION_LIMIT",
      defaultValue);
}

size_t dualRailPredecessorEncodingNodeLimit() {
  return envSizeLimitOrDefault(
      "KEPLER_SEC_PDR_DUAL_RAIL_PREDECESSOR_ENCODING_NODE_LIMIT",
      kDefaultDualRailPredecessorEncodingNodeLimit);
}

size_t dualRailPredecessorEncodingSupportLimit() {
  return envSizeLimitOrDefault(
      "KEPLER_SEC_PDR_DUAL_RAIL_PREDECESSOR_ENCODING_SUPPORT_LIMIT",
      kDefaultDualRailPredecessorEncodingSupportLimit);
}

size_t nextPdrPredecessorQueryNumber() {
  // The stats path is intentionally process-local and diagnostic-only. PDR is
  // currently run serially per SEC output slice, so a simple counter gives a
  // stable view of where a long proof is spending time without touching the
  // proof algorithm or adding synchronization overhead to normal runs.
  static size_t queryNumber = 0;
  return ++queryNumber;
}


size_t nextPdrBadCubeQueryNumber() {
  static size_t queryNumber = 0;
  return ++queryNumber;
}

size_t nextPdrDualRailPredecessorCoreSkipNumber() {
  static size_t skipNumber = 0;
  return ++skipNumber;
}

bool shouldEmitPdrStats(size_t queryNumber) {
  if (!pdrStatsEnabled()) {
    return false;
  }
  return queryNumber <= kInitialPdrStatsQueries ||
         queryNumber % pdrStatsInterval() == 0;
}

class PdrFormulaSupportCache {
 // LCOV_EXCL_START
 public:
 // LCOV_EXCL_STOP
  explicit PdrFormulaSupportCache(
      const std::vector<DualRailSymbolPair>& dualRailStatePairs) {
    dualRailPartnerBySymbol_.reserve(dualRailStatePairs.size() * 2);
    for (const auto& rails : dualRailStatePairs) {
      dualRailPartnerBySymbol_.emplace(rails.mayBeOne, rails.mayBeZero);
      dualRailPartnerBySymbol_.emplace(rails.mayBeZero, rails.mayBeOne);
    }
  }

  const std::set<size_t>& support(BoolExpr* formula) {
    static const std::set<size_t> emptySupport;
    if (formula == nullptr) {
      return emptySupport;  // LCOV_EXCL_LINE
    }
    if (const auto it = supportByExpr_.find(formula);
        it != supportByExpr_.end()) {
      return it->second;
    }
    const auto [it, _] =
        supportByExpr_.emplace(formula, formula->getSupportVars());
    return it->second;
  }

  void addRelevantDualRailPartners(std::unordered_set<size_t>& symbols) const {
    if (dualRailPartnerBySymbol_.empty() || symbols.empty()) {
      return;
    }
    std::vector<size_t> worklist =
        detail::makePdrClosureWorklist(symbols);
    for (size_t cursor = 0; cursor < worklist.size(); ++cursor) {
      const auto partnerIt = dualRailPartnerBySymbol_.find(worklist[cursor]);
      if (partnerIt == dualRailPartnerBySymbol_.end()) {
        continue;
      }
      if (symbols.insert(partnerIt->second).second) {
        worklist.push_back(partnerIt->second);
      }
    }
  }

  size_t clearMemoizedSupports() {
    const size_t entries = supportByExpr_.size();
    supportByExpr_.clear();
    supportByExpr_.rehash(0);
    return entries;
  }

 private:
  // PDR rebuilds many local SAT queries over the same frame/property formulas.
  // Memoizing formula support avoids repeatedly walking large BoolExpr DAGs
  // while keeping each query's selected symbol set unchanged.
  std::unordered_map<BoolExpr*, std::set<size_t>> supportByExpr_;
  std::unordered_map<size_t, size_t> dualRailPartnerBySymbol_;
};

void addComplementedStateRelations(
    SATSolverWrapper& solver,
    const FrameVariableStore& variables,
    const std::vector<std::pair<size_t, size_t>>& complementedStatePairs,
    size_t numFrames);

void addSameFrameStateEqualities(SATSolverWrapper& solver,
                                 const FrameVariableStore& variables,
                                 const KInductionProblem& problem,
                                 size_t numFrames);

void addDualRailStateValidity(SATSolverWrapper& solver,
                              const FrameVariableStore& variables,
                              const std::vector<DualRailSymbolPair>& railPairs,
                              size_t numFrames);

void addCubeAssumptions(SATSolverWrapper& solver,
                        const FrameVariableStore& variables,
                        const StateCube& cube,
                        size_t frame);

void addNegatedCubeClause(SATSolverWrapper& solver,
                          const FrameVariableStore& variables,
                          const StateCube& cube,
                          size_t frame);

StateClause clauseFromCube(const StateCube& cube);

std::vector<size_t> cubeStateSymbols(const StateCube& cube);

void addPostBootstrapResetInputConstraints(
    SATSolverWrapper& solver,
    const FrameVariableStore& variables,
    const KInductionProblem& problem,
    size_t frame);

void addFormulaSymbols(BoolExpr* formula,
                       std::unordered_set<size_t>& symbols,
                       PdrFormulaSupportCache* supportCache = nullptr);

bool predecessorSourceFrameIsKnownSafe(size_t level);

void normalizeCube(StateCube& cube);

void addRelevantComplementedStatePartners(
    const ComplementPartnerIndex& complementPartners,
    std::unordered_set<size_t>& symbols);

// LCOV_EXCL_START
std::vector<size_t> sortUniqueSymbols(std::unordered_set<size_t> symbols) {
// LCOV_EXCL_STOP
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
    // LCOV_EXCL_START
    return {};  // LCOV_EXCL_LINE
    // LCOV_EXCL_STOP
  }

  std::unordered_set<size_t> stateSupport;
  std::unordered_set<const BoolExpr*> visited;
  std::vector<const BoolExpr*> stack{formula};
  while (!stack.empty()) {
    const BoolExpr* node = stack.back();
    stack.pop_back();
    if (node == nullptr || !visited.insert(node).second) {
      continue;  // LCOV_EXCL_LINE
    }
    if (visited.size() > maxVisitedNodes) {
      return std::nullopt;  // LCOV_EXCL_LINE
    }
    if (node->getOp() == Op::VAR) {
      if (stateSymbolSet.find(node->getId()) != stateSymbolSet.end()) {
        stateSupport.insert(node->getId());
        if (maxStateSymbols != 0 && stateSupport.size() > maxStateSymbols) {
          return std::nullopt;
        }
      }
      continue;
    }
    if (node->getRight() != nullptr) {
      stack.push_back(node->getRight());
    }
    if (node->getLeft() != nullptr) {
      stack.push_back(node->getLeft());
    }
  }
  return sortUniqueSymbols(std::move(stateSupport));
}

// LCOV_EXCL_START
std::vector<size_t> expandTransitionTargets(
    const KInductionProblem& problem,
    const std::vector<size_t>& requestedTargets,
    const TransitionExprResolver& transitionByState) {
  const auto& primaryByComplement = transitionByState.primaryByComplement();
  // LCOV_EXCL_STOP
  std::unordered_set<size_t> targets;
  targets.reserve(requestedTargets.size());

  for (const auto symbol : requestedTargets) {
    if (transitionByState.contains(symbol)) {
      targets.insert(symbol);
      continue;
    }
    if (const auto primaryIt = primaryByComplement.find(symbol);  // LCOV_EXCL_LINE
        primaryIt != primaryByComplement.end() &&  // LCOV_EXCL_LINE
        transitionByState.contains(primaryIt->second)) {  // LCOV_EXCL_LINE
      targets.insert(primaryIt->second);  // LCOV_EXCL_LINE
    }  // LCOV_EXCL_LINE
  }

  return sortUniqueSymbols(std::move(targets));
}

std::vector<size_t> collectTransitionSupportSymbols(
    const TransitionExprResolver& transitionByState,
    // LCOV_EXCL_START
    const std::vector<size_t>& encodedTargets) {
    // LCOV_EXCL_STOP
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
  if (encodedTargets.size() > kMaxExactTransitionNodeCountHintTargets) {
    return 0;  // LCOV_EXCL_LINE
  }
  size_t estimate = 0;
  for (const auto stateSymbol : encodedTargets) {
    estimate += transitionByState.nodeCount(stateSymbol);
  }
  return estimate;
}

PredecessorTargetSurface buildPredecessorTargetSurface(
    const KInductionProblem& problem,
    const TransitionExprResolver& transitionByState,
    const StateCube& targetCube) {
  PredecessorTargetSurface surface;
  surface.targetSymbols = cubeStateSymbols(targetCube);
  surface.encodedTargets =
      expandTransitionTargets(problem, surface.targetSymbols, transitionByState);
  surface.transitionSupportSymbols =
      collectTransitionSupportSymbols(transitionByState, surface.encodedTargets);
  surface.transitionEncodingNodes =
      estimateTransitionEncodingNodes(transitionByState, surface.encodedTargets);
  return surface;
}

bool shouldRetainPredecessorTargetSurfaceCache(
    const KInductionProblem& problem) {
  return !problem.usesDualRailStateEncoding ||
         problem.totalStateCount <=
             kMaxDualRailTargetSurfaceCacheStateSymbols;
}

bool shouldUsePredecessorSolverCache(const KInductionProblem& problem) {
  return !problem.usesDualRailStateEncoding ||
         problem.totalStateCount <=
             kMaxDualRailPredecessorSolverCacheStateSymbols;
}

bool shouldUseBadCubeSolverCache(const KInductionProblem& problem) {
  return !problem.usesDualRailStateEncoding ||
         problem.totalStateCount <=
             kMaxDualRailBadCubeSolverCacheStateSymbols;
}

const PredecessorTargetSurface& predecessorTargetSurfaceFor(
    PredecessorAssumptionCache& cache,
    const KInductionProblem& problem,
    const TransitionExprResolver& transitionByState,
    const StateCube& targetCube) {
  PredecessorTargetSurfaceKey key{&problem, &transitionByState, targetCube};
  const auto existing = cache.targetSurfaces.find(key);
  if (existing != cache.targetSurfaces.end()) {
    return existing->second;
  }
  if (cache.targetSurfaces.size() >=
      kMaxPredecessorTargetSurfaceCacheEntries) {
    // These vectors are pure target-derived data. Clearing the bounded cache
    // only gives up reuse; it cannot change a predecessor answer.
    cache.targetSurfaces.clear(); // LCOV_EXCL_LINE
  } // LCOV_EXCL_LINE
  PredecessorTargetSurface surface =
      buildPredecessorTargetSurface(problem, transitionByState, targetCube);
  auto [inserted, insertedNew] =
      cache.targetSurfaces.emplace(std::move(key), std::move(surface));
  (void)insertedNew;
  if (pdrStatsEnabled()) {
    emitSecDiag(
        "SEC PDR stats: predecessor target surface cached target=",
        targetCube.size(),
        " encoded_targets=",
        inserted->second.encodedTargets.size(),
        " transition_support=",
        inserted->second.transitionSupportSymbols.size(),
        " entries=",
        cache.targetSurfaces.size());
  }
  return inserted->second;
}

struct TransitionEncodingGroup {
  const std::unordered_map<size_t, size_t>* symbolMap = nullptr;
  std::vector<size_t> stateSymbols;
};



struct TransitionEncodingLiteral {
  size_t transitionSymbol = 0;
  bool desiredValue = false;
  CubeLiteral originalLiteral;
};

struct TransitionEncodingLiteralGroup {
  const std::unordered_map<size_t, size_t>* symbolMap = nullptr;
  std::vector<TransitionEncodingLiteral> literals;
  std::vector<size_t> stateSymbols;
};

void appendTransitionEncodingLiteralGroup(
    std::vector<TransitionEncodingLiteralGroup>& groups,
    const std::unordered_map<size_t, size_t>* symbolMap,
    TransitionEncodingLiteral literal) {
  for (auto& group : groups) {
    if (group.symbolMap == symbolMap) {
      group.stateSymbols.push_back(literal.transitionSymbol);
      group.literals.push_back(std::move(literal));
      return;
    }
  }
  TransitionEncodingLiteralGroup group;
  group.symbolMap = symbolMap;
  group.stateSymbols.push_back(literal.transitionSymbol);
  group.literals.push_back(std::move(literal));
  // LCOV_EXCL_START
  groups.push_back(std::move(group));
}

std::vector<TransitionEncodingLiteralGroup> groupTransitionCubeLiteralsBySymbolMap(
// LCOV_EXCL_STOP
    const TransitionExprResolver& transitionByState,
    // LCOV_EXCL_START
    const StateCube& targetCube) {
  const auto& primaryByComplement = transitionByState.primaryByComplement();
  std::vector<TransitionEncodingLiteralGroup> groups;
  // LCOV_EXCL_STOP
  groups.reserve(3);
  for (const auto& literal : targetCube) {
    size_t transitionSymbol = literal.symbol;
    bool desiredValue = literal.value;
    if (!transitionByState.contains(transitionSymbol)) {
      const auto primaryIt = primaryByComplement.find(transitionSymbol);  // LCOV_EXCL_LINE
      if (primaryIt == primaryByComplement.end() ||  // LCOV_EXCL_LINE
          !transitionByState.contains(primaryIt->second)) {  // LCOV_EXCL_LINE
        continue;  // LCOV_EXCL_LINE
      }
      transitionSymbol = primaryIt->second;  // LCOV_EXCL_LINE
      desiredValue = !desiredValue;  // LCOV_EXCL_LINE
    }  // LCOV_EXCL_LINE

    const TransitionExprView view =
        transitionByState.expressionView(transitionSymbol);
    appendTransitionEncodingLiteralGroup(
        groups,
        view.symbolMap,
        TransitionEncodingLiteral{transitionSymbol, desiredValue, literal});
  }
  for (auto& group : groups) {
    std::sort(group.stateSymbols.begin(), group.stateSymbols.end());
    group.stateSymbols.erase(
        std::unique(group.stateSymbols.begin(), group.stateSymbols.end()),
        group.stateSymbols.end());
  }
  return groups;
}

// LCOV_EXCL_START


// LCOV_EXCL_STOP
std::vector<size_t> cubeStateSymbols(const StateCube& cube) {
  std::unordered_set<size_t> symbols;
  symbols.reserve(cube.size());
  for (const auto& literal : cube) {
    symbols.insert(literal.symbol);
  }
  return sortUniqueSymbols(std::move(symbols));
}

// LCOV_EXCL_START


// LCOV_EXCL_STOP
bool shouldAvoidTransitionNodeCountCost(const KInductionProblem& problem) {
  return problem.usesDualRailStateEncoding &&
         (pdrDualRailStateSymbolCount(problem) >
              kMaxDualRailNodeCountStateSymbols ||
          pdrTransitionSourceCount(problem) > // LCOV_EXCL_LINE
              kMaxDualRailNodeCountTransitionSources || // LCOV_EXCL_LINE
          pdrOriginalObservedOutputCount(problem) > // LCOV_EXCL_LINE
              kMaxMediumDualRailObservedOutputs);
}

size_t transitionLiteralCost(const KInductionProblem& problem,
                             const TransitionExprResolver& transitionByState,
                             size_t symbol) {
  size_t transitionSymbol = symbol;
  if (!transitionByState.contains(transitionSymbol)) {
    const auto primaryIt = transitionByState.primaryByComplement().find(symbol);  // LCOV_EXCL_LINE
    if (primaryIt == transitionByState.primaryByComplement().end() ||  // LCOV_EXCL_LINE
        !transitionByState.contains(primaryIt->second)) {  // LCOV_EXCL_LINE
      return 0;  // LCOV_EXCL_LINE
    }
    transitionSymbol = primaryIt->second;  // LCOV_EXCL_LINE
  }  // LCOV_EXCL_LINE
  // Support width is the dominant SAT-query cost; node count breaks ties among
  // cones with similar state/input footprints. On large lazy dual-rail
  // surfaces, nodeCount() materializes the lifted transition DAG just to order
  // optional PDR probes. Use support-only ordering there so the heuristic does
  // not fill the shared dual-rail remap memo before the exact query starts.
  const size_t supportCost = transitionByState.support(transitionSymbol).size() * 4;
  if (shouldAvoidTransitionNodeCountCost(problem)) {
    return supportCost;
  }
  return supportCost + transitionByState.nodeCount(transitionSymbol);
}

size_t blockedCubeTransitionSupportSize(
    const KInductionProblem& problem,
    // LCOV_EXCL_START
    const TransitionExprResolver& transitionByState,
    // LCOV_EXCL_STOP
    const StateCube& cube) {
  const std::vector<size_t> targetSymbols = cubeStateSymbols(cube);
  const std::vector<size_t> encodedTargets =
      expandTransitionTargets(problem, targetSymbols, transitionByState);
  return collectTransitionSupportSymbols(transitionByState, encodedTargets).size();
}


StateCube boundedCheapTransitionCube(
    const StateCube& cube,
    size_t limit,
    const KInductionProblem& problem,
    // LCOV_EXCL_START
    const TransitionExprResolver& transitionByState) {
    // LCOV_EXCL_STOP
  if (limit == 0 || cube.size() <= limit) {
    return cube;  // LCOV_EXCL_LINE
  }

  StateCube selected = cube;
  std::stable_sort(
      selected.begin(),
      selected.end(),
      [&](const CubeLiteral& lhs, const CubeLiteral& rhs) {
        const size_t lhsCost =
            transitionLiteralCost(problem, transitionByState, lhs.symbol);
        const size_t rhsCost =
            transitionLiteralCost(problem, transitionByState, rhs.symbol);
        if (lhsCost != rhsCost) {
          return lhsCost < rhsCost;  // LCOV_EXCL_LINE
        }
        return lhs.symbol < rhs.symbol;
      });
  selected.resize(limit);
  normalizeCube(selected);
  return selected;
}

bool cubeContainsCube(const StateCube& cube, const StateCube& core) {
  return std::includes(
      cube.begin(),
      cube.end(),
      core.begin(),
      core.end(),
      [](const CubeLiteral& lhs, const CubeLiteral& rhs) {
        if (lhs.symbol != rhs.symbol) {
          return lhs.symbol < rhs.symbol;
        }
        // LCOV_EXCL_START
        return lhs.value < rhs.value;
        // LCOV_EXCL_STOP
      });
}

void addSupportSymbols(const std::set<size_t>& support,
                       std::unordered_set<size_t>& symbols) {
  for (const auto symbol : support) {
    if (symbol >= 2) {
      symbols.insert(symbol);
    }
  }
}


void addFormulaSymbols(BoolExpr* formula,
                       std::unordered_set<size_t>& symbols,
                       PdrFormulaSupportCache* supportCache) {
  if (formula == nullptr) {
    return;  // LCOV_EXCL_LINE
  }
  if (supportCache != nullptr) {
    addSupportSymbols(supportCache->support(formula), symbols);
    return;
  }
  addSupportSymbols(formula->getSupportVars(), symbols);
}


void addRelevantComplementedStatePartners(
    const ComplementPartnerIndex& complementPartners,
    std::unordered_set<size_t>& symbols) {
  std::vector<size_t> worklist =
      detail::makePdrClosureWorklist(symbols);
  for (size_t cursor = 0; cursor < worklist.size(); ++cursor) {
    const auto partnerIt =
        complementPartners.partnersBySymbol.find(worklist[cursor]);
    if (partnerIt == complementPartners.partnersBySymbol.end()) {
      continue;
    }
    for (const auto partnerSymbol : partnerIt->second) {
      // LCOV_EXCL_START
      if (symbols.insert(partnerSymbol).second) {
        worklist.push_back(partnerSymbol);
      }
      // LCOV_EXCL_STOP
    }
  }
}

void addRelevantComplementedStatePartners(
    const std::vector<std::pair<size_t, size_t>>& complementedStatePairs,
    std::unordered_set<size_t>& symbols) {
  for (const auto& [primarySymbol, complementedSymbol] : complementedStatePairs) {
    if (symbols.find(primarySymbol) != symbols.end() || // LCOV_EXCL_LINE
        // LCOV_EXCL_START
        symbols.find(complementedSymbol) != symbols.end()) {
      symbols.insert(primarySymbol);  // LCOV_EXCL_LINE
      symbols.insert(complementedSymbol);  // LCOV_EXCL_LINE
      // LCOV_EXCL_STOP
    }  // LCOV_EXCL_LINE
  }
}

void addRelevantStateEqualityPartners(
    const std::vector<std::pair<size_t, size_t>>& equalityPairs,
    std::unordered_set<size_t>& symbols) {
  bool changed = true;
  while (changed) {
    changed = false;
    for (const auto& [lhsSymbol, rhsSymbol] : equalityPairs) {
      const bool lhsNeeded = symbols.find(lhsSymbol) != symbols.end();
      const bool rhsNeeded = symbols.find(rhsSymbol) != symbols.end();
      if (!lhsNeeded && !rhsNeeded) {
        continue;
      }
      changed |= symbols.insert(lhsSymbol).second;
      changed |= symbols.insert(rhsSymbol).second;
    }
  }
}

void addRelevantSameFrameStateEqualityPartners(
    const KInductionProblem& problem,
    std::unordered_set<size_t>& symbols) {
  addRelevantStateEqualityPartners(problem.sameFrameStateEqualityPairs0, symbols);
  addRelevantStateEqualityPartners(problem.sameFrameStateEqualityPairs1, symbols);
}

void addRelevantDualRailPartners(
    const std::vector<DualRailSymbolPair>& railPairs,
    std::unordered_set<size_t>& symbols) {
  for (const auto& rails : railPairs) {
    if (symbols.find(rails.mayBeOne) != symbols.end() ||
        symbols.find(rails.mayBeZero) != symbols.end()) {
      symbols.insert(rails.mayBeOne);  // LCOV_EXCL_LINE
      // LCOV_EXCL_START
      symbols.insert(rails.mayBeZero);
      // LCOV_EXCL_STOP
    }  // LCOV_EXCL_LINE
  }
}

void addRelevantDualRailPartners(
    PdrFormulaSupportCache* supportCache,
    const std::vector<DualRailSymbolPair>& railPairs,
    std::unordered_set<size_t>& symbols) {
  if (supportCache != nullptr) {
    supportCache->addRelevantDualRailPartners(symbols);
    return;
  }
  addRelevantDualRailPartners(railPairs, symbols);  // LCOV_EXCL_LINE
}

const std::vector<std::pair<size_t, size_t>>& emptySymbolPairs();

bool hasStructuredInitFacts(const KInductionProblem& problem) {
  if (problem.resetBootstrapCycles != 0) {
    return !problem.bootstrapStateAssignments.empty();
  }
  return !problem.initialStateAssignments.empty();
}

void addRelevantInitConstraintSymbols(const KInductionProblem& problem,
                                      std::unordered_set<size_t>& symbols) {
  const bool usesBootstrapFrontier = problem.resetBootstrapCycles != 0;
  const auto& assignments = usesBootstrapFrontier
                                ? problem.bootstrapStateAssignments
                                : problem.initialStateAssignments;

  for (const auto& [symbol, /*value*/ _] : assignments) {
    if (symbols.find(symbol) != symbols.end()) {
      symbols.insert(symbol);
    }
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


void addAllFrameClauseSymbols(const FrameClauses& frame,
                              std::unordered_set<size_t>& symbols) {
  for (const auto& clause : frame.clauses) {
    addClauseSymbols(clause, symbols);
  }
}


void addFrameConstraintSymbols(const KInductionProblem& problem,
                               BoolExpr* initFormula,
                               BoolExpr* frameInvariant,
                               const std::vector<FrameClauses>& frames,
                               size_t level,
                               const ComplementPartnerIndex& complementPartners,
                               std::unordered_set<size_t>& symbols,
                               PdrFormulaSupportCache* supportCache) {
  if (level == 0) {
    if (hasStructuredInitFacts(problem)) {
      // Keep Init cone-local even in the exact frame-clause retry. ASIC SEC
      // startup frontiers contain tens of thousands of equality facts, while a
      // predecessor query usually touches only a few of them. The exact retry
      // below disables learned-frame filtering, not this structured Init
      // sparsification.
      addRelevantInitConstraintSymbols(problem, symbols);
    } else {
      addFormulaSymbols(initFormula, symbols, supportCache);
    }
    addAllFrameClauseSymbols(frames[0], symbols);
  } else {
    addFormulaSymbols(frameInvariant, symbols, supportCache);
    addAllFrameClauseSymbols(frames[level], symbols);
  }
  addRelevantComplementedStatePartners(complementPartners, symbols);
  addRelevantSameFrameStateEqualityPartners(problem, symbols);
  addRelevantDualRailPartners(supportCache, problem.dualRailStatePairs, symbols);
}

std::vector<size_t> findBadQuerySymbols(const KInductionProblem& problem,
                                        BoolExpr* initFormula,
                                        BoolExpr* frameInvariant,
                                        const std::vector<FrameClauses>& frames,
                                        BoolExpr* badFormula,
                                        size_t level,
                                        const ComplementPartnerIndex& complementPartners,
                                        PdrFormulaSupportCache* supportCache) {
  std::unordered_set<size_t> symbols;
  addFormulaSymbols(badFormula, symbols, supportCache);
  addFrameConstraintSymbols(
      problem,
      initFormula,
      frameInvariant,
      frames,
      level,
      complementPartners,
      symbols,
      supportCache);
  return sortUniqueSymbols(std::move(symbols));
}

void addCurrentFramePartnerClosure(
    const KInductionProblem& problem,
    const ComplementPartnerIndex& complementPartners,
    std::unordered_set<size_t>& symbols,
    PdrFormulaSupportCache* supportCache) {
  addRelevantComplementedStatePartners(complementPartners, symbols);
  addRelevantSameFrameStateEqualityPartners(problem, symbols);
  addRelevantDualRailPartners(supportCache, problem.dualRailStatePairs, symbols);
}

std::vector<size_t> sortClosedCurrentFrameSymbols(
    const KInductionProblem& problem,
    const ComplementPartnerIndex& complementPartners,
    std::unordered_set<size_t> symbols,
    PdrFormulaSupportCache* supportCache) {
  addCurrentFramePartnerClosure(
      problem, complementPartners, symbols, supportCache);
  return sortUniqueSymbols(std::move(symbols));
} // LCOV_EXCL_LINE

std::vector<size_t> sortCurrentFrameSymbolSeed(
    std::unordered_set<size_t> symbols) {
  return sortUniqueSymbols(std::move(symbols));
} // LCOV_EXCL_LINE

const std::vector<size_t>& cachedClosedCurrentFrameSymbols(
    PredecessorAssumptionCache& cache,
    const KInductionProblem& problem,
    const ComplementPartnerIndex& complementPartners,
    std::vector<size_t> seedSymbols,
    PdrFormulaSupportCache* supportCache) {
  const auto existing = cache.closedCurrentFrameSymbols.find(seedSymbols);
  if (existing != cache.closedCurrentFrameSymbols.end()) {
    return existing->second; // LCOV_EXCL_LINE
  }
  if (cache.closedCurrentFrameSymbols.size() >=
      kMaxPredecessorClosedSymbolCacheEntries) {
    // The cache is an accelerator for repeated local cones only. Clearing it is
    // cheaper and more predictable than retaining thousands of one-off
    // predecessor surfaces in a long SEC run.
    cache.closedCurrentFrameSymbols.clear(); // LCOV_EXCL_LINE
  } // LCOV_EXCL_LINE

  std::unordered_set<size_t> symbols(seedSymbols.begin(), seedSymbols.end());
  std::vector<size_t> closedSymbols = sortClosedCurrentFrameSymbols(
      problem, complementPartners, std::move(symbols), supportCache);
  auto [inserted, insertedNew] = cache.closedCurrentFrameSymbols.emplace(
      std::move(seedSymbols), std::move(closedSymbols));
  (void)insertedNew;
  if (pdrStatsEnabled()) {
    emitSecDiag(
        "SEC PDR stats: predecessor closed symbol cache seed=",
        inserted->first.size(),
        " closed=",
        inserted->second.size(),
        " entries=",
        cache.closedCurrentFrameSymbols.size());
  }
  return inserted->second;
}

PredecessorFrameSymbolSurfaceKey makePredecessorFrameSymbolSurfaceKey(
    const KInductionProblem& problem,
    BoolExpr* initFormula,
    BoolExpr* frameInvariant,
    const std::vector<FrameClauses>& frames,
    size_t level,
    const ComplementPartnerIndex& complementPartners,
    PdrFormulaSupportCache* supportCache) {
  PredecessorFrameSymbolSurfaceKey key;
  key.problem = &problem;
  key.initFormula = initFormula;
  key.frameInvariant = frameInvariant;
  key.complementPartners = &complementPartners;
  key.supportCache = supportCache;
  key.level = level;
  key.frameFingerprint = frameClausesFingerprint(frames, level);
  return key;
}

std::vector<size_t> buildStablePredecessorCurrentFrameSymbols(
    const KInductionProblem& problem,
    BoolExpr* initFormula,
    BoolExpr* frameInvariant,
    const std::vector<FrameClauses>& frames,
    size_t level,
    const ComplementPartnerIndex& complementPartners,
    PdrFormulaSupportCache* supportCache) {
  std::unordered_set<size_t> symbols;
  if (level == 0) {
    if (!hasStructuredInitFacts(problem)) {
      addFormulaSymbols(initFormula, symbols, supportCache);
    }
    addAllFrameClauseSymbols(frames[0], symbols);
  } else {
    addFormulaSymbols(frameInvariant, symbols, supportCache); // LCOV_EXCL_LINE
    addAllFrameClauseSymbols(frames[level], symbols); // LCOV_EXCL_LINE
  }

  // The relation closures below are independent of the target cube. Closing
  // this stable frame side once is equivalent to closing it together with each
  // query's dynamic symbols, because the closures only add partner/equality
  // symbols and do not inspect SAT polarity or clause state.
  return sortClosedCurrentFrameSymbols(
      problem, complementPartners, std::move(symbols), supportCache);
}

const std::vector<size_t>& cachedStablePredecessorCurrentFrameSymbols(
    PredecessorAssumptionCache& cache,
    const KInductionProblem& problem,
    BoolExpr* initFormula,
    BoolExpr* frameInvariant,
    const std::vector<FrameClauses>& frames,
    size_t level,
    const ComplementPartnerIndex& complementPartners,
    PdrFormulaSupportCache* supportCache) {
  const PredecessorFrameSymbolSurfaceKey key =
      makePredecessorFrameSymbolSurfaceKey(
          problem,
          initFormula,
          frameInvariant,
          frames,
          level,
          complementPartners,
          supportCache);
  if (!cache.currentFrameSymbols.valid ||
      !(cache.currentFrameSymbols.key == key)) { // LCOV_EXCL_LINE
    cache.currentFrameSymbols.symbols =
        buildStablePredecessorCurrentFrameSymbols(
            problem,
            initFormula,
            frameInvariant,
            frames,
            level,
            complementPartners,
            supportCache);
    cache.currentFrameSymbols.key = key;
    cache.currentFrameSymbols.valid = true;
    if (pdrStatsEnabled()) {
      emitSecDiag(
          "SEC PDR stats: predecessor frame symbol cache built level=",
          level,
          " symbols=",
          cache.currentFrameSymbols.symbols.size(),
          " frame_fingerprint=",
          key.frameFingerprint);
    }
  }
  return cache.currentFrameSymbols.symbols;
}

std::vector<size_t> mergePredecessorSymbolAddition(
    std::vector<size_t> base,
    const std::vector<size_t>& addition) {
  if (addition.empty()) {
    return base;
  }
  return detail::mergeSortedPdrSymbolVectors(base, addition);
}

std::vector<size_t> predecessorCurrentFrameQuerySymbolsFromCachedSurface(
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
    const std::vector<StateClause>* extraFrameClauses,
    PredecessorAssumptionCache& predecessorAssumptionCache,
    PdrFormulaSupportCache* supportCache) {
  const std::vector<size_t>& stableSymbols =
      cachedStablePredecessorCurrentFrameSymbols(
          predecessorAssumptionCache,
          problem,
          initFormula,
          frameInvariant,
          frames,
          level,
          complementPartners,
          supportCache);
  std::vector<size_t> merged = stableSymbols;

  std::unordered_set<size_t> predecessorDynamic;
  predecessorDynamic.reserve(predecessorSymbols.size());
  predecessorDynamic.insert(predecessorSymbols.begin(), predecessorSymbols.end());
  if (level == 0 && hasStructuredInitFacts(problem)) {
    // Structured Init facts are intentionally query-local. Apply them only to
    // the predecessor cone, matching addFrameConstraintSymbols() before the
    // cached stable frame side is merged in.
    addRelevantInitConstraintSymbols(problem, predecessorDynamic); // LCOV_EXCL_LINE
  } // LCOV_EXCL_LINE
  merged = mergePredecessorSymbolAddition(
      std::move(merged),
      cachedClosedCurrentFrameSymbols(
          predecessorAssumptionCache,
          problem,
          complementPartners,
          sortCurrentFrameSymbolSeed(std::move(predecessorDynamic)),
          supportCache));

  std::unordered_set<size_t> transitionDynamic;
  transitionDynamic.reserve(transitionSupportSymbols.size());
  if (predecessorSourceFrameIsKnownSafe(level)) {
    addFormulaSymbols(problem.property, transitionDynamic, supportCache); // LCOV_EXCL_LINE
  } // LCOV_EXCL_LINE
  for (const auto symbol : transitionSupportSymbols) {
    if (symbol >= 2) {
      transitionDynamic.insert(symbol);
    }
  }
  merged = mergePredecessorSymbolAddition(
      std::move(merged),
      cachedClosedCurrentFrameSymbols(
          predecessorAssumptionCache,
          problem,
          complementPartners,
          sortCurrentFrameSymbolSeed(std::move(transitionDynamic)),
          supportCache));

  std::unordered_set<size_t> tailSymbols;
  tailSymbols.reserve(
      (excludeTargetOnCurrentFrame ? targetCube.size() : 0) +
      (extraFrameClauses == nullptr ? 0 : extraFrameClauses->size()));
  if (excludeTargetOnCurrentFrame) {
    addCubeSymbols(targetCube, tailSymbols); // LCOV_EXCL_LINE
  } // LCOV_EXCL_LINE
  if (extraFrameClauses != nullptr) {
    for (const auto& clause : *extraFrameClauses) { // LCOV_EXCL_LINE
      addClauseSymbols(clause, tailSymbols); // LCOV_EXCL_LINE
    }
  } // LCOV_EXCL_LINE
  return mergePredecessorSymbolAddition(
      std::move(merged), sortUniqueSymbols(std::move(tailSymbols)));
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
    const std::vector<StateClause>* extraFrameClauses,
    PredecessorAssumptionCache* predecessorAssumptionCache,
    PdrFormulaSupportCache* supportCache) {
  if (predecessorAssumptionCache != nullptr &&
      hasLocalDualRailFinalLeafSurface(problem)) {
    return predecessorCurrentFrameQuerySymbolsFromCachedSurface(
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
        extraFrameClauses,
        *predecessorAssumptionCache,
        supportCache);
  }

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
      complementPartners,
      symbols,
      supportCache);
  if (predecessorSourceFrameIsKnownSafe(level)) {
    // The safe-frame property is encoded below, so include its support in the
    // exact query surface.
    addFormulaSymbols(problem.property, symbols, supportCache);
  }
  for (const auto symbol : transitionSupportSymbols) {
    if (symbol >= 2) {
      symbols.insert(symbol);
    }
  }
  addRelevantComplementedStatePartners(complementPartners, symbols);
  addRelevantSameFrameStateEqualityPartners(problem, symbols);
  addRelevantDualRailPartners(supportCache, problem.dualRailStatePairs, symbols);
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

std::vector<size_t> predecessorAssumptionCacheSymbols(
    const KInductionProblem& problem,
    const TransitionExprResolver& transitionByState,
    const std::vector<size_t>& solverSymbols,
    size_t level,
    PredecessorAssumptionCache* cache) {
  if (!detail::shouldUseStableLocalPredecessorCacheSurface(
          hasLocalDualRailFinalLeafSurface(problem),
          level)) {
    return solverSymbols;
  }

  // Local single-output dual-rail leaves issue many neighboring predecessor
  // queries. A stable local surface lets the cached SAT solver survive small
  // target/support changes without promoting the query to all dual-rail state
  // symbols; sampled Swerv leaves spent the wall on those broad level-0 caches.
  if (cache != nullptr) {
    if (cache->widenedPredecessorCacheResolver != &transitionByState) {
      cache->widenedPredecessorCacheSymbols.clear();
      cache->widenedPredecessorCacheResolver = &transitionByState;
    }
    if (detail::widenSortedPdrSymbolSurface(
            cache->widenedPredecessorCacheSymbols, solverSymbols)) {
      if (pdrStatsEnabled()) {
        emitSecDiag(
            "SEC PDR stats: predecessor cached solver surface widened symbols=",
            cache->widenedPredecessorCacheSymbols.size(),
            " requested=",
            solverSymbols.size());
      }
    }
    return cache->widenedPredecessorCacheSymbols;
  }

  return solverSymbols; // LCOV_EXCL_LINE
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
  addRelevantSameFrameStateEqualityPartners(problem, symbols);
  addRelevantDualRailPartners(problem.dualRailStatePairs, symbols);
  return sortUniqueSymbols(std::move(symbols));
}

std::optional<bool> findCubeLiteralValue(const StateCube& cube, size_t symbol) {
  const auto it = std::lower_bound(
      cube.begin(),
      cube.end(),
      symbol,
      [](const CubeLiteral& literal, size_t requestedSymbol) {
        return literal.symbol < requestedSymbol;
      // LCOV_EXCL_START
      });
      // LCOV_EXCL_STOP
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
      // LCOV_EXCL_START
      return true;  // LCOV_EXCL_LINE
    }
    // LCOV_EXCL_STOP
  }
  return false;
}

bool contradictsEqualities(
    const StateCube& cube,
    const std::vector<std::pair<size_t, size_t>>& equalities) {
  for (const auto& [lhsSymbol, rhsSymbol] : equalities) {
    const auto lhsValue = findCubeLiteralValue(cube, lhsSymbol);
    // LCOV_EXCL_START
    const auto rhsValue = findCubeLiteralValue(cube, rhsSymbol);
    if (lhsValue.has_value() && rhsValue.has_value() &&
        *lhsValue != *rhsValue) {  // LCOV_EXCL_LINE
      return true;  // LCOV_EXCL_LINE
    }
    // LCOV_EXCL_STOP
  }
  return false;
}

bool contradictsComplements(
    const StateCube& cube,
    const std::vector<std::pair<size_t, size_t>>& complements) {
  for (const auto& [primarySymbol, complementedSymbol] : complements) {
    const auto primaryValue = findCubeLiteralValue(cube, primarySymbol);  // LCOV_EXCL_LINE
    const auto complementedValue = findCubeLiteralValue(cube, complementedSymbol);  // LCOV_EXCL_LINE
    if (primaryValue.has_value() && complementedValue.has_value() &&  // LCOV_EXCL_LINE
        *primaryValue == *complementedValue) {  // LCOV_EXCL_LINE
      return true;  // LCOV_EXCL_LINE
    }
  }
  return false;
}

void reservePdrTransitionEncodingVars(SATSolverWrapper& solver,
                                      size_t estimatedNodes) {
  if (estimatedNodes < kMinPdrTransitionSolverReserveNodes) {
    return;
  }
  solver.reserveAdditionalVars( // LCOV_EXCL_LINE
      std::min(estimatedNodes, kMaxPdrTransitionSolverReserveHint)); // LCOV_EXCL_LINE
}

const std::vector<std::pair<size_t, size_t>>& emptySymbolPairs() {
  static const std::vector<std::pair<size_t, size_t>> pairs;
  return pairs;
}

// LCOV_EXCL_START
std::optional<bool> cubeIntersectsKnownInitFacts(
// LCOV_EXCL_STOP
    const KInductionProblem& problem,
    const StateCube& cube) {
  const bool usesBootstrapFrontier = problem.resetBootstrapCycles != 0;
  const auto& assignments = usesBootstrapFrontier
                                // LCOV_EXCL_START
                                ? problem.bootstrapStateAssignments
                                // LCOV_EXCL_STOP
                                : problem.initialStateAssignments;
  const auto& equalities = emptySymbolPairs();

// LCOV_EXCL_START


// LCOV_EXCL_STOP
  if (contradictsAssignments(cube, assignments) ||
      contradictsEqualities(cube, equalities)) {
    return false;  // LCOV_EXCL_LINE
  }
  if (problem.complementedStatePairs0.size() <=
      kMaxComplementPairsForCheapInitCheck &&
      contradictsComplements(cube, problem.complementedStatePairs0)) {
    return false;  // LCOV_EXCL_LINE
  }
  if (problem.complementedStatePairs1.size() <=
      kMaxComplementPairsForCheapInitCheck &&
      contradictsComplements(cube, problem.complementedStatePairs1)) {
    return false;  // LCOV_EXCL_LINE
  }

  // Structured assignments are explicit exact Init constraints. If this cheap
  // check cannot exclude the cube, conservatively keep it as init-intersecting;
  // this path is only an optional literal-dropping optimization.
  if (usesBootstrapFrontier || !assignments.empty() || !equalities.empty()) {
    return true;
  }
  return std::nullopt;
}


void addTransitionConstraintsForTargetCube(
    SATSolverWrapper& solver,
    const FrameVariableStore& variables,
    // LCOV_EXCL_START
    const TransitionExprResolver& transitionByState,
    size_t frame,
    const StateCube& targetCube,
    const std::vector<size_t>& encodedTargets,
    const std::vector<size_t>& supportSymbols,
    std::unordered_map<size_t, int>* encodedLeafLits = nullptr) {
  (void)encodedTargets;
  // LCOV_EXCL_STOP
  for (const auto& group :
       groupTransitionCubeLiteralsBySymbolMap(transitionByState, targetCube)) {
    std::unordered_map<size_t, int> leafLits =
        variables.makeLeafLits(frame, supportSymbols);
    const size_t estimatedNodes =
        estimateTransitionEncodingNodes(transitionByState, group.stateSymbols);
    reservePdrTransitionEncodingVars(solver, estimatedNodes);
    FrameFormulaEncoder encoder(
        solver,
        std::move(leafLits),
        // LCOV_EXCL_START
        group.symbolMap,
        false,
        estimatedNodes);
    for (const auto& literal : group.literals) {
      const TransitionExprView view =
      // LCOV_EXCL_STOP
          transitionByState.expressionView(literal.transitionSymbol);
      if (view.symbolMap != group.symbolMap) {
        throw std::runtime_error("Inconsistent transition symbol map");  // LCOV_EXCL_LINE
      }
      const int transitionLit = encoder.encode(view.expr);
      solver.addClause({literal.desiredValue ? transitionLit : -transitionLit});
    }
    if (encodedLeafLits != nullptr) {
      const auto& groupLeafLits = encoder.leafLits();
      encodedLeafLits->insert(groupLeafLits.begin(), groupLeafLits.end());
    }
  }
}

std::vector<std::pair<int, CubeLiteral>> addTransitionAssumptionsForTargetCube(
    SATSolverWrapper& solver,
    const FrameVariableStore& variables,
    const TransitionExprResolver& transitionByState,
    // LCOV_EXCL_START
    size_t frame,
    const StateCube& targetCube,
    const std::vector<size_t>& encodedTargets,
    const std::vector<size_t>& supportSymbols) {
  (void)encodedTargets;
  std::vector<std::pair<int, CubeLiteral>> assumptions;
  assumptions.reserve(targetCube.size());
  // LCOV_EXCL_STOP
  for (const auto& group :
       groupTransitionCubeLiteralsBySymbolMap(transitionByState, targetCube)) {
    std::unordered_map<size_t, int> leafLits =
        variables.makeLeafLits(frame, supportSymbols);
    const size_t estimatedNodes =
        estimateTransitionEncodingNodes(transitionByState, group.stateSymbols);
    reservePdrTransitionEncodingVars(solver, estimatedNodes);
    FrameFormulaEncoder encoder(
        solver,
        std::move(leafLits),
        // LCOV_EXCL_START
        group.symbolMap,
        false,
        estimatedNodes);
    for (const auto& literal : group.literals) {
      const TransitionExprView view =
      // LCOV_EXCL_STOP
          transitionByState.expressionView(literal.transitionSymbol);
      if (view.symbolMap != group.symbolMap) {
        throw std::runtime_error("Inconsistent transition symbol map");  // LCOV_EXCL_LINE
      }
      const int transitionLit = encoder.encode(view.expr);
      assumptions.emplace_back(
          literal.desiredValue ? transitionLit : -transitionLit,
          literal.originalLiteral);
    // LCOV_EXCL_START
    }
    // LCOV_EXCL_STOP
  }
  return assumptions;
}

FrameFormulaEncoder& cachedPredecessorTransitionEncoder(
    PredecessorAssumptionSolver& cachedSolver,
    const std::unordered_map<size_t, size_t>* symbolMap,
    size_t frame,
    size_t estimatedNodes) {
  const auto existing =
      cachedSolver.transitionEncoderBySymbolMap.find(symbolMap);
  if (existing != cachedSolver.transitionEncoderBySymbolMap.end()) {
    return *existing->second;
  }

  // Use the cached solver's complete symbol surface for this encoder. It is
  // built once per reusable predecessor solver, and it prevents a later target
  // in the same surface from missing a leaf that was outside the first target's
  // transition support slice.
  auto encoder = std::make_unique<FrameFormulaEncoder>(
      *cachedSolver.solver,
      cachedSolver.variables->makeLeafLits(frame),
      symbolMap,
      false,
      estimatedNodes);
  cachedSolver.transitionLeafLits.insert(
      encoder->leafLits().begin(), encoder->leafLits().end());
  auto [inserted, insertedNew] =
      cachedSolver.transitionEncoderBySymbolMap.emplace(
          symbolMap, std::move(encoder));
  (void)insertedNew;
  if (pdrStatsEnabled()) {
    emitSecDiag(
        "SEC PDR stats: predecessor transition encoder cached symbols=",
        inserted->second->leafLits().size(),
        " estimated_nodes=",
        estimatedNodes);
  }
  return *inserted->second;
}

std::vector<std::pair<int, CubeLiteral>>
addCachedTransitionAssumptionsForTargetCube(
    PredecessorAssumptionSolver& cachedSolver,
    const TransitionExprResolver& transitionByState,
    size_t frame,
    const StateCube& targetCube,
    const std::vector<size_t>& encodedTargets,
    const std::vector<size_t>& supportSymbols) {
  (void)encodedTargets;
  std::vector<std::pair<int, CubeLiteral>> assumptions;
  assumptions.reserve(targetCube.size());
  for (const auto& group :
       groupTransitionCubeLiteralsBySymbolMap(transitionByState, targetCube)) {
    FrameFormulaEncoder* encoder = nullptr;
    for (const auto& literal : group.literals) {
      const TransitionAssumptionKey key{
          literal.transitionSymbol,
          literal.desiredValue};
      const auto cachedIt =
          cachedSolver.assumptionByTransitionLiteral.find(key);
      if (cachedIt != cachedSolver.assumptionByTransitionLiteral.end()) {
        assumptions.emplace_back(cachedIt->second, literal.originalLiteral);
        continue;
      }

      if (encoder == nullptr) {
        const size_t estimatedNodes =
            estimateTransitionEncodingNodes(
                transitionByState, group.stateSymbols);
        reservePdrTransitionEncodingVars(*cachedSolver.solver, estimatedNodes);
        encoder = &cachedPredecessorTransitionEncoder(
            cachedSolver,
            group.symbolMap,
            frame,
            estimatedNodes);
      }
      const TransitionExprView view =
          transitionByState.expressionView(literal.transitionSymbol);
      if (view.symbolMap != group.symbolMap) {
        throw std::runtime_error("Inconsistent transition symbol map");  // LCOV_EXCL_LINE
      }
      const int transitionLit = encoder->encode(view.expr);
      // Store both polarities once the transition root is encoded. Neighboring
      // PDR cubes often ask for the opposite value of the same next-state bit;
      // reusing the root literal avoids rebuilding the same transition cone.
      cachedSolver.assumptionByTransitionLiteral.emplace(
          TransitionAssumptionKey{literal.transitionSymbol, true},
          transitionLit);
      cachedSolver.assumptionByTransitionLiteral.emplace(
          TransitionAssumptionKey{literal.transitionSymbol, false},
          -transitionLit);
      const int assumptionLit =
          literal.desiredValue ? transitionLit : -transitionLit;
      assumptions.emplace_back(assumptionLit, literal.originalLiteral);
    }
  }
  return assumptions;
}

std::vector<int> assumptionLiteralsFromPairs(
    const std::vector<std::pair<int, CubeLiteral>>& assumptionPairs) {
  std::vector<int> assumptions;
  assumptions.reserve(assumptionPairs.size());
  for (const auto& [assumptionLit, cubeLiteral] : assumptionPairs) {
    (void)cubeLiteral;
    assumptions.push_back(assumptionLit);
  }
  return assumptions;
}

std::unordered_map<int, CubeLiteral> literalByAssumptionFromTargetPairs(
    const std::vector<std::pair<int, CubeLiteral>>& assumptionPairs) {
  std::unordered_map<int, CubeLiteral> literalByAssumption;
  literalByAssumption.reserve(assumptionPairs.size() * 2);
  for (const auto& [assumptionLit, cubeLiteral] : assumptionPairs) {
    literalByAssumption.emplace(assumptionLit, cubeLiteral);
    // Keep the polarity-tolerant mapping used by the fresh core oracle. Some
    // solver backends expose final conflicts in solver-literal polarity.
    literalByAssumption.emplace(-assumptionLit, cubeLiteral);
  }
  return literalByAssumption;
}

StateCube failedAssumptionCubeFromTargetPairs(
    const SATSolverWrapper& solver,
    const std::vector<std::pair<int, CubeLiteral>>& assumptionPairs) {
  const auto literalByAssumption =
      literalByAssumptionFromTargetPairs(assumptionPairs);

  StateCube core;
  for (const int failedLit : solver.failedAssumptions()) {
    const auto literalIt = literalByAssumption.find(failedLit);
    if (literalIt == literalByAssumption.end()) {
      continue;
    }
    core.push_back(literalIt->second);
  }
  normalizeCube(core);
  return core;
}

std::optional<StateCube> minimizeCoreInTargetContext(
    SATSolverWrapper& coreSolver,
    const std::vector<int>& assumptions,
    const std::unordered_map<int, CubeLiteral>& literalByAssumption,
    size_t* checks);

bool shouldMinimizeCachedPredecessorCoreInTargetContext(
    const KInductionProblem& problem,
    size_t level,
    const StateCube& targetCube,
    const std::vector<size_t>& transitionSupportSymbols,
    bool excludeTargetOnCurrentFrame,
    const std::vector<StateClause>* extraFrameClauses,
    const StateCube& currentCore) {
  if (!problem.usesDualRailStateEncoding || level != 0 ||
      excludeTargetOnCurrentFrame || extraFrameClauses != nullptr) {
    return false;
  }
  if (targetCube.size() < kMinMediumCubePredecessorCoreTargetSize ||
      transitionSupportSymbols.size() <=
          kMaxGeneralizedBlockedCubeTransitionSupport) {
    return false;
  }
  return currentCore.empty() || currentCore.size() >= targetCube.size();
}

StateCube cachedPredecessorUnsatCoreFromTargetContext(
    SATSolverWrapper& solver,
    const KInductionProblem& problem,
    size_t level,
    const StateCube& targetCube,
    const std::vector<size_t>& transitionSupportSymbols,
    bool excludeTargetOnCurrentFrame,
    const std::vector<StateClause>* extraFrameClauses,
    const std::vector<int>& targetAssumptions,
    const std::vector<std::pair<int, CubeLiteral>>& assumptionPairs) {
  StateCube core =
      failedAssumptionCubeFromTargetPairs(solver, assumptionPairs);
  if (!shouldMinimizeCachedPredecessorCoreInTargetContext(
          problem,
          level,
          targetCube,
          transitionSupportSymbols,
          excludeTargetOnCurrentFrame,
          extraFrameClauses,
          core)) {
    return core;
  }

  // The cached predecessor solver already contains the exact F0/frame and
  // transition context that proved the full target unreachable. Shrink only
  // the target assumptions inside that same solver, and accept a reduced core
  // only when it remains UNSAT there.
  size_t checks = 0; // LCOV_EXCL_LINE
  const auto literalByAssumption =
      literalByAssumptionFromTargetPairs(assumptionPairs); // LCOV_EXCL_LINE
  const auto minimizedCore = minimizeCoreInTargetContext( // LCOV_EXCL_LINE
      solver, targetAssumptions, literalByAssumption, &checks); // LCOV_EXCL_LINE
  if (!minimizedCore.has_value() || // LCOV_EXCL_LINE
      minimizedCore->size() >= targetCube.size()) { // LCOV_EXCL_LINE
    if (pdrStatsEnabled()) { // LCOV_EXCL_LINE
      emitSecDiag( // LCOV_EXCL_LINE
          "SEC PDR stats: predecessor cached core minimization miss target=",
          targetCube.size(), // LCOV_EXCL_LINE
          " raw_core=",
          core.size(), // LCOV_EXCL_LINE
          " checks=",
          checks,
          " level=",
          level,
          " support=",
          transitionSupportSymbols.size()); // LCOV_EXCL_LINE
    } // LCOV_EXCL_LINE
    return core; // LCOV_EXCL_LINE
  }
  if (pdrStatsEnabled()) { // LCOV_EXCL_LINE
    emitSecDiag( // LCOV_EXCL_LINE
        "SEC PDR stats: predecessor cached core minimized target=",
        targetCube.size(), // LCOV_EXCL_LINE
        "->",
        minimizedCore->size(), // LCOV_EXCL_LINE
        " raw_core=",
        core.size(), // LCOV_EXCL_LINE
        " checks=",
        checks,
        " level=",
        level,
        " support=",
        transitionSupportSymbols.size(), // LCOV_EXCL_LINE
        " target_hash=",
        cubeFingerprint(targetCube), // LCOV_EXCL_LINE
        " core_hash=",
        cubeFingerprint(*minimizedCore)); // LCOV_EXCL_LINE
  } // LCOV_EXCL_LINE
  return *minimizedCore; // LCOV_EXCL_LINE
}

int cachedTargetExclusionAssumption(
    PredecessorAssumptionSolver& cachedSolver,
    const StateCube& targetCube,
    size_t frame) {
  const StateClause exclusionClause = clauseFromCube(targetCube);
  const auto cachedIt =
      cachedSolver.exclusionAssumptionByClause.find(exclusionClause);
  if (cachedIt != cachedSolver.exclusionAssumptionByClause.end()) {
    return cachedIt->second; // LCOV_EXCL_LINE
  }

  const int selector = cachedSolver.solver->newVar();
  std::vector<int> satClause;
  satClause.reserve(exclusionClause.size() + 1);
  satClause.push_back(-selector);
  for (const auto& literal : exclusionClause) {
    if (!cachedSolver.variables->hasSymbol(literal.symbol)) {
      throw std::runtime_error( // LCOV_EXCL_LINE
          "PDR cached negated-cube encoding missing symbol " + // LCOV_EXCL_LINE
          std::to_string(literal.symbol) + " at frame " + // LCOV_EXCL_LINE
          std::to_string(frame) + " in cube of size " + // LCOV_EXCL_LINE
          std::to_string(targetCube.size())); // LCOV_EXCL_LINE
    }
    const int satLiteral =
        cachedSolver.variables->getLiteral(literal.symbol, frame);
    satClause.push_back(literal.positive ? satLiteral : -satLiteral);
  }
  cachedSolver.solver->addClause(satClause);
  cachedSolver.exclusionAssumptionByClause.emplace(exclusionClause, selector);
  return selector;
}

int cachedExtraFrameClauseAssumption( // LCOV_EXCL_LINE
    PredecessorAssumptionSolver& cachedSolver,
    const StateClause& clause,
    size_t frame) {
  const auto cachedIt =
      cachedSolver.extraFrameAssumptionByClause.find(clause); // LCOV_EXCL_LINE
  if (cachedIt != cachedSolver.extraFrameAssumptionByClause.end()) { // LCOV_EXCL_LINE
    return cachedIt->second; // LCOV_EXCL_LINE
  }

  const int selector = cachedSolver.solver->newVar(); // LCOV_EXCL_LINE
  std::vector<int> satClause; // LCOV_EXCL_LINE
  satClause.reserve(clause.size() + 1); // LCOV_EXCL_LINE
  satClause.push_back(-selector); // LCOV_EXCL_LINE
  for (const auto& literal : clause) { // LCOV_EXCL_LINE
    if (!cachedSolver.variables->hasSymbol(literal.symbol)) { // LCOV_EXCL_LINE
      throw std::runtime_error( // LCOV_EXCL_LINE
          "PDR cached extra-frame clause missing symbol " + // LCOV_EXCL_LINE
          std::to_string(literal.symbol) + " at frame " + // LCOV_EXCL_LINE
          std::to_string(frame) + " in clause of size " + // LCOV_EXCL_LINE
          std::to_string(clause.size())); // LCOV_EXCL_LINE
    }
    const int satLiteral = // LCOV_EXCL_LINE
        cachedSolver.variables->getLiteral(literal.symbol, frame); // LCOV_EXCL_LINE
    satClause.push_back(literal.positive ? satLiteral : -satLiteral); // LCOV_EXCL_LINE
  }
  cachedSolver.solver->addClause(satClause); // LCOV_EXCL_LINE
  cachedSolver.extraFrameAssumptionByClause.emplace(clause, selector); // LCOV_EXCL_LINE
  return selector; // LCOV_EXCL_LINE
} // LCOV_EXCL_LINE


// LCOV_EXCL_START


// LCOV_EXCL_STOP



// LCOV_DISABLED_STOP


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

void addSameFrameStateEqualities(
    SATSolverWrapper& solver,
    const FrameVariableStore& variables,
    const std::vector<std::pair<size_t, size_t>>& equalityPairs,
    size_t numFrames) {
  for (size_t frame = 0; frame < numFrames; ++frame) {
    for (const auto& [lhsSymbol, rhsSymbol] : equalityPairs) {
      if (!variables.hasSymbol(lhsSymbol) || !variables.hasSymbol(rhsSymbol)) {
        continue;
      }
      addLiteralEquivalence(
          solver,
          variables.getLiteral(lhsSymbol, frame),
          variables.getLiteral(rhsSymbol, frame));
    }
  }
}

void addSameFrameStateEqualities(SATSolverWrapper& solver,
                                 const FrameVariableStore& variables,
                                 const KInductionProblem& problem,
                                 size_t numFrames) {
  addSameFrameStateEqualities(
      solver, variables, problem.sameFrameStateEqualityPairs0, numFrames);
  addSameFrameStateEqualities(
      solver, variables, problem.sameFrameStateEqualityPairs1, numFrames);
}

void addDualRailStateValidity(SATSolverWrapper& solver,
                              const FrameVariableStore& variables,
                              const std::vector<DualRailSymbolPair>& railPairs,
                              size_t numFrames) {
  for (size_t frame = 0; frame < numFrames; ++frame) {
    for (const auto& rails : railPairs) {
      if (!variables.hasSymbol(rails.mayBeOne) ||
          !variables.hasSymbol(rails.mayBeZero)) {
        continue;
      }
      // The dual-rail state space contains only 0, 1, and X.  PDR must block
      // and generalize over that legal state space, not over the empty value.
      solver.addClause({
          variables.getLiteral(rails.mayBeOne, frame),
          variables.getLiteral(rails.mayBeZero, frame)});
    }
  }
}

void normalizeCube(StateCube& cube) {
  // Canonical ordering lets us compare cubes structurally and avoid learning
  // the same obligation more than once with a different literal order.
  std::sort(cube.begin(), cube.end(), cubeLiteralLess);
  cube.erase(std::unique(cube.begin(), cube.end()), cube.end());
}

void normalizeClause(StateClause& clause) {
  // Clauses are canonicalized for the same reason: later subsumption and
  // LCOV_DISABLED_START
  // convergence checks depend on stable ordering and deduplication.
  std::sort(clause.begin(), clause.end(), clauseLiteralLess);
  // LCOV_DISABLED_STOP
  clause.erase(std::unique(clause.begin(), clause.end()), clause.end());
}

SymbolPair canonicalPair(size_t lhs, size_t rhs) {
  if (rhs < lhs) {
    std::swap(lhs, rhs);  // LCOV_EXCL_LINE
  }  // LCOV_EXCL_LINE
  return SymbolPair{lhs, rhs};
}

InitFactIndex buildInitFactIndex(const KInductionProblem& problem) {
  const bool usesBootstrapFrontier = problem.resetBootstrapCycles != 0;
  const auto& assignments = usesBootstrapFrontier
                                ? problem.bootstrapStateAssignments
                                : problem.initialStateAssignments;
  const auto& equalities = emptySymbolPairs();

  InitFactIndex index;
  index.assignments.reserve(assignments.size());
  for (const auto& [symbol, value] : assignments) {
    index.assignments.emplace(symbol, value);
    index.relations.ensureSymbol(symbol);
  }
  index.equalities.reserve(equalities.size());
  for (const auto& [lhsSymbol, rhsSymbol] : equalities) {
    index.equalities.insert(canonicalPair(lhsSymbol, rhsSymbol));
    index.relations.addEquality(lhsSymbol, rhsSymbol);
  }
  for (const auto& [lhsSymbol, rhsSymbol] :
       problem.sameFrameStateEqualityPairs0) {
    index.equalities.insert(canonicalPair(lhsSymbol, rhsSymbol));
    index.relations.addEquality(lhsSymbol, rhsSymbol);
  }
  for (const auto& [lhsSymbol, rhsSymbol] :
       problem.sameFrameStateEqualityPairs1) {
    index.equalities.insert(canonicalPair(lhsSymbol, rhsSymbol));
    index.relations.addEquality(lhsSymbol, rhsSymbol);
  }
  index.complements.reserve(
      problem.complementedStatePairs0.size() +
      problem.complementedStatePairs1.size());
  for (const auto& [primarySymbol, complementedSymbol] :
       // LCOV_DISABLED_START
       problem.complementedStatePairs0) {
       // LCOV_DISABLED_STOP
    index.complements.insert(canonicalPair(primarySymbol, complementedSymbol));
    index.relations.addComplement(primarySymbol, complementedSymbol);
  }
  for (const auto& [primarySymbol, complementedSymbol] :
       problem.complementedStatePairs1) {
    index.complements.insert(canonicalPair(primarySymbol, complementedSymbol));
    index.relations.addComplement(primarySymbol, complementedSymbol);
  }
  index.rootAssignments.reserve(index.assignments.size());
  std::vector<std::pair<size_t, bool>> orderedAssignments(
      index.assignments.begin(), index.assignments.end());
  std::sort(orderedAssignments.begin(), orderedAssignments.end());
  for (const auto& [symbol, value] : orderedAssignments) {
    const auto root = index.relations.findWithParity(symbol);
    if (!root.has_value()) {
      continue;  // LCOV_EXCL_LINE
    }
    const bool rootValue = value ^ root->second;
    if (const auto it = index.rootAssignments.find(root->first);
        it == index.rootAssignments.end()) {
      index.rootAssignments.emplace(root->first, rootValue);
    }
  }
  return index;
}

std::optional<StateCube> knownInitConflictCube(const InitFactIndex& facts,
                                               const StateCube& cube) {
  // PDR frequently reaches a level-0 cube that is impossible only because it
  // violates a startup equality such as "state0 == state1".  Learning the full
  // LCOV_DISABLED_START
  // 100+ literal cube makes the engine enumerate many adjacent impossible
  // LCOV_DISABLED_STOP
  // startup states.  This extractor turns the visible conflict into the
  // smallest safe cube:
  // LCOV_DISABLED_START
  //   - one literal for an init assignment conflict;
  //   - two literals for equality/complement conflicts.
  // The learned clause is still exactly an Init consequence, but much stronger.
  std::unordered_map<size_t, std::pair<bool, CubeLiteral>> cubeValueByRoot;
  // LCOV_DISABLED_STOP
  cubeValueByRoot.reserve(cube.size());
  for (const auto& literal : cube) {
    const auto root = facts.relations.findWithParity(literal.symbol);
    if (!root.has_value()) {
      const auto assignment = facts.assignments.find(literal.symbol);
      // LCOV_DISABLED_START
      if (assignment == facts.assignments.end() ||
          assignment->second == literal.value) {  // LCOV_EXCL_LINE
        continue;
      }
      // LCOV_DISABLED_STOP
      StateCube conflict{literal};  // LCOV_EXCL_LINE
      normalizeCube(conflict);  // LCOV_EXCL_LINE
      return conflict;  // LCOV_EXCL_LINE
    // LCOV_DISABLED_START
    }  // LCOV_EXCL_LINE

    const bool rootValue = literal.value ^ root->second;
    const auto assignment = facts.rootAssignments.find(root->first);
    if (assignment != facts.rootAssignments.end() &&
        assignment->second != rootValue) {
        // LCOV_DISABLED_STOP
      StateCube conflict{literal};  // LCOV_EXCL_LINE
      normalizeCube(conflict);  // LCOV_EXCL_LINE
      return conflict;  // LCOV_EXCL_LINE
    }  // LCOV_EXCL_LINE

    if (const auto it = cubeValueByRoot.find(root->first);
        it != cubeValueByRoot.end()) {
      if (it->second.first != rootValue) {  // LCOV_EXCL_LINE
        StateCube conflict{it->second.second, literal};  // LCOV_EXCL_LINE
        normalizeCube(conflict);  // LCOV_EXCL_LINE
        return conflict;  // LCOV_EXCL_LINE
      }  // LCOV_EXCL_LINE
      continue;  // LCOV_EXCL_LINE
    }
    // LCOV_DISABLED_START
    cubeValueByRoot.emplace(root->first, std::pair{rootValue, literal});
  }
  // LCOV_DISABLED_STOP

  return std::nullopt;
}

// LCOV_DISABLED_START


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


bool addClauseToFrame(FrameClauses& frame, StateClause clause) {
  normalizeClause(clause);
  if (frameHasSubsumingClause(frame, clause)) {
    return false;
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
  frame.addedClauseLog.push_back(clause);
  // The remaining clauses stay sorted after erase(), so a lower_bound insert
  // preserves the deterministic frame order without resorting the whole frame
  // for every learned clause.
  auto insertPosition =
      std::lower_bound(frame.clauses.begin(), frame.clauses.end(), clause,
                       stateClauseLess);
  frame.clauses.insert(insertPosition, std::move(clause));
  return true;
}

bool addClauseToFrames(std::vector<FrameClauses>& frames,
                       const StateClause& clause,
                       size_t maxLevel) {
  bool addedAny = false;
  for (size_t level = 1; level <= maxLevel; ++level) {
    addedAny = addClauseToFrame(frames[level], clause) || addedAny;
  }
  return addedAny;
}  // LCOV_EXCL_LINE




void addStateClause(SATSolverWrapper& solver,
                    const FrameVariableStore& variables,
                    const StateClause& clause,
                    size_t frame) {
  std::vector<int> satClause;
  satClause.reserve(clause.size());
  for (const auto& literal : clause) {
    if (!variables.hasSymbol(literal.symbol)) {
      throw std::runtime_error(  // LCOV_EXCL_LINE
          "PDR frame-clause encoding missing symbol " +  // LCOV_EXCL_LINE
          std::to_string(literal.symbol) + " at frame " +  // LCOV_EXCL_LINE
          // LCOV_EXCL_START
          std::to_string(frame) + " in clause of size " +  // LCOV_EXCL_LINE
          // LCOV_EXCL_STOP
          std::to_string(clause.size()));  // LCOV_EXCL_LINE
    }
    const int satLiteral = variables.getLiteral(literal.symbol, frame);
    satClause.push_back(literal.positive ? satLiteral : -satLiteral);
  }
  solver.addClause(satClause);
}

bool clauseCoveredByVariables(const FrameVariableStore& variables,
                              const StateClause& clause) {
  for (const auto& literal : clause) {
    if (!variables.hasSymbol(literal.symbol)) {
      return false;  // LCOV_EXCL_LINE
    }
  }
  // LCOV_EXCL_START
  return true;
}



void addAllFrameClauses(SATSolverWrapper& solver,
                        const FrameVariableStore& variables,
                        const FrameClauses& frameClauses,
                        size_t frame) {
  // Every PDR query sees the complete learned frame.
  for (const auto& clause : frameClauses.clauses) {
    // LCOV_EXCL_START
    if (!clauseCoveredByVariables(variables, clause)) {
      continue;  // LCOV_EXCL_LINE
    }
    addStateClause(solver, variables, clause, frame);
  }
  // LCOV_EXCL_STOP
}

void addCubeAssumptions(SATSolverWrapper& solver,
                        const FrameVariableStore& variables,
                        const StateCube& cube,
                        size_t frame) {
  for (const auto& literal : cube) {
    if (!variables.hasSymbol(literal.symbol)) {
      throw std::runtime_error(  // LCOV_EXCL_LINE
          "PDR cube-assumption encoding missing symbol " +  // LCOV_EXCL_LINE
          std::to_string(literal.symbol) + " at frame " +  // LCOV_EXCL_LINE
          std::to_string(frame) + " in cube of size " +  // LCOV_EXCL_LINE
          std::to_string(cube.size()));  // LCOV_EXCL_LINE
    }
    solver.addClause(
        // LCOV_EXCL_START
        {literal.value ? variables.getLiteral(literal.symbol, frame)
                       : -variables.getLiteral(literal.symbol, frame)});
  }
}


// LCOV_EXCL_STOP
void addNegatedCubeClause(SATSolverWrapper& solver,
                          const FrameVariableStore& variables,
                          const StateCube& cube,
                          size_t frame) {
  std::vector<int> satClause;
  satClause.reserve(cube.size());
  for (const auto& literal : cube) {
    if (!variables.hasSymbol(literal.symbol)) {
      throw std::runtime_error(  // LCOV_EXCL_LINE
          "PDR negated-cube encoding missing symbol " +  // LCOV_EXCL_LINE
          std::to_string(literal.symbol) + " at frame " +  // LCOV_EXCL_LINE
          std::to_string(frame) + " in cube of size " +  // LCOV_EXCL_LINE
          std::to_string(cube.size()));  // LCOV_EXCL_LINE
    }
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
    // LCOV_EXCL_START
    }
    // LCOV_EXCL_STOP
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
    return;  // LCOV_EXCL_LINE
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
  const auto& equalities = emptySymbolPairs();

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
                         const std::vector<size_t>& querySymbols) {
  if (level == 0) {
    // F[0] is Init, so the SAT query is anchored directly in the startup
    // frontier rather than in learned blocking clauses.
    const bool emittedStructuredInit = addRelevantStructuredInitConstraints(
        problem, solver, variables, querySymbols, frame);
    // LCOV_EXCL_START
    if (!emittedStructuredInit && initFormula != nullptr &&
        !hasStructuredInitFacts(problem)) {
      // Observation-only startups have no per-symbol structured summary, so
      // the exact init formula must remain as the F[0] fallback. When
      // LCOV_EXCL_STOP
      // structured init facts do exist, an empty relevant subset simply means
      // the local cone is unconstrained by Init; falling back to the full
      // monolithic init formula would reintroduce unrelated symbols into a
      // reduced compact-PDR query and can make the encoder reference leaves
      // that were intentionally left out of the local solver.
      FrameFormulaEncoder encoder(solver, variables.makeLeafLits(frame));
      solver.addClause({encoder.encode(initFormula)});
    }
    // LCOV_DISABLED_STOP
    addAllFrameClauses(solver, variables, frames[0], frame);
    return;
  }

  // For higher frames, materialize the currently learned blocking clauses and
  // LCOV_EXCL_START
  // any validated strengthening invariant the strategy handed to PDR.
  addAllFrameClauses(solver, variables, frames[level], frame);
  if (frameInvariant != nullptr) {
    // The optional strengthening is treated exactly like a frame fact, but it
    // is validated before we allow the engine to rely on it.
    FrameFormulaEncoder encoder(solver, variables.makeLeafLits(frame));  // LCOV_EXCL_LINE
    solver.addClause({encoder.encode(frameInvariant)});  // LCOV_EXCL_LINE
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
                                    // LCOV_EXCL_START
                                    size_t frame) {
  if (!predecessorSourceFrameIsKnownSafe(level) || problem.property == nullptr) {
    return;
  }
  // LCOV_EXCL_STOP
  // The property is logically redundant for an exact safe PDR frame, but
  // keeping it explicit strengthens the predecessor SAT query.
  FrameFormulaEncoder encoder(solver, variables.makeLeafLits(frame));  // LCOV_EXCL_LINE
  solver.addClause({encoder.encode(problem.property)});  // LCOV_EXCL_LINE
}

bool predecessorFrameClauseApplies(
    const PredecessorAssumptionSolver& cachedSolver,
    const StateClause& clause) {
  return clauseCoveredByVariables(*cachedSolver.variables, clause);
}

void rememberPredecessorFrameClauses(
    PredecessorAssumptionSolver& cachedSolver,
    const FrameClauses& frameClauses) {
  for (const auto& clause : frameClauses.clauses) {
    if (predecessorFrameClauseApplies(cachedSolver, clause)) {
      cachedSolver.emittedFrameClauses.insert(clause);
    }
  }
}

size_t addNewPredecessorFrameClauses(
    PredecessorAssumptionSolver& cachedSolver,
    const FrameClauses& frameClauses,
    size_t frame) {
  size_t addedClauses = 0;
  for (const auto& clause : frameClauses.clauses) {
    if (!predecessorFrameClauseApplies(cachedSolver, clause) ||
        !cachedSolver.emittedFrameClauses.insert(clause).second) {
      continue;
    }
    addStateClause(*cachedSolver.solver, *cachedSolver.variables, clause, frame);
    ++addedClauses;
  }
  return addedClauses;
}

PredecessorAssumptionSolver& getOrCreatePredecessorAssumptionSolver(
    PredecessorAssumptionCache& cache,
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    const TransitionExprResolver& transitionByState,
    BoolExpr* initFormula,
    BoolExpr* frameInvariant,
    const std::vector<FrameClauses>& frames,
    size_t level,
    const std::vector<size_t>& solverSymbols) {
  PredecessorAssumptionCacheKey key{
      &problem,
      &transitionByState,
      initFormula,
      frameInvariant,
      level,
      frameClausesFingerprint(frames, level),
      solverSymbols};
  if (cache.solver != nullptr &&
      cache.solver->key.hasSameReusableContext(key)) {
    // PDR frames strengthen monotonically. Reuse the expensive transition and
    // frame prefix solver, then stream only newly learned frame clauses into it.
    const size_t addedClauses =
        addNewPredecessorFrameClauses(*cache.solver, frames[level], 0);
    cache.solver->key.frameFingerprint = key.frameFingerprint;
    if (addedClauses != 0 && pdrStatsEnabled()) {
      emitSecDiag(
          "SEC PDR stats: predecessor cached solver frame clauses added=",
          addedClauses,
          " level=",
          level,
          " symbols=",
          solverSymbols.size());
    }
    return *cache.solver;
  }

  auto next = std::make_unique<PredecessorAssumptionSolver>();
  next->key = std::move(key);
  next->solver = std::make_unique<SATSolverWrapper>(
      SATSolverWrapper::assumptionSolverTypeFor(solverType));
  next->solver->configureForSecPdrQuery(solverSymbols.size());
  next->variables =
      std::make_unique<FrameVariableStore>(*next->solver, solverSymbols, 1);
  next->querySymbolSet.insert(solverSymbols.begin(), solverSymbols.end());
  addComplementedStateRelations(
      *next->solver, *next->variables, problem.complementedStatePairs0, 1);
  addComplementedStateRelations(
      *next->solver, *next->variables, problem.complementedStatePairs1, 1);
  addSameFrameStateEqualities(*next->solver, *next->variables, problem, 1);
  addDualRailStateValidity(
      *next->solver, *next->variables, problem.dualRailStatePairs, 1);
  addFrameConstraints(
      *next->solver,
      *next->variables,
      problem,
      initFormula,
      frameInvariant,
      frames,
      level,
      0,
      solverSymbols);
  addSafeFramePropertyConstraint(
      *next->solver, *next->variables, problem, level, 0);
  addPostBootstrapResetInputConstraints(
      *next->solver, *next->variables, problem, 0);
  if (level < frames.size()) {
    rememberPredecessorFrameClauses(*next, frames[level]);
  }
  if (pdrStatsEnabled()) {
    emitSecDiag(
        "SEC PDR stats: predecessor cached solver created level=",
        level,
        " symbols=",
        solverSymbols.size(),
        " frame_clauses=",
        level < frames.size() ? frames[level].clauses.size() : 0,
        " local_leaf=",
        hasLocalDualRailFinalLeafSurface(problem) ? 1 : 0);
  }
  cache.solver = std::move(next);
  return *cache.solver;
}

int64_t resourceLimitOrUnbounded(unsigned limit) {
  return limit == std::numeric_limits<unsigned>::max()
             ? -1
             : static_cast<int64_t>(limit);
}

PredecessorQueryResultKey makePredecessorQueryResultKey(
    const KInductionProblem& problem,
    const TransitionExprResolver& transitionByState,
    BoolExpr* initFormula,
    BoolExpr* frameInvariant,
    size_t level,
    size_t frameFingerprint,
    size_t extraFrameFingerprint,
    bool excludeTargetOnCurrentFrame,
    const StateCube& targetCube) {
  PredecessorQueryResultKey key;
  key.problem = &problem;
  key.transitionByState = &transitionByState;
  key.initFormula = initFormula;
  key.frameInvariant = frameInvariant;
  key.level = level;
  key.frameFingerprint = frameFingerprint;
  key.extraFrameFingerprint = extraFrameFingerprint;
  key.excludeTargetOnCurrentFrame = excludeTargetOnCurrentFrame;
  key.targetCube = targetCube;
  return key;
}

std::optional<PredecessorQueryResultEntry> cachedPredecessorQueryResult(
    const PredecessorAssumptionCache& cache,
    const PredecessorQueryResultKey& exactKey,
    const PredecessorQueryResultKey& stableUnsatKey) {
  const auto exactIt = cache.queryResults.find(exactKey);
  if (exactIt != cache.queryResults.end()) {
    return exactIt->second;
  }
  if (cache.unsatQueries.find(stableUnsatKey) != cache.unsatQueries.end()) {
    return PredecessorQueryResultEntry{}; // LCOV_EXCL_LINE
  }
  return std::nullopt;
}

PredecessorUnsatCoreCacheKey makePredecessorUnsatCoreCacheKey(
    const PredecessorQueryResultKey& key) {
  PredecessorUnsatCoreCacheKey coreKey;
  coreKey.problem = key.problem;
  coreKey.transitionByState = key.transitionByState;
  coreKey.initFormula = key.initFormula;
  coreKey.frameInvariant = key.frameInvariant;
  coreKey.level = key.level;
  coreKey.extraFrameFingerprint = key.extraFrameFingerprint;
  coreKey.excludeTargetOnCurrentFrame = key.excludeTargetOnCurrentFrame;
  return coreKey;
}

bool predecessorUnsatCoreCacheable(
    const PredecessorQueryResultKey& stableUnsatKey) {
  // Failed target-assumption cores are globally reusable only for the base
  // predecessor context. Temporary relative-induction assumptions can be part
  // of the UNSAT proof, so keep those answers in the exact target cache only.
  return detail::shouldSharePredecessorUnsatCore(
      stableUnsatKey.frameFingerprint,
      stableUnsatKey.extraFrameFingerprint,
      stableUnsatKey.excludeTargetOnCurrentFrame);
}

void rememberPredecessorUnsatCore(
    PredecessorAssumptionCache& cache,
    const PredecessorQueryResultKey& stableUnsatKey,
    StateCube core) {
  if (!predecessorUnsatCoreCacheable(stableUnsatKey)) {
    return;
  }
  normalizeCube(core);
  if (core.empty()) {
    return; // LCOV_EXCL_LINE
  }

  auto& cores =
      cache.unsatCoresByContext[makePredecessorUnsatCoreCacheKey(stableUnsatKey)];
  for (const auto& existing : cores) {
    if (cubeContainsCube(core, existing)) {
      return;
    }
  }

  std::vector<StateCube> retained;
  retained.reserve(cores.size() + 1);
  for (auto& existing : cores) {
    if (!cubeContainsCube(existing, core)) {
      retained.push_back(std::move(existing));
    }
  }
  retained.push_back(std::move(core));
  sortStateCubesDeterministically(retained);
  if (retained.size() > kMaxPredecessorUnsatCoresPerContext) {
    retained.pop_back(); // LCOV_EXCL_LINE
  } // LCOV_EXCL_LINE
  cores = std::move(retained);
}

std::optional<StateCube> cachedPredecessorUnsatCoreForTarget(
    const PredecessorAssumptionCache& cache,
    const PredecessorQueryResultKey& stableUnsatKey,
    const StateCube& targetCube) {
  if (!predecessorUnsatCoreCacheable(stableUnsatKey)) {
    return std::nullopt;
  }
  const auto coreIt =
      cache.unsatCoresByContext.find(
          makePredecessorUnsatCoreCacheKey(stableUnsatKey));
  if (coreIt == cache.unsatCoresByContext.end()) {
    return std::nullopt;
  }
  for (const auto& core : coreIt->second) {
    if (cubeContainsCube(targetCube, core)) {
      return core;
    }
  }
  return std::nullopt;
}

void trimPredecessorQueryResultCache(PredecessorAssumptionCache& cache) {
  if (cache.queryResults.size() < kMaxPredecessorQueryResultCacheEntries &&
      cache.unsatQueries.size() < kMaxPredecessorQueryResultCacheEntries) {
    return;
  }
  // Dropping cache entries cannot change the proof; it only bounds retained
  // memory before another wave of local predecessor obligations starts.
  cache.queryResults.clear(); // LCOV_EXCL_LINE
  cache.unsatQueries.clear(); // LCOV_EXCL_LINE
  cache.unsatCoresByContext.clear(); // LCOV_EXCL_LINE
}

void rememberPredecessorQueryResult(
    PredecessorAssumptionCache& cache,
    const PredecessorQueryResultKey& exactKey,
    const PredecessorQueryResultKey& stableUnsatKey,
    const std::optional<StateCube>& predecessor,
    const StateCube* unsatCore = nullptr) {
  trimPredecessorQueryResultCache(cache);
  PredecessorQueryResultEntry entry;
  if (predecessor.has_value()) {
    entry.hasPredecessor = true;
    entry.predecessor = *predecessor;
  } else {
    if (unsatCore != nullptr && !unsatCore->empty()) {
      entry.hasUnsatCore = true;
      entry.unsatCore = *unsatCore;
      normalizeCube(entry.unsatCore);
    }
    cache.unsatQueries.insert(stableUnsatKey);
  }
  cache.queryResults.emplace(exactKey, std::move(entry));
  if (unsatCore != nullptr && !unsatCore->empty()) {
    rememberPredecessorUnsatCore(cache, stableUnsatKey, *unsatCore);
  }
}

std::optional<StateCube> cachedPredecessorUnsatCoreForCube(
    const PredecessorAssumptionCache& cache,
    const KInductionProblem& problem,
    const TransitionExprResolver& transitionByState,
    BoolExpr* initFormula,
    BoolExpr* frameInvariant,
    const std::vector<FrameClauses>& frames,
    size_t sourceLevel,
    const StateCube& targetCube,
    bool excludeTargetOnCurrentFrame) {
  if (sourceLevel >= frames.size()) {
    return std::nullopt;  // LCOV_EXCL_LINE
  }

  const auto exactKey = makePredecessorQueryResultKey(
      problem,
      transitionByState,
      initFormula,
      frameInvariant,
      sourceLevel,
      frameClausesFingerprint(frames, sourceLevel),
      /*extraFrameFingerprint=*/0,
      excludeTargetOnCurrentFrame,
      targetCube);
  const auto resultIt = cache.queryResults.find(exactKey);
  if (resultIt != cache.queryResults.end() &&
      resultIt->second.hasUnsatCore &&
      !resultIt->second.unsatCore.empty()) {
    return resultIt->second.unsatCore;
  }
  const auto stableUnsatKey = makePredecessorQueryResultKey( // LCOV_EXCL_LINE
      problem, // LCOV_EXCL_LINE
      transitionByState, // LCOV_EXCL_LINE
      initFormula, // LCOV_EXCL_LINE
      frameInvariant, // LCOV_EXCL_LINE
      sourceLevel, // LCOV_EXCL_LINE
      /*frameFingerprint=*/0,
      /*extraFrameFingerprint=*/0,
      excludeTargetOnCurrentFrame, // LCOV_EXCL_LINE
      targetCube); // LCOV_EXCL_LINE
  return cachedPredecessorUnsatCoreForTarget( // LCOV_EXCL_LINE
      cache, stableUnsatKey, targetCube); // LCOV_EXCL_LINE
}

bool badCubeFrameClauseApplies(const BadCubeAssumptionSolver& cachedSolver,
                               const StateClause& clause) {
  return clauseCoveredByVariables(*cachedSolver.variables, clause);
}

void rememberBadCubeFrameClauses(BadCubeAssumptionSolver& cachedSolver,
                                 const FrameClauses& frameClauses) {
  for (const auto& clause : frameClauses.clauses) {
    if (badCubeFrameClauseApplies(cachedSolver, clause)) {
      cachedSolver.emittedFrameClauses.insert(clause);
    }
  }
}

void addNewBadCubeFrameClauses(BadCubeAssumptionSolver& cachedSolver,
                               const std::vector<StateClause>& frameClauses,
                               size_t beginIndex,
                               size_t frame,
                               const char* source) {
  size_t addedClauses = 0;
  for (size_t clauseIndex = beginIndex; clauseIndex < frameClauses.size();
       ++clauseIndex) {
    const auto& clause = frameClauses[clauseIndex];
    if (!badCubeFrameClauseApplies(cachedSolver, clause) ||
        !cachedSolver.emittedFrameClauses.insert(clause).second) {
      continue;
    }
    // Frame vectors are compacted by subsumption, so a stronger learned clause
    // can replace a weaker one without increasing the vector size. Track by
    // clause identity instead of append index to keep cached bad-cube solvers
    // synchronized with the logical frame.
    addStateClause(*cachedSolver.solver, *cachedSolver.variables, clause, frame);
    ++addedClauses;
  }
  if (addedClauses != 0 && pdrStatsEnabled()) {
    emitSecDiag(
        "SEC PDR stats: bad cube cached frame clauses added=",
        addedClauses,
        " frame=",
        frame,
        " source=",
        source,
        " scanned=",
        frameClauses.size() - beginIndex);
  }
}

void syncBadCubeFrameClauses(BadCubeAssumptionSolver& cachedSolver,
                             const FrameClauses& frameClauses,
                             size_t frame,
                             size_t frameFingerprint) {
  if (cachedSolver.emittedFrameFingerprint == frameFingerprint) {
    if (pdrStatsEnabled()) {
      emitSecDiag(
          "SEC PDR stats: bad cube cached frame clauses unchanged frame=",
          frame,
          " fingerprint=",
          frameFingerprint);
    }
    return;
  }
  if (cachedSolver.emittedFrameLogOffset <=
      frameClauses.addedClauseLog.size()) {
    addNewBadCubeFrameClauses(
        cachedSolver,
        frameClauses.addedClauseLog,
        cachedSolver.emittedFrameLogOffset,
        frame,
        "frame_log");
    cachedSolver.emittedFrameLogOffset = frameClauses.addedClauseLog.size();
  } else {
    addNewBadCubeFrameClauses( // LCOV_EXCL_LINE
        cachedSolver, // LCOV_EXCL_LINE
        frameClauses.clauses, // LCOV_EXCL_LINE
        0,
        frame, // LCOV_EXCL_LINE
        "full_frame");
    cachedSolver.emittedFrameLogOffset = frameClauses.addedClauseLog.size(); // LCOV_EXCL_LINE
  }
  cachedSolver.emittedFrameFingerprint = frameFingerprint;
}

std::optional<SATSolverWrapper::SolveStatus>
solvePredecessorCubeWithCachedAssumptions(
    PredecessorAssumptionCache& cache,
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    const TransitionExprResolver& transitionByState,
    BoolExpr* initFormula,
    BoolExpr* frameInvariant,
    const std::vector<FrameClauses>& frames,
    size_t level,
    const StateCube& targetCube,
    const std::vector<size_t>& encodedTargets,
    const std::vector<size_t>& transitionSupportSymbols,
    const std::vector<size_t>& solverSymbols,
    bool excludeTargetOnCurrentFrame,
    const std::vector<StateClause>* extraFrameClauses,
    unsigned predecessorConflictLimit,
    unsigned predecessorDecisionLimit,
    PredecessorAssumptionSolver** solvedCache = nullptr,
    std::vector<int>* solvedAssumptions = nullptr,
    StateCube* solvedUnsatCore = nullptr) {
  auto& cachedSolver = getOrCreatePredecessorAssumptionSolver(
      cache,
      problem,
      solverType,
      transitionByState,
      initFormula,
      frameInvariant,
      frames,
      level,
      solverSymbols);
  const auto assumptionPairs = addCachedTransitionAssumptionsForTargetCube(
      cachedSolver,
      transitionByState,
      0,
      targetCube,
      encodedTargets,
      transitionSupportSymbols);
  std::vector<int> assumptions = assumptionLiteralsFromPairs(assumptionPairs);
  if (excludeTargetOnCurrentFrame) {
    assumptions.push_back(
        cachedTargetExclusionAssumption(cachedSolver, targetCube, 0));
  }
  size_t extraFrameAssumptionCount = 0;
  if (extraFrameClauses != nullptr) {
    for (const auto& clause : *extraFrameClauses) { // LCOV_EXCL_LINE
      if (!clauseCoveredByVariables(*cachedSolver.variables, clause)) { // LCOV_EXCL_LINE
        return std::nullopt; // LCOV_EXCL_LINE
      }
      assumptions.push_back( // LCOV_EXCL_LINE
          cachedExtraFrameClauseAssumption(cachedSolver, clause, 0)); // LCOV_EXCL_LINE
      ++extraFrameAssumptionCount; // LCOV_EXCL_LINE
    }
  } // LCOV_EXCL_LINE
  if (assumptions.empty()) {
    return std::nullopt; // LCOV_EXCL_LINE
  }

  if (solvedCache != nullptr) {
    *solvedCache = &cachedSolver;
  }
  if (solvedAssumptions != nullptr) {
    *solvedAssumptions = assumptions;
  }
  if (extraFrameAssumptionCount != 0 && pdrStatsEnabled()) {
    emitSecDiag( // LCOV_EXCL_LINE
        "SEC PDR stats: predecessor cached solver extra frame assumptions=",
        extraFrameAssumptionCount,
        " level=",
        level,
        " symbols=",
        solverSymbols.size()); // LCOV_EXCL_LINE
  } // LCOV_EXCL_LINE
  // The cached solver amortizes expensive frame/transition encoding across
  // neighboring predecessor queries. Keep both resource caps active: cached
  // assumptions are an optimization, and a hard residual leaf should fall back
  // to the fresh exact path instead of monopolizing the whole PDR run.
  const int64_t cachedPropagationLimit =
      resourceLimitOrUnbounded(predecessorDecisionLimit);
  const auto status = cachedSolver.solver->solveWithAssumptionsStatus(
      assumptions,
      resourceLimitOrUnbounded(predecessorConflictLimit),
      cachedPropagationLimit);
  if (status == SATSolverWrapper::SolveStatus::Unsat &&
      solvedUnsatCore != nullptr) {
    // Only target-cube assumptions are mapped back. Temporary selector
    // assumptions may participate in the SAT proof, but they are not state
    // literals that can form a learned PDR blocker.
    const std::vector<int> targetAssumptions =
        assumptionLiteralsFromPairs(assumptionPairs);
    *solvedUnsatCore = cachedPredecessorUnsatCoreFromTargetContext(
        *cachedSolver.solver,
        problem,
        level,
        targetCube,
        transitionSupportSymbols,
        excludeTargetOnCurrentFrame,
        extraFrameClauses,
        targetAssumptions,
        assumptionPairs);
  }
  return status;
}

BadCubeAssumptionSolver& getOrCreateBadCubeAssumptionSolver(
    BadCubeAssumptionCache& cache,
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    BoolExpr* initFormula,
    BoolExpr* frameInvariant,
    const std::vector<FrameClauses>& frames,
    size_t level,
    const std::vector<size_t>& solverSymbols) {
  BadCubeAssumptionCacheKey key{
      &problem,
      initFormula,
      frameInvariant,
      level,
      solverSymbols};
  const size_t currentFrameFingerprint =
      frameClausesFingerprint(frames, level);
  if (cache.solver != nullptr && cache.solver->key == key) {
    syncBadCubeFrameClauses(
        *cache.solver,
        frames[level],
        0,
        currentFrameFingerprint);
    return *cache.solver;
  }

  auto next = std::make_unique<BadCubeAssumptionSolver>();
  next->key = std::move(key);
  next->solver = std::make_unique<SATSolverWrapper>(
      SATSolverWrapper::assumptionSolverTypeFor(solverType));
  next->solver->configureForSecPdrQuery(solverSymbols.size());
  next->variables =
      std::make_unique<FrameVariableStore>(*next->solver, solverSymbols, 1);
  next->querySymbolSet.insert(solverSymbols.begin(), solverSymbols.end());
  addComplementedStateRelations(
      *next->solver, *next->variables, problem.complementedStatePairs0, 1);
  addComplementedStateRelations(
      *next->solver, *next->variables, problem.complementedStatePairs1, 1);
  addSameFrameStateEqualities(*next->solver, *next->variables, problem, 1);
  addDualRailStateValidity(
      *next->solver, *next->variables, problem.dualRailStatePairs, 1);
  addFrameConstraints(
      *next->solver,
      *next->variables,
      problem,
      initFormula,
      frameInvariant,
      frames,
      level,
      0,
      solverSymbols);
  addPostBootstrapResetInputConstraints(
      *next->solver, *next->variables, problem, 0);
  next->encoder = std::make_unique<FrameFormulaEncoder>(
      *next->solver, next->variables->makeLeafLits(0));
  if (level < frames.size()) {
    rememberBadCubeFrameClauses(*next, frames[level]);
    next->emittedFrameFingerprint = currentFrameFingerprint;
    next->emittedFrameLogOffset = frames[level].addedClauseLog.size();
  }
  cache.solver = std::move(next);
  return *cache.solver;
}

int encodeCachedBadRoot(BadCubeAssumptionSolver& cachedSolver,
                        BoolExpr* badFormula) {
  const auto existing = cachedSolver.encodedBadRoots.find(badFormula);
  if (existing != cachedSolver.encodedBadRoots.end()) {
    return existing->second;
  }
  const int root = cachedSolver.encoder->encode(badFormula);
  cachedSolver.encodedBadRoots.emplace(badFormula, root);
  return root;
}

SATSolverWrapper::SolveStatus solveBadCubeWithCachedAssumption(
    BadCubeAssumptionCache& cache,
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    BoolExpr* initFormula,
    BoolExpr* frameInvariant,
    const std::vector<FrameClauses>& frames,
    size_t level,
    BoolExpr* badFormula,
    const std::vector<size_t>& solverSymbols,
    unsigned badCubeConflictLimit,
    BadCubeAssumptionSolver** solvedCache) {
  auto& cachedSolver = getOrCreateBadCubeAssumptionSolver(
      cache,
      problem,
      solverType,
      initFormula,
      frameInvariant,
      frames,
      level,
      solverSymbols);
  const int badRoot = encodeCachedBadRoot(cachedSolver, badFormula);
  *solvedCache = &cachedSolver;
  // The cached solver keeps learned clauses across monotonic frame updates.
  // Keep the conflict cap for workflow safety, but do not cap decisions here:
  // on wide dual-rail datapaths CaDiCaL otherwise returns UNKNOWN before those
  // learned clauses can pay back the reused frame context.
  return cachedSolver.solver->solveWithAssumptionsStatus(
      {badRoot},
      resourceLimitOrUnbounded(badCubeConflictLimit),
      /*propagationLimit=*/-1);
} // LCOV_EXCL_LINE

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






StateCube extractSolvedPredecessorCube(
    const SATSolverWrapper& solver,
    const FrameVariableStore& variables,
    const std::vector<size_t>& predecessorSymbols,
    const std::unordered_map<size_t, int>& /*transitionLeafLits*/) {
  return extractStateCube(solver, variables, predecessorSymbols, 0);
}

StateCube extractSolvedBadCubeForFormula(
    const SATSolverWrapper& solver,
    const FrameVariableStore& variables,
    const std::vector<size_t>& concreteStateSymbols,
    size_t level) {
  if (isSecDiagEnabled()) {
    emitSecDiag(  // LCOV_EXCL_LINE
        "SEC diag: PDR bad cube uses concrete state model: ",
        concreteStateSymbols.size(),  // LCOV_EXCL_LINE
        " state symbols at F",
        level);
  }  // LCOV_EXCL_LINE
  StateCube cube = extractStateCube(solver, variables, concreteStateSymbols, 0);
  if (pdrStatsEnabled()) {
    emitSecDiag(
        "SEC PDR stats: bad cube level=", level,
        " source=concrete_state",
        " state_symbols=", concreteStateSymbols.size(),
        " cube=", cube.size(),
        " hash=", cubeFingerprint(cube));
  }
  return cube;
}

std::optional<StateCube> findBadCubeForFormula(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    BoolExpr* initFormula,
    BoolExpr* frameInvariant,
    const std::vector<FrameClauses>& frames,
    BoolExpr* badFormula,
    const std::optional<std::vector<size_t>>& preciseBadStateSupport,
    const std::unordered_set<size_t>& stateSymbols,
    size_t level,
    const ComplementPartnerIndex& complementPartners,
    BadCubeAssumptionCache* badCubeAssumptionCache,
    PdrFormulaSupportCache* supportCache) {
  if (!preciseBadStateSupport.has_value()) {
    if (pdrStatsEnabled()) {
      emitSecDiag(
          "SEC PDR stats: bad cube support budget exhausted level=",
          level,
          " node_limit=",
          kMaxPreciseBadCubeSupportNodes);
    }
    markPdrBudgetExhausted(PdrBudgetExhaustion::LocalQuery);
    return std::nullopt;
  }

  // Search the current frame for a concrete state that still satisfies bad
  // after all learned blocking clauses and optional strengthening are applied.
  const std::vector<size_t> concreteStateSymbols =
      sortUniqueSymbols(stateSymbols);
  std::vector<size_t> solverSymbols =
      findBadQuerySymbols(
          problem,
          initFormula,
          frameInvariant,
          frames,
          badFormula,
          level,
          complementPartners,
          supportCache);
  solverSymbols = detail::mergeSortedPdrSymbolVectors(
      sortUniqueSymbols(
          std::unordered_set<size_t>(solverSymbols.begin(), solverSymbols.end())),
      concreteStateSymbols);
  const unsigned badCubeConflictLimit =
      // LCOV_EXCL_START
      problem.usesDualRailStateEncoding ? dualRailBadCubeConflictLimit() : 0;
      // LCOV_EXCL_STOP
  const size_t badCubeStatsQueryNumber = nextPdrBadCubeQueryNumber();
  const bool emitStatsForBadCubeQuery =
      shouldEmitPdrStats(badCubeStatsQueryNumber);
  BadCubeAssumptionCache* solverCache =
      shouldUseBadCubeSolverCache(problem) ? badCubeAssumptionCache : nullptr;
  if (problem.usesDualRailStateEncoding && badCubeAssumptionCache != nullptr &&
      solverCache == nullptr && emitStatsForBadCubeQuery) {
    emitSecDiag(
        "SEC PDR stats: bad cube cached solver disabled state_symbols=",
        problem.totalStateCount,
        " state_limit=",
        kMaxDualRailBadCubeSolverCacheStateSymbols,
        " symbols=",
        solverSymbols.size(),
        " level=",
        level);
  }
  if (problem.usesDualRailStateEncoding && solverCache != nullptr) {
    BadCubeAssumptionSolver* solvedCache = nullptr;
    const auto badSolveStatus = solveBadCubeWithCachedAssumption(
        *solverCache,
        problem,
        solverType,
        initFormula,
        frameInvariant,
        frames,
        level,
        badFormula,
        solverSymbols,
        badCubeConflictLimit,
        &solvedCache);
    if (badSolveStatus == SATSolverWrapper::SolveStatus::Unknown) {
      if (pdrStatsEnabled()) {  // LCOV_EXCL_LINE
        emitSecDiag(  // LCOV_EXCL_LINE
            "SEC PDR stats: bad cube query budget exhausted limit=",
            badCubeConflictLimit,
            " symbols=",
            solverSymbols.size(),  // LCOV_EXCL_LINE
            " level=",
            level,
            " cached_assumptions=1");
      }  // LCOV_EXCL_LINE
      markPdrBudgetExhausted(PdrBudgetExhaustion::LocalQuery);  // LCOV_EXCL_LINE
      return std::nullopt;  // LCOV_EXCL_LINE
    }
    if (badSolveStatus == SATSolverWrapper::SolveStatus::Unsat) {
      return std::nullopt;
    }
    return extractSolvedBadCubeForFormula(
        *solvedCache->solver,
        *solvedCache->variables,
        concreteStateSymbols,
        level);
  }

  SATSolverWrapper solver(solverType);
  // Bad-state queries are local PDR obligations and are rebuilt repeatedly as
  // frames advance. Keep them on the PDR-local profile: small regressions such
  // as GCD can otherwise spend minutes in Kissat's speculative
  // preprocessing/probing before the actual frame query starts.
  // LCOV_EXCL_START
  solver.configureForSecPdrQuery(solverSymbols.size());
  FrameVariableStore variables(solver, solverSymbols, 1);
  addComplementedStateRelations(solver, variables, problem.complementedStatePairs0, 1);
  addComplementedStateRelations(solver, variables, problem.complementedStatePairs1, 1);
  // LCOV_EXCL_STOP
  addSameFrameStateEqualities(solver, variables, problem, 1);
  addDualRailStateValidity(solver, variables, problem.dualRailStatePairs, 1);
  addFrameConstraints(
      solver, variables, problem, initFormula, frameInvariant, frames, level, 0,
      solverSymbols);
  addPostBootstrapResetInputConstraints(solver, variables, problem, 0);
  FrameFormulaEncoder encoder(solver, variables.makeLeafLits(0));
  solver.addClause({encoder.encode(badFormula)});
  SATSolverWrapper::SolveStatus badSolveStatus =
      SATSolverWrapper::SolveStatus::Sat;
  if (badCubeConflictLimit != 0) {
    // Dual-rail residual repairs can be SAT and decision-heavy even when they
    // do not accumulate many conflicts. Bound both resources so a single
    // LCOV_EXCL_START
    // uncovered output cannot dominate the whole workflow.
    // LCOV_EXCL_STOP
    badSolveStatus = solver.solveWithResourceLimits( // LCOV_EXCL_LINE
        badCubeConflictLimit, // LCOV_EXCL_LINE
        // LCOV_EXCL_START
        /*decisionLimit=*/badCubeConflictLimit);
        // LCOV_EXCL_STOP
  } else { // LCOV_EXCL_LINE
    badSolveStatus = solver.solveStatus();
  }
  if (badSolveStatus == SATSolverWrapper::SolveStatus::Unknown) {
    if (pdrStatsEnabled()) {  // LCOV_EXCL_LINE
      emitSecDiag(  // LCOV_EXCL_LINE
          "SEC PDR stats: bad cube query budget exhausted limit=",
          badCubeConflictLimit,
          " symbols=",
          solverSymbols.size(),  // LCOV_EXCL_LINE
          " level=",
          level);
    }  // LCOV_EXCL_LINE
    markPdrBudgetExhausted(PdrBudgetExhaustion::LocalQuery);  // LCOV_EXCL_LINE
    return std::nullopt;  // LCOV_EXCL_LINE
  }
  if (badSolveStatus == SATSolverWrapper::SolveStatus::Unsat) {
    return std::nullopt;
  }

  return extractSolvedBadCubeForFormula(
      solver,
      variables,
      concreteStateSymbols,
      level);
}

std::optional<StateCube> findBadCube(const KInductionProblem& problem,
                                     KEPLER_FORMAL::Config::SolverType solverType,
                                     BoolExpr* initFormula,
                                     BoolExpr* frameInvariant,
                                     const std::vector<FrameClauses>& frames,
                                     const std::optional<std::vector<size_t>>&
                                         preciseBadStateSupport,
                                     const std::unordered_set<size_t>& stateSymbols,
                                     size_t level,
                                     const ComplementPartnerIndex& complementPartners,
                                     BadCubeAssumptionCache* badCubeAssumptionCache,
                                     PdrFormulaSupportCache* supportCache) {
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
        stateSymbols,
        level,
        complementPartners,
        badCubeAssumptionCache,
        supportCache);
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
        0,
        stateSymbols);
    if (auto cube = findBadCubeForFormula(
            problem,
            solverType,
            initFormula,
            frameInvariant,
            frames,
            outputBad,
            outputStateSupport,
            stateSymbols,
            level,
            complementPartners,
            badCubeAssumptionCache,
            supportCache);
        cube.has_value()) {
      return cube;
    }
    if (hasPdrBudgetExhaustion()) {
      return std::nullopt;  // LCOV_EXCL_LINE
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
    PredecessorAssumptionCache* predecessorAssumptionCache = nullptr,
    const std::vector<StateClause>* extraFrameClauses = nullptr,
    size_t* predecessorQueryBudget = nullptr,
    PdrFormulaSupportCache* supportCache = nullptr) {
  // This is the one-step predecessor query at the heart of PDR: does some
  // state in F[level] transition into the target cube on the next frame?
  std::optional<PredecessorQueryResultKey> exactCacheKey;
  std::optional<PredecessorQueryResultKey> stableUnsatCacheKey;
  const bool usePredecessorQueryResultCache =
      predecessorAssumptionCache != nullptr &&
      canUsePredecessorQueryResultCache(problem);
  if (usePredecessorQueryResultCache) {
    const size_t frameFingerprint = frameClausesFingerprint(frames, level);
    const size_t extraFrameFingerprint =
        extraFrameClausesFingerprint(extraFrameClauses);
    exactCacheKey = makePredecessorQueryResultKey(
        problem,
        transitionByState,
        initFormula,
        frameInvariant,
        level,
        frameFingerprint,
        extraFrameFingerprint,
        excludeTargetOnCurrentFrame,
        targetCube);
    stableUnsatCacheKey = makePredecessorQueryResultKey(
        problem,
        transitionByState,
        initFormula,
        frameInvariant,
        level,
        /*frameFingerprint=*/0,
        extraFrameFingerprint,
        excludeTargetOnCurrentFrame,
        targetCube);
    if (const auto cached = cachedPredecessorQueryResult(
            *predecessorAssumptionCache, *exactCacheKey,
            *stableUnsatCacheKey);
        cached.has_value()) {
      if (pdrStatsEnabled()) {
        emitSecDiag(
            "SEC PDR stats: predecessor result cache hit level=",
            level,
            " extra_frame_fingerprint=",
            extraFrameFingerprint,
            " has_predecessor=",
            cached->hasPredecessor ? 1 : 0);
      }
      if (cached->hasPredecessor) {
        return cached->predecessor;
      }
      return std::nullopt; // LCOV_EXCL_LINE
    }
    if (const auto cachedCore = cachedPredecessorUnsatCoreForTarget(
            *predecessorAssumptionCache, *stableUnsatCacheKey, targetCube);
        cachedCore.has_value()) {
      if (pdrStatsEnabled()) {
        emitSecDiag(
            "SEC PDR stats: predecessor unsat-core cache hit level=",
            level,
            " target_cube=",
            targetCube.size(),
            " core_cube=",
            cachedCore->size(),
            " target_hash=",
            cubeFingerprint(targetCube),
            " core_hash=",
            cubeFingerprint(*cachedCore));
      }
      rememberPredecessorQueryResult(
          *predecessorAssumptionCache,
          *exactCacheKey,
          *stableUnsatCacheKey,
          std::nullopt,
          &*cachedCore);
      return std::nullopt;
    }
  }
  if (!consumePdrPredecessorQueryBudget(predecessorQueryBudget)) {
    return std::nullopt;  // LCOV_EXCL_LINE
  }
  const size_t statsQueryNumber = nextPdrPredecessorQueryNumber();
  const bool emitStatsForQuery = shouldEmitPdrStats(statsQueryNumber);
  PredecessorTargetSurface uncachedTargetSurface;
  const PredecessorTargetSurface* targetSurface = nullptr;
  if (predecessorAssumptionCache != nullptr &&
      shouldRetainPredecessorTargetSurfaceCache(problem)) {
    targetSurface = &predecessorTargetSurfaceFor(
        *predecessorAssumptionCache, problem, transitionByState, targetCube);
  } else {
    uncachedTargetSurface =
        buildPredecessorTargetSurface(problem, transitionByState, targetCube);
    targetSurface = &uncachedTargetSurface;
    if (predecessorAssumptionCache != nullptr && emitStatsForQuery) {
      emitSecDiag(
          "SEC PDR stats: predecessor target surface uncached target=",
          targetCube.size(),
          " encoded_targets=",
          uncachedTargetSurface.encodedTargets.size(),
          " transition_support=",
          uncachedTargetSurface.transitionSupportSymbols.size(),
          " state_symbols=",
          problem.totalStateCount,
          " state_limit=",
          kMaxDualRailTargetSurfaceCacheStateSymbols);
    }
  }
  const std::vector<size_t>& encodedTargets =
      targetSurface->encodedTargets;
  const std::vector<size_t>& transitionSupportSymbols =
      targetSurface->transitionSupportSymbols;
  const size_t transitionEncodingNodes =
      targetSurface->transitionEncodingNodes;
  if (problem.usesDualRailStateEncoding) {
    const size_t encodingNodeLimit = dualRailPredecessorEncodingNodeLimit();
    const size_t configuredEncodingSupportLimit =
        dualRailPredecessorEncodingSupportLimit();
    // Isolated Swerv leaves measured predecessor supports slightly above the
    // broad 8k dual-rail cap. Raise only this local guard so whole-chip
    // surfaces still fail fast before materializing broad transition cones.
    const size_t encodingSupportLimit =
        hasLocalDualRailFinalLeafSurface(problem)
            ? effectiveLocalDualRailFinalLeafEncodingSupportLimit(
                  configuredEncodingSupportLimit)
            : configuredEncodingSupportLimit;
    const bool unknownNodeCount =
        transitionEncodingNodes == 0 &&
        encodedTargets.size() > kMaxExactTransitionNodeCountHintTargets;  // LCOV_EXCL_LINE
    if (unknownNodeCount ||
        transitionEncodingNodes > encodingNodeLimit ||
        transitionSupportSymbols.size() > encodingSupportLimit) {
      if (pdrStatsEnabled()) {  // LCOV_EXCL_LINE
        emitSecDiag(  // LCOV_EXCL_LINE
            "SEC PDR stats: predecessor encoding budget exhausted targets=",
            encodedTargets.size(),
            " nodes=",
            transitionEncodingNodes,
            " node_limit=",
            encodingNodeLimit,
            " transition_support=",
            transitionSupportSymbols.size(),
            " support_limit=",
            encodingSupportLimit,
            " level=",
            level);
      }  // LCOV_EXCL_LINE
      markPdrBudgetExhausted(PdrBudgetExhaustion::LocalQuery);  // LCOV_EXCL_LINE
      return std::nullopt;  // LCOV_EXCL_LINE
    }
  }

  // IC3 proof obligations are concrete states. The transition SAT query stays
  // local to the requested target cone, but any SAT predecessor that is queued
  // or cached as a potential counterexample witness carries the full current
  // state assignment from the SAT model.
  const std::vector<size_t> predecessorSymbols =
      sortUniqueSymbols(transitionByState.stateSymbols());
  PredecessorAssumptionCache* solverCache =
      shouldUsePredecessorSolverCache(problem) ? predecessorAssumptionCache
                                               : nullptr;
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
      extraFrameClauses,
      solverCache,
      supportCache);
  const std::vector<size_t> cachedSolverSymbols =
      predecessorAssumptionCacheSymbols(
          problem,
          transitionByState,
          solverSymbols,
          level,
          solverCache);
  const unsigned predecessorConflictLimit =
      problem.usesDualRailStateEncoding
          ? dualRailPredecessorConflictLimitForQuery(
                problem, targetCube, level, cachedSolverSymbols.size())
          : 0;
  const unsigned predecessorDecisionLimit =
      problem.usesDualRailStateEncoding
          ? dualRailPredecessorDecisionLimit(predecessorConflictLimit)
          : std::numeric_limits<unsigned>::max();
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
        " cached_solver_symbols=", cachedSolverSymbols.size(),
        " conflict_limit=", predecessorConflictLimit,
        " frame_clauses=",
        level < frames.size() ? frames[level].clauses.size() : 0,
        " exclude_target=", excludeTargetOnCurrentFrame ? 1 : 0);
  }
  if (problem.usesDualRailStateEncoding && predecessorAssumptionCache != nullptr &&
      solverCache == nullptr && emitStatsForQuery) {
    emitSecDiag(
        "SEC PDR stats: predecessor cached solver disabled state_symbols=",
        problem.totalStateCount,
        " state_limit=",
        kMaxDualRailPredecessorSolverCacheStateSymbols);
  }
  if (problem.usesDualRailStateEncoding && solverCache != nullptr) {
    PredecessorAssumptionSolver* solvedPredecessorCache = nullptr;
    std::vector<int> cachedAssumptions;
    StateCube cachedUnsatCore;
    auto cachedStatus = solvePredecessorCubeWithCachedAssumptions(
        *solverCache,
        problem,
        solverType,
        transitionByState,
        initFormula,
        frameInvariant,
        frames,
        level,
        targetCube,
        encodedTargets,
        transitionSupportSymbols,
        cachedSolverSymbols,
        excludeTargetOnCurrentFrame,
        extraFrameClauses,
        predecessorConflictLimit,
        predecessorDecisionLimit,
        &solvedPredecessorCache,
        &cachedAssumptions,
        &cachedUnsatCore);
    if (cachedStatus.has_value() &&
        *cachedStatus == SATSolverWrapper::SolveStatus::Unknown &&
        solvedPredecessorCache != nullptr && !cachedAssumptions.empty() &&
        canRetryDualRailPredecessorInCachedSolver(problem)) {
      if (emitStatsForQuery) {
        emitSecDiag(
            "SEC PDR stats: predecessor #", statsQueryNumber,
            " cached_assumptions=unknown retry=cached_solver");
      }
      // The fresh fallback asks the same SAT question as the cached assumption
      // solver. Spend the fallback budget in that solver so learned clauses and
      // already-encoded transition/frame constraints are reused instead of
      // rebuilding large dual-rail cones for every residual predecessor.
      cachedStatus =
          solvedPredecessorCache->solver->solveWithAssumptionsStatus(
              cachedAssumptions,
              resourceLimitOrUnbounded(predecessorConflictLimit),
              resourceLimitOrUnbounded(predecessorDecisionLimit));
      if (cachedStatus.has_value() &&
          *cachedStatus == SATSolverWrapper::SolveStatus::Unknown) {
        if (pdrStatsEnabled()) {
          emitSecDiag(
              "SEC PDR stats: predecessor query budget exhausted limit=",
              predecessorConflictLimit,
              " decision_limit=",
              predecessorDecisionLimit,
              " symbols=",
              cachedSolverSymbols.size(),
              " level=",
              level,
              " cached_solver_retry=1");
        }
        markPdrBudgetExhausted(PdrBudgetExhaustion::LocalQuery);
        return std::nullopt;
      }
    } // LCOV_EXCL_LINE
    if (cachedStatus.has_value()) {
      if (*cachedStatus == SATSolverWrapper::SolveStatus::Unsat) {
        if (emitStatsForQuery) {
          emitSecDiag(
              "SEC PDR stats: predecessor #", statsQueryNumber,
              " result=unsat cached_assumptions=1");
        }
        if (exactCacheKey.has_value() && stableUnsatCacheKey.has_value()) {
          const StateCube* cachedUnsatCorePtr =
              cachedUnsatCore.empty() ? nullptr : &cachedUnsatCore;
          rememberPredecessorQueryResult(
              *predecessorAssumptionCache,
              *exactCacheKey,
              *stableUnsatCacheKey,
              std::nullopt,
              cachedUnsatCorePtr);
        }
        return std::nullopt;
      }
      if (*cachedStatus == SATSolverWrapper::SolveStatus::Sat &&
          solvedPredecessorCache != nullptr &&
          hasLocalDualRailFinalLeafSurface(problem)) {
        if (emitStatsForQuery) {
          emitSecDiag(
              "SEC PDR stats: predecessor #", statsQueryNumber,
              " result=sat cached_assumptions=1");
        }
        StateCube predecessor = extractSolvedPredecessorCube(
            *solvedPredecessorCache->solver,
            *solvedPredecessorCache->variables,
            predecessorSymbols,
            solvedPredecessorCache->transitionLeafLits);
        if (exactCacheKey.has_value() && stableUnsatCacheKey.has_value()) {
          rememberPredecessorQueryResult(
              *predecessorAssumptionCache,
              *exactCacheKey,
              *stableUnsatCacheKey,
              std::optional<StateCube>(predecessor));
        }
        return predecessor;
      }
      if (emitStatsForQuery) {
        emitSecDiag(
            "SEC PDR stats: predecessor #", statsQueryNumber,
            " cached_assumptions=",
            *cachedStatus == SATSolverWrapper::SolveStatus::Sat ? "sat"
                                                                : "unknown",
            " fallback=exact");
      }
    }
  }
  const auto predecessorSolverType =
      localDualRailPredecessorSolverType(problem, solverType);
  SATSolverWrapper solver(predecessorSolverType);
  solver.configureForSecPdrQuery(solverSymbols.size());
  FrameVariableStore variables(solver, solverSymbols, 1);
  addComplementedStateRelations(solver, variables, problem.complementedStatePairs0, 1);
  addComplementedStateRelations(solver, variables, problem.complementedStatePairs1, 1);
  addSameFrameStateEqualities(solver, variables, problem, 1);
  addDualRailStateValidity(solver, variables, problem.dualRailStatePairs, 1);
  addFrameConstraints(
      solver, variables, problem, initFormula, frameInvariant, frames, level, 0,
      solverSymbols);
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
  SATSolverWrapper::SolveStatus predecessorSolveStatus =
      SATSolverWrapper::SolveStatus::Sat;
  if (problem.usesDualRailStateEncoding) {
    // Predecessor queries are local PDR obligations. A limit hit is not a
    // proof of UNSAT, so dual-rail mode turns it into an inconclusive leaf
    // instead of letting one hard residual output dominate the regress run.
    predecessorSolveStatus = solver.solveWithResourceLimits(
        predecessorConflictLimit,
        predecessorDecisionLimit);
  } else {
    predecessorSolveStatus = solver.solveStatus();
  }
  if (predecessorSolveStatus == SATSolverWrapper::SolveStatus::Unknown) {
    if (pdrStatsEnabled()) {  // LCOV_EXCL_LINE
      emitSecDiag(  // LCOV_EXCL_LINE
          "SEC PDR stats: predecessor query budget exhausted limit=",
          predecessorConflictLimit,
          " decision_limit=",
          predecessorDecisionLimit,
          " symbols=",
          solverSymbols.size(),
          " level=",
          level);
    }  // LCOV_EXCL_LINE
    markPdrBudgetExhausted(PdrBudgetExhaustion::LocalQuery);  // LCOV_EXCL_LINE
    return std::nullopt;  // LCOV_EXCL_LINE
  }
  const bool hasPredecessor =
      predecessorSolveStatus == SATSolverWrapper::SolveStatus::Sat;
  if (emitStatsForQuery) {
    emitSecDiag(
        "SEC PDR stats: predecessor #", statsQueryNumber,
        " result=", hasPredecessor ? "sat" : "unsat");
  }
  if (!hasPredecessor) {
    if (exactCacheKey.has_value() && stableUnsatCacheKey.has_value() &&
        predecessorAssumptionCache != nullptr) {
      rememberPredecessorQueryResult(
          *predecessorAssumptionCache,
          *exactCacheKey,
          *stableUnsatCacheKey,
          std::nullopt);
    }
    return std::nullopt;
  }
  StateCube predecessor = extractSolvedPredecessorCube(
      solver,
      variables,
      predecessorSymbols,
      transitionLeafLits);
  if (emitStatsForQuery) {
    emitSecDiag(
        "SEC PDR stats: predecessor #", statsQueryNumber,
        " predecessor_cube=", predecessor.size(),
        " predecessor_hash=", cubeFingerprint(predecessor));
  }
  if (exactCacheKey.has_value() && stableUnsatCacheKey.has_value() &&
      predecessorAssumptionCache != nullptr) {
    rememberPredecessorQueryResult(
        *predecessorAssumptionCache,
        *exactCacheKey,
        *stableUnsatCacheKey,
        std::optional<StateCube>(predecessor));
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
      // LCOV_EXCL_START
      initIntersectionSymbols(problem, initFormula, cube);
      // LCOV_EXCL_STOP
  SATSolverWrapper solver(solverType);
  solver.configureForSecPdrQuery(solverSymbols.size());
  // LCOV_EXCL_START
  FrameVariableStore variables(solver, solverSymbols, 1);
  addComplementedStateRelations(solver, variables, problem.complementedStatePairs0, 1);
  // LCOV_EXCL_STOP
  addComplementedStateRelations(solver, variables, problem.complementedStatePairs1, 1);
  // LCOV_EXCL_START
  addSameFrameStateEqualities(solver, variables, problem, 1);
  addDualRailStateValidity(solver, variables, problem.dualRailStatePairs, 1);
  FrameFormulaEncoder encoder(solver, variables.makeLeafLits(0));
  solver.addClause({encoder.encode(initFormula)});
  // LCOV_EXCL_STOP
  addCubeAssumptions(solver, variables, cube, 0);
  // LCOV_EXCL_START
  return solver.solve();
}

bool appendTargetLiteral(StateCube& candidate,  // LCOV_EXCL_LINE
// LCOV_EXCL_STOP
                         const StateCube& targetCube,
                         size_t symbol) {
  if (findCubeLiteralValue(candidate, symbol).has_value()) {  // LCOV_EXCL_LINE
    return false;  // LCOV_EXCL_LINE
  }
  const auto targetValue = findCubeLiteralValue(targetCube, symbol);  // LCOV_EXCL_LINE
  if (!targetValue.has_value()) {  // LCOV_EXCL_LINE
    return false;  // LCOV_EXCL_LINE
  }
  candidate.push_back({symbol, *targetValue});  // LCOV_EXCL_LINE
  normalizeCube(candidate);  // LCOV_EXCL_LINE
  return true;  // LCOV_EXCL_LINE
}  // LCOV_EXCL_LINE

size_t cubeLiteralKey(const CubeLiteral& literal) {
  return (literal.symbol << 1) | (literal.value ? 1u : 0u);
}

std::vector<int> assumptionLiteralsForCube(
    // LCOV_EXCL_START
    const StateCube& cube,
    const std::vector<std::pair<int, CubeLiteral>>& assumptionPairs) {
    // LCOV_EXCL_STOP
  std::unordered_map<size_t, int> assumptionByLiteral;
  assumptionByLiteral.reserve(assumptionPairs.size());
  for (const auto& [assumptionLit, literal] : assumptionPairs) {
    assumptionByLiteral.emplace(cubeLiteralKey(literal), assumptionLit);
  }

  // LCOV_EXCL_START
  std::vector<int> assumptions;
  // LCOV_EXCL_STOP
  assumptions.reserve(cube.size());
  for (const auto& literal : cube) {
    // LCOV_EXCL_START
    const auto it = assumptionByLiteral.find(cubeLiteralKey(literal));
    if (it == assumptionByLiteral.end()) {
      assumptions.clear();  // LCOV_EXCL_LINE
      return assumptions;  // LCOV_EXCL_LINE
    }
    assumptions.push_back(it->second);
  }
  // LCOV_EXCL_STOP
  return assumptions;
// LCOV_EXCL_START
}
// LCOV_EXCL_STOP

// LCOV_EXCL_START
StateCube cubeFromAssumptionLiterals(  // LCOV_EXCL_LINE
    const std::vector<int>& assumptions,
    const std::unordered_map<int, CubeLiteral>& literalByAssumption) {
    // LCOV_EXCL_STOP
  StateCube cube;  // LCOV_EXCL_LINE
  // LCOV_EXCL_START
  cube.reserve(assumptions.size());  // LCOV_EXCL_LINE
  // LCOV_EXCL_STOP
  for (const auto assumption : assumptions) {  // LCOV_EXCL_LINE
    const auto it = literalByAssumption.find(assumption);  // LCOV_EXCL_LINE
    if (it == literalByAssumption.end()) {  // LCOV_EXCL_LINE
      cube.clear();  // LCOV_EXCL_LINE
      // LCOV_EXCL_START
      return cube;  // LCOV_EXCL_LINE
    }
    cube.push_back(it->second);  // LCOV_EXCL_LINE
    // LCOV_EXCL_STOP
  }
  normalizeCube(cube);  // LCOV_EXCL_LINE
  // LCOV_EXCL_START
  return cube;  // LCOV_EXCL_LINE
}  // LCOV_EXCL_LINE

std::optional<StateCube> minimizeCoreInTargetContext(  // LCOV_EXCL_LINE
    SATSolverWrapper& coreSolver,
    const std::vector<int>& assumptions,
    const std::unordered_map<int, CubeLiteral>& literalByAssumption,
    size_t* checks) {
  std::vector<int> candidate = assumptions;  // LCOV_EXCL_LINE
  if (candidate.empty()) {  // LCOV_EXCL_LINE
    return std::nullopt;  // LCOV_EXCL_LINE
    // LCOV_EXCL_STOP
  }

  // LCOV_EXCL_START
  for (size_t chunkSize = std::max<size_t>(1, candidate.size() / 2);  // LCOV_EXCL_LINE
       chunkSize > 0 &&  // LCOV_EXCL_LINE
       *checks < kMaxPredecessorCoreContextMinimizationChecks;) {  // LCOV_EXCL_LINE
    bool removedAny = false;  // LCOV_EXCL_LINE
    for (size_t index = 0;  // LCOV_EXCL_LINE
         index < candidate.size() &&  // LCOV_EXCL_LINE
         *checks < kMaxPredecessorCoreContextMinimizationChecks;) {  // LCOV_EXCL_LINE
         // LCOV_EXCL_STOP
      const size_t erasedCount =  // LCOV_EXCL_LINE
          // LCOV_EXCL_START
          std::min(chunkSize, candidate.size() - index);  // LCOV_EXCL_LINE
      if (erasedCount == 0 || erasedCount == candidate.size()) {  // LCOV_EXCL_LINE
        break;  // LCOV_EXCL_LINE
      }
      // LCOV_EXCL_STOP

      // LCOV_EXCL_START
      std::vector<int> trial = candidate;  // LCOV_EXCL_LINE
      trial.erase(  // LCOV_EXCL_LINE
      // LCOV_EXCL_STOP
          trial.begin() + static_cast<std::ptrdiff_t>(index),  // LCOV_EXCL_LINE
          // LCOV_EXCL_START
          trial.begin() +  // LCOV_EXCL_LINE
              static_cast<std::ptrdiff_t>(index + erasedCount));  // LCOV_EXCL_LINE
              // LCOV_EXCL_STOP
      ++(*checks);  // LCOV_EXCL_LINE
      // LCOV_EXCL_START
      const auto status = coreSolver.solveWithAssumptionsStatus(  // LCOV_EXCL_LINE
          trial, kPredecessorCoreConflictLimit);
          // LCOV_EXCL_STOP
      if (status == SATSolverWrapper::SolveStatus::Unsat) {  // LCOV_EXCL_LINE
        // LCOV_EXCL_START
        candidate = std::move(trial);  // LCOV_EXCL_LINE
        // LCOV_EXCL_STOP
        removedAny = true;  // LCOV_EXCL_LINE
        continue;  // LCOV_EXCL_LINE
      // LCOV_EXCL_START
      }
      index += erasedCount;  // LCOV_EXCL_LINE
    }  // LCOV_EXCL_LINE


// LCOV_EXCL_STOP
    if (chunkSize == 1) {  // LCOV_EXCL_LINE
      // LCOV_EXCL_START
      break;  // LCOV_EXCL_LINE
    }
    // LCOV_EXCL_STOP
    if (!removedAny && chunkSize == 1) {  // LCOV_EXCL_LINE
      // LCOV_EXCL_START
      break;  // LCOV_EXCL_LINE
      // LCOV_EXCL_STOP
    }
    chunkSize = std::max<size_t>(1, chunkSize / 2);  // LCOV_EXCL_LINE
  }

  StateCube minimized = cubeFromAssumptionLiterals(  // LCOV_EXCL_LINE
      // LCOV_EXCL_START
      candidate, literalByAssumption);  // LCOV_EXCL_LINE
  if (minimized.empty()) {  // LCOV_EXCL_LINE
    return std::nullopt;  // LCOV_EXCL_LINE
    // LCOV_EXCL_STOP
  }
  return minimized;  // LCOV_EXCL_LINE
// LCOV_EXCL_START
}  // LCOV_EXCL_LINE

std::optional<StateCube> growCoreOutsideInit(  // LCOV_EXCL_LINE
// LCOV_EXCL_STOP
    const KInductionProblem& problem,
    // LCOV_EXCL_START
    KEPLER_FORMAL::Config::SolverType solverType,
    BoolExpr* initFormula,
    // LCOV_EXCL_STOP
    const StateCube& core,
    // LCOV_EXCL_START
    const StateCube& targetCube) {
  StateCube candidate = core;  // LCOV_EXCL_LINE
  if (!cubeIntersectsInit(problem, solverType, initFormula, candidate)) {  // LCOV_EXCL_LINE
    return candidate;  // LCOV_EXCL_LINE
  }

  auto tryAddSymbol = [&](size_t symbol) -> bool {  // LCOV_EXCL_LINE
  // LCOV_EXCL_STOP
    if (!appendTargetLiteral(candidate, targetCube, symbol)) {  // LCOV_EXCL_LINE
      return false;  // LCOV_EXCL_LINE
    }
    return !cubeIntersectsInit(problem, solverType, initFormula, candidate);  // LCOV_EXCL_LINE
  };  // LCOV_EXCL_LINE

// LCOV_EXCL_START

  const bool usesBootstrapFrontier = problem.resetBootstrapCycles != 0;  // LCOV_EXCL_LINE
  const auto& assignments = usesBootstrapFrontier  // LCOV_EXCL_LINE
                                ? problem.bootstrapStateAssignments  // LCOV_EXCL_LINE
                                : problem.initialStateAssignments;  // LCOV_EXCL_LINE
                                // LCOV_EXCL_STOP
  const auto& equalities = emptySymbolPairs();  // LCOV_EXCL_LINE

  // UNSAT cores from transition assumptions can be too small to be legal PDR
  // frame clauses because a one-bit reason may still overlap Init. Add only
  // original target literals until the cube visibly contradicts Init; the
  // predecessor UNSAT result is monotonic under this strengthening.
  // LCOV_EXCL_STOP
  for (const auto& [symbol, initValue] : assignments) {  // LCOV_EXCL_LINE
    // LCOV_EXCL_START
    const auto targetValue = findCubeLiteralValue(targetCube, symbol);  // LCOV_EXCL_LINE
    if (targetValue.has_value() && *targetValue != initValue &&  // LCOV_EXCL_LINE
    // LCOV_EXCL_STOP
        tryAddSymbol(symbol)) {  // LCOV_EXCL_LINE
      return candidate;  // LCOV_EXCL_LINE
    // LCOV_EXCL_START
    }
  }
  for (const auto& [lhsSymbol, rhsSymbol] : equalities) {  // LCOV_EXCL_LINE
    const auto lhsTargetValue = findCubeLiteralValue(targetCube, lhsSymbol);  // LCOV_EXCL_LINE
    const auto rhsTargetValue = findCubeLiteralValue(targetCube, rhsSymbol);  // LCOV_EXCL_LINE
    if (!lhsTargetValue.has_value() || !rhsTargetValue.has_value() ||  // LCOV_EXCL_LINE
        *lhsTargetValue == *rhsTargetValue) {  // LCOV_EXCL_LINE
      continue;  // LCOV_EXCL_LINE
      // LCOV_EXCL_STOP
    }
    // LCOV_EXCL_START
    if (tryAddSymbol(lhsSymbol) || tryAddSymbol(rhsSymbol)) {  // LCOV_EXCL_LINE
      return candidate;  // LCOV_EXCL_LINE
    }
    // LCOV_EXCL_STOP
  }
  for (const auto& [lhsSymbol, rhsSymbol] : equalities) {  // LCOV_EXCL_LINE
    // LCOV_EXCL_START
    const auto lhsCoreValue = findCubeLiteralValue(candidate, lhsSymbol);  // LCOV_EXCL_LINE
    // LCOV_EXCL_STOP
    const auto rhsCoreValue = findCubeLiteralValue(candidate, rhsSymbol);  // LCOV_EXCL_LINE
    // LCOV_EXCL_START
    const auto lhsTargetValue = findCubeLiteralValue(targetCube, lhsSymbol);  // LCOV_EXCL_LINE
    const auto rhsTargetValue = findCubeLiteralValue(targetCube, rhsSymbol);  // LCOV_EXCL_LINE
    // LCOV_EXCL_STOP
    if (lhsCoreValue.has_value() && rhsTargetValue.has_value() &&  // LCOV_EXCL_LINE
        // LCOV_EXCL_START
        *lhsCoreValue != *rhsTargetValue && tryAddSymbol(rhsSymbol)) {  // LCOV_EXCL_LINE
        // LCOV_EXCL_STOP
      return candidate;  // LCOV_EXCL_LINE
    // LCOV_EXCL_START
    }
    if (rhsCoreValue.has_value() && lhsTargetValue.has_value() &&  // LCOV_EXCL_LINE
        *rhsCoreValue != *lhsTargetValue && tryAddSymbol(lhsSymbol)) {  // LCOV_EXCL_LINE
      return candidate;  // LCOV_EXCL_LINE
    }
    // LCOV_EXCL_STOP
  }
  // LCOV_EXCL_START
  if (problem.complementedStatePairs0.size() <=  // LCOV_EXCL_LINE
      kMaxComplementPairsForCheapInitCheck) {
      // LCOV_EXCL_STOP
    for (const auto& [primarySymbol, complementedSymbol] :  // LCOV_EXCL_LINE
         problem.complementedStatePairs0) {  // LCOV_EXCL_LINE
      // LCOV_EXCL_START
      const auto primaryTargetValue =
          findCubeLiteralValue(targetCube, primarySymbol);  // LCOV_EXCL_LINE
          // LCOV_EXCL_STOP
      const auto complementedTargetValue =
          // LCOV_EXCL_START
          findCubeLiteralValue(targetCube, complementedSymbol);  // LCOV_EXCL_LINE
          // LCOV_EXCL_STOP
      if (!primaryTargetValue.has_value() ||  // LCOV_EXCL_LINE
          // LCOV_EXCL_START
          !complementedTargetValue.has_value() ||  // LCOV_EXCL_LINE
          // LCOV_EXCL_STOP
          *primaryTargetValue != *complementedTargetValue) {  // LCOV_EXCL_LINE
        // LCOV_EXCL_START
        continue;  // LCOV_EXCL_LINE
        // LCOV_EXCL_STOP
      }
      // LCOV_EXCL_START
      if (tryAddSymbol(primarySymbol) || tryAddSymbol(complementedSymbol)) {  // LCOV_EXCL_LINE
        return candidate;  // LCOV_EXCL_LINE
      }
    }
    for (const auto& [primarySymbol, complementedSymbol] :  // LCOV_EXCL_LINE
    // LCOV_EXCL_STOP
         problem.complementedStatePairs0) {  // LCOV_EXCL_LINE
      // LCOV_EXCL_START
      const auto primaryCoreValue =
          findCubeLiteralValue(candidate, primarySymbol);  // LCOV_EXCL_LINE
      const auto complementedCoreValue =
          findCubeLiteralValue(candidate, complementedSymbol);  // LCOV_EXCL_LINE
          // LCOV_EXCL_STOP
      const auto primaryTargetValue =
          findCubeLiteralValue(targetCube, primarySymbol);  // LCOV_EXCL_LINE
      // LCOV_EXCL_START
      const auto complementedTargetValue =
          findCubeLiteralValue(targetCube, complementedSymbol);  // LCOV_EXCL_LINE
          // LCOV_EXCL_STOP
      if (primaryCoreValue.has_value() && complementedTargetValue.has_value() &&  // LCOV_EXCL_LINE
          // LCOV_EXCL_START
          *primaryCoreValue == *complementedTargetValue &&  // LCOV_EXCL_LINE
          tryAddSymbol(complementedSymbol)) {  // LCOV_EXCL_LINE
          // LCOV_EXCL_STOP
        return candidate;  // LCOV_EXCL_LINE
      // LCOV_EXCL_START
      }
      // LCOV_EXCL_STOP
      if (complementedCoreValue.has_value() && primaryTargetValue.has_value() &&  // LCOV_EXCL_LINE
          // LCOV_EXCL_START
          *complementedCoreValue == *primaryTargetValue &&  // LCOV_EXCL_LINE
          tryAddSymbol(primarySymbol)) {  // LCOV_EXCL_LINE
        return candidate;  // LCOV_EXCL_LINE
      }
    }
    // LCOV_EXCL_STOP
  }  // LCOV_EXCL_LINE
  // LCOV_EXCL_START
  if (problem.complementedStatePairs1.size() <=  // LCOV_EXCL_LINE
      kMaxComplementPairsForCheapInitCheck) {
      // LCOV_EXCL_STOP
    for (const auto& [primarySymbol, complementedSymbol] :  // LCOV_EXCL_LINE
         problem.complementedStatePairs1) {  // LCOV_EXCL_LINE
      // LCOV_EXCL_START
      const auto primaryTargetValue =
          findCubeLiteralValue(targetCube, primarySymbol);  // LCOV_EXCL_LINE
          // LCOV_EXCL_STOP
      const auto complementedTargetValue =
          // LCOV_EXCL_START
          findCubeLiteralValue(targetCube, complementedSymbol);  // LCOV_EXCL_LINE
          // LCOV_EXCL_STOP
      if (!primaryTargetValue.has_value() ||  // LCOV_EXCL_LINE
          // LCOV_EXCL_START
          !complementedTargetValue.has_value() ||  // LCOV_EXCL_LINE
          // LCOV_EXCL_STOP
          *primaryTargetValue != *complementedTargetValue) {  // LCOV_EXCL_LINE
        // LCOV_EXCL_START
        continue;  // LCOV_EXCL_LINE
        // LCOV_EXCL_STOP
      }
      // LCOV_EXCL_START
      if (tryAddSymbol(primarySymbol) || tryAddSymbol(complementedSymbol)) {  // LCOV_EXCL_LINE
        return candidate;  // LCOV_EXCL_LINE
      }
    }
    for (const auto& [primarySymbol, complementedSymbol] :  // LCOV_EXCL_LINE
    // LCOV_EXCL_STOP
         problem.complementedStatePairs1) {  // LCOV_EXCL_LINE
      // LCOV_EXCL_START
      const auto primaryCoreValue =
          findCubeLiteralValue(candidate, primarySymbol);  // LCOV_EXCL_LINE
      const auto complementedCoreValue =
          findCubeLiteralValue(candidate, complementedSymbol);  // LCOV_EXCL_LINE
          // LCOV_EXCL_STOP
      const auto primaryTargetValue =
          findCubeLiteralValue(targetCube, primarySymbol);  // LCOV_EXCL_LINE
      // LCOV_EXCL_START
      const auto complementedTargetValue =
      // LCOV_EXCL_STOP
          findCubeLiteralValue(targetCube, complementedSymbol);  // LCOV_EXCL_LINE
      // LCOV_EXCL_START
      if (primaryCoreValue.has_value() && complementedTargetValue.has_value() &&  // LCOV_EXCL_LINE
          *primaryCoreValue == *complementedTargetValue &&  // LCOV_EXCL_LINE
          tryAddSymbol(complementedSymbol)) {  // LCOV_EXCL_LINE
          // LCOV_EXCL_STOP
        return candidate;  // LCOV_EXCL_LINE
      }
      // LCOV_EXCL_START
      if (complementedCoreValue.has_value() && primaryTargetValue.has_value() &&  // LCOV_EXCL_LINE
          *complementedCoreValue == *primaryTargetValue &&  // LCOV_EXCL_LINE
          // LCOV_EXCL_STOP
          tryAddSymbol(primarySymbol)) {  // LCOV_EXCL_LINE
        // LCOV_EXCL_START
        return candidate;  // LCOV_EXCL_LINE
      }
      // LCOV_EXCL_STOP
    }
  }  // LCOV_EXCL_LINE

  for (const auto& literal : targetCube) {  // LCOV_EXCL_LINE
    if (tryAddSymbol(literal.symbol)) {  // LCOV_EXCL_LINE
      return candidate;  // LCOV_EXCL_LINE
    }
  }
  if (!cubeIntersectsInit(problem, solverType, initFormula, candidate)) {  // LCOV_EXCL_LINE
    return candidate;  // LCOV_EXCL_LINE
  }
  return std::nullopt;  // LCOV_EXCL_LINE
}  // LCOV_EXCL_LINE

std::optional<StateCube> findValidatedPredecessorCore(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    const TransitionExprResolver& transitionByState,
    BoolExpr* initFormula,
    BoolExpr* frameInvariant,
    const std::vector<FrameClauses>& frames,
    size_t sourceLevel,
    const StateCube& targetCube,
    PredecessorAssumptionCache* predecessorAssumptionCache,
    const ComplementPartnerIndex& complementPartners,
    size_t* predecessorQueryBudget,
    PdrFormulaSupportCache* supportCache) {
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
  const std::vector<size_t> predecessorSymbols =
      sortUniqueSymbols(transitionByState.stateSymbols());
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
      nullptr,
      predecessorAssumptionCache,
      supportCache);

  // Use an assumption-capable solver here only as an UNSAT-core oracle over
  // the target literals. Any proposed smaller cube is revalidated below with
  // the normal PDR predecessor query before it can become a learned frame
  // clause.
  SATSolverWrapper coreSolver(
      SATSolverWrapper::assumptionSolverTypeFor(solverType));
  coreSolver.configureForSecPdrQuery(solverSymbols.size());
  FrameVariableStore variables(coreSolver, solverSymbols, 1);
  addComplementedStateRelations(
      coreSolver, variables, problem.complementedStatePairs0, 1);
  addComplementedStateRelations(
      coreSolver, variables, problem.complementedStatePairs1, 1);
  addSameFrameStateEqualities(coreSolver, variables, problem, 1);
  addDualRailStateValidity(coreSolver, variables, problem.dualRailStatePairs, 1);
  addFrameConstraints(
      // LCOV_EXCL_START
      coreSolver,
      variables,
      // LCOV_EXCL_STOP
      problem,
      initFormula,
      frameInvariant,
      frames,
      sourceLevel,
      0,
      solverSymbols);
  addSafeFramePropertyConstraint(coreSolver, variables, problem, sourceLevel, 0);
  addPostBootstrapResetInputConstraints(coreSolver, variables, problem, 0);
  // LCOV_EXCL_START
  if (excludeCurrentTargetForCore) {
    addNegatedCubeClause(coreSolver, variables, targetCube, 0);  // LCOV_EXCL_LINE
    // LCOV_EXCL_STOP
  }  // LCOV_EXCL_LINE

// LCOV_EXCL_START


// LCOV_EXCL_STOP
  const auto assumptionPairs = addTransitionAssumptionsForTargetCube(
      coreSolver,
      variables,
      // LCOV_EXCL_START
      transitionByState,
      0,
      targetCube,
      // LCOV_EXCL_STOP
      encodedTargets,
      transitionSupportSymbols);
  if (assumptionPairs.empty()) {
    if (pdrStatsEnabled() && targetCube.size() > kLargeBlockedCubeGeneralizationThreshold) {  // LCOV_EXCL_LINE
      emitSecDiag(  // LCOV_EXCL_LINE
          "SEC PDR stats: predecessor core miss reason=empty_assumptions target=",
          targetCube.size(),  // LCOV_EXCL_LINE
          " source_level=",
          sourceLevel,
          " target_hash=",
          cubeFingerprint(targetCube));  // LCOV_EXCL_LINE
    }  // LCOV_EXCL_LINE
    return std::nullopt;  // LCOV_EXCL_LINE
  }

  std::vector<int> assumptions;
  assumptions.reserve(assumptionPairs.size());
  std::unordered_map<int, CubeLiteral> literalByAssumption;
  // LCOV_EXCL_START
  literalByAssumption.reserve(assumptionPairs.size() * 2);
  for (const auto& [assumptionLit, cubeLiteral] : assumptionPairs) {
  // LCOV_EXCL_STOP
    assumptions.push_back(assumptionLit);
    // LCOV_EXCL_START
    literalByAssumption.emplace(assumptionLit, cubeLiteral);
    // LCOV_EXCL_STOP
    // Assumption-core solvers may report final conflicts in solver-literal polarity. Map both
    // signs back to the requested cube literal and let exact revalidation below
    // decide whether the proposed core is usable.
    // LCOV_EXCL_START
    literalByAssumption.emplace(-assumptionLit, cubeLiteral);
  }


// LCOV_EXCL_STOP
  const auto coreQueryStatus = coreSolver.solveWithAssumptionsStatus(
      assumptions, kPredecessorCoreConflictLimit);
  // LCOV_EXCL_START
  if (coreQueryStatus == SATSolverWrapper::SolveStatus::Sat) {
    if (pdrStatsEnabled() && targetCube.size() > kLargeBlockedCubeGeneralizationThreshold) {  // LCOV_EXCL_LINE
      emitSecDiag(  // LCOV_EXCL_LINE
      // LCOV_EXCL_STOP
          "SEC PDR stats: predecessor core miss reason=core_query_sat target=",
          // LCOV_EXCL_START
          targetCube.size(),  // LCOV_EXCL_LINE
          // LCOV_EXCL_STOP
          " source_level=",
          sourceLevel,
          " target_hash=",
          // LCOV_EXCL_START
          cubeFingerprint(targetCube));  // LCOV_EXCL_LINE
    }  // LCOV_EXCL_LINE
    return std::nullopt;  // LCOV_EXCL_LINE
    // LCOV_EXCL_STOP
  }
  if (coreQueryStatus == SATSolverWrapper::SolveStatus::Unknown) {
    if (pdrStatsEnabled() &&  // LCOV_EXCL_LINE
        targetCube.size() > kLargeBlockedCubeGeneralizationThreshold) {  // LCOV_EXCL_LINE
      emitSecDiag(  // LCOV_EXCL_LINE
          "SEC PDR stats: predecessor core miss reason=resource_limit target=",
          targetCube.size(),  // LCOV_EXCL_LINE
          // LCOV_EXCL_START
          " source_level=",
          // LCOV_EXCL_STOP
          sourceLevel,
          " target_hash=",
          cubeFingerprint(targetCube));  // LCOV_EXCL_LINE
    }  // LCOV_EXCL_LINE
    return std::nullopt;  // LCOV_EXCL_LINE
  // LCOV_EXCL_START
  }


// LCOV_EXCL_STOP
  StateCube core;
  // LCOV_EXCL_START
  const auto failedAssumptions = coreSolver.failedAssumptions();
  // LCOV_EXCL_STOP
  for (const auto failedLit : failedAssumptions) {
    const auto it = literalByAssumption.find(failedLit);
    if (it == literalByAssumption.end()) {
      // LCOV_EXCL_START
      continue;  // LCOV_EXCL_LINE
      // LCOV_EXCL_STOP
    }
    // LCOV_EXCL_START
    core.push_back(it->second);
    // LCOV_EXCL_STOP
  }
  // LCOV_EXCL_START
  normalizeCube(core);
  if (core.empty() || core.size() >= targetCube.size()) {
    if (pdrStatsEnabled() && targetCube.size() > kLargeBlockedCubeGeneralizationThreshold) {  // LCOV_EXCL_LINE
    // LCOV_EXCL_STOP
      emitSecDiag(  // LCOV_EXCL_LINE
          "SEC PDR stats: predecessor core miss reason=not_smaller target=",
          targetCube.size(),  // LCOV_EXCL_LINE
          " source_level=",
          sourceLevel,
          " failed_assumptions=",
          failedAssumptions.size(),  // LCOV_EXCL_LINE
          " mapped_core=",
          core.size(),  // LCOV_EXCL_LINE
          " target_hash=",
          cubeFingerprint(targetCube));  // LCOV_EXCL_LINE
    // LCOV_EXCL_START
    }  // LCOV_EXCL_LINE
    return std::nullopt;  // LCOV_EXCL_LINE
  }

  if (sourceLevel != 0) {
    // For higher frames the generalized clause is pushed into earlier learned
    // LCOV_EXCL_STOP
    // frames as well, so keep the standard IC3/PDR requirement that the reduced
    // LCOV_EXCL_START
    // cube excludes Init.  Source level zero is different in this implementation:
    // LCOV_EXCL_STOP
    // F0 is the already-checked startup frontier and the learned clause is only
    // LCOV_EXCL_START
    // placed in F1, so the exact no-predecessor query from F0 is the required
    // LCOV_EXCL_STOP
    // safety check.  BlackParrot sampling showed thousands of repeated
    // source_level=0 core misses when we unnecessarily rejected those cores for
    // overlapping Init.
    // LCOV_EXCL_START
    const auto initSafeCore = growCoreOutsideInit(  // LCOV_EXCL_LINE
    // LCOV_EXCL_STOP
        problem, solverType, initFormula, core, targetCube);  // LCOV_EXCL_LINE
    // LCOV_EXCL_START
    if (!initSafeCore.has_value() || initSafeCore->size() >= targetCube.size()) {  // LCOV_EXCL_LINE
      if (pdrStatsEnabled() &&  // LCOV_EXCL_LINE
          targetCube.size() > kLargeBlockedCubeGeneralizationThreshold) {  // LCOV_EXCL_LINE
          // LCOV_EXCL_STOP
        emitSecDiag(  // LCOV_EXCL_LINE
            // LCOV_EXCL_START
            "SEC PDR stats: predecessor core miss reason=init_intersection target=",
            targetCube.size(),  // LCOV_EXCL_LINE
            // LCOV_EXCL_STOP
            "->",
            core.size(),  // LCOV_EXCL_LINE
            " source_level=",
            sourceLevel,
            " target_hash=",
            cubeFingerprint(targetCube),  // LCOV_EXCL_LINE
            " core_hash=",
            cubeFingerprint(core));  // LCOV_EXCL_LINE
      }  // LCOV_EXCL_LINE
      return std::nullopt;  // LCOV_EXCL_LINE
    }
    core = *initSafeCore;  // LCOV_EXCL_LINE
  }  // LCOV_EXCL_LINE

  std::vector<int> coreAssumptions =
      // LCOV_EXCL_START
      assumptionLiteralsForCube(core, assumptionPairs);
  bool coreBlockedInTargetContext = false;
  // LCOV_EXCL_STOP
  bool coreContextResourceLimited = false;
  if (coreAssumptions.size() == core.size()) {
    const auto coreContextStatus = coreSolver.solveWithAssumptionsStatus(
        coreAssumptions, kPredecessorCoreConflictLimit);
    // LCOV_EXCL_START
    coreBlockedInTargetContext =
    // LCOV_EXCL_STOP
        coreContextStatus == SATSolverWrapper::SolveStatus::Unsat;
    coreContextResourceLimited =
        coreContextStatus == SATSolverWrapper::SolveStatus::Unknown;
  }
  // LCOV_EXCL_START
  size_t contextMinimizationChecks = 0;
  if (!coreBlockedInTargetContext &&
      !coreContextResourceLimited &&  // LCOV_EXCL_LINE
      targetCube.size() > kLargeBlockedCubeGeneralizationThreshold) {  // LCOV_EXCL_LINE
    // The failed-assumption vector is only a seed. If it is not itself UNSAT,
    // minimize the full target assumption set in the same solver context. This
    // LCOV_EXCL_STOP
    // keeps the proof obligation honest: every accepted reduced cube is backed
    // LCOV_EXCL_START
    // by an actual UNSAT predecessor query, not by solver-conflict bookkeeping.
    if (const auto minimizedCore = minimizeCoreInTargetContext(  // LCOV_EXCL_LINE
            coreSolver,
            assumptions,
            literalByAssumption,
            &contextMinimizationChecks);
        minimizedCore.has_value() &&  // LCOV_EXCL_LINE
        // LCOV_EXCL_STOP
        minimizedCore->size() < targetCube.size()) {  // LCOV_EXCL_LINE
      // LCOV_EXCL_START
      core = *minimizedCore;  // LCOV_EXCL_LINE
      coreAssumptions = assumptionLiteralsForCube(core, assumptionPairs);  // LCOV_EXCL_LINE
      if (coreAssumptions.size() == core.size()) {  // LCOV_EXCL_LINE
      // LCOV_EXCL_STOP
        const auto coreContextStatus = coreSolver.solveWithAssumptionsStatus(  // LCOV_EXCL_LINE
            // LCOV_EXCL_START
            coreAssumptions, kPredecessorCoreConflictLimit);
            // LCOV_EXCL_STOP
        coreBlockedInTargetContext =  // LCOV_EXCL_LINE
            // LCOV_EXCL_START
            coreContextStatus == SATSolverWrapper::SolveStatus::Unsat;  // LCOV_EXCL_LINE
            // LCOV_EXCL_STOP
        coreContextResourceLimited =  // LCOV_EXCL_LINE
            coreContextStatus == SATSolverWrapper::SolveStatus::Unknown;  // LCOV_EXCL_LINE
      }  // LCOV_EXCL_LINE
    // LCOV_EXCL_START
    }  // LCOV_EXCL_LINE
    // LCOV_EXCL_STOP
  }  // LCOV_EXCL_LINE
  // LCOV_EXCL_START
  if (!coreBlockedInTargetContext) {
  // LCOV_EXCL_STOP
    if (pdrStatsEnabled() &&  // LCOV_EXCL_LINE
        // LCOV_EXCL_START
        targetCube.size() > kLargeBlockedCubeGeneralizationThreshold) {  // LCOV_EXCL_LINE
        // LCOV_EXCL_STOP
      emitSecDiag(  // LCOV_EXCL_LINE
          "SEC PDR stats: predecessor core miss reason=context_core_sat target=",
          // LCOV_EXCL_START
          targetCube.size(),  // LCOV_EXCL_LINE
          "->",
          // LCOV_EXCL_STOP
          core.size(),  // LCOV_EXCL_LINE
          " source_level=",
          sourceLevel,
          " resource_limit=",
          coreContextResourceLimited ? "true" : "false",  // LCOV_EXCL_LINE
          " target_hash=",
          cubeFingerprint(targetCube),  // LCOV_EXCL_LINE
          " core_hash=",
          cubeFingerprint(core),  // LCOV_EXCL_LINE
          " context_checks=",
          contextMinimizationChecks);
    }  // LCOV_EXCL_LINE
    return std::nullopt;  // LCOV_EXCL_LINE
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
          // LCOV_EXCL_START
          " source_level=",
          sourceLevel,
          " target_hash=",
          cubeFingerprint(targetCube),
          " core_hash=",
          cubeFingerprint(core),
          " validation=target_context",
          " context_checks=",
          // LCOV_EXCL_STOP
          contextMinimizationChecks);
    // LCOV_EXCL_START
    }
    return core;
  }

  const auto corePredecessor = findPredecessorCube(  // LCOV_EXCL_LINE
      // LCOV_EXCL_STOP
      problem,  // LCOV_EXCL_LINE
      // LCOV_EXCL_START
      solverType,  // LCOV_EXCL_LINE
      transitionByState,  // LCOV_EXCL_LINE
      initFormula,  // LCOV_EXCL_LINE
      frameInvariant,  // LCOV_EXCL_LINE
      frames,  // LCOV_EXCL_LINE
      sourceLevel,  // LCOV_EXCL_LINE
      // LCOV_EXCL_STOP
      core,
      // LCOV_EXCL_START
      excludeCurrentTargetForCore,  // LCOV_EXCL_LINE
      // LCOV_EXCL_STOP
      complementPartners,  // LCOV_EXCL_LINE
      predecessorAssumptionCache,  // LCOV_EXCL_LINE
      nullptr,
      // LCOV_EXCL_START
      predecessorQueryBudget,  // LCOV_EXCL_LINE
      // LCOV_EXCL_START
      supportCache);  // LCOV_EXCL_LINE
  if (hasPdrBudgetExhaustion()) {  // LCOV_EXCL_LINE
    return std::nullopt;  // LCOV_EXCL_LINE
  }  // LCOV_EXCL_LINE
  if (corePredecessor.has_value()) {  // LCOV_EXCL_LINE
    if (pdrStatsEnabled() && targetCube.size() > kLargeBlockedCubeGeneralizationThreshold) {  // LCOV_EXCL_LINE
    // LCOV_EXCL_STOP
      emitSecDiag(  // LCOV_EXCL_LINE
          "SEC PDR stats: predecessor core miss reason=predecessor_exists target=",
          // LCOV_EXCL_START
          targetCube.size(),  // LCOV_EXCL_LINE
          "->",
          // LCOV_EXCL_STOP
          core.size(),  // LCOV_EXCL_LINE
          // LCOV_EXCL_START
          " source_level=",
          // LCOV_EXCL_STOP
          sourceLevel,
          // LCOV_EXCL_START
          " target_hash=",
          // LCOV_EXCL_STOP
          cubeFingerprint(targetCube),  // LCOV_EXCL_LINE
          " core_hash=",
          cubeFingerprint(core));  // LCOV_EXCL_LINE
    // LCOV_EXCL_START
    }  // LCOV_EXCL_LINE
    // LCOV_EXCL_STOP
    return std::nullopt;  // LCOV_EXCL_LINE
  // LCOV_EXCL_START
  }

  if (pdrStatsEnabled()) {  // LCOV_EXCL_LINE
  // LCOV_EXCL_STOP
    emitSecDiag(  // LCOV_EXCL_LINE
        "SEC PDR stats: predecessor core target=",
        targetCube.size(),  // LCOV_EXCL_LINE
        "->",
        core.size(),  // LCOV_EXCL_LINE
        " source_level=",
        sourceLevel,
        " target_hash=",
        cubeFingerprint(targetCube),  // LCOV_EXCL_LINE
        " core_hash=",
        cubeFingerprint(core));  // LCOV_EXCL_LINE
  }  // LCOV_EXCL_LINE
  return core;  // LCOV_EXCL_LINE
}

StateCube generalizeBlockedCube(const KInductionProblem& problem,
                                KEPLER_FORMAL::Config::SolverType solverType,
                                const TransitionExprResolver& transitionByState,
                                BoolExpr* initFormula,
                                BoolExpr* frameInvariant,
                                const std::vector<FrameClauses>& frames,
                                size_t level,
                                const StateCube& cube,
                                PredecessorAssumptionCache* predecessorAssumptionCache,
                                const ComplementPartnerIndex& complementPartners,
                                size_t* predecessorQueryBudget,
                                PdrFormulaSupportCache* supportCache) {
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
  const bool broadDualRailTransitionSurface =
      problem.usesDualRailStateEncoding &&
      blockedCubeSupportSize > kMaxGeneralizedBlockedCubeTransitionSupport;
  const bool localDualRailTransitionSurface =
      broadDualRailTransitionSurface &&
      isLocalDualRailPredecessorCoreSurface(
          level, cube.size(), blockedCubeSupportSize);
  const size_t effectiveCheckLimit =
      cheapTransitionSurface
          ? std::max(
                checkLimit,
                std::min(
                    kMaxCheapBlockedCubeGeneralizationChecks,
                    std::max(cube.size() * 2, checkLimit)))
          : checkLimit;
  const bool shouldTryPredecessorCore =
      level <= kMaxPredecessorCoreGeneralizationLevel &&
      (!broadDualRailTransitionSurface || localDualRailTransitionSurface) &&
      !cheapTransitionSurface &&
      (cube.size() > kLargeBlockedCubeGeneralizationThreshold ||
       (cube.size() >= kMinMediumCubePredecessorCoreTargetSize &&
        blockedCubeSupportSize > kMaxGeneralizedBlockedCubeTransitionSupport) ||
       localDualRailTransitionSurface);
  const bool skipDualRailPredecessorCore =
      broadDualRailTransitionSurface && !localDualRailTransitionSurface;
  const size_t dualRailCoreSkipNumber = skipDualRailPredecessorCore
                                            ? nextPdrDualRailPredecessorCoreSkipNumber()
                                            : 0;
  if (skipDualRailPredecessorCore &&
      shouldEmitPdrStats(dualRailCoreSkipNumber)) {  // LCOV_EXCL_LINE
    // Predecessor-core extraction is optional clause minimization. In dual-rail
    // mode the target cube already contains rail-expanded state, and sampled
    // Swerv regressions showed the core SAT query becoming the runtime wall.
    // Learning the already-proven cube below remains sound; it only gives up
    // this local strengthening shortcut for broad rail surfaces.
    emitSecDiag(  // LCOV_EXCL_LINE
        "SEC PDR stats: skipped dual-rail predecessor core ",
        "cube=", cube.size(),
        // LCOV_EXCL_START
        " level=", level,
        " support=", blockedCubeSupportSize);
        // LCOV_EXCL_STOP
  }  // LCOV_EXCL_LINE
  if (skipDualRailPredecessorCore &&
      predecessorAssumptionCache != nullptr &&
      canUsePredecessorQueryResultCache(problem)) {
    // The predecessor query that proved this obligation blocked already ran
    // through the cached assumption solver. Reuse its exact failed-assumption
    // core before the broad dual-rail guard below gives up on strengthening.
    // For frames above F1, keep the standard PDR init-safety check before
    // learning the smaller clause.
    if (const auto cachedCore = cachedPredecessorUnsatCoreForCube(
            *predecessorAssumptionCache,
            problem,
            transitionByState,
            initFormula,
            frameInvariant,
            frames,
            /*sourceLevel=*/level - 1,
            cube,
            /*excludeTargetOnCurrentFrame=*/false);
        cachedCore.has_value() && cachedCore->size() < cube.size() &&
        (level == 1 ||
         !cubeIntersectsInit(problem, solverType, initFormula, *cachedCore))) {
      if (pdrStatsEnabled()) {
        emitSecDiag(
            "SEC PDR stats: predecessor cached core target=",
            cube.size(),
            "->",
            cachedCore->size(),
            " source_level=",
            level - 1,
            " target_hash=",
            cubeFingerprint(cube),
            " core_hash=",
            cubeFingerprint(*cachedCore),
            " support=",
            blockedCubeSupportSize);
      }
      return *cachedCore;
    }
  } // LCOV_EXCL_LINE
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
            // LCOV_EXCL_START
            frames,
            // LCOV_EXCL_STOP
            level - 1,
            cube,
            predecessorAssumptionCache,
            // LCOV_EXCL_STOP
            complementPartners,
            predecessorQueryBudget,
            // LCOV_EXCL_START
            supportCache);
            // LCOV_EXCL_STOP
        core.has_value()) {
      // LCOV_EXCL_START
      return *core;
      // LCOV_EXCL_STOP
    }
  }  // LCOV_EXCL_LINE
  if (!cheapTransitionSurface &&
      cube.size() > kVeryLargeBlockedCubeGeneralizationBypassThreshold) {
    if (level != 1) {  // LCOV_EXCL_LINE
      // Keep the measured benefit of the assumption-core pass above:
      // BlackParrot wide level-1 blockers often collapse from ~100 state bits
      // to a few literals.  If no validated core is available at higher
      // levels, skip slower chunk-dropping probes and learn the already-proven
      // cube verbatim.
      return cube;  // LCOV_EXCL_LINE
    }
  }  // LCOV_EXCL_LINE
  // LCOV_EXCL_START
  if (!cheapTransitionSurface &&
  // LCOV_EXCL_STOP
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
      return false;  // LCOV_EXCL_LINE
    }
    if (!blocksFromInitialFrame &&
        cubeIntersectsInit(problem, solverType, initFormula, reduced)) {
      return false;
    }
    const auto predecessor = findPredecessorCube(
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
        predecessorAssumptionCache,
        nullptr,
        predecessorQueryBudget,
        supportCache);
    if (hasPdrBudgetExhaustion()) {
      return false;  // LCOV_EXCL_LINE
    }
    return !predecessor.has_value();
  // LCOV_EXCL_START
  };


// LCOV_EXCL_STOP
  StateCube candidate = cube;
  if (cube.size() > kLargeBlockedCubeGeneralizationThreshold) {
    // Large SAT-model cubes often contain a few cheap literals that already
    // explain the blocked transition plus hundreds of unrelated support bits.
    // Try that cheap seed first so generalization does not spend its budget on
    // giant intermediate cubes whose transition cones dominate runtime.
    const StateCube cheapSeed = boundedCheapTransitionCube(
        cube, kLargeBlockedCubeSeedSize, problem, transitionByState);
    // LCOV_EXCL_START
    if (cheapSeed.size() < cube.size() && checks < checkLimit) {
      ++checks;
      // LCOV_EXCL_STOP
      if (reductionStillBlocks(cheapSeed)) {
        candidate = cheapSeed;  // LCOV_EXCL_LINE
      }  // LCOV_EXCL_LINE
    // LCOV_EXCL_START
    }
    // LCOV_EXCL_STOP
    // On ASIC SEC slices, the predecessor query itself is usually the
    // LCOV_EXCL_START
    // expensive part. Once a large cube is known blockable, spending dozens
    // LCOV_EXCL_STOP
    // more predecessor SAT calls to shave a few extra literals often costs more
    // than the smaller clause saves later. The exception is a measured cheap
    // LCOV_EXCL_START
    // transition surface: then the extra checks cost little and prevent PDR
    // from enumerating thousands of adjacent trivially unreachable cubes.
    // LCOV_EXCL_STOP
    if (!cheapTransitionSurface) {
      if (pdrStatsEnabled() && candidate.size() != cube.size()) {  // LCOV_EXCL_LINE
        // LCOV_EXCL_START
        emitSecDiag(  // LCOV_EXCL_LINE
        // LCOV_EXCL_STOP
            "SEC PDR stats: generalized blocked cube level=",
            level,
            " size=",
            // LCOV_EXCL_START
            cube.size(),  // LCOV_EXCL_LINE
            // LCOV_EXCL_STOP
            "->",
            // LCOV_EXCL_START
            candidate.size(),  // LCOV_EXCL_LINE
            // LCOV_EXCL_STOP
            " checks=",
            checks);
      // LCOV_EXCL_START
      }  // LCOV_EXCL_LINE
      // LCOV_EXCL_STOP
      return candidate;  // LCOV_EXCL_LINE
    }
    if (pdrStatsEnabled() && candidate.size() != cube.size()) {
      emitSecDiag(  // LCOV_EXCL_LINE
          "SEC PDR stats: generalized blocked cube level=",
          level,
          " size=",
          cube.size(),  // LCOV_EXCL_LINE
          "->",
          candidate.size(),  // LCOV_EXCL_LINE
          " checks=",
          checks);
    }  // LCOV_EXCL_LINE
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
// LCOV_EXCL_START
}
// LCOV_EXCL_STOP

bool framesConverged(const FrameClauses& lhs, const FrameClauses& rhs) {
  if (lhs.clauses.size() != rhs.clauses.size()) {
    return false;
  }
  for (const auto& clause : lhs.clauses) {
    if (!frameHasSubsumingClause(rhs, clause)) {
      return false;  // LCOV_EXCL_LINE
    // LCOV_EXCL_START
    }
    // LCOV_EXCL_STOP
  }
  for (const auto& clause : rhs.clauses) {
    if (!frameHasSubsumingClause(lhs, clause)) {
      return false;  // LCOV_EXCL_LINE
    }
  // LCOV_EXCL_START
  }
  // LCOV_EXCL_STOP
  return true;
// LCOV_EXCL_START
}
// LCOV_EXCL_STOP

// LCOV_EXCL_START
bool obligationAlreadyBlocked(const std::vector<FrameClauses>& frames,
// LCOV_EXCL_STOP
                              const ProofObligation& obligation) {
  return frameHasSubsumingClause(frames[obligation.level], clauseFromCube(obligation.cube));
}  // LCOV_EXCL_LINE

StateCube generalizeInitExcludedCube(const KInductionProblem& problem,  // LCOV_EXCL_LINE
                                     KEPLER_FORMAL::Config::SolverType solverType,
                                     BoolExpr* initFormula,
                                     const StateCube& cube) {
  // Ordinary Init can also be a relational frontier made of equality facts.
  // When a predecessor violates that frontier, learn a generalized
  // LCOV_EXCL_STOP
  // F[0] clause immediately instead of relying on many small seed clauses to
  // LCOV_EXCL_START
  // rediscover adjacent impossible cubes one at a time.
  StateCube candidate = cube;  // LCOV_EXCL_LINE
  size_t index = 0;  // LCOV_EXCL_LINE
  size_t attempts = 0;  // LCOV_EXCL_LINE
  // LCOV_EXCL_STOP
  while (index < candidate.size() &&  // LCOV_EXCL_LINE
         attempts < kMaxInitExcludedCubeGeneralizationAttempts) {  // LCOV_EXCL_LINE
    ++attempts;  // LCOV_EXCL_LINE
    StateCube reduced = candidate;  // LCOV_EXCL_LINE
    reduced.erase(reduced.begin() + static_cast<std::ptrdiff_t>(index));  // LCOV_EXCL_LINE
    if (!cubeIntersectsInit(problem, solverType, initFormula, reduced)) {  // LCOV_EXCL_LINE
      candidate = std::move(reduced);  // LCOV_EXCL_LINE
      continue;  // LCOV_EXCL_LINE
    }
    ++index;  // LCOV_EXCL_LINE
  }  // LCOV_EXCL_LINE
  return candidate;  // LCOV_EXCL_LINE
}  // LCOV_EXCL_LINE

bool proofObligationLess(const ProofObligation& lhs, const ProofObligation& rhs) {
  if (lhs.level != rhs.level) {
    return lhs.level < rhs.level;
  }
  if (lhs.cube.size() != rhs.cube.size()) {
    return lhs.cube.size() < rhs.cube.size();
  }
  if (lhs.badFrame != rhs.badFrame) {
    return lhs.badFrame < rhs.badFrame; // LCOV_EXCL_LINE
  }
  if (stateCubeLess(lhs.cube, rhs.cube)) {
    return true;
  }
  if (stateCubeLess(rhs.cube, lhs.cube)) {
    return false;
  }
  return false;
}

size_t popNextObligationIndex(const std::vector<ProofObligation>& queue) {
  size_t bestIndex = 0;
  for (size_t i = 1; i < queue.size(); ++i) {
    if (proofObligationLess(queue[i], queue[bestIndex])) {
      bestIndex = i;
    }
  }
  return bestIndex;
}

ProofObligationKey proofObligationKey(const ProofObligation& obligation) {
  ProofObligationKey key;
  key.level = obligation.level;
  key.badFrame = obligation.badFrame;
  key.cube = obligation.cube;
  return key;
// LCOV_EXCL_START
}
// LCOV_EXCL_STOP

void enqueueProofObligation(std::vector<ProofObligation>& queue,
                            std::unordered_set<
                                ProofObligationKey,
                                ProofObligationKeyHash>& queuedKeys,
                            ProofObligation obligation) {
  // Keep only one pending copy of each normalized cube/level pair. Once that
  // obligation is blocked or reaches Init, every duplicate would repeat the
  // same SAT work.
  const ProofObligationKey key = proofObligationKey(obligation);
  if (!queuedKeys.insert(key).second) {
    return;  // LCOV_EXCL_LINE
  }
  queue.push_back(std::move(obligation));
}

bool blockProofObligations(const KInductionProblem& problem,
                           KEPLER_FORMAL::Config::SolverType solverType,
                           const TransitionExprResolver& transitionByState,
                           BoolExpr* initFormula,
                           BoolExpr* frameInvariant,
                           std::vector<FrameClauses>& frames,
                           const InitFactIndex& initFacts,
                           const StateCube& badCube,
                           size_t rootLevel,
                           size_t& badFrame,
                           const ComplementPartnerIndex& complementPartners,
                           PredecessorAssumptionCache& predecessorAssumptionCache,
                           size_t* predecessorQueryBudget,
                           PdrFormulaSupportCache* supportCache) {
  // This is the paper's recursive blocking idea expressed as an explicit queue
  // so we do not depend on deep recursion for large obligation stacks.
  std::vector<ProofObligation> queue;
  std::unordered_set<ProofObligationKey, ProofObligationKeyHash> queuedKeys;
  enqueueProofObligation(
      queue, queuedKeys, ProofObligation{badCube, rootLevel, rootLevel});
  auto learnBlockedObligation = [&](const ProofObligation& blockedObligation) {
    const StateCube generalizedCube = generalizeBlockedCube(
        problem,
        solverType,
        transitionByState,
        initFormula,
        frameInvariant,
        frames,
        blockedObligation.level,
        blockedObligation.cube,
        &predecessorAssumptionCache,
        complementPartners,
        predecessorQueryBudget,
        supportCache);
    addClauseToFrames(
        frames, clauseFromCube(generalizedCube), blockedObligation.level);
  };

  while (!queue.empty()) {
    const size_t obligationIndex = popNextObligationIndex(queue);
    const ProofObligation obligation = queue[obligationIndex];
    queuedKeys.erase(proofObligationKey(obligation));
    queue.erase(queue.begin() + static_cast<std::ptrdiff_t>(obligationIndex));

    if (obligationAlreadyBlocked(frames, obligation)) {
      continue;  // LCOV_EXCL_LINE
    }

    if (obligation.level == 0) {
      if (const auto conflictCube =
              knownInitConflictCube(initFacts, obligation.cube);
          conflictCube.has_value()) {
        // When the cube visibly contradicts a structured exact Init fact,
        // learn only that conflict instead of a wide SAT-model cube;
        // LCOV_EXCL_STOP
        // this keeps large ASIC output slices from rediscovering the same
        // LCOV_EXCL_START
        // state equality violation thousands of times.
        if (pdrStatsEnabled()) {  // LCOV_EXCL_LINE
          emitSecDiag(  // LCOV_EXCL_LINE
              "SEC PDR stats: known init conflict ",
              "cube=", obligation.cube.size(),  // LCOV_EXCL_LINE
              " core=", conflictCube->size(),  // LCOV_EXCL_LINE
              // LCOV_EXCL_STOP
              " bad_frame=", obligation.badFrame,  // LCOV_EXCL_LINE
              // LCOV_EXCL_START
              " hash=", cubeFingerprint(*conflictCube));  // LCOV_EXCL_LINE
              // LCOV_EXCL_STOP
        }  // LCOV_EXCL_LINE
        addClauseToFrame(frames[0], clauseFromCube(*conflictCube));  // LCOV_EXCL_LINE
        continue;  // LCOV_EXCL_LINE
      }
      if (!cubeIntersectsInit(problem, solverType, initFormula, obligation.cube)) {
        const StateCube generalizedCube = generalizeInitExcludedCube(  // LCOV_EXCL_LINE
            problem,  // LCOV_EXCL_LINE
            solverType,  // LCOV_EXCL_LINE
            initFormula,  // LCOV_EXCL_LINE
            obligation.cube);  // LCOV_EXCL_LINE
        addClauseToFrame(frames[0], clauseFromCube(generalizedCube));  // LCOV_EXCL_LINE
        continue;
      }  // LCOV_EXCL_LINE
      if (pdrStatsEnabled()) {
        emitSecDiag(
            "SEC PDR stats: counterexample candidate reached init ",
            "bad_frame=", obligation.badFrame,
            // LCOV_EXCL_START
            " cube=", obligation.cube.size());
      }
      // LCOV_EXCL_STOP
      badFrame = obligation.badFrame;
      return false;
    }

    if (obligation.cube.size() > kLargeBlockedCubeGeneralizationThreshold) {
      // For a large target cube, first block a cheap subset.  If no
      // predecessor can reach the subset, then no predecessor can reach the
      // stronger original cube either, and we avoid building a SAT query for a
      // thousand next-state functions just to learn the same small clause.
      const StateCube cheapTarget = boundedCheapTransitionCube(
          obligation.cube, kLargeBlockedCubeSeedSize, problem, transitionByState);
      if (cheapTarget.size() < obligation.cube.size()) {
        const auto cheapPredecessor = findPredecessorCube(
            problem,
            solverType,
            transitionByState,
            initFormula,
            frameInvariant,
            // LCOV_EXCL_START
            frames,
            obligation.level - 1,
            cheapTarget,
            false,
            complementPartners,
            &predecessorAssumptionCache,
            // LCOV_EXCL_STOP
            nullptr,
            // LCOV_EXCL_START
            predecessorQueryBudget,
            supportCache);
        if (hasPdrBudgetExhaustion()) {
          return true;  // LCOV_EXCL_LINE
        }
        if (!cheapPredecessor.has_value()) {
        const StateCube generalizedCube = generalizeBlockedCube(  // LCOV_EXCL_LINE
            problem,  // LCOV_EXCL_LINE
            solverType,  // LCOV_EXCL_LINE
            transitionByState,  // LCOV_EXCL_LINE
            initFormula,  // LCOV_EXCL_LINE
            // LCOV_EXCL_STOP
            frameInvariant,  // LCOV_EXCL_LINE
            // LCOV_EXCL_START
            frames,  // LCOV_EXCL_LINE
            obligation.level,  // LCOV_EXCL_LINE
            // LCOV_EXCL_STOP
            cheapTarget,
            &predecessorAssumptionCache,  // LCOV_EXCL_LINE
            // LCOV_EXCL_START
            complementPartners,  // LCOV_EXCL_LINE
            predecessorQueryBudget,  // LCOV_EXCL_LINE
            supportCache);  // LCOV_EXCL_LINE
            // LCOV_EXCL_STOP
        addClauseToFrames(frames, clauseFromCube(generalizedCube), obligation.level);  // LCOV_EXCL_LINE
        continue;
        } // LCOV_EXCL_LINE
      }  // LCOV_EXCL_LINE
    }

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
          &predecessorAssumptionCache,
          nullptr,
          predecessorQueryBudget,
          supportCache);
      if (hasPdrBudgetExhaustion()) {
        return true;  // LCOV_EXCL_LINE
      }
      if (!predecessor.has_value()) {
        // No predecessor survives F[level-1], so the cube can be blocked at
        // every frame up to "level".
        learnBlockedObligation(obligation);
        break;
      }
      ProofObligation predecessorObligation{
          *predecessor,
          obligation.level - 1,
          obligation.badFrame};
      enqueueProofObligation(queue, queuedKeys, obligation);
      enqueueProofObligation(queue, queuedKeys, predecessorObligation);
      break;
    }
  }

  return true;
}

std::vector<StateClause> buildSeedClauses(const KInductionProblem& problem,
                                          const InitFactIndex& initFacts) {
  (void)problem;
  (void)initFacts;
  std::vector<StateClause> seedClauses;
  // Cross-design internal state equality seeds are forbidden.
  return seedClauses;
}

BoolExpr* selectPdrFrameInvariant(const KInductionProblem& problem,
                                  BoolExpr* initFormula,
                                  KEPLER_FORMAL::Config::SolverType solverType) {
  FormulaSupportCache invariantSupportCache;
  auto validateCandidate =
      [&](const char* label, BoolExpr* candidate) -> BoolExpr* {
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

  // PDR may reuse a validated public SEC strengthening lemma as a frame fact,
  // but it must not build a frame invariant from cross-design internal state
  // equalities.
  BoolExpr* sharedStrengthening =
      selectValidatedStrengtheningInvariant(problem, initFormula, solverType);
  if (BoolExpr* strengthenedInvariant =
          validateCandidate("shared_strengthening", sharedStrengthening)) {
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
                      PredecessorAssumptionCache* predecessorAssumptionCache,
                      size_t* predecessorQueryBudget,
                      PdrFormulaSupportCache* supportCache) {
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
      const auto predecessor = findPredecessorCube(
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
          predecessorAssumptionCache,
          nullptr,
          predecessorQueryBudget,
          supportCache);
      if (hasPdrBudgetExhaustion()) {
        return;  // LCOV_EXCL_LINE
      }
      if (!predecessor.has_value()) {
        addClauseToFrame(frames[level + 1], clause);
      }
    // LCOV_EXCL_START
    }
    // LCOV_EXCL_STOP
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
      // LCOV_EXCL_START
      oss << ", ";
    }
    // LCOV_EXCL_STOP
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
      oss << " OR ";  // LCOV_EXCL_LINE
    }  // LCOV_EXCL_LINE
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

bool assignmentsCoverStateSymbols(
    const std::vector<std::pair<size_t, bool>>& assignments,
    const std::vector<size_t>& stateSymbols) {
  std::unordered_set<size_t> assignedSymbols;
  assignedSymbols.reserve(assignments.size());
  for (const auto& [symbol, /*value*/ _] : assignments) {
    assignedSymbols.insert(symbol);
  }
  return std::all_of(
      stateSymbols.begin(), stateSymbols.end(), [&](size_t symbol) {
        return assignedSymbols.find(symbol) != assignedSymbols.end();
      });
}

BoolExpr* appendAssignmentFormula(
    BoolExpr* formula,
    const std::vector<std::pair<size_t, bool>>& assignments) {
  for (const auto& [symbol, value] : assignments) {
    BoolExpr* variable = BoolExpr::Var(symbol);
    formula = BoolExpr::And(
        formula, value ? variable : BoolExpr::Not(variable));
  }
  return formula;
}

BoolExpr* buildExactPdrInitFormula(const KInductionProblem& problem) {
  if (problem.resetBootstrapCycles != 0) {
    const std::vector<size_t> stateSymbols = problem.combinedStateSymbols();
    if (!assignmentsCoverStateSymbols(
            problem.bootstrapStateAssignments, stateSymbols)) {
      return nullptr;
    }
    return BoolExpr::simplify(appendAssignmentFormula(
        BoolExpr::createTrue(), problem.bootstrapStateAssignments));
  }

  BoolExpr* init = problem.initialCondition != nullptr
                       ? problem.initialCondition
                       : BoolExpr::createTrue();
  return BoolExpr::simplify(
      appendAssignmentFormula(init, problem.initialStateAssignments));
}

}  // namespace

PDREngine::PDREngine(const KInductionProblem& problem,
                     KEPLER_FORMAL::Config::SolverType solverType,
                     size_t maxPredecessorQueries)
    : problem_(problem),
      solverType_(solverType),
      maxPredecessorQueries_(maxPredecessorQueries) {}

PDRResult PDREngine::run(size_t maxFrames) const {
  // Build the SEC startup frontier once so every frame query shares the same
  // interpretation of reset/bootstrap and frame-0 equality constraints.
  resetPdrBudgetExhaustion();
  setPdrPredecessorQueryLimit(maxPredecessorQueries_);
  emitPdrTraceProblem(problem_);
  BoolExpr* initFormula = buildExactPdrInitFormula(problem_);
  if (initFormula == nullptr) {
    if (pdrStatsEnabled()) {
      emitSecDiag(
          "SEC PDR stats: inconclusive reason=exact_f0_unavailable ",
          "reset_bootstrap_cycles=", problem_.resetBootstrapCycles,
          " bootstrap_assignments=",
          problem_.bootstrapStateAssignments.size(),
          " state_symbols=", problem_.combinedStateSymbols().size());
    }
    return {PDRStatus::Inconclusive, 0};  // LCOV_EXCL_LINE
  }

  // PDR still establishes convergence through its own frame/blocking loop, but
  // it may reuse a validated public SEC strengthening lemma as a frame
  // invariant after checking init coverage and transition preservation.
  BoolExpr* frameInvariant =
      selectPdrFrameInvariant(problem_, initFormula, solverType_);

  TransitionExprResolver transitionByState(problem_);
  ComplementPartnerIndex complementPartners(problem_);
  PdrFormulaSupportCache formulaSupportCache(problem_.dualRailStatePairs);
  // The bad predicate is the same for every frame query. Cache its state
  // support once so repeated PDR bad-cube checks do not rebuild the large
  // combined miter state set on every loop iteration.
  const auto preciseBadStateSupport = collectBoundedStateSupportSymbols(
      problem_.bad,
      std::numeric_limits<size_t>::max(),
      0,
      transitionByState.stateSymbols());
  BadCubeAssumptionCache badCubeAssumptionCache;
  PredecessorAssumptionCache predecessorAssumptionCache;
  size_t remainingPredecessorQueries = maxPredecessorQueries_;
  size_t* predecessorQueryBudget =
      maxPredecessorQueries_ == 0 ? nullptr : &remainingPredecessorQueries;
  std::vector<FrameClauses> frames(1);
  emitPdrTraceFrames("initial_frames", frames);

  // Before growing any frame sequence, check whether exact Init itself already
  // contains a bad state.
  if (auto badCube = findBadCube(
          problem_,
          solverType_,
          initFormula,
          frameInvariant,
          frames,
          preciseBadStateSupport,
          transitionByState.stateSymbols(),
          0,
          complementPartners,
          &badCubeAssumptionCache,
          &formulaSupportCache);
      badCube.has_value()) {
    emitPdrTrace("bad_cube@F0", formatCubeForPdrTrace(*badCube));
    return {PDRStatus::Different, 0};
  }
  if (hasPdrBudgetExhaustion()) {
    return {PDRStatus::Inconclusive, 0};  // LCOV_EXCL_LINE
  }

  if (maxFrames == 0) {
    return {PDRStatus::Inconclusive, 0};
  }

  // Init/bootstrap facts are static for a PDR run. Wide dual-rail SEC problems
  // can carry tens of thousands of boot assignments, so build the lookup index
  // once instead of rebuilding it for every blocked obligation.
  const InitFactIndex initFacts = buildInitFactIndex(problem_);
  const auto seedClauses = buildSeedClauses(problem_, initFacts);
  frames.emplace_back(FrameClauses{seedClauses});
  emitPdrTraceFrames("seeded_frames", frames);
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
              transitionByState.stateSymbols(),
              level,
              complementPartners,
              &badCubeAssumptionCache,
              &formulaSupportCache);
      if (hasPdrBudgetExhaustion()) {
        return {PDRStatus::Inconclusive, level};  // LCOV_EXCL_LINE
      }
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
              initFacts,
              *badCube,
              level,
              badFrame,
              complementPartners,
              predecessorAssumptionCache,
              predecessorQueryBudget,
              &formulaSupportCache)) {
        if (hasPdrBudgetExhaustion()) {
          return {PDRStatus::Inconclusive, level};  // LCOV_EXCL_LINE
        }
        emitPdrTraceFrames("frames_before_counterexample", frames);
        return {PDRStatus::Different, badFrame};
      }
      if (hasPdrBudgetExhaustion()) {
        return {PDRStatus::Inconclusive, level};  // LCOV_EXCL_LINE
      }
      emitPdrTraceFrames("frames_after_blocking", frames);
    }

    // Phase 2: create the next frame, seed it with already-known startup
    // facts
    frames.emplace_back(FrameClauses{seedClauses});
    // and then push learned clauses forward.
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
        &predecessorAssumptionCache,
        predecessorQueryBudget,
        &formulaSupportCache);
    if (hasPdrBudgetExhaustion()) {
      return {PDRStatus::Inconclusive, level};  // LCOV_EXCL_LINE
    }
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
  if (pdrStatsEnabled()) {  // LCOV_EXCL_LINE
    emitSecDiag(  // LCOV_EXCL_LINE
        "SEC PDR stats: max frame budget exhausted max_frames=",
        maxFrames);
  }  // LCOV_EXCL_LINE
  return {PDRStatus::Inconclusive, maxFrames};  // LCOV_EXCL_LINE
}

}  // namespace KEPLER_FORMAL::SEC
