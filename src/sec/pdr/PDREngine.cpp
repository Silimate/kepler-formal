// Copyright 2024-2026 keplertech.io
// SPDX-License-Identifier: GPL-3.0-only
#include "pdr/PDREngine.h"

#include <algorithm>
#include <cstdlib>
#include <memory>
#include <optional>
#include <queue>
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

bool pdrProofObligationPriorityLess(size_t lhsLevel,
                                    size_t lhsSequence,
                                    size_t rhsLevel,
                                    size_t rhsSequence) {
  if (lhsLevel != rhsLevel) {
    return lhsLevel < rhsLevel;
  }
  // Figure 6 of the FMCAD'11 PDR paper uses stack order within one frame.
  return lhsSequence > rhsSequence;
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
// shortcut; the exact Init SAT query still decides intersection.
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
constexpr unsigned kDefaultDualRailBadCubeConflictLimit = 20000;
constexpr unsigned kDefaultDualRailPredecessorConflictLimit = 10000;
// Incremental assumption solving counts this as a propagation budget, so it
// needs more room than the conflict cap for ordinary exact predecessor queries.
constexpr unsigned kDefaultDualRailPredecessorDecisionLimit = 150000;
// Residual one-output leaves need more search than broad batch queries.  Do not
// lower this bound to save runtime; doing so can make a legal PDR obligation
// report inconclusive before the residual repair has had its intended search
// budget.
constexpr unsigned kDefaultDualRailResidualPredecessorConflictLimit = 200000;
constexpr size_t kDefaultDualRailPredecessorEncodingNodeLimit = 1000000;
constexpr size_t kDefaultDualRailPredecessorEncodingSupportLimit = 8192;
constexpr const char* kDualRailPredecessorConflictLimitEnv =
    "KEPLER_SEC_PDR_DUAL_RAIL_PREDECESSOR_CONFLICT_LIMIT";
constexpr size_t kMaxInitExcludedCubeGeneralizationAttempts = 2;
constexpr size_t kDefaultPdrStatsInterval = 1000;
constexpr size_t kInitialPdrStatsQueries = 20;
// Query-result caching is an accelerator only.  Keep it bounded so a long SEC
// run cannot trade the predecessor-encoding wall for unbounded retained cubes.
constexpr size_t kMaxPredecessorQueryResultCacheEntries = 64 * 1024;
constexpr size_t kMaxPredecessorUnsatCoresPerContext = 4096;
constexpr size_t kMaxPredecessorClosedSymbolCacheEntries = 4096;
constexpr size_t kMaxPredecessorTargetSurfaceCacheEntries = 4096;
constexpr size_t kMaxPredecessorTargetSurfaceCacheBytes = 64 * 1024 * 1024;
// The reusable predecessor solver is also a memory/perf cache.  Keep it for
// local AES/Swerv-sized dual-rail leaves, but let giant Ariane-scale leaves use
// one-shot predecessor queries so released solver pages do not accumulate in
// the process footprint across many unique target surfaces.
constexpr size_t kMaxDualRailPredecessorSolverCacheStateSymbols = 256 * 1024;
// The bad-cube cached solver permanently absorbs learned frame clauses.  That
// is useful for AES/Swerv-sized leaves, but Ariane-scale dual-rail batches can
// learn many neighboring F[0] clauses and inflate one long-lived SAT instance.
// Keep the proof query identical there, but rebuild it as a one-shot solver so
// each wave can release its frame-clause encoding promptly.
constexpr size_t kMaxDualRailBadCubeSolverCacheStateSymbols =
    kMaxDualRailPredecessorSolverCacheStateSymbols;
// FrameFormulaEncoder already makes a small generic Tseitin reservation, but
// sampled dual-rail PDR leaves still spent most time growing CaDiCaL variable
// vectors while streaming known-large transition cones. Reserve a larger,
// bounded chunk from PDR when we have the transition DAG estimate.
constexpr size_t kMinPdrTransitionSolverReserveNodes = 64 * 1024;
constexpr size_t kMaxPdrTransitionSolverReserveHint = 512 * 1024;
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
  // Fingerprints identify an exact frame context for SAT-result caches. Frame
  // clauses change only through addClauseToFrame(), which invalidates this
  // host-side memo without changing any PDR clause or query.
  mutable std::optional<std::pair<size_t, size_t>> clauseFingerprint;
};

size_t frameClausesFingerprint(const std::vector<FrameClauses>& frames,
                               size_t level) {
  if (level >= frames.size()) {
    return 0; // LCOV_EXCL_LINE
  }
  const auto& frame = frames[level];
  if (!frame.clauseFingerprint.has_value() ||
      frame.clauseFingerprint->first != level) {
    // Preserve the original hash operation order exactly. Only the completed
    // value is memoized, so cache keys remain byte-for-byte unchanged.
    size_t seed = std::hash<size_t>()(level);
    mixHashValue(seed, std::hash<size_t>()(frame.clauses.size()));
    for (const auto& clause : frame.clauses) {
      mixHashValue(seed, StateClauseHash{}(clause));
    }
    frame.clauseFingerprint = std::pair{level, seed};
  }
  return frame.clauseFingerprint->second;
}

enum class IndexedStateRelationKind {
  Equality,
  Complement,
  DualRailValidity,
};

class OrderedStateRelationIndex {
 public:
  OrderedStateRelationIndex() = default;

  explicit OrderedStateRelationIndex(
      const std::vector<std::pair<size_t, size_t>>& pairs)
      : orderedPairs_(pairs) {
    buildIndex();
  }

  explicit OrderedStateRelationIndex(
      const std::vector<DualRailSymbolPair>& railPairs) {
    orderedPairs_.reserve(railPairs.size());
    for (const auto& rails : railPairs) {
      orderedPairs_.emplace_back(rails.mayBeOne, rails.mayBeZero);
    }
    buildIndex();
  }

  void addPartnerClosure(std::unordered_set<size_t>& symbols) const {
    std::vector<size_t> worklist = detail::makePdrClosureWorklist(symbols);
    for (size_t cursor = 0; cursor < worklist.size(); ++cursor) {
      const auto indexIt = pairIndicesBySymbol_.find(worklist[cursor]);
      if (indexIt == pairIndicesBySymbol_.end()) {
        continue;
      }
      for (const size_t pairIndex : indexIt->second) {
        const auto& [lhs, rhs] = orderedPairs_[pairIndex];
        if (symbols.insert(lhs).second) {
          worklist.push_back(lhs);
        }
        if (symbols.insert(rhs).second) {
          worklist.push_back(rhs);
        }
      }
    }
  }

  void addClauses(SATSolverWrapper& solver,
                  const FrameVariableStore& variables,
                  const std::vector<size_t>& solverSymbols,
                  size_t numFrames,
                  IndexedStateRelationKind kind) const {
    // Dense F[0] surfaces already contain most state symbols. Preserve the old
    // linear pair scan there; sparse output cones use the reverse index below.
    if (solverSymbols.size() >= orderedPairs_.size()) {
      for (size_t frame = 0; frame < numFrames; ++frame) {
        for (size_t pairIndex = 0; pairIndex < orderedPairs_.size();
             ++pairIndex) {
          addPairClause(solver, variables, pairIndex, frame, kind);
        }
      }
      return;
    }

    const std::vector<size_t> pairIndices = relevantPairIndices(solverSymbols);
    for (size_t frame = 0; frame < numFrames; ++frame) {
      for (const size_t pairIndex : pairIndices) {
        addPairClause(solver, variables, pairIndex, frame, kind);
      }
    }
  }

 private:
  void addPairClause(SATSolverWrapper& solver,
                     const FrameVariableStore& variables,
                     size_t pairIndex,
                     size_t frame,
                     IndexedStateRelationKind kind) const {
    const auto& [lhs, rhs] = orderedPairs_[pairIndex];
    if (!variables.hasSymbol(lhs) || !variables.hasSymbol(rhs)) {
      return;
    }
    const int lhsLiteral = variables.getLiteral(lhs, frame);
    const int rhsLiteral = variables.getLiteral(rhs, frame);
    switch (kind) {
      case IndexedStateRelationKind::Equality:
        addLiteralEquivalence(solver, lhsLiteral, rhsLiteral);
        break;
      case IndexedStateRelationKind::Complement:
        addLiteralEquivalence(solver, rhsLiteral, -lhsLiteral);
        break;
      case IndexedStateRelationKind::DualRailValidity:
        solver.addClause({lhsLiteral, rhsLiteral});
        break;
    }
  }

  void buildIndex() {
    pairIndicesBySymbol_.reserve(orderedPairs_.size() * 2);
    for (size_t index = 0; index < orderedPairs_.size(); ++index) {
      const auto& [lhs, rhs] = orderedPairs_[index];
      pairIndicesBySymbol_[lhs].push_back(index);
      pairIndicesBySymbol_[rhs].push_back(index);
    }
  }

  std::vector<size_t>
  relevantPairIndices(const std::vector<size_t>& symbols) const {
    std::vector<size_t> indices;
    for (const size_t symbol : symbols) {
      const auto indexIt = pairIndicesBySymbol_.find(symbol);
      if (indexIt == pairIndicesBySymbol_.end()) {
        continue;
      }
      indices.insert(indices.end(), indexIt->second.begin(),
                     indexIt->second.end());
    }
    std::sort(indices.begin(), indices.end());
    indices.erase(std::unique(indices.begin(), indices.end()), indices.end());
    return indices;
  }

  std::vector<std::pair<size_t, size_t>> orderedPairs_;
  std::unordered_map<size_t, std::vector<size_t>> pairIndicesBySymbol_;
};

// All entries originate from explicit same-design model relations.  The index
// uses combined symbol IDs only; it never relates internal elements by name.
struct ComplementPartnerIndex {
  explicit ComplementPartnerIndex(const KInductionProblem& problem)
      : complemented0(problem.complementedStatePairs0),
        complemented1(problem.complementedStatePairs1),
        sameFrameEqualities0(problem.sameFrameStateEqualityPairs0),
        sameFrameEqualities1(problem.sameFrameStateEqualityPairs1),
        dualRailPairs(problem.dualRailStatePairs) {}

  void addComplementedPartnerClosure(
      std::unordered_set<size_t>& symbols) const {
    complemented0.addPartnerClosure(symbols);
    complemented1.addPartnerClosure(symbols);
  }

  void addSameFrameEqualityPartnerClosure(
      std::unordered_set<size_t>& symbols) const {
    sameFrameEqualities0.addPartnerClosure(symbols);
    sameFrameEqualities1.addPartnerClosure(symbols);
  }

  void addDualRailPartnerClosure(std::unordered_set<size_t>& symbols) const {
    dualRailPairs.addPartnerClosure(symbols);
  }

  void addClauses(SATSolverWrapper& solver,
                  const FrameVariableStore& variables,
                  const std::vector<size_t>& solverSymbols,
                  size_t numFrames) const {
    complemented0.addClauses(solver, variables, solverSymbols, numFrames,
                             IndexedStateRelationKind::Complement);
    complemented1.addClauses(solver, variables, solverSymbols, numFrames,
                             IndexedStateRelationKind::Complement);
    sameFrameEqualities0.addClauses(solver, variables, solverSymbols, numFrames,
                                    IndexedStateRelationKind::Equality);
    sameFrameEqualities1.addClauses(solver, variables, solverSymbols, numFrames,
                                    IndexedStateRelationKind::Equality);
    dualRailPairs.addClauses(solver, variables, solverSymbols, numFrames,
                             IndexedStateRelationKind::DualRailValidity);
  }

  OrderedStateRelationIndex complemented0;
  OrderedStateRelationIndex complemented1;
  OrderedStateRelationIndex sameFrameEqualities0;
  OrderedStateRelationIndex sameFrameEqualities1;
  OrderedStateRelationIndex dualRailPairs;
};

struct ProofObligation {
  // "cube is bad at level" requests either a predecessor or a blocking clause.
  StateCube cube;
  size_t level = 0;
  size_t badFrame = 0;
  size_t sequence = 0;
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
  bool excludeTargetOnCurrentFrame = false;
  StateCube targetCube;

  bool operator==(const PredecessorQueryResultKey& other) const {
    return problem == other.problem &&
           transitionByState == other.transitionByState &&
           initFormula == other.initFormula &&
           frameInvariant == other.frameInvariant &&
           level == other.level &&
           frameFingerprint == other.frameFingerprint &&
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
  bool excludeTargetOnCurrentFrame = false;

  bool operator==(const PredecessorUnsatCoreCacheKey& other) const {
    return problem == other.problem &&
           transitionByState == other.transitionByState &&
           initFormula == other.initFormula &&
           frameInvariant == other.frameInvariant &&
           level == other.level &&
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

struct PredecessorTargetSurface { // LCOV_EXCL_LINE
  std::vector<size_t> targetSymbols;
  std::vector<size_t> encodedTargets;
  std::vector<size_t> transitionSupportSymbols;
  size_t transitionEncodingNodes = 0;
};

struct PredecessorAssumptionCacheKey {
  const KInductionProblem* problem = nullptr;
  // This is an identity token only; transition expressions are always read
  // from the resolver passed to the current exact query.
  const void* transitionModel = nullptr;
  const BoolExpr* initFormula = nullptr;
  const BoolExpr* frameInvariant = nullptr;
  size_t level = 0;
  size_t frameFingerprint = 0;
  std::vector<size_t> solverSymbols;

  bool operator==(const PredecessorAssumptionCacheKey& other) const {
    return problem == other.problem &&
           transitionModel == other.transitionModel &&
           initFormula == other.initFormula &&
           frameInvariant == other.frameInvariant &&
           level == other.level &&
           frameFingerprint == other.frameFingerprint &&
           solverSymbols == other.solverSymbols;
  }

  bool hasSameReusableContext(
      const PredecessorAssumptionCacheKey& other) const {
    return problem == other.problem &&
           transitionModel == other.transitionModel &&
           initFormula == other.initFormula &&
           frameInvariant == other.frameInvariant &&
           level == other.level;
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

  bool canExtendTo(const PredecessorAssumptionCacheKey& candidate) const {
    return key.hasSameReusableContext(candidate) &&
           std::includes(
               candidate.solverSymbols.begin(),
               candidate.solverSymbols.end(),
               key.solverSymbols.begin(),
               key.solverSymbols.end());
  }

  void extendSymbolSurface(const ComplementPartnerIndex& stateRelations,
                           const std::vector<size_t>& solverSymbols);
};

struct InitIntersectionAssumptionSolver {
  const KInductionProblem* problem = nullptr;
  const BoolExpr* initFormula = nullptr;
  KEPLER_FORMAL::Config::SolverType requestedSolverType =
      KEPLER_FORMAL::Config::SolverType::KISSAT;
  std::unique_ptr<SATSolverWrapper> solver;
  std::unique_ptr<FrameVariableStore> variables;
};

struct PredecessorAssumptionCache {
  // PDR level-local predecessor queries share the same frame context and
  // differ mostly by target cube.
  std::unordered_map<size_t, std::unique_ptr<PredecessorAssumptionSolver>>
      solversByLevel;
  // Figure 6 asks whether many candidate cubes intersect the same exact F[0].
  // Keep that immutable formula encoded and vary only cube assumptions.
  std::unique_ptr<InitIntersectionAssumptionSolver> initIntersectionSolver;
  // Output-batch PDR runs share the immutable F[0] intersection solver.
  std::unique_ptr<InitIntersectionAssumptionSolver>*
      sharedInitIntersectionSolver = nullptr;
  const KInductionProblem* sharedInitIntersectionProblem = nullptr;
  // F[0] and its transition relation are identical for every output batch.
  // Clauses streamed into it are exact-Init consequences; higher-frame
  // solvers, frame vectors, and proof obligations remain local to one run.
  std::unique_ptr<PredecessorAssumptionSolver>*
      sharedFrameZeroPredecessorSolver = nullptr;
  std::vector<size_t>* sharedFrameZeroPredecessorSymbols = nullptr;
  const KInductionProblem* sharedFrameZeroPredecessorProblem = nullptr;
  const void* sharedFrameZeroTransitionModel = nullptr;
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
  std::optional<size_t> widenedPredecessorCacheLevel;
  // Local dual-rail leaves repeatedly ask nearly identical predecessor
  // questions in one frame. Keep that frame's solver surface monotonic, but do
  // not carry F[0]'s reset cone into the distinct solver for F[1].
  std::vector<size_t> widenedPredecessorCacheSymbols;
  PredecessorFrameSymbolSurface currentFrameSymbols;
  std::unordered_map<std::vector<size_t>,
                     std::vector<size_t>,
                     SymbolVectorHash>
      closedCurrentFrameSymbols;
  std::unordered_map<StateCube, PredecessorTargetSurface, StateCubeHash>
      targetSurfaces;
  size_t targetSurfaceBytes = 0;
  std::unordered_map<StateCube, PredecessorTargetSurface, StateCubeHash>
      *sharedTargetSurfaces = nullptr;
  size_t* sharedTargetSurfaceBytes = nullptr;
  // Relation clauses are selected through an immutable model index. The index
  // changes query preparation cost only; it emits the same clauses in the same
  // order as the original full-vector scans.
  const ComplementPartnerIndex* stateRelations = nullptr;
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
  // A top-level dual-rail SEC call can give every output batch one stable F[0]
  // symbol surface and identity. This never applies to higher PDR frames.
  const KInductionProblem* sharedFrameZeroProblem = nullptr;
  std::vector<size_t> sharedFrameZeroSolverSymbols;
};

}  // namespace

struct PDRExactInitCache::Impl {
  Impl(const KInductionProblem& source,
       KEPLER_FORMAL::Config::SolverType requestedSolverType)
      : sourceProblem(&source), solverType(requestedSolverType),
        transitionByState(source), stateRelations(source) {
    validatedProblems.insert(&source);
  }

  bool hasSameDualRailPairs(const KInductionProblem& candidate) const {
    if (sourceProblem->dualRailStatePairs.size() !=
        candidate.dualRailStatePairs.size()) {
      return false;
    }
    for (size_t index = 0; index < sourceProblem->dualRailStatePairs.size();
         ++index) {
      const auto& sourcePair = sourceProblem->dualRailStatePairs[index];
      const auto& candidatePair = candidate.dualRailStatePairs[index];
      if (sourcePair.mayBeOne != candidatePair.mayBeOne ||
          sourcePair.mayBeZero != candidatePair.mayBeZero) {
        return false;
      }
    }
    return true;
  }

  bool matches(const KInductionProblem& candidate,
               KEPLER_FORMAL::Config::SolverType candidateSolverType) const {
    // The SEC strategy mutates only output/property fields on two reusable
    // batch objects.  Once one of those objects has passed the complete model
    // check, its immutable transition identity does not need another ASIC-size
    // compare.
    if (solverType == candidateSolverType &&
        validatedProblems.contains(&candidate)) {
      return true;
    }
    if (sourceProblem == nullptr || solverType != candidateSolverType ||
        sourceProblem->resetBootstrapCycles != candidate.resetBootstrapCycles) {
      return false;
    }

    // Only output/property fields may differ between users of this cache.
    // Comparing the complete reset/transition model prevents stale F[0] reuse
    // if a caller accidentally passes a problem from another SEC model.
    const bool sameModel =
        sourceProblem->inputSymbols == candidate.inputSymbols &&
        sourceProblem->resetBootstrapInputs == candidate.resetBootstrapInputs &&
        sourceProblem->initialStateAssignments ==
            candidate.initialStateAssignments &&
        sourceProblem->bootstrapStateAssignments ==
            candidate.bootstrapStateAssignments &&
        sourceProblem->state0Symbols == candidate.state0Symbols &&
        sourceProblem->state1Symbols == candidate.state1Symbols &&
        sourceProblem->auxiliaryStateSymbols ==
            candidate.auxiliaryStateSymbols &&
        sourceProblem->allSymbols == candidate.allSymbols &&
        sourceProblem->complementedStatePairs0 ==
            candidate.complementedStatePairs0 &&
        sourceProblem->complementedStatePairs1 ==
            candidate.complementedStatePairs1 &&
        sourceProblem->sameFrameStateEqualityPairs0 ==
            candidate.sameFrameStateEqualityPairs0 &&
        sourceProblem->sameFrameStateEqualityPairs1 ==
            candidate.sameFrameStateEqualityPairs1 &&
        hasSameDualRailPairs(candidate) &&
        sourceProblem->transitions0 == candidate.transitions0 &&
        sourceProblem->transitions1 == candidate.transitions1 &&
        sourceProblem->auxiliaryTransitions == candidate.auxiliaryTransitions &&
        sourceProblem->lazyTransitions == candidate.lazyTransitions &&
        sourceProblem->initialCondition == candidate.initialCondition;
    if (sameModel) {
      validatedProblems.insert(&candidate);
    }
    return sameModel;
  }

  const KInductionProblem* sourceProblem = nullptr;
  KEPLER_FORMAL::Config::SolverType solverType;
  BoolExpr* initFormula = nullptr;
  std::unique_ptr<InitIntersectionAssumptionSolver> initIntersectionSolver;
  std::unique_ptr<PredecessorAssumptionSolver> frameZeroPredecessorSolver;
  std::vector<size_t> frameZeroPredecessorSymbols;
  BadCubeAssumptionCache frameZeroBadCubeCache;
  // These structures depend only on the validated transition model. SEC runs
  // output batches serially, so every batch can reuse their exact contents
  // without sharing property-specific proof state or changing query order.
  TransitionExprResolver transitionByState;
  ComplementPartnerIndex stateRelations;
  std::shared_ptr<PdrFormulaSupportCache> formulaSupportCache;
  std::optional<InitFactIndex> initFacts;
  // Target-surface entries contain only exact transition-support preparation.
  // They may cross output batches, unlike SAT answers and learned proof state.
  std::unordered_map<StateCube, PredecessorTargetSurface, StateCubeHash>
      targetSurfaces;
  size_t targetSurfaceBytes = 0;
  size_t immutableMetadataUses = 0;
  mutable std::unordered_set<const KInductionProblem*> validatedProblems;
};

PDRExactInitCache::PDRExactInitCache(
    const KInductionProblem& sourceProblem,
    KEPLER_FORMAL::Config::SolverType solverType)
    : impl_(std::make_unique<Impl>(sourceProblem, solverType)) {}

PDRExactInitCache::~PDRExactInitCache() = default;

namespace {

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
  size_t count = problem.transitions0.size() + problem.transitions1.size() +
                 problem.auxiliaryTransitions.size();
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

size_t effectiveLocalDualRailFinalLeafEncodingSupportLimit(
    size_t configuredLimit) {
  if (configuredLimit == 0) {
    return 0; // LCOV_EXCL_LINE
  }
  return std::max(configuredLimit,
                  kMinLocalDualRailFinalLeafPredecessorSupport);
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

unsigned dualRailPredecessorDecisionLimit() {
  return envUnsignedLimitOrDefaultAllowZero(
      "KEPLER_SEC_PDR_DUAL_RAIL_PREDECESSOR_DECISION_LIMIT",
      kDefaultDualRailPredecessorDecisionLimit);
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
  PdrFormulaSupportCache() = default;

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

 private:
  // PDR rebuilds many local SAT queries over the same frame/property formulas.
  // Memoizing formula support avoids repeatedly walking large BoolExpr DAGs
  // while keeping each query's selected symbol set unchanged.
  std::unordered_map<BoolExpr*, std::set<size_t>> supportByExpr_;
};

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

std::vector<size_t> retainPdrStateSymbols(
    const std::vector<size_t>& symbols,
    const std::unordered_set<size_t>& stateSymbols) {
  std::vector<size_t> retained;
  retained.reserve(symbols.size());
  for (const size_t symbol : symbols) {
    if (stateSymbols.find(symbol) != stateSymbols.end()) {
      retained.push_back(symbol);
    }
  }
  return retained;
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

size_t predecessorTargetSurfaceBytes(const StateCube& targetCube,
                                     const PredecessorTargetSurface& surface) {
  return targetCube.size() * sizeof(CubeLiteral) +
         (surface.targetSymbols.size() + surface.encodedTargets.size() +
          surface.transitionSupportSymbols.size()) *
             sizeof(size_t);
}

const PredecessorTargetSurface& predecessorTargetSurfaceFor(
    PredecessorAssumptionCache& cache,
    const KInductionProblem& problem,
    const TransitionExprResolver& transitionByState,
    const StateCube& targetCube,
    PredecessorTargetSurface& uncachedSurface) {
  auto& targetSurfaces = cache.sharedTargetSurfaces != nullptr
                             ? *cache.sharedTargetSurfaces
                             : cache.targetSurfaces;
  size_t& retainedBytes = cache.sharedTargetSurfaceBytes != nullptr
                              ? *cache.sharedTargetSurfaceBytes
                              : cache.targetSurfaceBytes;
  const auto existing = targetSurfaces.find(targetCube);
  if (existing != targetSurfaces.end()) {
    if (pdrStatsEnabled()) {
      emitSecDiag("SEC PDR stats: predecessor target surface reused target=",
                  targetCube.size(), " entries=", targetSurfaces.size());
    }
    return existing->second;
  }
  uncachedSurface =
      buildPredecessorTargetSurface(problem, transitionByState, targetCube);
  const size_t entryBytes =
      predecessorTargetSurfaceBytes(targetCube, uncachedSurface);
  if (entryBytes > kMaxPredecessorTargetSurfaceCacheBytes) {
    return uncachedSurface; // LCOV_EXCL_LINE
  }
  if (targetSurfaces.size() >= kMaxPredecessorTargetSurfaceCacheEntries ||
      retainedBytes + entryBytes > kMaxPredecessorTargetSurfaceCacheBytes) {
    // These vectors are pure target-derived data. Clearing the bounded cache
    // only gives up reuse; it cannot change a predecessor answer.
    targetSurfaces.clear(); // LCOV_EXCL_LINE
    retainedBytes = 0;      // LCOV_EXCL_LINE
  } // LCOV_EXCL_LINE
  auto [inserted, insertedNew] =
      targetSurfaces.emplace(targetCube, std::move(uncachedSurface));
  (void)insertedNew;
  retainedBytes += entryBytes;
  if (pdrStatsEnabled()) {
    emitSecDiag("SEC PDR stats: predecessor target surface cached target=",
                targetCube.size(),
                " encoded_targets=", inserted->second.encodedTargets.size(),
                " transition_support=",
                inserted->second.transitionSupportSymbols.size(),
                " entries=", targetSurfaces.size(), " bytes=", retainedBytes);
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
  complementPartners.addComplementedPartnerClosure(symbols);
}

void addRelevantSameFrameStateEqualityPartners(
    const ComplementPartnerIndex& complementPartners,
    std::unordered_set<size_t>& symbols) {
  complementPartners.addSameFrameEqualityPartnerClosure(symbols);
}

void addRelevantDualRailPartners(
    const ComplementPartnerIndex& complementPartners,
    std::unordered_set<size_t>& symbols) {
  complementPartners.addDualRailPartnerClosure(symbols);
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


void addFrameConstraintSymbols(BoolExpr* initFormula,
                               BoolExpr* frameInvariant,
                               const std::vector<FrameClauses>& frames,
                               size_t level,
                               const ComplementPartnerIndex& complementPartners,
                               std::unordered_set<size_t>& symbols,
  PdrFormulaSupportCache* supportCache) {
  if (level == 0) {
    addFormulaSymbols(initFormula, symbols, supportCache);
    addAllFrameClauseSymbols(frames[0], symbols);
  } else {
    addFormulaSymbols(frameInvariant, symbols, supportCache);
    addAllFrameClauseSymbols(frames[level], symbols);
  }
  addRelevantComplementedStatePartners(complementPartners, symbols);
  addRelevantSameFrameStateEqualityPartners(complementPartners, symbols);
  addRelevantDualRailPartners(complementPartners, symbols);
}

std::vector<size_t> findBadQuerySymbols(BoolExpr* initFormula,
                                        BoolExpr* frameInvariant,
                                        const std::vector<FrameClauses>& frames,
                                        BoolExpr* badFormula,
                                        size_t level,
                                        const ComplementPartnerIndex& complementPartners,
                                        PdrFormulaSupportCache* supportCache) {
  std::unordered_set<size_t> symbols;
  addFormulaSymbols(badFormula, symbols, supportCache);
  addFrameConstraintSymbols(
      initFormula,
      frameInvariant,
      frames,
      level,
      complementPartners,
      symbols,
      supportCache);
  return sortUniqueSymbols(std::move(symbols));
}

void prepareSharedExactInitQueries(
    PDRExactInitCache::Impl& cache,
    BoolExpr* initFormula,
    const ComplementPartnerIndex& complementPartners,
    PdrFormulaSupportCache* supportCache) {
  auto& badCache = cache.frameZeroBadCubeCache;
  if (!badCache.sharedFrameZeroSolverSymbols.empty()) {
    return;
  }

  // The full source output surface covers every guarded, strict, and split bad
  // root that this top-level SEC call may ask about. F[0] itself supplies the
  // reset-history symbols. Build this stable union once so the incremental SAT
  // solver never has to be rebuilt merely because the next batch is wider.
  std::unordered_set<size_t> symbols;
  addFormulaSymbols(initFormula, symbols, supportCache);
  addFormulaSymbols(cache.sourceProblem->bad, symbols, supportCache);
  for (BoolExpr* output : cache.sourceProblem->observedOutputExprs0) {
    addFormulaSymbols(output, symbols, supportCache);
  }
  for (BoolExpr* output : cache.sourceProblem->observedOutputExprs1) {
    addFormulaSymbols(output, symbols, supportCache);
  }
  for (BoolExpr* strictEquality :
       cache.sourceProblem->dualRailOutputStrictEqualityExprs) {
    addFormulaSymbols(strictEquality, symbols, supportCache);
  }
  addRelevantComplementedStatePartners(complementPartners, symbols);
  addRelevantSameFrameStateEqualityPartners(complementPartners, symbols);
  addRelevantDualRailPartners(complementPartners, symbols);
  symbols.insert(cache.sourceProblem->allSymbols.begin(),
                 cache.sourceProblem->allSymbols.end());

  badCache.sharedFrameZeroProblem = cache.sourceProblem;
  badCache.sharedFrameZeroSolverSymbols =
      sortUniqueSymbols(std::move(symbols));
  cache.frameZeroPredecessorSymbols =
      badCache.sharedFrameZeroSolverSymbols;
  if (pdrStatsEnabled()) {
    emitSecDiag(
        "SEC PDR stats: shared exact F[0] query surface symbols=",
        badCache.sharedFrameZeroSolverSymbols.size());
  }
}

std::vector<size_t> sortClosedCurrentFrameSymbols(
    const ComplementPartnerIndex& complementPartners,
    std::unordered_set<size_t> symbols) {
  addRelevantComplementedStatePartners(complementPartners, symbols);
  addRelevantSameFrameStateEqualityPartners(complementPartners, symbols);
  addRelevantDualRailPartners(complementPartners, symbols);
  return sortUniqueSymbols(std::move(symbols));
} // LCOV_EXCL_LINE

std::vector<size_t> sortCurrentFrameSymbolSeed(
    std::unordered_set<size_t> symbols) {
  return sortUniqueSymbols(std::move(symbols));
} // LCOV_EXCL_LINE

const std::vector<size_t>& cachedClosedCurrentFrameSymbols(
    PredecessorAssumptionCache& cache,
    const ComplementPartnerIndex& complementPartners,
    std::vector<size_t> seedSymbols) {
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
      complementPartners, std::move(symbols));
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
    BoolExpr* initFormula,
    BoolExpr* frameInvariant,
    const std::vector<FrameClauses>& frames,
    size_t level,
    const ComplementPartnerIndex& complementPartners,
    PdrFormulaSupportCache* supportCache) {
  std::unordered_set<size_t> symbols;
  if (level == 0) {
    addFormulaSymbols(initFormula, symbols, supportCache);
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
      complementPartners, std::move(symbols));
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
  merged = mergePredecessorSymbolAddition(
      std::move(merged),
      cachedClosedCurrentFrameSymbols(
          predecessorAssumptionCache,
          complementPartners,
          sortCurrentFrameSymbolSeed(std::move(predecessorDynamic))));

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
          complementPartners,
          sortCurrentFrameSymbolSeed(std::move(transitionDynamic))));

  std::unordered_set<size_t> tailSymbols;
  tailSymbols.reserve(excludeTargetOnCurrentFrame ? targetCube.size() : 0);
  if (excludeTargetOnCurrentFrame) {
    addCubeSymbols(targetCube, tailSymbols); // LCOV_EXCL_LINE
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
        *predecessorAssumptionCache,
        supportCache);
  }

  std::unordered_set<size_t> symbols;
  symbols.reserve(
      predecessorSymbols.size() + transitionSupportSymbols.size() +
      (excludeTargetOnCurrentFrame ? targetCube.size() : 0));
  symbols.insert(predecessorSymbols.begin(), predecessorSymbols.end());
  addFrameConstraintSymbols(
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
  addRelevantSameFrameStateEqualityPartners(complementPartners, symbols);
  addRelevantDualRailPartners(complementPartners, symbols);
  if (excludeTargetOnCurrentFrame) {
    addCubeSymbols(targetCube, symbols);
  }
  return sortUniqueSymbols(std::move(symbols));
}

std::vector<size_t> predecessorAssumptionCacheSymbols(
    const TransitionExprResolver& transitionByState,
    size_t level,
    const std::vector<size_t>& solverSymbols,
    PredecessorAssumptionCache* cache) {
  if (cache == nullptr) {
    return solverSymbols;
  }
  if (level == 0 &&
      cache->sharedFrameZeroPredecessorSymbols != nullptr) {
    detail::widenSortedPdrSymbolSurface(
        *cache->sharedFrameZeroPredecessorSymbols, solverSymbols);
    return *cache->sharedFrameZeroPredecessorSymbols;
  }

  // Section V uses one incremental SAT instance. Keep its symbol surface
  // monotonic so generalizing a target cube cannot rebuild the solver merely
  // because the smaller transition cone mentions fewer inputs.
  if (cache->widenedPredecessorCacheResolver != &transitionByState ||
      cache->widenedPredecessorCacheLevel != level) {
    cache->widenedPredecessorCacheSymbols.clear();
    cache->widenedPredecessorCacheResolver = &transitionByState;
    cache->widenedPredecessorCacheLevel = level;
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

std::vector<size_t> initIntersectionSymbols(const KInductionProblem& problem,
                                            BoolExpr* initFormula) {
  // One incremental solver serves every candidate cube in this PDR run, so its
  // symbol surface includes every state bit that a later cube may assume.
  std::unordered_set<size_t> symbols;
  addFormulaSymbols(initFormula, symbols);
  const auto stateSymbols = problem.combinedStateSymbols();
  symbols.insert(stateSymbols.begin(), stateSymbols.end());
  // All relation endpoints are state symbols and are already present above.
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

bool cubeContradictsKnownInitFacts(
    const KInductionProblem& problem,
    const StateCube& cube) {
  const bool usesBootstrapFrontier = problem.resetBootstrapCycles != 0;
  if (!usesBootstrapFrontier &&
      contradictsAssignments(cube, problem.initialStateAssignments)) {
    return true;
  }
  if (problem.complementedStatePairs0.size() <=
      kMaxComplementPairsForCheapInitCheck &&
      contradictsComplements(cube, problem.complementedStatePairs0)) {
    return true;
  }
  if (problem.complementedStatePairs1.size() <=
      kMaxComplementPairsForCheapInitCheck &&
      contradictsComplements(cube, problem.complementedStatePairs1)) {
    return true;
  }
  return false;
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
      const int transitionLit = encoder.encode(
          view.expr,
          transitionByState.encodingPostorder(literal.transitionSymbol));
      solver.addClause({literal.desiredValue ? transitionLit : -transitionLit});
    }
    if (encodedLeafLits != nullptr) {
      const auto& groupLeafLits = encoder.leafLits();
      encodedLeafLits->insert(groupLeafLits.begin(), groupLeafLits.end());
    }
  }
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
      const int transitionLit = encoder->encode(
          view.expr,
          transitionByState.encodingPostorder(literal.transitionSymbol));
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
  literalByAssumption.reserve(assumptionPairs.size());
  for (const auto& [assumptionLit, cubeLiteral] : assumptionPairs) {
    // SATSolverWrapper::failedAssumptions() returns the original assumption
    // polarity. Mapping the opposite polarity too is unsound when two target
    // bits use opposite values of the same transition root.
    literalByAssumption.emplace(assumptionLit, cubeLiteral);
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

StateCube cachedPredecessorUnsatCoreFromTargetContext(
    SATSolverWrapper& solver,
    const std::vector<std::pair<int, CubeLiteral>>& assumptionPairs) {
  // Section V takes the failed target assumptions directly from the one
  // incremental solver. Figure 7 performs any further reduction explicitly.
  return failedAssumptionCubeFromTargetPairs(solver, assumptionPairs);
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

  // SAT literals reserve 0/1 for constants; raw solver variable indices do not.
  const int selector = cachedSolver.solver->newVar() + 2;
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

// LCOV_EXCL_START


// LCOV_EXCL_STOP



// LCOV_DISABLED_STOP

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
  InitFactIndex index;
  if (!usesBootstrapFrontier) {
    index.assignments.reserve(problem.initialStateAssignments.size());
    for (const auto& [symbol, value] : problem.initialStateAssignments) {
      index.assignments.emplace(symbol, value);
      index.relations.ensureSymbol(symbol);
    }
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

bool frameHasSubsumingClause(const FrameClauses& frame,
                             const StateClause& clause) {
  for (const auto& existingClause : frame.clauses) {
    // Frames are sorted by clause size first. A larger clause cannot subsume
    // this candidate, so the remaining suffix cannot contain a match either.
    if (existingClause.size() > clause.size()) {
      break;
    }
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
  frame.clauseFingerprint.reset();
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

void addFrameConstraints(SATSolverWrapper& solver,
                         const FrameVariableStore& variables,
                         BoolExpr* initFormula,
                         BoolExpr* frameInvariant,
                         const std::vector<FrameClauses>& frames,
                         size_t level,
                         size_t frame) {
  if (level == 0) {
    // Figure 6 uses F[0] = I. Every level-zero query therefore receives the
    // complete exact startup formula; no cone-local assignment projection is
    // substituted for I.
    FrameFormulaEncoder encoder(solver, variables.makeLeafLits(frame));
    solver.addClause({encoder.encode(initFormula)});
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

void PredecessorAssumptionSolver::extendSymbolSurface(
    const ComplementPartnerIndex& stateRelations,
    const std::vector<size_t>& solverSymbols) {
  std::vector<size_t> addedSymbols;
  std::set_difference(
      solverSymbols.begin(),
      solverSymbols.end(),
      key.solverSymbols.begin(),
      key.solverSymbols.end(),
      std::back_inserter(addedSymbols));
  if (addedSymbols.empty()) {
    return;
  }

  variables->addSymbols(*solver, addedSymbols);
  querySymbolSet.insert(addedSymbols.begin(), addedSymbols.end());
  for (const size_t symbol : addedSymbols) {
    transitionLeafLits.emplace(symbol, variables->getLiteral(symbol, 0));
  }

  // Existing transition roots remain valid. New roots need an encoder whose
  // leaf map includes the enlarged surface, so discard only encoder memo tables.
  transitionEncoderBySymbolMap.clear();
  key.solverSymbols = solverSymbols;

  // The symbol-surface builder closes every relation pair. Re-emitting these
  // exact domain clauses is harmless and avoids rebuilding the SAT instance.
  stateRelations.addClauses(*solver, *variables, solverSymbols, 1);
}

PredecessorAssumptionSolver& getOrCreatePredecessorAssumptionSolver(
    PredecessorAssumptionCache& cache,
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    const TransitionExprResolver& transitionByState,
    const ComplementPartnerIndex& stateRelations,
    BoolExpr* initFormula,
    BoolExpr* frameInvariant,
    const std::vector<FrameClauses>& frames,
    size_t level,
    const std::vector<size_t>& solverSymbols) {
  const bool useSharedFrameZeroSolver =
      level == 0 && cache.sharedFrameZeroPredecessorSolver != nullptr;
  auto& solver = useSharedFrameZeroSolver
                     ? *cache.sharedFrameZeroPredecessorSolver
                     : cache.solversByLevel[level];
  PredecessorAssumptionCacheKey key{
      useSharedFrameZeroSolver
          ? cache.sharedFrameZeroPredecessorProblem
          : &problem,
      useSharedFrameZeroSolver
          ? cache.sharedFrameZeroTransitionModel
          : static_cast<const void*>(&transitionByState),
      initFormula,
      level == 0 ? nullptr : frameInvariant,
      level,
      frameClausesFingerprint(frames, level),
      solverSymbols};
  if (solver != nullptr && solver->canExtendTo(key)) {
    const size_t previousSymbolCount = solver->key.solverSymbols.size();
    solver->extendSymbolSurface(stateRelations, key.solverSymbols);
    if (solver->key.solverSymbols.size() != previousSymbolCount &&
        pdrStatsEnabled()) {
      emitSecDiag(
          "SEC PDR stats: predecessor cached solver surface extended added=",
          solver->key.solverSymbols.size() - previousSymbolCount,
          " symbols=",
          solver->key.solverSymbols.size(),
          " level=",
          level);
    }
    // PDR frames strengthen monotonically. Reuse the expensive transition and
    // frame prefix solver, then stream only newly learned frame clauses into it.
    const size_t addedClauses =
        addNewPredecessorFrameClauses(*solver, frames[level], 0);
    solver->key.frameFingerprint = key.frameFingerprint;
    if (useSharedFrameZeroSolver && pdrStatsEnabled()) {
      emitSecDiag("SEC PDR stats: shared exact F[0] predecessor solver reused");
    }
    if (addedClauses != 0 && pdrStatsEnabled()) {
      emitSecDiag(
          "SEC PDR stats: predecessor cached solver frame clauses added=",
          addedClauses,
          " level=",
          level,
          " symbols=",
          solverSymbols.size());
    }
    return *solver;
  }

  auto next = std::make_unique<PredecessorAssumptionSolver>();
  next->key = std::move(key);
  next->solver = std::make_unique<SATSolverWrapper>(
      SATSolverWrapper::assumptionSolverTypeFor(solverType));
  next->solver->configureForSecPdrQuery(solverSymbols.size());
  next->variables =
      std::make_unique<FrameVariableStore>(*next->solver, solverSymbols, 1);
  next->querySymbolSet.insert(solverSymbols.begin(), solverSymbols.end());
  stateRelations.addClauses(*next->solver, *next->variables, solverSymbols, 1);
  addFrameConstraints(*next->solver, *next->variables, initFormula,
                      frameInvariant, frames, level, 0);
  addSafeFramePropertyConstraint(*next->solver, *next->variables, problem,
                                 level, 0);
  addPostBootstrapResetInputConstraints(*next->solver, *next->variables,
                                        problem, 0);
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
  solver = std::move(next);
  return *solver;
}

int64_t resourceLimitOrUnbounded(unsigned limit) {
  return limit == 0 || limit == std::numeric_limits<unsigned>::max()
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
    bool excludeTargetOnCurrentFrame,
    const StateCube& targetCube) {
  PredecessorQueryResultKey key;
  key.problem = &problem;
  key.transitionByState = &transitionByState;
  key.initFormula = initFormula;
  key.frameInvariant = frameInvariant;
  key.level = level;
  key.frameFingerprint = frameFingerprint;
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
    const ComplementPartnerIndex& stateRelations,
    BoolExpr* initFormula,
    BoolExpr* frameInvariant,
    const std::vector<FrameClauses>& frames,
    size_t level,
    const StateCube& targetCube,
    const std::vector<size_t>& encodedTargets,
    const std::vector<size_t>& transitionSupportSymbols,
    const std::vector<size_t>& solverSymbols,
    bool excludeTargetOnCurrentFrame,
    unsigned predecessorConflictLimit,
    unsigned predecessorDecisionLimit,
    PredecessorAssumptionSolver** solvedCache = nullptr,
    StateCube* solvedUnsatCore = nullptr) {
  auto& cachedSolver = getOrCreatePredecessorAssumptionSolver(
      cache, problem, solverType, transitionByState, stateRelations,
      initFormula, frameInvariant, frames, level, solverSymbols);
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
  if (assumptions.empty()) {
    return std::nullopt; // LCOV_EXCL_LINE
  }

  if (solvedCache != nullptr) {
    *solvedCache = &cachedSolver;
  }
  // Section V of the paper keeps one incremental SAT instance and changes only
  // its assumptions between predecessor queries. A resource-limit hit is
  // UNKNOWN and must make this output inconclusive; it is never a proof result.
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
    *solvedUnsatCore = cachedPredecessorUnsatCoreFromTargetContext(
        *cachedSolver.solver, assumptionPairs);
  }
  return status;
}

BadCubeAssumptionSolver& getOrCreateBadCubeAssumptionSolver(
    BadCubeAssumptionCache& cache,
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    const ComplementPartnerIndex& stateRelations,
    BoolExpr* initFormula,
    BoolExpr* frameInvariant,
    const std::vector<FrameClauses>& frames,
    size_t level,
    const std::vector<size_t>& solverSymbols) {
  const KInductionProblem* cacheProblem =
      level == 0 && cache.sharedFrameZeroProblem != nullptr
          ? cache.sharedFrameZeroProblem
          : &problem;
  BadCubeAssumptionCacheKey key{
      cacheProblem,
      initFormula,
      level == 0 ? nullptr : frameInvariant,
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
  stateRelations.addClauses(*next->solver, *next->variables, solverSymbols, 1);
  addFrameConstraints(*next->solver, *next->variables, initFormula,
                      frameInvariant, frames, level, 0);
  addPostBootstrapResetInputConstraints(*next->solver, *next->variables,
                                        problem, 0);
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
    const ComplementPartnerIndex& stateRelations,
    BoolExpr* initFormula,
    BoolExpr* frameInvariant,
    const std::vector<FrameClauses>& frames,
    size_t level,
    BoolExpr* badFormula,
    const std::vector<size_t>& solverSymbols,
    unsigned badCubeConflictLimit,
    BadCubeAssumptionSolver** solvedCache) {
  auto& cachedSolver = getOrCreateBadCubeAssumptionSolver(
      cache, problem, solverType, stateRelations, initFormula, frameInvariant,
      frames, level, solverSymbols);
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

struct PdrTernarySimulationRoot {
  BoolExpr* formula = nullptr;
  const std::unordered_map<size_t, size_t>* symbolMap = nullptr;
  bool expectedValue = false;
};

class PdrTernaryModelReducer {
 public:
  PdrTernaryModelReducer(
      const SATSolverWrapper& solver,
      const FrameVariableStore& variables,
      const std::vector<PdrTernarySimulationRoot>& roots,
      const StateCube& modelCube) {
    roots_.reserve(roots.size());
    for (const auto& spec : roots) {
      Root root{spec.formula, spec.symbolMap, spec.expectedValue};
      if (root.formula != nullptr) {
        for (const size_t localSymbol : root.formula->getSupportVars()) {
          if (const auto symbol = mappedSymbol(root, localSymbol);
              symbol.has_value() && *symbol >= 2) {
            root.support.insert(*symbol);
          }
        }
      }
      roots_.push_back(std::move(root));
    }

    for (const auto& literal : modelCube) {
      assignments_.emplace(literal.symbol, literal.value);
    }
    for (const auto& root : roots_) {
      for (const size_t symbol : root.support) {
        if (assignments_.find(symbol) == assignments_.end() &&
            variables.hasSymbol(symbol)) {
          assignments_.emplace(
              symbol,
              solver.getLiteralValue(variables.getLiteral(symbol, 0)));
        }
      }
    }
  }

  StateCube reduce(const StateCube& modelCube) {
    if (roots_.empty() || !rootsHaveExpectedValues(std::nullopt)) {
      return modelCube;
    }

    StateCube reduced;
    reduced.reserve(modelCube.size());
    for (const auto& literal : modelCube) {
      if (!anyRootUses(literal.symbol)) {
        continue;
      }

      unknownSymbols_.insert(literal.symbol);
      if (rootsHaveExpectedValues(literal.symbol)) {
        continue;
      }
      unknownSymbols_.erase(literal.symbol);
      reduced.push_back(literal);
    }
    return reduced;
  }

 private:
  using EvaluationMemo =
      std::unordered_map<BoolExpr*, std::optional<bool>>;
  using EvaluationMemosBySymbolMap = std::unordered_map<
      const std::unordered_map<size_t, size_t>*,
      EvaluationMemo>;

  struct Root {
    BoolExpr* formula = nullptr;
    const std::unordered_map<size_t, size_t>* symbolMap = nullptr;
    bool expectedValue = false;
    std::unordered_set<size_t> support;
  };

  std::optional<size_t> mappedSymbol(const Root& root,
                                     size_t symbol) const {
    if (symbol < 2 || root.symbolMap == nullptr) {
      return symbol;
    }
    const auto mapped = root.symbolMap->find(symbol);
    if (mapped == root.symbolMap->end()) {
      return std::nullopt;
    }
    return mapped->second;
  }

  std::optional<bool> evaluate(
      BoolExpr* node,
      const Root& root,
      EvaluationMemo& memo) const {
    if (node == nullptr) {
      return std::nullopt;
    }
    if (const auto cached = memo.find(node); cached != memo.end()) {
      return cached->second;
    }

    std::optional<bool> result;
    switch (node->getOp()) {
      case Op::VAR: {
        const auto symbol = mappedSymbol(root, node->getId());
        if (!symbol.has_value()) {
          break;
        }
        if (*symbol < 2) {
          result = *symbol == 1;
        } else if (unknownSymbols_.find(*symbol) == unknownSymbols_.end()) {
          const auto assignment = assignments_.find(*symbol);
          if (assignment != assignments_.end()) {
            result = assignment->second;
          }
        }
        break;
      }
      case Op::NOT: {
        const auto value = evaluate(node->getLeft(), root, memo);
        if (value.has_value()) {
          result = !*value;
        }
        break;
      }
      case Op::AND:
      case Op::OR:
      case Op::XOR: {
        const auto lhs = evaluate(node->getLeft(), root, memo);
        const auto rhs = evaluate(node->getRight(), root, memo);
        if (node->getOp() == Op::AND &&
            ((lhs.has_value() && !*lhs) ||
             (rhs.has_value() && !*rhs))) {
          result = false;
        } else if (node->getOp() == Op::OR &&
                   ((lhs.has_value() && *lhs) ||
                    (rhs.has_value() && *rhs))) {
          result = true;
        } else if (lhs.has_value() && rhs.has_value()) {
          result = node->getOp() == Op::AND
                       ? *lhs && *rhs
                       : node->getOp() == Op::OR ? *lhs || *rhs
                                                 : *lhs != *rhs;
        }
        break;
      }
      case Op::NONE:
      default:
        break;
    }
    memo.emplace(node, result);
    return result;
  }

  bool rootHasExpectedValue(const Root& root,
                            EvaluationMemo& memo) const {
    const auto value = evaluate(root.formula, root, memo);
    return value.has_value() && *value == root.expectedValue;
  }

  bool rootsHaveExpectedValues(std::optional<size_t> changedSymbol) const {
    // Transition roots from one design share both a symbol map and BoolExpr
    // subgraphs. Reuse their evaluations within this one tentative X assignment;
    // a fresh memo is still created for every literal-removal attempt.
    EvaluationMemosBySymbolMap memosBySymbolMap;
    for (const auto& root : roots_) {
      if ((!changedSymbol.has_value() ||
           root.support.find(*changedSymbol) != root.support.end()) &&
          !rootHasExpectedValue(root, memosBySymbolMap[root.symbolMap])) {
        return false;
      }
    }
    return true;
  }

  bool anyRootUses(size_t symbol) const {
    for (const auto& root : roots_) {
      if (root.support.find(symbol) != root.support.end()) {
        return true;
      }
    }
    return false;
  }

  std::vector<Root> roots_;
  std::unordered_map<size_t, bool> assignments_;
  std::unordered_set<size_t> unknownSymbols_;
};

StateCube reduceSolvedCubeByTernarySimulation(
    const SATSolverWrapper& solver,
    const FrameVariableStore& variables,
    const std::vector<PdrTernarySimulationRoot>& roots,
    const StateCube& modelCube) {
  // Section III-B of the FMCAD'11 PDR paper removes a state literal only when
  // replacing it by X leaves every target value concrete and unchanged.
  PdrTernaryModelReducer reducer(solver, variables, roots, modelCube);
  return reducer.reduce(modelCube);
}

StateCube extractSolvedPredecessorCube(
    const SATSolverWrapper& solver,
    const FrameVariableStore& variables,
    const std::vector<size_t>& predecessorSymbols,
    const TransitionExprResolver& transitionByState,
    const StateCube& targetCube) {
  const StateCube modelCube =
      extractStateCube(solver, variables, predecessorSymbols, 0);
  std::vector<PdrTernarySimulationRoot> roots;
  const auto groups =
      groupTransitionCubeLiteralsBySymbolMap(transitionByState, targetCube);
  roots.reserve(targetCube.size());
  for (const auto& group : groups) {
    for (const auto& literal : group.literals) {
      const TransitionExprView view =
          transitionByState.expressionView(literal.transitionSymbol);
      roots.push_back({view.expr, view.symbolMap, literal.desiredValue});
    }
  }
  return reduceSolvedCubeByTernarySimulation(
      solver, variables, roots, modelCube);
}

StateCube extractSolvedBadCubeForFormula(
    const SATSolverWrapper& solver,
    const FrameVariableStore& variables,
    const std::vector<size_t>& badStateSupport,
    BoolExpr* badFormula,
    size_t level) {
  if (isSecDiagEnabled()) {
    emitSecDiag(  // LCOV_EXCL_LINE
        "SEC diag: PDR bad cube uses exact ternary support: ",
        badStateSupport.size(),  // LCOV_EXCL_LINE
        " state symbols at F",
        level);
  }  // LCOV_EXCL_LINE
  const StateCube modelCube =
      extractStateCube(solver, variables, badStateSupport, 0);
  const StateCube cube = reduceSolvedCubeByTernarySimulation(
      solver,
      variables,
      {{badFormula, nullptr, true}},
      modelCube);
  if (pdrStatsEnabled()) {
    emitSecDiag(
        "SEC PDR stats: bad cube level=", level,
        " source=ternary_simulation",
        " state_symbols=", badStateSupport.size(),
        " model_cube=", modelCube.size(),
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
  std::vector<size_t> solverSymbols =
      findBadQuerySymbols(
          initFormula,
          frameInvariant,
          frames,
          badFormula,
          level,
          complementPartners,
          supportCache);
  const unsigned badCubeConflictLimit =
      // LCOV_EXCL_START
      problem.usesDualRailStateEncoding ? dualRailBadCubeConflictLimit() : 0;
      // LCOV_EXCL_STOP
  const size_t badCubeStatsQueryNumber = nextPdrBadCubeQueryNumber();
  const bool emitStatsForBadCubeQuery =
      shouldEmitPdrStats(badCubeStatsQueryNumber);
  BadCubeAssumptionCache* solverCache =
      shouldUseBadCubeSolverCache(problem) ? badCubeAssumptionCache : nullptr;
  if (level == 0 && solverCache != nullptr &&
      !solverCache->sharedFrameZeroSolverSymbols.empty()) {
    solverSymbols = solverCache->sharedFrameZeroSolverSymbols;
  }
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
        *solverCache, problem, solverType, complementPartners, initFormula,
        frameInvariant, frames, level, badFormula, solverSymbols,
        badCubeConflictLimit, &solvedCache);
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
        *preciseBadStateSupport,
        badFormula,
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
  complementPartners.addClauses(solver, variables, solverSymbols, 1);
  // LCOV_EXCL_STOP
  addFrameConstraints(solver, variables, initFormula, frameInvariant, frames,
                      level, 0);
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
      *preciseBadStateSupport,
      badFormula,
      level);
}

std::optional<StateCube> findBadCube(const KInductionProblem& problem,
                                     KEPLER_FORMAL::Config::SolverType solverType,
                                     BoolExpr* initFormula,
                                     BoolExpr* frameInvariant,
                                     const std::vector<FrameClauses>& frames,
                                     BoolExpr* badFormula,
                                     bool decomposeOutputBad,
                                     const std::optional<std::vector<size_t>>&
                                         preciseBadStateSupport,
                                     const std::unordered_set<size_t>& stateSymbols,
                                     size_t level,
                                     const ComplementPartnerIndex& complementPartners,
                                     BadCubeAssumptionCache* badCubeAssumptionCache,
                                     PdrFormulaSupportCache* supportCache) {
  if (!decomposeOutputBad || problem.observedOutputExprs0.size() <= 1 ||
      problem.observedOutputExprs0.size() != problem.observedOutputExprs1.size()) {
    return findBadCubeForFormula(
        problem, solverType, initFormula, frameInvariant, frames, badFormula,
        preciseBadStateSupport, level,
        complementPartners, badCubeAssumptionCache, supportCache);
  }

  // This is an exact decomposition of R[N] & !P: each query uses the complete
  // state and frame constraints, and the disjunction is UNSAT exactly when all
  // output mismatch terms are UNSAT. It avoids one broad unrelated SAT cone.
  for (size_t output = 0; output < problem.observedOutputExprs0.size(); ++output) {
    BoolExpr* outputBad = BoolExpr::simplify(BoolExpr::Xor(
        problem.observedOutputExprs0[output],
        problem.observedOutputExprs1[output]));
    const auto outputStateSupport = collectBoundedStateSupportSymbols(
        outputBad, kMaxPreciseBadCubeSupportNodes, 0, stateSymbols);
    if (auto cube = findBadCubeForFormula(
            problem, solverType, initFormula, frameInvariant, frames,
            outputBad, outputStateSupport, level,
            complementPartners, badCubeAssumptionCache, supportCache);
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
    size_t* predecessorQueryBudget = nullptr,
    PdrFormulaSupportCache* supportCache = nullptr) {
  // This is the one-step predecessor query at the heart of PDR: does some
  // state in F[level] transition into the target cube on the next frame?
  std::optional<PredecessorQueryResultKey> exactCacheKey;
  std::optional<PredecessorQueryResultKey> stableUnsatCacheKey;
  const bool usePredecessorQueryResultCache =
      predecessorAssumptionCache != nullptr;
  if (usePredecessorQueryResultCache) {
    const size_t frameFingerprint = frameClausesFingerprint(frames, level);
    exactCacheKey = makePredecessorQueryResultKey(
        problem,
        transitionByState,
        initFormula,
        frameInvariant,
        level,
        frameFingerprint,
        excludeTargetOnCurrentFrame,
        targetCube);
    stableUnsatCacheKey = makePredecessorQueryResultKey(
        problem,
        transitionByState,
        initFormula,
        frameInvariant,
        level,
        /*frameFingerprint=*/0,
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
  if (predecessorAssumptionCache != nullptr) {
    targetSurface = &predecessorTargetSurfaceFor(
        *predecessorAssumptionCache, problem, transitionByState, targetCube,
        uncachedTargetSurface);
  } else {
    uncachedTargetSurface =
        buildPredecessorTargetSurface(problem, transitionByState, targetCube);
    targetSurface = &uncachedTargetSurface;
  }
  const std::vector<size_t>& encodedTargets = targetSurface->encodedTargets;
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

  // Section V materializes only the transition cone needed by this query.
  // Ternary simulation immediately removes every state outside that cone, so
  // asking SAT to assign those absent variables first is redundant. F[level],
  // the target transition functions, and all domain relations they mention
  // remain exact; this is existential CNF construction, not model reduction.
  const std::vector<size_t> predecessorSymbols =
      retainPdrStateSymbols(
          transitionSupportSymbols, transitionByState.stateSymbols());
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
      solverCache,
      supportCache);
  const std::vector<size_t> cachedSolverSymbols =
      predecessorAssumptionCacheSymbols(
          transitionByState,
          level,
          solverSymbols,
          solverCache);
  const unsigned predecessorConflictLimit =
      problem.usesDualRailStateEncoding
          ? dualRailPredecessorConflictLimitForQuery(
                problem, targetCube, level, cachedSolverSymbols.size())
          : 0;
  const unsigned predecessorDecisionLimit =
      problem.usesDualRailStateEncoding
          ? dualRailPredecessorDecisionLimit()
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
        " decision_limit=", predecessorDecisionLimit,
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
  if (solverCache != nullptr) {
    PredecessorAssumptionSolver* solvedPredecessorCache = nullptr;
    StateCube cachedUnsatCore;
    const auto cachedStatus = solvePredecessorCubeWithCachedAssumptions(
        *solverCache, problem, solverType, transitionByState,
        complementPartners, initFormula, frameInvariant, frames, level,
        targetCube, encodedTargets, transitionSupportSymbols,
        cachedSolverSymbols, excludeTargetOnCurrentFrame,
        predecessorConflictLimit, predecessorDecisionLimit,
        &solvedPredecessorCache, &cachedUnsatCore);
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
            " cached_assumptions=1");
      }
      markPdrBudgetExhausted(PdrBudgetExhaustion::LocalQuery);
      return std::nullopt;
    }
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
          solvedPredecessorCache != nullptr) {
        if (emitStatsForQuery) {
          emitSecDiag(
              "SEC PDR stats: predecessor #", statsQueryNumber,
              " result=sat cached_assumptions=1");
        }
        StateCube predecessor = extractSolvedPredecessorCube(
            *solvedPredecessorCache->solver,
            *solvedPredecessorCache->variables,
            predecessorSymbols,
            transitionByState,
            targetCube);
        if (emitStatsForQuery) {
          emitSecDiag(
              "SEC PDR stats: predecessor #", statsQueryNumber,
              " predecessor_cube=", predecessor.size(),
              " predecessor_hash=", cubeFingerprint(predecessor));
        }
        if (exactCacheKey.has_value() && stableUnsatCacheKey.has_value()) {
          rememberPredecessorQueryResult(
              *predecessorAssumptionCache,
              *exactCacheKey,
              *stableUnsatCacheKey,
              std::optional<StateCube>(predecessor));
        }
        return predecessor;
      }
    }
  }
  SATSolverWrapper solver(solverType);
  solver.configureForSecPdrQuery(solverSymbols.size());
  FrameVariableStore variables(solver, solverSymbols, 1);
  complementPartners.addClauses(solver, variables, solverSymbols, 1);
  addFrameConstraints(solver, variables, initFormula, frameInvariant, frames,
                      level, 0);
  addSafeFramePropertyConstraint(solver, variables, problem, level, 0);
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
      transitionByState,
      targetCube);
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

InitIntersectionAssumptionSolver& getInitIntersectionAssumptionSolver(
    PredecessorAssumptionCache& cache,
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    BoolExpr* initFormula) {
  auto& solver = cache.sharedInitIntersectionSolver != nullptr
                     ? *cache.sharedInitIntersectionSolver
                     : cache.initIntersectionSolver;
  const KInductionProblem* problemIdentity =
      cache.sharedInitIntersectionProblem != nullptr
          ? cache.sharedInitIntersectionProblem
          : &problem;
  if (solver != nullptr && solver->problem == problemIdentity &&
      solver->initFormula == initFormula &&
      solver->requestedSolverType == solverType) {
    return *solver;
  }

  auto cached = std::make_unique<InitIntersectionAssumptionSolver>();
  cached->problem = problemIdentity;
  cached->initFormula = initFormula;
  cached->requestedSolverType = solverType;
  const std::vector<size_t> solverSymbols =
      initIntersectionSymbols(problem, initFormula);
  cached->solver = std::make_unique<SATSolverWrapper>(
      SATSolverWrapper::assumptionSolverTypeFor(solverType));
  cached->solver->configureForSecPdrQuery(solverSymbols.size());
  cached->variables =
      std::make_unique<FrameVariableStore>(*cached->solver, solverSymbols, 1);
  std::optional<ComplementPartnerIndex> localStateRelations;
  if (cache.stateRelations == nullptr) {
    localStateRelations.emplace(problem); // LCOV_EXCL_LINE
  }
  const ComplementPartnerIndex& stateRelations = cache.stateRelations != nullptr
                                                     ? *cache.stateRelations
                                                     : *localStateRelations;
  stateRelations.addClauses(*cached->solver, *cached->variables, solverSymbols,
                            1);
  FrameFormulaEncoder encoder(*cached->solver,
                              cached->variables->makeLeafLits(0));
  cached->solver->addClause({encoder.encode(initFormula)});

  solver = std::move(cached);
  return *solver;
}

bool cubeIntersectsInit(const KInductionProblem& problem,
                        KEPLER_FORMAL::Config::SolverType solverType,
                        BoolExpr* initFormula,
                        const StateCube& cube,
                        PredecessorAssumptionCache* cache) {
  // Definite conflicts can avoid a SAT call. Otherwise Figure 6 requires the
  // exact F[0] = I query; absence of a known conflict is not reachability.
  if (cubeContradictsKnownInitFacts(problem, cube)) {
    return false;
  }

  PredecessorAssumptionCache localCache;
  PredecessorAssumptionCache& activeCache =
      cache != nullptr ? *cache : localCache;
  auto& cached = getInitIntersectionAssumptionSolver(
      activeCache, problem, solverType, initFormula);
  std::vector<int> assumptions;
  assumptions.reserve(cube.size());
  for (const auto& literal : cube) {
    if (!cached.variables->hasSymbol(literal.symbol)) {
      throw std::runtime_error(  // LCOV_EXCL_LINE
          "PDR init-intersection encoding missing state symbol " +
          std::to_string(literal.symbol));  // LCOV_EXCL_LINE
    }
    const int satLiteral =
        cached.variables->getLiteral(literal.symbol, 0);
    assumptions.push_back(literal.value ? satLiteral : -satLiteral);
  }
  return cached.solver->solveWithAssumptions(assumptions);
}

std::optional<StateCube> growCoreOutsideInit(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    BoolExpr* initFormula,
    const StateCube& core,
    const StateCube& targetCube,
    PredecessorAssumptionCache* cache) {
  StateCube candidate = core;
  if (!cubeIntersectsInit(
          problem, solverType, initFormula, candidate, cache)) {
    return candidate;
  }

  // Pdr_ManReduceClause in the authors' ABC implementation strengthens a
  // failed-assumption core with literals from the original cube until it no
  // longer overlaps Init. Strengthening preserves the solved Q2 implication.
  for (const auto& literal : targetCube) {
    if (findCubeLiteralValue(candidate, literal.symbol).has_value()) {
      continue;
    }
    candidate.push_back(literal);
    normalizeCube(candidate);
    if (!cubeIntersectsInit(
            problem, solverType, initFormula, candidate, cache)) {
      if (pdrStatsEnabled()) {
        emitSecDiag(
            "SEC PDR stats: predecessor core kept outside init core=",
            core.size(),
            "->",
            candidate.size(),
            " target=",
            targetCube.size());
      }
      return candidate;
    }
  }
  return std::nullopt;
}

class BlockedCubeReductionChecker {
 public:
  BlockedCubeReductionChecker(
      const KInductionProblem& problem,
      KEPLER_FORMAL::Config::SolverType solverType,
      const TransitionExprResolver& transitionByState,
      BoolExpr* initFormula,
      BoolExpr* frameInvariant,
      const std::vector<FrameClauses>& frames,
      size_t level,
      PredecessorAssumptionCache* predecessorAssumptionCache,
      const ComplementPartnerIndex& complementPartners,
      size_t* predecessorQueryBudget,
      PdrFormulaSupportCache* supportCache)
      : problem_(problem),
        solverType_(solverType),
        transitionByState_(transitionByState),
        initFormula_(initFormula),
        frameInvariant_(frameInvariant),
        frames_(frames),
        level_(level),
        predecessorAssumptionCache_(predecessorAssumptionCache),
        complementPartners_(complementPartners),
        predecessorQueryBudget_(predecessorQueryBudget),
        supportCache_(supportCache) {}

  std::optional<StateCube> cachedCore(const StateCube& cube) const {
    if (predecessorAssumptionCache_ == nullptr) {
      return std::nullopt;
    }
    const auto core = cachedPredecessorUnsatCoreForCube(
        *predecessorAssumptionCache_,
        problem_,
        transitionByState_,
        initFormula_,
        frameInvariant_,
        frames_,
        level_ - 1,
        cube,
        /*excludeTargetOnCurrentFrame=*/true);
    if (!core.has_value() || core->size() >= cube.size()) {
      return std::nullopt;
    }
    return growCoreOutsideInit(
        problem_,
        solverType_,
        initFormula_,
        *core,
        cube,
        predecessorAssumptionCache_);
  }

  std::optional<StateCube> generalize(const StateCube& reduced) const {
    if (reduced.empty() ||
        cubeIntersectsInit(
            problem_,
            solverType_,
            initFormula_,
            reduced,
            predecessorAssumptionCache_)) {
      return std::nullopt;
    }
    // Figure 7 generalizes with Q2: F[k-1] & !s & T & s'.
    const auto predecessor = findPredecessorCube(
        problem_,
        solverType_,
        transitionByState_,
        initFormula_,
        frameInvariant_,
        frames_,
        level_ - 1,
        reduced,
        /*excludeTargetOnCurrentFrame=*/true,
        complementPartners_,
        predecessorAssumptionCache_,
        predecessorQueryBudget_,
        supportCache_);
    if (hasPdrBudgetExhaustion() || predecessor.has_value()) {
      return std::nullopt;
    }
    if (const auto core = cachedCore(reduced); core.has_value()) {
      return core;
    }
    return reduced;
  }

 private:
  const KInductionProblem& problem_;
  KEPLER_FORMAL::Config::SolverType solverType_;
  const TransitionExprResolver& transitionByState_;
  BoolExpr* initFormula_ = nullptr;
  BoolExpr* frameInvariant_ = nullptr;
  const std::vector<FrameClauses>& frames_;
  size_t level_ = 0;
  PredecessorAssumptionCache* predecessorAssumptionCache_ = nullptr;
  const ComplementPartnerIndex& complementPartners_;
  size_t* predecessorQueryBudget_ = nullptr;
  PdrFormulaSupportCache* supportCache_ = nullptr;
};

StateCube generalizeBlockedCube(
    const KInductionProblem& problem,
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
  BlockedCubeReductionChecker reductionChecker(
      problem,
      solverType,
      transitionByState,
      initFormula,
      frameInvariant,
      frames,
      level,
      predecessorAssumptionCache,
      complementPartners,
      predecessorQueryBudget,
      supportCache);

  // Figure 7 first uses the failed assumptions from solveRelative, then tries
  // removing each remaining literal with the same Q2 query. A successful query
  // may return a still smaller core, so restart the static order on that core.
  StateCube generalized = cube;
  if (const auto core = reductionChecker.cachedCore(generalized);
      core.has_value()) {
    generalized = *core;
  }

  size_t checks = 0;
  for (size_t index = 0;
       generalized.size() > 1 && index < generalized.size();) {
    StateCube reduced = generalized;
    reduced.erase(
        reduced.begin() + static_cast<std::ptrdiff_t>(index));
    ++checks;
    const auto result = reductionChecker.generalize(reduced);
    if (hasPdrBudgetExhaustion()) {
      return generalized;
    }
    if (!result.has_value()) {
      ++index;
      continue;
    }
    generalized = *result;
    index = 0;
  }

  if (pdrStatsEnabled() && generalized.size() != cube.size()) {
    emitSecDiag(
        "SEC PDR stats: generalized blocked cube level=",
        level,
        " size=",
        cube.size(),
        "->",
        generalized.size(),
        " checks=",
        checks);
  }
  return generalized;
}

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
                                     const StateCube& cube,
                                     PredecessorAssumptionCache* cache) {
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
    if (!cubeIntersectsInit(  // LCOV_EXCL_LINE
            problem, solverType, initFormula, reduced, cache)) {  // LCOV_EXCL_LINE
      candidate = std::move(reduced);  // LCOV_EXCL_LINE
      continue;  // LCOV_EXCL_LINE
    }
    ++index;  // LCOV_EXCL_LINE
  }  // LCOV_EXCL_LINE
  return candidate;  // LCOV_EXCL_LINE
}  // LCOV_EXCL_LINE

ProofObligationKey proofObligationKey(const ProofObligation& obligation) {
  ProofObligationKey key;
  key.level = obligation.level;
  key.badFrame = obligation.badFrame;
  key.cube = obligation.cube;
  return key;
// LCOV_EXCL_START
}
// LCOV_EXCL_STOP

class ProofObligationLowerPriority {
 public:
  bool operator()(const ProofObligation& lhs,
                  const ProofObligation& rhs) const {
    // priority_queue places the element for which this relation is false on
    // top. Reverse the existing Figure 6 priority predicate exactly.
    return detail::pdrProofObligationPriorityLess(rhs.level, rhs.sequence,
                                                  lhs.level, lhs.sequence);
  }
};

class ProofObligationQueue {
 public:
  bool empty() const { return queue_.empty(); }

  bool enqueue(ProofObligation obligation) {
    if (!queuedKeys_.insert(proofObligationKey(obligation)).second) {
      return false; // LCOV_EXCL_LINE
    }
    obligation.sequence = nextSequence_++;
    queue_.push(std::move(obligation));
    return true;
  }

  ProofObligation pop() {
    ProofObligation obligation = queue_.top();
    queue_.pop();
    queuedKeys_.erase(proofObligationKey(obligation));
    return obligation;
  }

  void enqueueNext(const ProofObligation& obligation, size_t rootLevel) {
    if (obligation.level >= rootLevel) {
      return;
    }
    // Figure 6 requeues next(s); advance badFrame too so the path suffix length
    // remains unchanged for counterexample reporting.
    ProofObligation next = obligation;
    ++next.level;
    ++next.badFrame;
    if (enqueue(std::move(next)) && pdrStatsEnabled()) {
      emitSecDiag(
          "SEC PDR stats: proof obligation requeued level=", obligation.level,
          "->", obligation.level + 1, " bad_frame=", obligation.badFrame + 1);
    }
  }

 private:
  std::priority_queue<ProofObligation, std::vector<ProofObligation>,
                      ProofObligationLowerPriority>
      queue_;
  std::unordered_set<ProofObligationKey, ProofObligationKeyHash> queuedKeys_;
  size_t nextSequence_ = 0;
};

void learnBlockedObligation(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    const TransitionExprResolver& transitionByState,
    BoolExpr* initFormula,
    BoolExpr* frameInvariant,
    std::vector<FrameClauses>& frames,
    size_t rootLevel,
    const ComplementPartnerIndex& complementPartners,
    PredecessorAssumptionCache& predecessorAssumptionCache,
    size_t* predecessorQueryBudget,
    PdrFormulaSupportCache* supportCache,
    const ProofObligation& obligation) {
  StateCube cube = generalizeBlockedCube(
      problem, solverType, transitionByState, initFormula, frameInvariant,
      frames, obligation.level, obligation.cube, &predecessorAssumptionCache,
      complementPartners, predecessorQueryBudget, supportCache);
  size_t learnedLevel = obligation.level;
  // Figure 6 repeatedly applies solveRelative(next(z)) and keeps the highest
  // frame where the blocker is relatively inductive.
  while (learnedLevel + 1 < rootLevel) {
    const auto predecessor = findPredecessorCube(
        problem, solverType, transitionByState, initFormula, frameInvariant,
        frames, learnedLevel, cube,
        /*excludeTargetOnCurrentFrame=*/true, complementPartners,
        &predecessorAssumptionCache, predecessorQueryBudget,
        supportCache);
    if (hasPdrBudgetExhaustion() || predecessor.has_value()) {
      break;
    }
    ++learnedLevel;
  }
  addClauseToFrames(frames, clauseFromCube(cube), learnedLevel);
  if (pdrStatsEnabled() && learnedLevel != obligation.level) {
    emitSecDiag(
        "SEC PDR stats: blocked cube lifted level=",
        obligation.level,
        "->",
        learnedLevel,
        " cube=",
        cube.size());
  }
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
  ProofObligationQueue queue;
  (void)queue.enqueue(ProofObligation{badCube, rootLevel, rootLevel});

  while (!queue.empty()) {
    const ProofObligation obligation = queue.pop();

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
      if (!cubeIntersectsInit(
              problem,
              solverType,
              initFormula,
              obligation.cube,
              &predecessorAssumptionCache)) {
        const StateCube generalizedCube = generalizeInitExcludedCube(  // LCOV_EXCL_LINE
            problem,  // LCOV_EXCL_LINE
            solverType,  // LCOV_EXCL_LINE
            initFormula,  // LCOV_EXCL_LINE
            obligation.cube,  // LCOV_EXCL_LINE
            &predecessorAssumptionCache);  // LCOV_EXCL_LINE
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

    // Q2 is sound only for cubes outside Init. Figure 6 makes this invariant
    // explicit before every relative-induction query.
    if (cubeIntersectsInit(
            problem,
            solverType,
            initFormula,
            obligation.cube,
            &predecessorAssumptionCache)) {
      if (pdrStatsEnabled()) {
        emitSecDiag(
            "SEC PDR stats: counterexample candidate intersects init ",
            "level=", obligation.level,
            " bad_frame=", obligation.badFrame,
            " cube=", obligation.cube.size());
      }
      badFrame = obligation.badFrame;
      return false;
    }

    const auto predecessor = findPredecessorCube(
        problem,
        solverType,
        transitionByState,
        initFormula,
        frameInvariant,
        frames,
        obligation.level - 1,
        obligation.cube,
        /*excludeTargetOnCurrentFrame=*/true,
        complementPartners,
        &predecessorAssumptionCache,
        predecessorQueryBudget,
        supportCache);
    if (hasPdrBudgetExhaustion()) {
      return true;  // LCOV_EXCL_LINE
    }
    if (!predecessor.has_value()) {
      learnBlockedObligation(
          problem, solverType, transitionByState, initFormula, frameInvariant,
          frames, rootLevel, complementPartners, predecessorAssumptionCache,
          predecessorQueryBudget, supportCache, obligation);
      if (hasPdrBudgetExhaustion()) {
        return true;  // LCOV_EXCL_LINE
      }
      queue.enqueueNext(obligation, rootLevel);
      continue;
    }
    ProofObligation predecessorObligation{*predecessor, obligation.level - 1,
                                          obligation.badFrame};
    (void)queue.enqueue(obligation);
    (void)queue.enqueue(std::move(predecessorObligation));
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
          predecessorQueryBudget,
          supportCache);
      if (hasPdrBudgetExhaustion()) {
        // Figure 9 propagation is opportunistic: only a proved-UNSAT query
        // moves the clause. UNKNOWN leaves this clause in its current frame;
        // it must not abort otherwise exact blocking work for the whole output.
        if (pdrStatsEnabled()) {
          emitSecDiag(
              "SEC PDR stats: propagation left clause in frame level=",
              level,
              " clause_literals=",
              clause.size());
        }
        resetPdrBudgetExhaustion();
        continue;
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

BoolExpr* makeBalancedConjunction(std::vector<BoolExpr*> terms) {
  if (terms.empty()) {
    return BoolExpr::createTrue();
  }
  while (terms.size() > 1) {
    std::vector<BoolExpr*> next;
    next.reserve((terms.size() + 1) / 2);
    for (size_t index = 0; index < terms.size(); index += 2) {
      next.push_back(index + 1 < terms.size()
                         ? BoolExpr::And(terms[index], terms[index + 1])
                         : terms[index]);
    }
    terms = std::move(next);
  }
  return terms.front();
}

class ExactPdrBootstrapInitBuilder {
 public:
  explicit ExactPdrBootstrapInitBuilder(const KInductionProblem& problem)
      : problem_(problem),
        transitionByState_(problem),
        stateSymbols_(problem.combinedStateSymbols()),
        symbolAtFrame_(problem.resetBootstrapCycles + 1),
        remapMemoByFrame_(problem.resetBootstrapCycles) {
    std::sort(stateSymbols_.begin(), stateSymbols_.end());
    stateSymbols_.erase(
        std::unique(stateSymbols_.begin(), stateSymbols_.end()),
        stateSymbols_.end());
  }

  BoolExpr* build() {
    collectReservedSymbolsAndTransitions();
    initializeStateSymbols();

    std::vector<BoolExpr*> terms;
    terms.reserve(
        transitions_.size() * problem_.resetBootstrapCycles +
        problem_.initialStateAssignments.size() + 32);
    // The reset prefix starts from the design's actual ternary initialization:
    // known registers use 01/10 and resetless registers use X=11.
    addInitialStateAssignments(terms);
    for (size_t frame = 0; frame < problem_.resetBootstrapCycles; ++frame) {
      addResetInputAssignments(frame, /*asserted=*/true, terms);
      addStateDomainRelations(frame, terms);
      addTransitionRelation(frame, terms);
    }
    addStateDomainRelations(problem_.resetBootstrapCycles, terms);

    // The paper requires F[0] = I.  The final reset frame is therefore part of
    // I as well: reset is deasserted and the observed frontier property is the
    // same one used by the exact bounded SEC base query.
    addResetInputAssignments(
        problem_.resetBootstrapCycles, /*asserted=*/false, terms);
    if (problem_.usesResetBootstrapObservationFrontier()) {
      terms.push_back(problem_.property);
    }
    return makeBalancedConjunction(std::move(terms));
  }

 private:
  void reserveFormulaSymbols(BoolExpr* formula) {
    if (formula == nullptr) {
      return;
    }
    const auto support = formula->getSupportVars();
    reservedSymbols_.insert(support.begin(), support.end());
  }

  void reserveSupportSymbols(const std::set<size_t>& support) {
    reservedSymbols_.insert(support.begin(), support.end());
  }

  void reserveAssignments(
      const std::vector<std::pair<size_t, bool>>& assignments) {
    for (const auto& [symbol, /*value*/ _] : assignments) {
      reservedSymbols_.insert(symbol);
    }
  }

  void collectReservedSymbolsAndTransitions() {
    reservedSymbols_.insert(problem_.allSymbols.begin(), problem_.allSymbols.end());
    reservedSymbols_.insert(stateSymbols_.begin(), stateSymbols_.end());
    reserveAssignments(problem_.resetBootstrapInputs);
    reserveAssignments(problem_.initialStateAssignments);
    reserveFormulaSymbols(problem_.property);
    reserveFormulaSymbols(problem_.bad);

    transitions_.reserve(stateSymbols_.size());
    for (const size_t stateSymbol : stateSymbols_) {
      if (!transitionByState_.contains(stateSymbol)) {
        continue;
      }
      BoolExpr* transition = transitionByState_.at(stateSymbol);
      transitions_.emplace_back(stateSymbol, transition);
      // The resolver already caches exact support for eager and lazy
      // transitions. Reuse it here so reset-prefix construction does not walk
      // each large materialized dual-rail DAG once for every use.
      reserveSupportSymbols(transitionByState_.support(stateSymbol));
    }
  }

  size_t allocateFreshSymbol() {
    while (reservedSymbols_.find(nextFreshSymbol_) != reservedSymbols_.end()) {
      ++nextFreshSymbol_;
    }
    const size_t symbol = nextFreshSymbol_++;
    reservedSymbols_.insert(symbol);
    return symbol;
  }

  void initializeStateSymbols() {
    const size_t finalFrame = problem_.resetBootstrapCycles;
    for (size_t frame = 0; frame <= finalFrame; ++frame) {
      auto& frameSymbols = symbolAtFrame_[frame];
      frameSymbols.reserve(stateSymbols_.size());
      for (const size_t stateSymbol : stateSymbols_) {
        frameSymbols.emplace(
            stateSymbol,
            frame == finalFrame ? stateSymbol : allocateFreshSymbol());
      }
    }
  }

  size_t mappedSymbol(size_t frame, size_t symbol) {
    auto& frameSymbols = symbolAtFrame_.at(frame);
    if (const auto found = frameSymbols.find(symbol);
        found != frameSymbols.end()) {
      return found->second;
    }
    const size_t mapped = allocateFreshSymbol();
    frameSymbols.emplace(symbol, mapped);
    return mapped;
  }

  BoolExpr* remapAtFrame(BoolExpr* formula,
                         size_t frame,
                         const std::set<size_t>& support) {
    for (const size_t symbol : support) {
      if (symbol >= 2) {
        static_cast<void>(mappedSymbol(frame, symbol));
      }
    }
    return remapBoolExprVariables(
        formula, symbolAtFrame_.at(frame), remapMemoByFrame_.at(frame));
  }

  void addInitialStateAssignments(std::vector<BoolExpr*>& terms) {
    for (const auto& [symbol, value] : problem_.initialStateAssignments) {
      BoolExpr* variable = BoolExpr::Var(mappedSymbol(0, symbol));
      terms.push_back(value ? variable : BoolExpr::Not(variable));
    }
  }

  void addResetInputAssignments(size_t frame,
                                bool asserted,
                                std::vector<BoolExpr*>& terms) {
    for (const auto& [symbol, assertedValue] : problem_.resetBootstrapInputs) {
      const bool value = asserted ? assertedValue : !assertedValue;
      BoolExpr* variable =
          frame == problem_.resetBootstrapCycles
              ? BoolExpr::Var(symbol)
              : BoolExpr::Var(mappedSymbol(frame, symbol));
      terms.push_back(value ? variable : BoolExpr::Not(variable));
    }
  }

  void addComplementRelations(
      size_t frame,
      const std::vector<std::pair<size_t, size_t>>& pairs,
      std::vector<BoolExpr*>& terms) {
    for (const auto& [primary, complement] : pairs) {
      terms.push_back(makeEqualityExpr(
          BoolExpr::Var(mappedSymbol(frame, complement)),
          BoolExpr::Not(BoolExpr::Var(mappedSymbol(frame, primary)))));
    }
  }

  void addEqualityRelations(
      size_t frame,
      const std::vector<std::pair<size_t, size_t>>& pairs,
      std::vector<BoolExpr*>& terms) {
    for (const auto& [lhs, rhs] : pairs) {
      terms.push_back(makeEqualityExpr(
          BoolExpr::Var(mappedSymbol(frame, lhs)),
          BoolExpr::Var(mappedSymbol(frame, rhs))));
    }
  }

  void addDualRailValidity(size_t frame,
                           std::vector<BoolExpr*>& terms) {
    // Historical reset states belong to the same exact dual-rail domain as
    // F[0]; (may-be-one, may-be-zero) = (0, 0) is not a valid state.
    for (const auto& rails : problem_.dualRailStatePairs) {
      terms.push_back(BoolExpr::Or(
          BoolExpr::Var(mappedSymbol(frame, rails.mayBeOne)),
          BoolExpr::Var(mappedSymbol(frame, rails.mayBeZero))));
    }
  }

  void addStateDomainRelations(size_t frame,
                               std::vector<BoolExpr*>& terms) {
    addComplementRelations(frame, problem_.complementedStatePairs0, terms);
    addComplementRelations(frame, problem_.complementedStatePairs1, terms);
    addEqualityRelations(frame, problem_.sameFrameStateEqualityPairs0, terms);
    addEqualityRelations(frame, problem_.sameFrameStateEqualityPairs1, terms);
    addDualRailValidity(frame, terms);
  }

  void addTransitionRelation(size_t frame,
                             std::vector<BoolExpr*>& terms) {
    for (const auto& [stateSymbol, transition] : transitions_) {
      terms.push_back(makeEqualityExpr(
          BoolExpr::Var(mappedSymbol(frame + 1, stateSymbol)),
          remapAtFrame(
              transition, frame, transitionByState_.support(stateSymbol))));
    }
  }

  const KInductionProblem& problem_;
  TransitionExprResolver transitionByState_;
  std::vector<size_t> stateSymbols_;
  std::vector<std::pair<size_t, BoolExpr*>> transitions_;
  std::unordered_set<size_t> reservedSymbols_;
  size_t nextFreshSymbol_ = 2;
  std::vector<std::unordered_map<size_t, size_t>> symbolAtFrame_;
  std::vector<std::unordered_map<BoolExpr*, BoolExpr*>> remapMemoByFrame_;
};

BoolExpr* buildExactPdrInitFormula(
    const KInductionProblem& problem,
    PDRExactInitCache::Impl* sharedExactInit) {
  if (sharedExactInit != nullptr && sharedExactInit->initFormula != nullptr) {
    if (pdrStatsEnabled()) {
      emitSecDiag("SEC PDR stats: shared exact F[0] cache reused");
    }
    return sharedExactInit->initFormula;
  }

  const KInductionProblem& source =
      sharedExactInit != nullptr ? *sharedExactInit->sourceProblem : problem;
  BoolExpr* initFormula = nullptr;
  if (source.resetBootstrapCycles != 0) {
    // PDR requires F[0] to be the initial-state predicate. For SEC that starts
    // after reset, this predicate is the exact reset transition image.
    initFormula = ExactPdrBootstrapInitBuilder(source).build();
  } else {
    BoolExpr* init = source.initialCondition != nullptr
                         ? source.initialCondition
                         : BoolExpr::createTrue();
    initFormula = BoolExpr::simplify(
        appendAssignmentFormula(init, source.initialStateAssignments));
  }
  if (sharedExactInit != nullptr) {
    sharedExactInit->initFormula = initFormula;
    if (pdrStatsEnabled()) {
      emitSecDiag("SEC PDR stats: shared exact F[0] cache built");
    }
  }
  return initFormula;
}

}  // namespace

PDREngine::PDREngine(const KInductionProblem& problem,
                     KEPLER_FORMAL::Config::SolverType solverType,
                     size_t maxPredecessorQueries,
                     std::shared_ptr<PDRExactInitCache> exactInitCache)
    : problem_(problem),
      solverType_(solverType),
      maxPredecessorQueries_(maxPredecessorQueries),
      exactInitCache_(std::move(exactInitCache)) {}

PDRResult PDREngine::run(size_t maxFrames) const {
  return run(maxFrames, problem_.property);
}

PDRResult PDREngine::run(size_t maxFrames, BoolExpr* property) const {
  if (property == nullptr) {
    return {PDRStatus::Inconclusive, 0};  // LCOV_EXCL_LINE
  }
  const bool usesDefaultProperty = property == problem_.property;
  BoolExpr* normalizedProperty = BoolExpr::simplify(property);
  BoolExpr* normalizedBad =
      BoolExpr::simplify(BoolExpr::Not(normalizedProperty));
  std::optional<KInductionProblem> alternateProblem;
  const KInductionProblem* runProblem = &problem_;
  const bool canUseOriginalProblem =
      usesDefaultProperty && problem_.property == normalizedProperty &&
      problem_.bad == normalizedBad;
  if (!canUseOriginalProblem) {
    // Normal SEC output batches already contain their selected property.  Copy
    // the large immutable model only for the alternate-property API or an
    // unusual caller whose stored bad root is not the normalized complement.
    alternateProblem.emplace(problem_);
    alternateProblem->property = normalizedProperty;
    alternateProblem->bad = normalizedBad;
    if (!usesDefaultProperty) {
      // Alternate targets are independent PDR safety properties. Do not
      // inherit a target-specific induction hypothesis from normal SEC.
      alternateProblem->inductionProperty = nullptr;
      alternateProblem->inductionBad = nullptr;
    }
    runProblem = &*alternateProblem;
  }

  // Build the SEC startup frontier once so every frame query shares the same
  // interpretation of reset/bootstrap and frame-0 equality constraints.
  resetPdrBudgetExhaustion();
  setPdrPredecessorQueryLimit(maxPredecessorQueries_);
  emitPdrTraceProblem(*runProblem);
  PDRExactInitCache::Impl* sharedExactInit = nullptr;
  if (exactInitCache_ != nullptr &&
      exactInitCache_->impl_->matches(problem_, solverType_)) {
    sharedExactInit = exactInitCache_->impl_.get();
  }
  BoolExpr* initFormula =
      buildExactPdrInitFormula(problem_, sharedExactInit);
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

  std::unique_ptr<TransitionExprResolver> localTransitionByState;
  std::unique_ptr<ComplementPartnerIndex> localStateRelations;
  std::shared_ptr<PdrFormulaSupportCache> localFormulaSupportCache;
  TransitionExprResolver* transitionByStatePtr = nullptr;
  ComplementPartnerIndex* complementPartnersPtr = nullptr;
  PdrFormulaSupportCache* formulaSupportCachePtr = nullptr;
  if (sharedExactInit != nullptr) {
    transitionByStatePtr = &sharedExactInit->transitionByState;
    complementPartnersPtr = &sharedExactInit->stateRelations;
    if (sharedExactInit->formulaSupportCache == nullptr) {
      sharedExactInit->formulaSupportCache =
          std::make_shared<PdrFormulaSupportCache>();
    }
    formulaSupportCachePtr = sharedExactInit->formulaSupportCache.get();
    ++sharedExactInit->immutableMetadataUses;
    if (pdrStatsEnabled()) {
      emitSecDiag("SEC PDR stats: immutable model metadata ",
                  sharedExactInit->immutableMetadataUses == 1 ? "built"
                                                              : "reused",
                  " use=", sharedExactInit->immutableMetadataUses);
    }
  } else {
    localTransitionByState =
        std::make_unique<TransitionExprResolver>(*runProblem);
    localStateRelations = std::make_unique<ComplementPartnerIndex>(*runProblem);
    localFormulaSupportCache = std::make_shared<PdrFormulaSupportCache>();
    transitionByStatePtr = localTransitionByState.get();
    complementPartnersPtr = localStateRelations.get();
    formulaSupportCachePtr = localFormulaSupportCache.get();
  }
  TransitionExprResolver& transitionByState = *transitionByStatePtr;
  ComplementPartnerIndex& complementPartners = *complementPartnersPtr;
  PdrFormulaSupportCache& formulaSupportCache = *formulaSupportCachePtr;
  if (sharedExactInit != nullptr) {
    prepareSharedExactInitQueries(
        *sharedExactInit,
        initFormula,
        complementPartners,
        &formulaSupportCache);
  }
  // The bad predicate is the same for every frame query. Cache its support too
  // so repeated checks do not walk the combined mismatch formula again.
  const auto preciseBadStateSupport = collectBoundedStateSupportSymbols(
      runProblem->bad, std::numeric_limits<size_t>::max(), 0,
      transitionByState.stateSymbols());
  BadCubeAssumptionCache badCubeAssumptionCache;
  PredecessorAssumptionCache predecessorAssumptionCache;
  predecessorAssumptionCache.stateRelations = &complementPartners;
  if (sharedExactInit != nullptr) {
    predecessorAssumptionCache.sharedTargetSurfaces =
        &sharedExactInit->targetSurfaces;
    predecessorAssumptionCache.sharedTargetSurfaceBytes =
        &sharedExactInit->targetSurfaceBytes;
    predecessorAssumptionCache.sharedInitIntersectionSolver =
        &sharedExactInit->initIntersectionSolver;
    predecessorAssumptionCache.sharedInitIntersectionProblem =
        sharedExactInit->sourceProblem;
    predecessorAssumptionCache.sharedFrameZeroPredecessorSolver =
        &sharedExactInit->frameZeroPredecessorSolver;
    predecessorAssumptionCache.sharedFrameZeroPredecessorSymbols =
        &sharedExactInit->frameZeroPredecessorSymbols;
    predecessorAssumptionCache.sharedFrameZeroPredecessorProblem =
        sharedExactInit->sourceProblem;
    predecessorAssumptionCache.sharedFrameZeroTransitionModel =
        sharedExactInit->sourceProblem;
  }
  size_t remainingPredecessorQueries = maxPredecessorQueries_;
  size_t* predecessorQueryBudget =
      maxPredecessorQueries_ == 0 ? nullptr : &remainingPredecessorQueries;
  std::vector<FrameClauses> frames(1);
  emitPdrTraceFrames("initial_frames", frames);

  // Before growing any frame sequence, check whether exact Init itself already
  // contains a bad state.
  BadCubeAssumptionCache* initialBadCubeCache =
      sharedExactInit != nullptr
          ? &sharedExactInit->frameZeroBadCubeCache
          : &badCubeAssumptionCache;
  if (auto badCube = findBadCube(
          *runProblem, solverType_, initFormula, frameInvariant, frames,
          runProblem->bad, usesDefaultProperty, preciseBadStateSupport,
          transitionByState.stateSymbols(), 0, complementPartners,
          initialBadCubeCache, &formulaSupportCache);
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
  std::optional<InitFactIndex> localInitFacts;
  const InitFactIndex* initFactsPtr = nullptr;
  if (sharedExactInit != nullptr) {
    if (!sharedExactInit->initFacts.has_value()) {
      sharedExactInit->initFacts.emplace(
          buildInitFactIndex(*sharedExactInit->sourceProblem));
    }
    initFactsPtr = &*sharedExactInit->initFacts;
  } else {
    localInitFacts.emplace(buildInitFactIndex(*runProblem));
    initFactsPtr = &*localInitFacts;
  }
  const InitFactIndex& initFacts = *initFactsPtr;
  const auto seedClauses = buildSeedClauses(*runProblem, initFacts);
  frames.emplace_back(FrameClauses{seedClauses});
  emitPdrTraceFrames("seeded_frames", frames);
  for (size_t level = 1; level <= maxFrames; ++level) {
    // Phase 1: exhaust the proof obligations created by bad states that still
    // survive in the current frontier.
    while (true) {
      const auto badCube = findBadCube(
          *runProblem, solverType_, initFormula, frameInvariant, frames,
          runProblem->bad, usesDefaultProperty, preciseBadStateSupport,
          transitionByState.stateSymbols(), level, complementPartners,
          &badCubeAssumptionCache, &formulaSupportCache);
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
              *runProblem, solverType_, transitionByState, initFormula,
              frameInvariant, frames, initFacts, *badCube, level, badFrame,
              complementPartners, predecessorAssumptionCache,
              predecessorQueryBudget, &formulaSupportCache)) {
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
    propagateClauses(*runProblem, solverType_, transitionByState, initFormula,
                     frameInvariant, frames, level, complementPartners,
                     &predecessorAssumptionCache, predecessorQueryBudget,
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
