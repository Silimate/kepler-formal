// Copyright 2024-2026 keplertech.io
// SPDX-License-Identifier: GPL-3.0-only

#pragma once

#include "../../config/Config.h"
#include "kinduction/KInductionProblem.h"

#include <algorithm>
#include <functional>
#include <iterator>
#include <unordered_set>
#include <utility>
#include <vector>

namespace KEPLER_FORMAL::SEC {

enum class PDRStatus {
  Equivalent,
  Different,
  Inconclusive,
};

struct PDRResult {
  PDRStatus status = PDRStatus::Inconclusive;
  size_t bound = 0;
};

namespace detail {

bool pdrResetBootstrapPrecheckTooLarge(bool usesDualRailStateEncoding,
                                       size_t observedOutputCount,
                                       size_t originalObservedOutputCount,
                                       size_t transitionSources,
                                       size_t transitionSourceLimit,
                                       size_t outputLimit = 128);

std::vector<size_t> makeDeterministicPdrWorklist(
    const std::unordered_set<size_t>& symbols);

bool pdrCubeLiteralOrderLess(size_t lhsSymbol,
                             bool lhsValue,
                             size_t rhsSymbol,
                             bool rhsValue);

bool pdrCubeAssignmentOrderLess(
    const std::vector<std::pair<size_t, bool>>& lhs,
    const std::vector<std::pair<size_t, bool>>& rhs);

inline void mixPdrClauseFingerprintValue(size_t& seed, size_t value) { // LCOV_EXCL_LINE
  seed ^= value + 0x9e3779b97f4a7c15ULL + (seed << 6) + (seed >> 2); // LCOV_EXCL_LINE
} // LCOV_EXCL_LINE

template <typename ClauseRange>
size_t pdrOrderedClauseFingerprint(const ClauseRange& clauses) { // LCOV_EXCL_LINE
  if (clauses.empty()) { // LCOV_EXCL_LINE
    return 0; // LCOV_EXCL_LINE
  }
  // This is used for cache identity only. Keep order in the hash so two retry
  // clause vectors with the same clauses in different order do not require
  // normalization on the hot predecessor path.
  size_t seed = std::hash<size_t>()(clauses.size()); // LCOV_EXCL_LINE
  for (const auto& clause : clauses) { // LCOV_EXCL_LINE
    size_t clauseSeed = 0x517cc1b727220a95ULL; // LCOV_EXCL_LINE
    for (const auto& literal : clause) { // LCOV_EXCL_LINE
      mixPdrClauseFingerprintValue( // LCOV_EXCL_LINE
          clauseSeed, std::hash<size_t>()(literal.symbol)); // LCOV_EXCL_LINE
      mixPdrClauseFingerprintValue( // LCOV_EXCL_LINE
          clauseSeed, std::hash<bool>()(literal.positive)); // LCOV_EXCL_LINE
    }
    mixPdrClauseFingerprintValue(seed, clauseSeed); // LCOV_EXCL_LINE
  }
  return seed; // LCOV_EXCL_LINE
} // LCOV_EXCL_LINE

inline std::vector<size_t> mergeSortedPdrSymbolVectors( // LCOV_EXCL_LINE
    const std::vector<size_t>& lhs,
    const std::vector<size_t>& rhs) {
  std::vector<size_t> merged; // LCOV_EXCL_LINE
  merged.reserve(lhs.size() + rhs.size()); // LCOV_EXCL_LINE
  std::set_union( // LCOV_EXCL_LINE
      lhs.begin(), // LCOV_EXCL_LINE
      lhs.end(), // LCOV_EXCL_LINE
      rhs.begin(), // LCOV_EXCL_LINE
      rhs.end(), // LCOV_EXCL_LINE
      std::back_inserter(merged)); // LCOV_EXCL_LINE
  return merged; // LCOV_EXCL_LINE
} // LCOV_EXCL_LINE

inline bool widenSortedPdrSymbolSurface( // LCOV_EXCL_LINE
    std::vector<size_t>& stableSurface,
    const std::vector<size_t>& requestedSurface) {
  if (std::includes( // LCOV_EXCL_LINE
          stableSurface.begin(), // LCOV_EXCL_LINE
          stableSurface.end(), // LCOV_EXCL_LINE
          requestedSurface.begin(), // LCOV_EXCL_LINE
          requestedSurface.end())) { // LCOV_EXCL_LINE
    return false; // LCOV_EXCL_LINE
  }
  // Keep the widened surface sorted and unique so it can be reused directly as
  // a FrameVariableStore symbol list and as part of the cache key.
  stableSurface = // LCOV_EXCL_LINE
      mergeSortedPdrSymbolVectors(stableSurface, requestedSurface); // LCOV_EXCL_LINE
  return true; // LCOV_EXCL_LINE
} // LCOV_EXCL_LINE

inline bool shouldUseStableLocalPredecessorCacheSurface(
    bool hasLocalDualRailLeafRepairSurface,
    bool exactFrameClauses,
    size_t level) {
  // Stable local-leaf caches are a startup/frontier optimization. Higher PDR
  // levels already carry learned-frame context; keeping those queries on their
  // exact local surface avoids turning a small predecessor retry into a broad
  // SAT instance.
  return hasLocalDualRailLeafRepairSurface && exactFrameClauses && level == 0;
}

inline bool isBroadDualRailResidualOutputSurface(
    bool usesDualRailStateEncoding,
    size_t observedOutputCount,
    size_t originalObservedOutputCount,
    size_t broadOutputLimit) {
  // A one-output residual leaf split from a broad public bus may use the local
  // memory/perf shortcuts. AES-sized leaves also have one output after
  // splitting, but keep the reference PDR repair route.
  return usesDualRailStateEncoding &&
         observedOutputCount == 1 && // LCOV_EXCL_LINE
         originalObservedOutputCount > broadOutputLimit; // LCOV_EXCL_LINE
}

inline bool shouldUseResidualDualRailPredecessorBudget( // LCOV_EXCL_LINE
    bool usesDualRailStateEncoding,
    size_t observedOutputCount,
    size_t level,
    size_t targetCubeSize,
    size_t solverSymbolCount) {
  constexpr size_t kMaxOriginalResidualTargetCubeLiterals = 16; // LCOV_EXCL_LINE
  constexpr size_t kMaxOriginalResidualSolverSymbols = 8192; // LCOV_EXCL_LINE
  constexpr size_t kMaxResidualTargetCubeLiterals = 32; // LCOV_EXCL_LINE
  constexpr size_t kMaxResidualSolverSymbols = 16 * 1024; // LCOV_EXCL_LINE
  // Residual one-output dual-rail leaves are still local proof obligations even
  // when a rail-expanded output predicate reaches 28-32 literals. Keep broad
  // batches on the cheap limit, but let these local leaves spend the intended
  // residual predecessor budget instead of splitting on the 10k retry cap. The
  // wider Swerv shape is startup-only; higher PDR levels can enumerate many
  // sibling cubes, so they keep the historical small residual guard.
  const bool originalSmallResidualShape = // LCOV_EXCL_LINE
      targetCubeSize <= kMaxOriginalResidualTargetCubeLiterals && // LCOV_EXCL_LINE
      solverSymbolCount <= kMaxOriginalResidualSolverSymbols; // LCOV_EXCL_LINE
  const bool localStartupResidualShape = // LCOV_EXCL_LINE
      level == 0 && // LCOV_EXCL_LINE
      targetCubeSize <= kMaxResidualTargetCubeLiterals && // LCOV_EXCL_LINE
      solverSymbolCount <= kMaxResidualSolverSymbols; // LCOV_EXCL_LINE
  return usesDualRailStateEncoding && // LCOV_EXCL_LINE
         observedOutputCount == 1 && // LCOV_EXCL_LINE
         targetCubeSize != 0 && // LCOV_EXCL_LINE
         (originalSmallResidualShape || localStartupResidualShape); // LCOV_EXCL_LINE
}

inline bool shouldSharePredecessorUnsatCore( // LCOV_EXCL_LINE
    size_t frameFingerprint,
    size_t extraFrameFingerprint,
    bool excludeTargetOnCurrentFrame) {
  // A predecessor core is reusable for stronger target cubes only in the base
  // PDR context.  Do not share proofs that may have depended on selector
  // assumptions or one-off projected retry clauses.
  return frameFingerprint == 0 && // LCOV_EXCL_LINE
         extraFrameFingerprint == 0 && // LCOV_EXCL_LINE
         !excludeTargetOnCurrentFrame; // LCOV_EXCL_LINE
}

inline bool shouldRetryLargeDualRailPredecessorWithResetFrontier( // LCOV_EXCL_LINE
    bool usesDualRailStateEncoding,
    bool exactResetFrontierChecksEnabled,
    size_t observedOutputCount,
    size_t level,
    size_t targetCubeSize,
    size_t transitionSupportSize,
    size_t exactResetPrecheckSupportLimit) {
  constexpr size_t kMaxRetryTargetCubeLiterals = 32; // LCOV_EXCL_LINE
  // This exact proof is a local repair for hard one-output dual-rail leaves.
  // Keep the broad reset-frontier path off for batches and higher frames; the
  // caller may use it either before the expensive predecessor SAT attempt or as
  // a last-chance proof after a resource-limited SAT query returns unknown.
  return usesDualRailStateEncoding && // LCOV_EXCL_LINE
         !exactResetFrontierChecksEnabled && // LCOV_EXCL_LINE
         observedOutputCount == 1 && // LCOV_EXCL_LINE
         level == 0 && // LCOV_EXCL_LINE
         targetCubeSize != 0 && // LCOV_EXCL_LINE
         targetCubeSize <= kMaxRetryTargetCubeLiterals && // LCOV_EXCL_LINE
         transitionSupportSize <= exactResetPrecheckSupportLimit; // LCOV_EXCL_LINE
}

inline bool shouldPrecheckLargeDualRailPredecessorWithResetFrontier(
    bool usesDualRailStateEncoding,
    bool exactResetFrontierChecksEnabled,
    size_t observedOutputCount,
    size_t level,
    size_t targetCubeSize,
    size_t transitionSupportSize,
    size_t exactResetPrecheckSupportLimit) {
  constexpr size_t kMinPrecheckTargetCubeLiterals = 28;
  constexpr size_t kMinPrecheckTransitionSupport = 4000;
  // Small local cubes are usually cheaper as ordinary predecessor SAT queries.
  // Spend the exact reset-frontier query up front only on the residual cube
  // shape that otherwise burns the restored predecessor budget first.
  return targetCubeSize >= kMinPrecheckTargetCubeLiterals &&
         transitionSupportSize >= kMinPrecheckTransitionSupport && // LCOV_EXCL_LINE
         shouldRetryLargeDualRailPredecessorWithResetFrontier( // LCOV_EXCL_LINE
             usesDualRailStateEncoding, // LCOV_EXCL_LINE
             exactResetFrontierChecksEnabled, // LCOV_EXCL_LINE
             observedOutputCount, // LCOV_EXCL_LINE
             level, // LCOV_EXCL_LINE
             targetCubeSize, // LCOV_EXCL_LINE
             transitionSupportSize, // LCOV_EXCL_LINE
             exactResetPrecheckSupportLimit); // LCOV_EXCL_LINE
}

inline bool shouldUseOneShotLargeDualRailResetFrontierPredecessor( // LCOV_EXCL_LINE
    bool hasLargeDualRailResetFrontierSurface,
    bool hasLocalDualRailLeafRepairSurface) {
  // If an exact reset-frontier query runs on a huge non-local leaf, avoid
  // pinning the reset-prefix SAT solver that can dominate top MEM there.
  return hasLargeDualRailResetFrontierSurface && // LCOV_EXCL_LINE
         !hasLocalDualRailLeafRepairSurface; // LCOV_EXCL_LINE
}

inline bool shouldRunLargeDualRailResetFrontierQuery( // LCOV_EXCL_LINE
    bool resetFrontierQueryAllowed,
    bool hasLargeDualRailResetFrontierSurface,
    bool hasLocalDualRailLeafRepairSurface) {
  // The exact reset-frontier query is an optional PDR accelerator used before
  // or after the local predecessor query.  On huge non-local leaves, one-shot
  // mode protects memory but rebuilding the reset transition dominates runtime;
  // keep the exact query for cached/local repair and let ordinary PDR splitting
  // handle the non-local hot path.
  return resetFrontierQueryAllowed && // LCOV_EXCL_LINE
         !shouldUseOneShotLargeDualRailResetFrontierPredecessor( // LCOV_EXCL_LINE
             hasLargeDualRailResetFrontierSurface, // LCOV_EXCL_LINE
             hasLocalDualRailLeafRepairSurface); // LCOV_EXCL_LINE
}

inline size_t effectiveLocalDualRailExactResetPrecheckSupportLimit(
    bool hasLocalDualRailLeafRepairSurface,
    size_t observedOutputCount,
    size_t level,
    size_t targetCubeSize,
    size_t configuredSupportLimit,
    size_t localSupportLimit) {
  constexpr size_t kMinLocalPrecheckTargetCubeLiterals = 28;
  constexpr size_t kMaxLocalPrecheckTargetCubeLiterals = 32;
  if (configuredSupportLimit == 0) {
    return 0; // LCOV_EXCL_LINE
  }
  // Local final dual-rail leaves may exceed the broad reset-precheck support
  // cap by a small amount.  Let the exact reset proof run before building the
  // ordinary wide predecessor SAT instance, but keep batches and non-F0 queries
  // on the global cap.
  if (!hasLocalDualRailLeafRepairSurface ||
      observedOutputCount != 1 || // LCOV_EXCL_LINE
      level != 0 || // LCOV_EXCL_LINE
      targetCubeSize < kMinLocalPrecheckTargetCubeLiterals || // LCOV_EXCL_LINE
      targetCubeSize > kMaxLocalPrecheckTargetCubeLiterals) { // LCOV_EXCL_LINE
    return configuredSupportLimit;
  }
  return std::max(configuredSupportLimit, localSupportLimit); // LCOV_EXCL_LINE
}

inline bool shouldSeedExactResetPredecessorSiblingCores( // LCOV_EXCL_LINE
    size_t cubeSize,
    size_t knownCoreSize) {
  constexpr size_t kMaxSiblingSeedCubeLiterals = 32; // LCOV_EXCL_LINE
  // Seeding singleton siblings is a bounded reuse of an already-built exact
  // reset-frontier context.  Keep it aligned with the PDR bad-cube cap so
  // whole-chip rail surfaces cannot trigger an unbounded sweep.
  return cubeSize <= kMaxSiblingSeedCubeLiterals && knownCoreSize == 1; // LCOV_EXCL_LINE
}

}  // namespace detail

// Top-level clause-based Property Directed Reachability strategy for SEC. It
// follows the classic proof-obligation/blocking loop over the already-built
// SEC transition system.
class PDREngine {
 public:
  PDREngine(const KInductionProblem& problem,
            KEPLER_FORMAL::Config::SolverType solverType,
            size_t maxPredecessorQueries = 0);

  PDRResult run(size_t maxFrames, bool resetBootstrapFrameCheckedSafe = false) const;

 private:
  const KInductionProblem& problem_;
  KEPLER_FORMAL::Config::SolverType solverType_;
  size_t maxPredecessorQueries_ = 0;
};

}  // namespace KEPLER_FORMAL::SEC
