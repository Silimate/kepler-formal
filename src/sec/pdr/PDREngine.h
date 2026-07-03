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

bool pdrStateEqualitySubsetPrefersCadical(
    bool usesDualRailStateEncoding,
    size_t equalityPairCount,
    KEPLER_FORMAL::Config::SolverType solverType,
    size_t solverSymbols,
    size_t pairLimit = 64,
    size_t symbolLimit = 256);

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

inline void mixPdrClauseFingerprintValue(size_t& seed, size_t value) {
  seed ^= value + 0x9e3779b97f4a7c15ULL + (seed << 6) + (seed >> 2);
}

template <typename ClauseRange>
size_t pdrOrderedClauseFingerprint(const ClauseRange& clauses) {
  if (clauses.empty()) {
    return 0;
  }
  // This is used for cache identity only. Keep order in the hash so two retry
  // clause vectors with the same clauses in different order do not require
  // normalization on the hot predecessor path.
  size_t seed = std::hash<size_t>()(clauses.size());
  for (const auto& clause : clauses) {
    size_t clauseSeed = 0x517cc1b727220a95ULL;
    for (const auto& literal : clause) {
      mixPdrClauseFingerprintValue(
          clauseSeed, std::hash<size_t>()(literal.symbol));
      mixPdrClauseFingerprintValue(
          clauseSeed, std::hash<bool>()(literal.positive));
    }
    mixPdrClauseFingerprintValue(seed, clauseSeed);
  }
  return seed;
}

inline std::vector<size_t> mergeSortedPdrSymbolVectors(
    const std::vector<size_t>& lhs,
    const std::vector<size_t>& rhs) {
  std::vector<size_t> merged;
  merged.reserve(lhs.size() + rhs.size());
  std::set_union(
      lhs.begin(),
      lhs.end(),
      rhs.begin(),
      rhs.end(),
      std::back_inserter(merged));
  return merged;
}

inline bool widenSortedPdrSymbolSurface(
    std::vector<size_t>& stableSurface,
    const std::vector<size_t>& requestedSurface) {
  if (std::includes(
          stableSurface.begin(),
          stableSurface.end(),
          requestedSurface.begin(),
          requestedSurface.end())) {
    return false;
  }
  // Keep the widened surface sorted and unique so it can be reused directly as
  // a FrameVariableStore symbol list and as part of the cache key.
  stableSurface =
      mergeSortedPdrSymbolVectors(stableSurface, requestedSurface);
  return true;
}

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

inline bool shouldUseResidualDualRailPredecessorBudget(
    bool usesDualRailStateEncoding,
    size_t observedOutputCount,
    size_t level,
    size_t targetCubeSize,
    size_t solverSymbolCount) {
  constexpr size_t kMaxOriginalResidualTargetCubeLiterals = 16;
  constexpr size_t kMaxOriginalResidualSolverSymbols = 8192;
  constexpr size_t kMaxResidualTargetCubeLiterals = 32;
  constexpr size_t kMaxResidualSolverSymbols = 16 * 1024;
  // Residual one-output dual-rail leaves are still local proof obligations even
  // when a rail-expanded output predicate reaches 28-32 literals. Keep broad
  // batches on the cheap limit, but let these local leaves spend the intended
  // residual predecessor budget instead of splitting on the 10k retry cap. The
  // wider Swerv shape is startup-only; higher PDR levels can enumerate many
  // sibling cubes, so they keep the historical small residual guard.
  const bool originalSmallResidualShape =
      targetCubeSize <= kMaxOriginalResidualTargetCubeLiterals &&
      solverSymbolCount <= kMaxOriginalResidualSolverSymbols;
  const bool localStartupResidualShape =
      level == 0 &&
      targetCubeSize <= kMaxResidualTargetCubeLiterals &&
      solverSymbolCount <= kMaxResidualSolverSymbols;
  return usesDualRailStateEncoding &&
         observedOutputCount == 1 &&
         targetCubeSize != 0 &&
         (originalSmallResidualShape || localStartupResidualShape);
}

inline bool shouldSharePredecessorUnsatCore(
    size_t frameFingerprint,
    size_t extraFrameFingerprint,
    bool excludeTargetOnCurrentFrame) {
  // A predecessor core is reusable for stronger target cubes only in the base
  // PDR context.  Do not share proofs that may have depended on selector
  // assumptions or one-off projected retry clauses.
  return frameFingerprint == 0 &&
         extraFrameFingerprint == 0 &&
         !excludeTargetOnCurrentFrame;
}

inline bool shouldRetryLargeDualRailPredecessorWithResetFrontier(
    bool usesDualRailStateEncoding,
    bool exactResetFrontierChecksEnabled,
    size_t observedOutputCount,
    size_t level,
    size_t targetCubeSize,
    size_t transitionSupportSize,
    size_t exactResetPrecheckSupportLimit) {
  constexpr size_t kMaxRetryTargetCubeLiterals = 32;
  // This exact proof is a local repair for hard one-output dual-rail leaves.
  // Keep the broad reset-frontier path off for batches and higher frames; the
  // caller may use it either before the expensive predecessor SAT attempt or as
  // a last-chance proof after a resource-limited SAT query returns unknown.
  return usesDualRailStateEncoding &&
         !exactResetFrontierChecksEnabled &&
         observedOutputCount == 1 &&
         level == 0 &&
         targetCubeSize != 0 &&
         targetCubeSize <= kMaxRetryTargetCubeLiterals &&
         transitionSupportSize <= exactResetPrecheckSupportLimit;
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
         transitionSupportSize >= kMinPrecheckTransitionSupport &&
         shouldRetryLargeDualRailPredecessorWithResetFrontier(
             usesDualRailStateEncoding,
             exactResetFrontierChecksEnabled,
             observedOutputCount,
             level,
             targetCubeSize,
             transitionSupportSize,
             exactResetPrecheckSupportLimit);
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
    return 0;
  }
  // Local final dual-rail leaves may exceed the broad reset-precheck support
  // cap by a small amount.  Let the exact reset proof run before building the
  // ordinary wide predecessor SAT instance, but keep batches and non-F0 queries
  // on the global cap.
  if (!hasLocalDualRailLeafRepairSurface ||
      observedOutputCount != 1 ||
      level != 0 ||
      targetCubeSize < kMinLocalPrecheckTargetCubeLiterals ||
      targetCubeSize > kMaxLocalPrecheckTargetCubeLiterals) {
    return configuredSupportLimit;
  }
  return std::max(configuredSupportLimit, localSupportLimit);
}

inline bool shouldUseCachedResetPredecessorCore(
    bool hasResetBootstrap,
    size_t level,
    bool hasCachedCore) {
  // Cached reset-predecessor cores come from exact concrete reset-frontier
  // proofs.  Reusing them is only a level-0 predecessor shortcut; higher PDR
  // frames still need ordinary frame-relative predecessor checks.
  return hasResetBootstrap && level == 0 && hasCachedCore;
}

inline bool shouldSeedExactResetPredecessorSiblingCores(
    size_t cubeSize,
    size_t knownCoreSize) {
  constexpr size_t kMaxSiblingSeedCubeLiterals = 32;
  // Seeding singleton siblings is a bounded reuse of an already-built exact
  // reset-frontier context.  Keep it aligned with the PDR bad-cube cap so
  // whole-chip rail surfaces cannot trigger an unbounded sweep.
  return cubeSize <= kMaxSiblingSeedCubeLiterals && knownCoreSize == 1;
}

}  // namespace detail

// Top-level clause-based Property Directed Reachability strategy for SEC. It
// follows the classic proof-obligation/blocking loop over the already-built
// SEC transition system.
class PDREngine {
 public:
  static constexpr size_t kDefaultPredecessorProjectionLimit = 32;
  static constexpr size_t kDefaultPreciseBadCubeStateLimit = 32;
  static constexpr size_t kDefaultBoundedRootGeneralizationAttempts = 16;

  PDREngine(const KInductionProblem& problem,
            KEPLER_FORMAL::Config::SolverType solverType,
            size_t predecessorProjectionLimit =
                kDefaultPredecessorProjectionLimit,
            size_t preciseBadCubeStateLimit =
                kDefaultPreciseBadCubeStateLimit,
            bool useExactFrameClauses = false,
            size_t maxPredecessorQueries = 0,
            bool refineProjectedCounterexamples = true,
            size_t maxBoundedRootGeneralizationAttempts =
                kDefaultBoundedRootGeneralizationAttempts,
            bool learnValidatedBadFormulaClauses = false,
            bool useExactResetFrontierChecks = true,
            size_t maxProjectedCounterexampleRefinements = 0);

  PDRResult run(size_t maxFrames, bool resetBootstrapFrameCheckedSafe = false) const;

 private:
  const KInductionProblem& problem_;
  KEPLER_FORMAL::Config::SolverType solverType_;
  size_t predecessorProjectionLimit_ = kDefaultPredecessorProjectionLimit;
  // Exact learned-frame encoding and predecessor-cube projection are separate
  // knobs. Large SEC PDR runs may need the full learned frame to avoid stale
  // abstract predecessors, while still carrying compact predecessor cubes so
  // blocking does not enumerate thousands of full SAT models.
  bool useExactFrameClauses_ = false;
  // Limits the precise state support used for the first bad obligation. SEC
  // can set this to the same width as predecessor projection so the first PDR
  // query does not start wider than later obligations.
  size_t preciseBadCubeStateLimit_ = kDefaultPreciseBadCubeStateLimit;
  // Projected SEC/PDR retries are intentionally approximate and can sometimes
  // enumerate abstract SAT predecessors without strengthening the proof. A
  // zero value is unlimited; non-zero budgets let those projected stages
  // return inconclusive and hand off to a stronger exact-frame retry.
  size_t maxPredecessorQueries_ = 0;
  // When true, a projected init-reaching obligation is validated internally
  // against the concrete bounded prefix and refined if it is abstract-only.
  // SEC strategy retry stages can disable this because they already validate
  // every PDR difference with the top-level concrete BMC checker before
  // accepting it.
  bool refineProjectedCounterexamples_ = true;
  // Literal-dropping on rejected abstract root cubes is sound but can be very
  // expensive on ASIC one-output cones. The final SEC retry may set this to
  // zero to learn the exact unreachable root cube directly after validation.
  size_t maxBoundedRootGeneralizationAttempts_ =
      kDefaultBoundedRootGeneralizationAttempts;
  // Optional final-stage CEGAR refinement: after exact BMC rejects an abstract
  // bad trace, learn the small state-only bad formula's CNF clauses in the PDR
  // frames. This blocks every valuation of that bad predicate at once.
  bool learnValidatedBadFormulaClauses_ = false;
  // Projected SEC/PDR stages are followed by concrete BMC validation in the
  // strategy. They can skip expensive exact reset-frontier SAT prechecks and
  // escalate on an abstract trace, while final self-refining PDR keeps them.
  bool useExactResetFrontierChecks_ = true;
  // Zero is unlimited. SEC uses a finite budget for dual-rail final batches so
  // an abstract-only root loop can be split or skipped instead of monopolizing
  // the run.
  size_t maxProjectedCounterexampleRefinements_ = 0;
};

}  // namespace KEPLER_FORMAL::SEC
