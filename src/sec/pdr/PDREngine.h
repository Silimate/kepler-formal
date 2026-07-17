// Copyright 2024-2026 keplertech.io
// SPDX-License-Identifier: GPL-3.0-only

#pragma once

#include "../../config/Config.h"
#include "kinduction/KInductionProblem.h"

#include <algorithm>
#include <iterator>
#include <memory>
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

// Output batches from one SEC problem have the same exact dual-rail startup
// relation. This scoped cache keeps that immutable F[0] work across PDR runs;
// learned frames and predecessor obligations remain local to each engine.
class PDRExactInitCache {
 public:
  struct Impl;

  PDRExactInitCache(
      const KInductionProblem& sourceProblem,
      KEPLER_FORMAL::Config::SolverType solverType);
  ~PDRExactInitCache();

  PDRExactInitCache(const PDRExactInitCache&) = delete;
  PDRExactInitCache& operator=(const PDRExactInitCache&) = delete;

 private:
  std::unique_ptr<Impl> impl_;

  friend class PDREngine;
};

namespace detail {

std::vector<size_t> makeDeterministicPdrWorklist(
    const std::unordered_set<size_t>& symbols);

bool pdrCubeLiteralOrderLess(size_t lhsSymbol,
                             bool lhsValue,
                             size_t rhsSymbol,
                             bool rhsValue);

bool pdrCubeAssignmentOrderLess(
    const std::vector<std::pair<size_t, bool>>& lhs,
    const std::vector<std::pair<size_t, bool>>& rhs);

bool pdrProofObligationPriorityLess(size_t lhsLevel,
                                    size_t lhsSequence,
                                    size_t rhsLevel,
                                    size_t rhsSequence);

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

inline bool isBroadDualRailResidualOutputSurface(
    bool usesDualRailStateEncoding,
    size_t observedOutputCount,
    size_t originalObservedOutputCount,
    size_t broadOutputLimit) {
  // A one-output residual leaf split from a broad public bus may use the local
  // memory/perf shortcuts. AES-sized leaves also have one output after
  // splitting, but keep the reference PDR route.
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
  // residual predecessor budget instead of stopping at the 10k query cap. The
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
    bool excludeTargetOnCurrentFrame) {
  // A predecessor core is reusable for stronger target cubes only in the base
  // PDR context. Do not share proofs that depended on the Q2 cube-exclusion
  // selector.
  return frameFingerprint == 0 && // LCOV_EXCL_LINE
         !excludeTargetOnCurrentFrame; // LCOV_EXCL_LINE
}

}  // namespace detail

// Top-level clause-based Property Directed Reachability strategy for SEC. It
// follows the classic proof-obligation/blocking loop over the already-built
// SEC transition system.
class PDREngine {
 public:
  PDREngine(const KInductionProblem& problem,
            KEPLER_FORMAL::Config::SolverType solverType,
            size_t maxPredecessorQueries = 0,
            std::shared_ptr<PDRExactInitCache> exactInitCache = nullptr);

  PDRResult run(size_t maxFrames) const;
  // Run the same transition system against an alternate safety property.
  // The target is deliberately separate from the model so it cannot alter
  // exact F[0]; the corresponding bad predicate is derived internally.
  PDRResult run(size_t maxFrames, BoolExpr* property) const;

 private:
  const KInductionProblem& problem_;
  KEPLER_FORMAL::Config::SolverType solverType_;
  size_t maxPredecessorQueries_ = 0;
  std::shared_ptr<PDRExactInitCache> exactInitCache_;
};

}  // namespace KEPLER_FORMAL::SEC
