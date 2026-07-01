// Copyright 2024-2026 keplertech.io
// SPDX-License-Identifier: GPL-3.0-only

#pragma once

#include "../../config/Config.h"
#include "kinduction/KInductionProblem.h"

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
