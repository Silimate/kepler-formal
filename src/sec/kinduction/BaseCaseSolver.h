// Copyright 2024-2026 keplertech.io
// SPDX-License-Identifier: GPL-3.0-only

#pragma once

#include <cstddef>
#include <memory>
#include <optional>
#include <utility>
#include <vector>

#include "../../config/Config.h"
#include "kinduction/KInductionEngine.h"
#include "kinduction/KInductionProblem.h"

namespace KEPLER_FORMAL::SEC {

class TransitionExprResolver;
struct ResetFrontierReachabilityContext;

// Solves the bounded SEC base case for a single horizon k and reconstructs the
// first concrete counterexample if the property can fail within that prefix.
std::optional<KInductionResult::CounterexampleWitness> findBaseCounterexample(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    size_t k);

// Same bounded transition prefix as findBaseCounterexample(k), but the bad
// predicate is asserted only on the newest frontier frame. K-induction calls
// this after previous smaller frontiers were already proved safe, avoiding a
// repeated OR over old bad frames on every depth.
std::optional<KInductionResult::CounterexampleWitness>
findBaseCounterexampleAtFrontier(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    size_t k);

// Checks whether a concrete reset/bootstrap prefix can reach a state cube at
// the requested post-bootstrap depth. PDR uses this as an exact CEGAR check for
// abstract startup-frontier obligations; it shares the base-case COI machinery
// so ASIC-sized memories do not force a full transition unroll.
bool isStateCubeReachableAtResetFrontier(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    const std::vector<std::pair<size_t, bool>>& cube,
    size_t postBootstrapSteps);

// PDR already owns a transition resolver for its blocking loop. Reusing it here
// keeps the reset-frontier CEGAR query exact without rebuilding the large
// state-to-transition index for every blocked cube.
bool isStateCubeReachableAtResetFrontier(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    const TransitionExprResolver& transitionByState,
    const std::vector<std::pair<size_t, bool>>& cube,
    size_t postBootstrapSteps);

// Builds the immutable indexing needed by repeated reset-frontier cube checks.
// PDR uses this for level-zero CEGAR refinements so thousands of tiny cubes do
// not rescan the same initial/bootstrap equality tables.
std::shared_ptr<ResetFrontierReachabilityContext>
makeResetFrontierReachabilityContext(
    const KInductionProblem& problem,
    const TransitionExprResolver& transitionByState);

bool isStateCubeReachableAtResetFrontier(
    const ResetFrontierReachabilityContext& context,
    KEPLER_FORMAL::Config::SolverType solverType,
    const std::vector<std::pair<size_t, bool>>& cube,
    size_t postBootstrapSteps);

// Same exact bounded-prefix check as the cached API above, but encodes the
// queried cube as unit clauses in a fresh solver. This is intentionally used
// for isolated final PDR candidate validation, where BlackParrot sampling
// showed a single incremental Glucose assumption query dominating runtime.
bool isStateCubeReachableAtResetFrontierOneShot(
    const ResetFrontierReachabilityContext& context,
    KEPLER_FORMAL::Config::SolverType solverType,
    const std::vector<std::pair<size_t, bool>>& cube,
    size_t postBootstrapSteps);

// Returns a smaller cube that is still unreachable at the requested
// reset/bootstrap frontier, when the assumption-capable reset solver can
// extract such a core. std::nullopt means the original cube is reachable.
std::optional<std::vector<std::pair<size_t, bool>>>
findResetFrontierUnreachableCubeCore(
    const ResetFrontierReachabilityContext& context,
    KEPLER_FORMAL::Config::SolverType solverType,
    const std::vector<std::pair<size_t, bool>>& cube,
    size_t postBootstrapSteps);

}  // namespace KEPLER_FORMAL::SEC
