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

// Same exact frontier query, but only returns SAT/UNSAT. This keeps
// multi-output SEC validation as one batch formula instead of localizing the
// witness per output, which is much cheaper for PDR CEGAR refinements that only
// need to know whether the candidate bad formula is concretely reachable. It
// also avoids re-encoding previously checked safe frames and uses the PDR
// solver profile because this is a short-lived PDR obligation, not a standalone
// k-induction proof.
bool hasBaseCounterexampleAtFrontier(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    size_t k);

// Exact one-sided PDR refinement helper: returns true only when an
// over-approximate, startup-pruned base query proves the frontier bad predicate
// unreachable. A false result is inconclusive, not a counterexample, because
// the pruned query may admit abstract startup states that the full SEC base
// query would reject.
bool provesNoBaseCounterexampleAtFrontier(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    size_t k);

// Same frontier proof as the original SEC base-case flow: keep the multi-output
// bad predicate as one formula, constrain earlier safe frames, and use the
// cone-proof solver profile. Exact-frame PDR uses this for large whole-batch
// bad-formula learning where the PDR proof-only profile can be slower.
bool provesNoBaseCounterexampleAtFrontierWithSecConeProof(
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
    const TransitionExprResolver& transitionByState,
    BoolExpr* frameInvariant = nullptr);

// Records an externally-proved unreachable reset-frontier cube in the same
// cache used by exact reset-frontier SAT queries. PDR uses this when a cheaper
// reset-specialized proof has already established unreachability, allowing
// later post-bootstrap queries to reuse that fact as a safe-prefix blocker.
void rememberResetFrontierUnreachableCube(
    const ResetFrontierReachabilityContext& context,
    const std::vector<std::pair<size_t, bool>>& cube,
    size_t postBootstrapSteps);

bool isStateCubeReachableAtResetFrontier(
    const ResetFrontierReachabilityContext& context,
    KEPLER_FORMAL::Config::SolverType solverType,
    const std::vector<std::pair<size_t, bool>>& cube,
    size_t postBootstrapSteps,
    bool usePostBootstrapPrechecks = true,
    int64_t startupConflictLimit = -1,
    int64_t startupPropagationLimit = -1);

// Prebuilds the shared assumption-capable reset-frontier solver for a cube
// support. Later exact cube queries whose symbols are covered by this support
// reuse the solver instead of rebuilding the same bounded reset prefix.
void primeResetFrontierReachabilitySolver(
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
    size_t postBootstrapSteps,
    bool usePostBootstrapPrechecks = true);

// Checks the same cube against every concrete reset/bootstrap frontier from
// post-bootstrap step 0 through maxPostBootstrapSteps using one shared unroll.
// This is for PDR final-candidate validation where rebuilding the same reset
// prefix once per frame dominates runtime.
bool isStateCubeReachableWithinResetFrontier(
    const ResetFrontierReachabilityContext& context,
    KEPLER_FORMAL::Config::SolverType solverType,
    const std::vector<std::pair<size_t, bool>>& cube,
    size_t maxPostBootstrapSteps);

// Checks whether any one of several state cubes can appear at any concrete
// reset/bootstrap frontier up to maxPostBootstrapSteps. This is the batched
// form of the cube API above: it encodes one shared prefix and one disjunction
// over the requested cubes, so PDR can validate small state-only bad CNFs
// without solving one reset-frontier query per assignment.
bool anyStateCubeReachableWithinResetFrontier(
    const ResetFrontierReachabilityContext& context,
    KEPLER_FORMAL::Config::SolverType solverType,
    const std::vector<std::vector<std::pair<size_t, bool>>>& cubes,
    size_t maxPostBootstrapSteps);

// Checks whether any one of several state cubes can appear at exactly the
// requested post-bootstrap frontier. Unknown/resource-limited SAT queries are
// treated as reachable, so callers can use this as a bounded refinement proof:
// false is a sound unreachable result, true is reachable or inconclusive.
bool anyStateCubeReachableAtResetFrontier(
    const ResetFrontierReachabilityContext& context,
    KEPLER_FORMAL::Config::SolverType solverType,
    const std::vector<std::vector<std::pair<size_t, bool>>>& cubes,
    size_t postBootstrapSteps,
    long long glucoseConflictLimit,
    long long glucosePropagationLimit);

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
