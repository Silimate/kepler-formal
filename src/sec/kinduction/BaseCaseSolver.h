// Copyright 2024-2026 keplertech.io
// SPDX-License-Identifier: GPL-3.0-only

#pragma once

#include <cstddef>
#include <optional>

#include "../../config/Config.h"
#include "kinduction/KInductionEngine.h"
#include "kinduction/KInductionProblem.h"

namespace KEPLER_FORMAL::SEC {

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

}  // namespace KEPLER_FORMAL::SEC
