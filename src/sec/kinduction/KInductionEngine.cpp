// Copyright 2024-2026 keplertech.io
// SPDX-License-Identifier: GPL-3.0-only

#include "kinduction/KInductionEngine.h"

#include "kinduction/BaseCaseSolver.h"
#include "kinduction/InductionStepSolver.h"

namespace KEPLER_FORMAL::SEC {

KInductionEngine::KInductionEngine(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType)
    : problem_(problem), solverType_(solverType) {}

KInductionResult KInductionEngine::run(size_t maxK) const {
  // Handle the purely combinational mismatch case before any unrolling.
  if (auto witness = findBaseCounterexample(0); witness.has_value()) {
    return {KInductionStatus::Different, witness->badFrame, std::move(witness)};
  }

  // If there is no state, the base check already decided the whole problem.
  if (problem_.combinedStateSymbols().empty()) {
    return {KInductionStatus::Equivalent, 0};
  }

  // Search the whole bounded horizon for concrete counterexamples before an
  // induction proof is allowed to conclude equivalence. This keeps SEC honest
  // when a later output divergence exists even though a small-k induction step
  // happens to be too coarse to expose it yet.
  for (size_t k = 1; k <= maxK; ++k) {
    printf("Checking k=%zu...\n", k);
    if (auto witness = findBaseCounterexample(k); witness.has_value()) {
      return {KInductionStatus::Different, witness->badFrame, std::move(witness)};
    }
  // }

  // for (size_t k = 1; k <= maxK; ++k) {
    // Induction step: assume the property along a simple path of length k and
    // ask whether the last frame can still be bad.
    if (provesByInduction(k)) {
      return {KInductionStatus::Equivalent, k};
    }
  }

  return {KInductionStatus::Inconclusive, maxK};
}

std::optional<KInductionResult::CounterexampleWitness>
KInductionEngine::findBaseCounterexample(size_t k) const {
  return SEC::findBaseCounterexample(problem_, solverType_, k);
}

bool KInductionEngine::provesByInduction(size_t k) const {
  return SEC::provesByInduction(problem_, solverType_, k);
}

}  // namespace KEPLER_FORMAL::SEC
