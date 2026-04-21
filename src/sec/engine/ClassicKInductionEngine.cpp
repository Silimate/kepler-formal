// Copyright 2024-2026 keplertech.io
// SPDX-License-Identifier: GPL-3.0-only

#include "engine/ClassicKInductionEngine.h"

namespace KEPLER_FORMAL::SEC {

// Overall classic-k-induction wrapper algorithm:
// 1. Run the shared k-induction engine on the already-built SEC problem.
// 2. Preserve its proof/counterexample depth exactly.
// 3. Translate the generic k-induction status into the dedicated public status
//    used by the explicit "classic k-induction" SEC engine selection.

ClassicKInductionEngine::ClassicKInductionEngine(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType)
    : problem_(problem), solverType_(solverType) {}

ClassicKInductionResult ClassicKInductionEngine::run(size_t maxK) const {
  // This engine is intentionally thin: the separation here is about API and
  // top-level engine choice, not about duplicating the underlying algorithm.
  KInductionEngine engine(problem_, solverType_);
  const auto result = engine.run(maxK);

  // Re-express the shared result in the dedicated result type so callers can
  // tell which top-level SEC engine was selected without inspecting internals.
  switch (result.status) {
    case KInductionStatus::Equivalent:
      return {ClassicKInductionStatus::Equivalent, result.bound, result.witness};
    case KInductionStatus::Different:
      return {ClassicKInductionStatus::Different, result.bound, result.witness};
    case KInductionStatus::Inconclusive:
    default:
      return {ClassicKInductionStatus::Inconclusive, result.bound, result.witness};
  }
}

}  // namespace KEPLER_FORMAL::SEC
