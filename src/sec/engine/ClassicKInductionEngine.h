// Copyright 2024-2026 keplertech.io
// SPDX-License-Identifier: GPL-3.0-only

#pragma once

#include <optional>

#include "../../config/Config.h"
#include "engine/KInductionEngine.h"
#include "kinduction/KInductionProblem.h"

namespace KEPLER_FORMAL::SEC {

enum class ClassicKInductionStatus {
  Equivalent,
  Different,
  Inconclusive,
};

struct ClassicKInductionResult {
  ClassicKInductionStatus status = ClassicKInductionStatus::Inconclusive;
  size_t bound = 0;
  std::optional<KInductionResult::CounterexampleWitness> witness;
};

// A thin top-level engine that exposes the classic SEC k-induction flow as an
// explicit selectable mode, separate from the legacy hybrid path.
class ClassicKInductionEngine {
 public:
  ClassicKInductionEngine(const KInductionProblem& problem,
                          KEPLER_FORMAL::Config::SolverType solverType);

  ClassicKInductionResult run(size_t maxK) const;

 private:
  const KInductionProblem& problem_;
  KEPLER_FORMAL::Config::SolverType solverType_;
};

}  // namespace KEPLER_FORMAL::SEC
