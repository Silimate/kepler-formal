// Copyright 2024-2026 keplertech.io
// SPDX-License-Identifier: GPL-3.0-only

#pragma once

#include <cstddef>

#include "../../config/Config.h"
#include "kinduction/KInductionProblem.h"

namespace KEPLER_FORMAL::SEC {

enum class KInductionStatus {
  Equivalent,
  Different,
  Inconclusive,
};

struct KInductionResult {
  KInductionStatus status = KInductionStatus::Inconclusive;
  size_t bound = 0;
};

// Runs the standard k-induction loop for the SEC problem: a BMC-style base
// search for counterexamples plus an induction step over simple paths.
class KInductionEngine {
 public:
  KInductionEngine(const KInductionProblem& problem,
                   KEPLER_FORMAL::Config::SolverType solverType);

  KInductionResult run(size_t maxK) const;

 private:
  bool hasBaseCounterexample(size_t k) const;
  bool provesByInduction(size_t k) const;

  const KInductionProblem& problem_;
  KEPLER_FORMAL::Config::SolverType solverType_;
};

}  // namespace KEPLER_FORMAL::SEC
