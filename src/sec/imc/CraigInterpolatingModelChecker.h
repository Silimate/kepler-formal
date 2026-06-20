// Copyright 2024-2026 keplertech.io
// SPDX-License-Identifier: GPL-3.0-only

#pragma once

#include <cstddef>

#include "kinduction/KInductionProblem.h"

namespace KEPLER_FORMAL::SEC {

enum class CraigImcStatus {
  Equivalent,
  NoProgress,
};

struct CraigImcResult {
  CraigImcStatus status = CraigImcStatus::NoProgress;
  size_t iterations = 0;
};

// Large-state IMC based on proof-derived Craig interpolants. Internal state in
// the two designs remains independent; the only relational clauses retained by
// this checker are clauses emitted by CaDiCaL's UNSAT proof.
class CraigInterpolatingModelChecker {
 public:
  explicit CraigInterpolatingModelChecker(const KInductionProblem& problem);

  CraigImcResult run(size_t maxIterations) const;

 private:
  const KInductionProblem& problem_;
};

}  // namespace KEPLER_FORMAL::SEC
