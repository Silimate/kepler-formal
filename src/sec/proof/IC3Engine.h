// Copyright 2024-2026 keplertech.io
// SPDX-License-Identifier: GPL-3.0-only

#pragma once

#include "../../config/Config.h"
#include "kinduction/KInductionProblem.h"

namespace KEPLER_FORMAL::SEC {

enum class IC3Status {
  Equivalent,
  Different,
  Inconclusive,
};

struct IC3Result {
  IC3Status status = IC3Status::Inconclusive;
  size_t bound = 0;
};

// A lightweight IC3/PDR engine for compact SEC problems. It blocks concrete
// state cubes rather than generalized clauses, so it is intentionally size
// gated, but it is a real SAT-based proof engine and not a shortcut.
class IC3Engine {
 public:
  IC3Engine(const KInductionProblem& problem,
            KEPLER_FORMAL::Config::SolverType solverType);

  IC3Result run(size_t maxFrames, size_t maxStateBits = 18) const;

 private:
  const KInductionProblem& problem_;
  KEPLER_FORMAL::Config::SolverType solverType_;
};

}  // namespace KEPLER_FORMAL::SEC
