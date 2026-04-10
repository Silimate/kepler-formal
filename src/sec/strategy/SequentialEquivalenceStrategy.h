// Copyright 2024-2026 keplertech.io
// SPDX-License-Identifier: GPL-3.0-only

#pragma once

#include <cstddef>
#include <string>

#include "../../config/Config.h"

namespace naja::NL {
class SNLDesign;
}

namespace KEPLER_FORMAL::SEC {

enum class SequentialEquivalenceStatus {
  Equivalent,
  Different,
  Inconclusive,
  Unsupported,
};

struct SequentialEquivalenceResult {
  SequentialEquivalenceStatus status = SequentialEquivalenceStatus::Unsupported;
  size_t bound = 0;
  std::string reason;
};

// Builds a combined SEC problem from two sequential designs and discharges it
// with the k-induction engine.
class SequentialEquivalenceStrategy {
 public:
  SequentialEquivalenceStrategy(
      naja::NL::SNLDesign* top0,
      naja::NL::SNLDesign* top1,
      KEPLER_FORMAL::Config::SolverType solverType =
          KEPLER_FORMAL::Config::getSolverType());

  SequentialEquivalenceResult run(size_t maxK) const;

 private:
  naja::NL::SNLDesign* top0_;
  naja::NL::SNLDesign* top1_;
  KEPLER_FORMAL::Config::SolverType solverType_;
};

}  // namespace KEPLER_FORMAL::SEC
