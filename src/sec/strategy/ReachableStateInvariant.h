// Copyright 2024-2026 keplertech.io
// SPDX-License-Identifier: GPL-3.0-only

#pragma once

#include <cstddef>
#include <unordered_map>

#include "model/SequentialDesignModel.h"

namespace KEPLER_FORMAL::SEC {

// Startup strengthening is design-local only.  It may derive concrete
// per-design reset/bootstrap state values, but it must never relate internal
// state bits from the two SEC designs.
struct ReachableStateInvariant {
  size_t bootstrapCycles = 0;
  std::unordered_map<SignalKey, bool, SignalKeyHash> bootstrapValues0;
  std::unordered_map<SignalKey, bool, SignalKeyHash> bootstrapValues1;
};

ReachableStateInvariant buildReachableStateInvariant(
    const SequentialDesignModel& model0,
    const SequentialDesignModel& model1,
    bool deriveResetBootstrapStrengthening = true);

}  // namespace KEPLER_FORMAL::SEC
