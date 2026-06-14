// Copyright 2024-2026 keplertech.io
// SPDX-License-Identifier: GPL-3.0-only

#pragma once

#include <cstddef>
#include <limits>

namespace KEPLER_FORMAL::SEC {

// LCOV_EXCL_START
inline size_t makePrivateProofLeafSymbol(size_t designIndex, size_t localSymbol) {
// LCOV_EXCL_STOP
  // Lazy SEC transitions may expose design-local support that is not a top
  // input or a modeled state bit. Keep it in a high, design-salted symbol range
  // so it cannot collide with the dense shared SEC symbols allocated from 2 up.
  // LCOV_EXCL_START
  const size_t max = std::numeric_limits<size_t>::max();
  const size_t salt =
      localSymbol <= (max - 3) / 2 ? localSymbol * 2 + (designIndex & 1) : localSymbol;
  return max - salt;
  // LCOV_EXCL_STOP
}

}  // namespace KEPLER_FORMAL::SEC
