// Copyright 2024-2026 keplertech.io
// SPDX-License-Identifier: GPL-3.0-only

#pragma once

#include <sstream>
#include <string>

#include "../../strategies/miter/BuildPrimaryOutputClauses.h"

namespace KEPLER_FORMAL::SEC {

using SignalKey = KEPLER_FORMAL::BuildPrimaryOutputClauses::PathKey;
using SignalKeyHash = KEPLER_FORMAL::BuildPrimaryOutputClauses::KeyHash;

struct SignalKeyLess {
  bool operator()(const SignalKey& lhs, const SignalKey& rhs) const {
    return lhs < rhs;
  }
};

inline std::string signalKeyToString(const SignalKey& key) {
  std::ostringstream oss;
  for (const auto& nameID : key.first) {
    oss << nameID << ".";
  }
  for (const auto& objectID : key.second) {
    oss << objectID << ".";
  }
  return oss.str();
}

}  // namespace KEPLER_FORMAL::SEC
