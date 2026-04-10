// Copyright 2024-2026 keplertech.io
// SPDX-License-Identifier: GPL-3.0-only

#pragma once

#include <string>
#include <utility>
#include <vector>

#include "BoolExpr.h"
#include "common/SignalKey.h"

namespace KEPLER_FORMAL::SEC {

struct KInductionProblem {
  std::vector<SignalKey> environmentInputs;
  std::vector<SignalKey> stateBits;
  std::vector<SignalKey> observedOutputs;
  std::vector<std::string> environmentInputNames;
  std::vector<std::string> stateBitNames;
  std::vector<std::string> observedOutputNames;
  std::vector<size_t> inputSymbols;
  std::vector<size_t> state0Symbols;
  std::vector<size_t> state1Symbols;
  std::vector<size_t> allSymbols;
  std::vector<std::pair<size_t, size_t>> complementedStatePairs0;
  std::vector<std::pair<size_t, size_t>> complementedStatePairs1;
  std::vector<BoolExpr*> observedOutputExprs0;
  std::vector<BoolExpr*> observedOutputExprs1;
  std::vector<std::pair<size_t, BoolExpr*>> transitions0;
  std::vector<std::pair<size_t, BoolExpr*>> transitions1;
  BoolExpr* property = nullptr;
  BoolExpr* bad = nullptr;
  std::string description;

  std::vector<size_t> combinedStateSymbols() const {
    std::vector<size_t> combined = state0Symbols;
    combined.insert(combined.end(), state1Symbols.begin(), state1Symbols.end());
    return combined;
  }
};

}  // namespace KEPLER_FORMAL::SEC
