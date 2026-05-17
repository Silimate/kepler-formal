// Copyright 2024-2026 keplertech.io
// SPDX-License-Identifier: GPL-3.0-only

#pragma once

#include <array>
#include <memory>
#include <set>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

#include "BoolExpr.h"
#include "common/SignalKey.h"

namespace KEPLER_FORMAL::SEC {

struct LazyTransitionSource {
  size_t designIndex = 0;
  BoolExpr* localExpr = nullptr;
};

struct LazyTransitionStore {
  // Large SEC designs can have hundreds of thousands of modeled state bits.
  // K-induction proves one output cone at a time, so eagerly remapping every
  // state update into the shared symbol space wastes time and memory before
  // COI reduction can remove most of it. This store keeps the original local
  // next-state expressions plus the per-design symbol remap tables; the
  // k-induction encoders remap only transition equations that are actually
  // pulled into the current proof cone.
  std::unordered_map<size_t, LazyTransitionSource> sourceByStateSymbol;
  std::array<std::unordered_map<size_t, size_t>, 2> localToCombinedByDesign;
  mutable std::array<std::unordered_map<BoolExpr*, BoolExpr*>, 2> remapMemoByDesign;
  mutable std::unordered_map<size_t, BoolExpr*> remappedByStateSymbol;
  // Output-batched SEC creates a fresh transition resolver for each PDR slice.
  // Keep lazy support and size metadata with the shared transition store so
  // reset-frontier COI rebuilding does not repeatedly walk the same large
  // source BoolExpr DAGs across batches.
  mutable std::unordered_map<size_t, std::set<size_t>> supportByStateSymbol;
  mutable std::unordered_map<size_t, size_t> nodeCountByStateSymbol;
};

struct KInductionProblem {
  std::vector<SignalKey> environmentInputs;
  std::vector<SignalKey> observedOutputs;
  std::vector<std::string> environmentInputNames;
  std::vector<std::string> observedOutputNames;
  std::vector<size_t> inputSymbols;
  size_t resetBootstrapCycles = 0;
  std::vector<std::pair<size_t, bool>> resetBootstrapInputs;
  std::vector<std::pair<size_t, bool>> initialStateAssignments;
  std::vector<std::pair<size_t, size_t>> initialStateEqualityPairs;
  std::vector<std::pair<size_t, bool>> bootstrapStateAssignments;
  std::vector<std::pair<size_t, size_t>> bootstrapStateEqualityPairs;
  std::vector<std::pair<size_t, size_t>> inductiveStateEqualityPairs;
  std::vector<size_t> state0Symbols;
  std::vector<size_t> state1Symbols;
  std::vector<size_t> allSymbols;
  std::vector<std::pair<size_t, size_t>> complementedStatePairs0;
  std::vector<std::pair<size_t, size_t>> complementedStatePairs1;
  std::vector<BoolExpr*> observedOutputExprs0;
  std::vector<BoolExpr*> observedOutputExprs1;
  std::vector<std::pair<size_t, BoolExpr*>> transitions0;
  std::vector<std::pair<size_t, BoolExpr*>> transitions1;
  std::shared_ptr<LazyTransitionStore> lazyTransitions;
  BoolExpr* initialCondition = nullptr;
  size_t initializedStateCount = 0;
  size_t totalStateCount = 0;
  BoolExpr* property = nullptr;
  BoolExpr* bad = nullptr;
  BoolExpr* inductionProperty = nullptr;
  BoolExpr* inductionBad = nullptr;
  bool inductionPropertyAssumesInductiveStateEqualities = false;
  std::string description;

  bool hasSequentialState() const {
    return !state0Symbols.empty() || !state1Symbols.empty();
  }

  bool hasExplicitInitialState() const {
    return initializedStateCount != 0;
  }

  bool hasCompleteInitialState() const {
    return initializedStateCount != 0 && initializedStateCount == totalStateCount;
  }

  bool hasResetBootstrap() const {
    return !resetBootstrapInputs.empty();
  }

  std::vector<size_t> combinedStateSymbols() const {
    std::vector<size_t> combined = state0Symbols;
    combined.insert(combined.end(), state1Symbols.begin(), state1Symbols.end());
    return combined;
  }
};

}  // namespace KEPLER_FORMAL::SEC
