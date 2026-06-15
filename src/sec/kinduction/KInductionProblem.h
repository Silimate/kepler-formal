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
#include "proof/DualRailEncoding.h"

namespace KEPLER_FORMAL::SEC {

enum class LazyTransitionRail {
  Binary,
  DualRailOne,
  DualRailZero,
};

struct DualRailSymbolPair {
  size_t mayBeOne = 0;
  size_t mayBeZero = 0;
};

struct LazyTransitionSource {
  size_t designIndex = 0;
  BoolExpr* localExpr = nullptr;
  LazyTransitionRail rail = LazyTransitionRail::Binary;
};

struct PdrStateEqualitySubsetCacheEntry {
  std::vector<std::pair<size_t, size_t>> inputPairs;
  std::vector<std::pair<size_t, bool>> resetBootstrapInputs;
  size_t resetBootstrapCycles = 0;
  std::vector<std::pair<size_t, bool>> initialStateAssignments;
  std::vector<std::pair<size_t, size_t>> initialStateEqualityPairs;
  std::vector<std::pair<size_t, bool>> bootstrapStateAssignments;
  std::vector<std::pair<size_t, size_t>> bootstrapStateEqualityPairs;
  std::vector<std::pair<size_t, size_t>> selectedPairs;
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
  std::array<std::unordered_map<size_t, DualRailSymbolPair>, 2>
      dualRailStateByLocalSymbolByDesign;
  mutable std::array<std::unordered_map<BoolExpr*, BoolExpr*>, 2> remapMemoByDesign;
  mutable std::array<std::unordered_map<BoolExpr*, DualRailBoolExpr>, 2>
      dualRailRemapMemoByDesign;
  mutable std::unordered_map<size_t, BoolExpr*> remappedByStateSymbol;
  // Output-batched PDR slices share the same transition store. Cache validated
  // state-equality subsets here so split leaves do not re-prove the same
  // transition-preserved relation for every output batch.
  mutable std::vector<PdrStateEqualitySubsetCacheEntry>
      pdrStateEqualitySubsetCache;
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
  // Preserve the top-level SEC output width after batching/slicing. Some PDR
  // heuristics must size themselves by the original property, not by the
  // currently selected one-output leaf.
  size_t originalObservedOutputCount = 0;
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
  // Same-design state equalities that hold in every frame. Dual-rail SEC uses
  // this for Q/QN complemented state outputs, where the structural relation is
  // cross-rail equality rather than Boolean complement on one rail.
  std::vector<std::pair<size_t, size_t>> sameFrameStateEqualityPairs0;
  std::vector<std::pair<size_t, size_t>> sameFrameStateEqualityPairs1;
  std::vector<DualRailSymbolPair> dualRailStatePairs;
  std::vector<BoolExpr*> observedOutputExprs0;
  std::vector<BoolExpr*> observedOutputExprs1;
  std::vector<bool> outputImpliedByInductionCore;
  std::vector<std::string> dualRailOutputSkipReasons;
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
  // Dual-rail SEC has a complete rail-valued boot state, but it still needs
  // the normal reset-bootstrap prefix so reset controls are driven exactly as
  // they are in the binary SEC flow.
  bool usesDualRailStateEncoding = false;
  // Output-batched dual-rail KI proves each output slice independently.  When
  // this flag is set, the slice skips local base checks because the caller will
  // validate the shared full-output base prefix once after all slices prove.
  bool deferBaseCaseChecks = false;
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

  size_t effectiveTotalStateCount() const {
    return totalStateCount != 0 ? totalStateCount
                                : state0Symbols.size() + state1Symbols.size();
  }

  bool hasCompleteBootstrapStateAssignments() const {
    const size_t stateCount = effectiveTotalStateCount();
    return stateCount != 0 && bootstrapStateAssignments.size() >= stateCount;
  }

  bool usesResetBootstrapObservationFrontier() const {
    // Binary SEC cannot compare internal resetless state across designs.  When
    // reset/bootstrap leaves part of the startup state arbitrary, use the same
    // top-observation frontier as incomplete-init SEC instead of reporting an
    // arbitrary post-reset flop value as a cycle-0 counterexample.
    return !usesDualRailStateEncoding && hasSequentialState() &&
           hasResetBootstrap() && resetBootstrapCycles != 0 &&
           property != nullptr && !hasCompleteBootstrapStateAssignments();
  }

  std::vector<size_t> combinedStateSymbols() const {
    std::vector<size_t> combined = state0Symbols;
    combined.insert(combined.end(), state1Symbols.begin(), state1Symbols.end());
    return combined;
  }
};

}  // namespace KEPLER_FORMAL::SEC
