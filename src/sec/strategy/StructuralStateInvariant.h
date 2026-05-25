// Copyright 2024-2026 keplertech.io
// SPDX-License-Identifier: GPL-3.0-only

#pragma once

#include <memory_resource>
#include <unordered_map>
#include <utility>

#include "BoolExpr.h"
#include "../../config/Config.h"
#include "common/AlignedSignals.h"
#include "model/SequentialDesignModel.h"

namespace KEPLER_FORMAL::SEC {

using LocalToAbstractVarMap = std::unordered_map<size_t, size_t>;

struct AbstractExprPairHash {
  size_t operator()(const std::pair<BoolExpr*, BoolExpr*>& pair) const noexcept {
    size_t seed = std::hash<const void*>()(pair.first);
    seed ^= std::hash<const void*>()(pair.second) + 0x9e3779b9 +
            (seed << 6) + (seed >> 2);
    return seed;
  }
};

using AbstractExprPairMemo =
    std::pmr::unordered_map<std::pair<BoolExpr*, BoolExpr*>, bool, AbstractExprPairHash>;

// Rewrites each design into a shared abstract symbol space where matched SEC
// inputs and already-correlated state bits use the same variable IDs. This is
// the common base used by the structural matcher and by later proof
// strengtheners that need naming-independent comparisons.
std::pair<LocalToAbstractVarMap, LocalToAbstractVarMap> buildAbstractTransitionMaps(
    const SequentialDesignModel& model0,
    const SequentialDesignModel& model1,
    const AlignedSignals& alignedInputs,
    const AlignedSignals& alignedStates);

// Checks whether two BoolExpr transition fragments are structurally identical
// after remapping each design into the shared abstract symbol space.
bool areEquivalentUnderAbstractMaps(
    BoolExpr* expr0,
    BoolExpr* expr1,
    const LocalToAbstractVarMap& abstractMap0,
    const LocalToAbstractVarMap& abstractMap1);

// Same comparison, but with caller-owned memoization. Reset/bootstrap
// strengthening may compare hundreds of thousands of related next-state
// formulas under one abstract map; sharing the memo lets common sub-DAGs pay
// for the structural comparison once.
bool areEquivalentUnderAbstractMaps(
    BoolExpr* expr0,
    BoolExpr* expr1,
    const LocalToAbstractVarMap& abstractMap0,
    const LocalToAbstractVarMap& abstractMap1,
    AbstractExprPairMemo& memo);

// Matches state bits by a fixed point over their transition structure instead
// of by display names. This keeps the invariant reusable for renamed designs.
AlignedSignals inferStructurallyEquivalentStatePairs(
    const SequentialDesignModel& model0,
    const SequentialDesignModel& model1,
    const AlignedSignals& alignedInputs,
    const AlignedSignals& alignedOutputs,
    KEPLER_FORMAL::Config::SolverType solverType =
        KEPLER_FORMAL::Config::getSolverType());

// Uses only the aligned top-observed output cones to propose state pairs for
// later reset-bootstrap validation. These pairs are not inductive facts by
// themselves; callers must prove them at the reset frontier before assuming
// them in a proof problem.
AlignedSignals inferStructurallyEquivalentOutputConeStatePairs(
    const SequentialDesignModel& model0,
    const SequentialDesignModel& model1,
    const AlignedSignals& alignedInputs,
    const AlignedSignals& alignedOutputs,
    KEPLER_FORMAL::Config::SolverType solverType =
        KEPLER_FORMAL::Config::getSolverType());

AlignedSignals inferStructurallyEquivalentStatePairs(
    const SequentialDesignModel& model0,
    const SequentialDesignModel& model1,
    const AlignedSignals& alignedInputs,
    KEPLER_FORMAL::Config::SolverType solverType =
        KEPLER_FORMAL::Config::getSolverType());

}  // namespace KEPLER_FORMAL::SEC
