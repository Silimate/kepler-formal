// Copyright 2024-2026 keplertech.io
// SPDX-License-Identifier: GPL-3.0-only

#pragma once

#include <cstddef>
#include <cstdint>
#include <unordered_set>
#include <vector>

#include "kinduction/KInductionProblem.h"

namespace KEPLER_FORMAL::SEC {

struct RegionLiteral {
  // Large Craig proofs contain millions of literals. Bit fields keep each
  // literal in one word instead of padding two booleans around a size_t.
  size_t isState : 1 = false;
  size_t index : (sizeof(size_t) * 8 - 2) = 0;
  size_t positive : 1 = true;
};
static_assert(sizeof(RegionLiteral) == sizeof(size_t));

struct InterpolantRegion {
  enum class Type {
    False,
    True,
    Normal,
  };

  Type type = Type::False;
  size_t auxiliaryCount = 0;
  // Flat clause storage avoids one heap allocation and one vector object per
  // Tseitin clause while preserving the exact interpolant CNF.
  std::vector<RegionLiteral> definitionLiterals;
  std::vector<size_t> definitionClauseEnds;
  RegionLiteral root;
};

enum class CraigImcStatus {
  Equivalent,
  CounterexampleCandidate,
  ConcreteNoProgress,
  BudgetExceeded,
  NoProgress,
};

struct CraigImcGrowthBudget {
  bool enabled = false;
  size_t maxQExpansionPass = 0;
  size_t maxInterpolantClauses = 0;
  size_t maxInterpolantLiterals = 0;
  size_t maxInterpolantAuxiliaries = 0;
  std::int64_t maxImageSolveMilliseconds = 0;
};

struct CraigImcOptions {
  // Large dual-rail IMC may derive transition-proven constants from the
  // bootstrap cube to prune Craig image queries. The environment switch still
  // enables the same path for direct checker experiments.
  bool enableAuxiliaryInvariants = false;
  CraigImcGrowthBudget growthBudget;
};

struct CraigImcResult {
  CraigImcStatus status = CraigImcStatus::NoProgress;
  size_t iterations = 0;
  std::vector<InterpolantRegion> invariantRegions;
  std::unordered_set<size_t> trackedStates;
};

// IMC stores proof interpolants in a compact CNF-like region form. This cleanup
// is intentionally IMC-local: it removes redundant interpolant clauses before
// later Craig reachability iterations re-instantiate them.
InterpolantRegion simplifyCraigInterpolantRegion(InterpolantRegion region);

// Large-state IMC based on proof-derived Craig interpolants. Internal state in
// the two designs remains independent; the only relational clauses retained by
// this checker are clauses emitted by CaDiCaL's UNSAT proof. A SAT result is
// reported with its concrete lookahead so the caller can reconstruct exactly
// that counterexample instead of repeating the complete bounded sweep.
class CraigInterpolatingModelChecker {
 public:
  explicit CraigInterpolatingModelChecker(
      const KInductionProblem& problem,
      const std::vector<InterpolantRegion>* helperInvariantRegions = nullptr,
      const std::unordered_set<size_t>* initialTrackedStates = nullptr,
      CraigImcOptions options = {});

  CraigImcResult run(size_t maxLookahead) const;

 private:
  const KInductionProblem& problem_;
  const std::vector<InterpolantRegion>* helperInvariantRegions_;
  const std::unordered_set<size_t>* initialTrackedStates_;
  CraigImcOptions options_;
};

bool craigInvariantExcludesBad(
    const KInductionProblem& problem,
    const std::unordered_set<size_t>& trackedStates,
    const std::vector<InterpolantRegion>& invariantRegions,
    const std::vector<std::pair<size_t, bool>>& auxiliaryStateInvariants = {});

// Computes the same state projection closure that Craig IMC will discover
// before SAT solving. This is an IMC batching aid only: it follows each
// design's own transition support and never relates internal state across
// designs.
std::unordered_set<size_t> computeCraigImcProjectionClosure(
    const KInductionProblem& problem,
    const std::unordered_set<size_t>& seedSupport);

}  // namespace KEPLER_FORMAL::SEC
