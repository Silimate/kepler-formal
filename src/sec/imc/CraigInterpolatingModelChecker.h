// Copyright 2024-2026 keplertech.io
// SPDX-License-Identifier: GPL-3.0-only

#pragma once

#include <cstddef>
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
  NoProgress,
};

struct CraigImcResult {
  CraigImcStatus status = CraigImcStatus::NoProgress;
  size_t iterations = 0;
  std::vector<InterpolantRegion> invariantRegions;
  std::unordered_set<size_t> trackedStates;
};

// Large-state IMC based on proof-derived Craig interpolants. Internal state in
// the two designs remains independent; the only relational clauses retained by
// this checker are clauses emitted by CaDiCaL's UNSAT proof. A SAT result is
// reported with its concrete lookahead so the caller can reconstruct exactly
// that counterexample instead of repeating the complete bounded sweep.
class CraigInterpolatingModelChecker {
 public:
  explicit CraigInterpolatingModelChecker(const KInductionProblem& problem);

  CraigImcResult run(size_t maxIterations) const;

 private:
  const KInductionProblem& problem_;
};

bool craigInvariantExcludesBad(
    const KInductionProblem& problem,
    const std::unordered_set<size_t>& trackedStates,
    const std::vector<InterpolantRegion>& invariantRegions,
    const std::vector<std::pair<size_t, bool>>& auxiliaryStateInvariants = {});

}  // namespace KEPLER_FORMAL::SEC
