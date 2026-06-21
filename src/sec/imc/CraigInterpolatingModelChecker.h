// Copyright 2024-2026 keplertech.io
// SPDX-License-Identifier: GPL-3.0-only

#pragma once

#include <cstddef>
#include <unordered_set>
#include <vector>

#include "kinduction/KInductionProblem.h"

namespace KEPLER_FORMAL::SEC {

struct RegionLiteral {
  bool isState = false;
  size_t index = 0;
  bool positive = true;
};

struct InterpolantRegion {
  enum class Type {
    False,
    True,
    Normal,
  };

  Type type = Type::False;
  size_t auxiliaryCount = 0;
  std::vector<std::vector<RegionLiteral>> definitionClauses;
  RegionLiteral root;
};

enum class CraigImcStatus {
  Equivalent,
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
// this checker are clauses emitted by CaDiCaL's UNSAT proof.
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
    const std::vector<InterpolantRegion>& invariantRegions);

}  // namespace KEPLER_FORMAL::SEC
