// Copyright 2024-2026 keplertech.io
// SPDX-License-Identifier: GPL-3.0-only

#pragma once

#include <unordered_map>

#include "kinduction/KInductionProblem.h"

namespace KEPLER_FORMAL::SEC {

class TransitionExprResolver {
 public:
  explicit TransitionExprResolver(const KInductionProblem& problem);

  bool contains(size_t stateSymbol) const;
  BoolExpr* at(size_t stateSymbol) const;

 private:
  const KInductionProblem& problem_;
  std::unordered_map<size_t, BoolExpr*> eagerByStateSymbol_;
};

}  // namespace KEPLER_FORMAL::SEC
