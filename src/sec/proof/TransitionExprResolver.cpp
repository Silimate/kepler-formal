// Copyright 2024-2026 keplertech.io
// SPDX-License-Identifier: GPL-3.0-only

#include "proof/TransitionExprResolver.h"

#include <stdexcept>
#include <string>

#include "common/BoolExprUtils.h"

namespace KEPLER_FORMAL::SEC {

TransitionExprResolver::TransitionExprResolver(const KInductionProblem& problem)
    : problem_(problem) {
  eagerByStateSymbol_.reserve(
      problem.transitions0.size() + problem.transitions1.size());
  for (const auto& [stateSymbol, expr] : problem.transitions0) {
    eagerByStateSymbol_.emplace(stateSymbol, expr);
  }
  for (const auto& [stateSymbol, expr] : problem.transitions1) {
    eagerByStateSymbol_.emplace(stateSymbol, expr);
  }
}

bool TransitionExprResolver::contains(size_t stateSymbol) const {
  if (eagerByStateSymbol_.find(stateSymbol) != eagerByStateSymbol_.end()) {
    return true;
  }
  return problem_.lazyTransitions != nullptr &&
         problem_.lazyTransitions->sourceByStateSymbol.find(stateSymbol) !=
             problem_.lazyTransitions->sourceByStateSymbol.end();
}

BoolExpr* TransitionExprResolver::at(size_t stateSymbol) const {
  if (const auto eagerIt = eagerByStateSymbol_.find(stateSymbol);
      eagerIt != eagerByStateSymbol_.end()) {
    return eagerIt->second;
  }

  if (problem_.lazyTransitions == nullptr) {
    throw std::runtime_error(
        "Missing transition expression for state symbol " +
        std::to_string(stateSymbol));
  }

  auto& store = *problem_.lazyTransitions;
  if (const auto cachedIt = store.remappedByStateSymbol.find(stateSymbol);
      cachedIt != store.remappedByStateSymbol.end()) {
    return cachedIt->second;
  }

  const auto sourceIt = store.sourceByStateSymbol.find(stateSymbol);
  if (sourceIt == store.sourceByStateSymbol.end()) {
    throw std::runtime_error(
        "Missing lazy transition expression for state symbol " +
        std::to_string(stateSymbol));
  }
  const LazyTransitionSource& source = sourceIt->second;
  if (source.designIndex >= store.localToCombinedByDesign.size()) {
    throw std::runtime_error("Invalid lazy transition design index");  // LCOV_EXCL_LINE
  }

  BoolExpr* remapped = remapBoolExprVariables(
      source.localExpr,
      store.localToCombinedByDesign[source.designIndex],
      store.remapMemoByDesign[source.designIndex]);
  store.remappedByStateSymbol.emplace(stateSymbol, remapped);
  return remapped;
}

}  // namespace KEPLER_FORMAL::SEC
