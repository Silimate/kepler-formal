// Copyright 2024-2026 keplertech.io
// SPDX-License-Identifier: GPL-3.0-only

#include "proof/TransitionExprResolver.h"

#include <memory_resource>
#include <stdexcept>
#include <string>
#include <unordered_set>
#include <vector>

#include "common/BoolExprUtils.h"

namespace KEPLER_FORMAL::SEC {

namespace {

size_t countBoolExprNodes(BoolExpr* formula) {
  if (formula == nullptr) {
    return 0;  // LCOV_EXCL_LINE
  }

  std::unordered_set<BoolExpr*> visited;
  std::vector<BoolExpr*> stack{formula};
  while (!stack.empty()) {
    BoolExpr* node = stack.back();
    stack.pop_back();
    if (!visited.insert(node).second) {
      continue;
    }
    if (node->getRight() != nullptr) {
      stack.push_back(node->getRight());
    }
    if (node->getLeft() != nullptr) {
      stack.push_back(node->getLeft());
    }
  }
  return visited.size();
}

template <typename SymbolMapper>
std::set<size_t> collectBoolExprSupport(BoolExpr* formula,
                                        SymbolMapper&& mapSymbol) {
  std::set<size_t> support;
  if (formula == nullptr) {
    return support;  // LCOV_EXCL_LINE
  }

  // BoolExpr::getSupportVars() is intentionally stateless, but SEC/PDR asks
  // for many transition supports while validating projected candidates. Use an
  // arena-backed visited set here so each support walk avoids thousands of
  // tiny malloc/free operations before the result is stored in the resolver's
  // shared per-transition cache.
  std::pmr::monotonic_buffer_resource visitedResource;
  std::pmr::unordered_set<BoolExpr*> visited{&visitedResource};
  visited.reserve(4096);
  std::vector<BoolExpr*> stack;
  stack.reserve(1024);
  stack.push_back(formula);
  while (!stack.empty()) {
    BoolExpr* node = stack.back();
    stack.pop_back();
    if (node == nullptr || !visited.insert(node).second) {
      continue;
    }
    if (node->getOp() == Op::VAR) {
      support.insert(mapSymbol(node->getId()));
      continue;
    }
    if (node->getRight() != nullptr) {
      stack.push_back(node->getRight());
    }
    if (node->getLeft() != nullptr) {
      stack.push_back(node->getLeft());
    }
  }
  return support;
}

std::set<size_t> identitySupport(BoolExpr* formula) {
  return collectBoolExprSupport(
      formula, [](size_t symbol) { return symbol; });
}

std::set<size_t> remappedSupport(
    BoolExpr* formula,
    const std::unordered_map<size_t, size_t>& symbolMap) {
  return collectBoolExprSupport(formula, [&](size_t localSymbol) {
    if (localSymbol < 2) {
      return localSymbol;
    }
    const auto mappedIt = symbolMap.find(localSymbol);
    if (mappedIt == symbolMap.end()) {
      throw std::runtime_error(
          "Missing BoolExpr support remap for variable " +
          std::to_string(localSymbol));
    }
    return mappedIt->second;
  });
}

}  // namespace

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

const std::set<size_t>& TransitionExprResolver::support(size_t stateSymbol) const {
  if (const auto cachedIt = supportByStateSymbol_.find(stateSymbol);
      cachedIt != supportByStateSymbol_.end()) {
    return cachedIt->second;
  }

  // PDR asks for the same transition cone many times while blocking and
  // generalizing related cubes. BoolExpr::getSupportVars() intentionally walks
  // the DAG without owning a global cache, so the transition resolver keeps a
  // local per-proof cache and avoids rebuilding identical support sets.  For
  // lazy SEC transitions, compute support in the source model's local symbol
  // space and remap only the support IDs; remapping the full Boolean DAG just
  // to know its support dominated BlackParrot batch setup.
  if (const auto eagerIt = eagerByStateSymbol_.find(stateSymbol);
      eagerIt != eagerByStateSymbol_.end()) {
    auto [insertedIt, _] =
        supportByStateSymbol_.emplace(stateSymbol, identitySupport(eagerIt->second));
    return insertedIt->second;
  }

  if (problem_.lazyTransitions == nullptr) {
    throw std::runtime_error(
        "Missing transition expression for state symbol " +
        std::to_string(stateSymbol));
  }
  const auto& store = *problem_.lazyTransitions;
  if (const auto cachedIt = store.supportByStateSymbol.find(stateSymbol);
      cachedIt != store.supportByStateSymbol.end()) {
    return cachedIt->second;
  }
  const auto sourceIt = store.sourceByStateSymbol.find(stateSymbol);
  if (sourceIt == store.sourceByStateSymbol.end()) {
    throw std::runtime_error(
        "Missing lazy transition expression for state symbol " +
        std::to_string(stateSymbol));
  }
  if (sourceIt->second.designIndex >= store.localToCombinedByDesign.size()) {
    throw std::runtime_error("Invalid lazy transition design index");  // LCOV_EXCL_LINE
  }
  auto [insertedIt, _] = store.supportByStateSymbol.emplace(
      stateSymbol,
      remappedSupport(
          sourceIt->second.localExpr,
          store.localToCombinedByDesign[sourceIt->second.designIndex]));
  return insertedIt->second;
}

size_t TransitionExprResolver::nodeCount(size_t stateSymbol) const {
  if (const auto cachedIt = nodeCountByStateSymbol_.find(stateSymbol);
      cachedIt != nodeCountByStateSymbol_.end()) {
    return cachedIt->second;
  }

  // The SAT encoder needs a rough size hint before it starts streaming clauses.
  // Computing this once per transition expression is cheaper than repeatedly
  // letting large PDR predecessor queries grow and rehash their per-query DAG
  // map while the same state transition is encoded over and over.  Lazy
  // transitions can use the source expression's node count because variable
  // remapping preserves the DAG shape.
  BoolExpr* expr = nullptr;
  if (const auto eagerIt = eagerByStateSymbol_.find(stateSymbol);
      eagerIt != eagerByStateSymbol_.end()) {
    expr = eagerIt->second;
  } else if (problem_.lazyTransitions != nullptr) {
    const auto& store = *problem_.lazyTransitions;
    if (const auto cachedIt = store.nodeCountByStateSymbol.find(stateSymbol);
        cachedIt != store.nodeCountByStateSymbol.end()) {
      nodeCountByStateSymbol_.emplace(stateSymbol, cachedIt->second);
      return cachedIt->second;
    }
    const auto sourceIt = store.sourceByStateSymbol.find(stateSymbol);
    if (sourceIt != store.sourceByStateSymbol.end()) {
      expr = sourceIt->second.localExpr;
    }
  }
  if (expr == nullptr) {
    expr = at(stateSymbol);  // LCOV_EXCL_LINE
  }
  const size_t nodeCount = countBoolExprNodes(expr);
  if (problem_.lazyTransitions != nullptr &&
      eagerByStateSymbol_.find(stateSymbol) == eagerByStateSymbol_.end()) {
    problem_.lazyTransitions->nodeCountByStateSymbol.emplace(stateSymbol, nodeCount);
  }
  auto [insertedIt, _] = nodeCountByStateSymbol_.emplace(stateSymbol, nodeCount);
  return insertedIt->second;
}

const std::unordered_set<size_t>& TransitionExprResolver::stateSymbols() const {
  if (stateSymbolsInitialized_) {
    return stateSymbols_;
  }

  // The PDR predecessor loop repeatedly asks whether a symbol belongs to the
  // combined state space. Build that lookup once per proof instead of
  // allocating the same set for every obligation.
  stateSymbols_.reserve(
      problem_.state0Symbols.size() + problem_.state1Symbols.size());
  stateSymbols_.insert(problem_.state0Symbols.begin(), problem_.state0Symbols.end());
  stateSymbols_.insert(problem_.state1Symbols.begin(), problem_.state1Symbols.end());
  stateSymbolsInitialized_ = true;
  return stateSymbols_;
}

const std::unordered_map<size_t, size_t>&
TransitionExprResolver::primaryByComplement() const {
  if (primaryByComplementInitialized_) {
    return primaryByComplement_;
  }

  // Complemented flop outputs do not have independent transition equations;
  // their next value is tied to the primary flop. Cache the reverse lookup so
  // each PDR target expansion does not rescan all complemented pairs.
  primaryByComplement_.reserve(
      problem_.complementedStatePairs0.size() +
      problem_.complementedStatePairs1.size());
  for (const auto& [primarySymbol, complementedSymbol] :
       problem_.complementedStatePairs0) {
    primaryByComplement_.emplace(complementedSymbol, primarySymbol);
  }
  for (const auto& [primarySymbol, complementedSymbol] :
       problem_.complementedStatePairs1) {
    primaryByComplement_.emplace(complementedSymbol, primarySymbol);
  }
  primaryByComplementInitialized_ = true;
  return primaryByComplement_;
}

}  // namespace KEPLER_FORMAL::SEC
