// Copyright 2024-2026 keplertech.io
// SPDX-License-Identifier: GPL-3.0-only

#include "kinduction/SatEncoding.h"

#include <stack>
#include <stdexcept>

namespace KEPLER_FORMAL::SEC {

namespace {

int newSolverLiteral(SATSolverWrapper& solver) {
  // BoolExpr reserves 0/1 for false/true, so fresh SAT literals start above
  // those special ids.
  return solver.newVar() + 2;
}

class FrameAliasUnionFind {
 public:
  explicit FrameAliasUnionFind(const std::vector<size_t>& symbols) {
    parent_.reserve(symbols.size());
    for (const auto symbol : symbols) {
      parent_.emplace(symbol, symbol);
    }
  }

  bool contains(size_t symbol) const {
    return parent_.find(symbol) != parent_.end();
  }

  void unite(size_t lhs, size_t rhs) {
    if (!contains(lhs) || !contains(rhs)) {
      return;
    }
    const size_t lhsRoot = find(lhs);
    const size_t rhsRoot = find(rhs);
    if (lhsRoot == rhsRoot) {
      return;
    }
    const size_t representative = std::min(lhsRoot, rhsRoot);
    const size_t merged = std::max(lhsRoot, rhsRoot);
    parent_[merged] = representative;
  }

  size_t find(size_t symbol) {
    auto it = parent_.find(symbol);
    if (it == parent_.end()) {
      throw std::runtime_error("Missing frame alias symbol " +
                               std::to_string(symbol));
    }
    if (it->second != symbol) {
      it->second = find(it->second);
    }
    return it->second;
  }

 private:
  std::unordered_map<size_t, size_t> parent_;
};

FrameSymbolAliases emptyAliases() {
  return {};
}

}  // namespace

FrameVariableStore::FrameVariableStore(SATSolverWrapper& solver,
                                       const std::vector<size_t>& symbols,
                                       size_t numFrames)
    : FrameVariableStore(solver, symbols, numFrames, emptyAliases()) {}

FrameVariableStore::FrameVariableStore(SATSolverWrapper& solver,
                                       const std::vector<size_t>& symbols,
                                       size_t numFrames,
                                       const FrameSymbolAliases& aliasesByFrame) {
  // Every symbolic SEC variable gets one SAT literal per time frame.
  for (const auto symbol : symbols) {
    symbolFrameLits_[symbol].reserve(numFrames);
  }

  for (size_t frame = 0; frame < numFrames; ++frame) {
    FrameAliasUnionFind aliases(symbols);
    if (frame < aliasesByFrame.size()) {
      for (const auto& [lhs, rhs] : aliasesByFrame[frame]) {
        aliases.unite(lhs, rhs);
      }
    }

    std::unordered_map<size_t, int> litByRepresentative;
    litByRepresentative.reserve(symbols.size());
    for (const auto symbol : symbols) {
      const size_t representative = aliases.find(symbol);
      auto [litIt, inserted] =
          litByRepresentative.emplace(representative, 0);
      if (inserted) {
        litIt->second = newSolverLiteral(solver);
      }
      symbolFrameLits_[symbol].push_back(litIt->second);
    }
  }
}

bool FrameVariableStore::hasSymbol(size_t symbol) const {
  return symbolFrameLits_.find(symbol) != symbolFrameLits_.end();
}

int FrameVariableStore::getLiteral(size_t symbol, size_t frame) const {
  auto it = symbolFrameLits_.find(symbol);
  if (it == symbolFrameLits_.end() || frame >= it->second.size()) {
    throw std::runtime_error("Missing frame variable for symbol " +
                             std::to_string(symbol));
  }
  return it->second[frame];
}

std::unordered_map<size_t, int> FrameVariableStore::makeLeafLits(
    size_t frame) const {
  std::unordered_map<size_t, int> leafLits;
  leafLits.reserve(symbolFrameLits_.size());
  for (const auto& [symbol, frameLits] : symbolFrameLits_) {
    if (frame >= frameLits.size()) {
      throw std::runtime_error("Frame index is out of range");
    }
    leafLits.emplace(symbol, frameLits[frame]);
  }
  return leafLits;
}

std::unordered_map<size_t, int> FrameVariableStore::makeLeafLits(
    size_t frame,
    const std::vector<size_t>& symbols) const {
  // Large SEC instances can have hundreds of thousands of state bits, while a
  // single proof obligation usually touches a much smaller cone. Building a
  // per-formula leaf map keeps the SAT encoder from materializing unused
  // variables for every frame.
  std::unordered_map<size_t, int> leafLits;
  leafLits.reserve(symbols.size());
  for (const auto symbol : symbols) {
    if (symbol < 2) {
      continue;
    }
    auto it = symbolFrameLits_.find(symbol);
    if (it == symbolFrameLits_.end() || frame >= it->second.size()) {
      throw std::runtime_error("Missing frame variable for symbol " +
                               std::to_string(symbol));
    }
    leafLits.emplace(symbol, it->second[frame]);
  }
  return leafLits;
}

std::unordered_map<size_t, int> FrameVariableStore::makeLeafLits(
    size_t frame,
    const std::set<size_t>& symbols) const {
  std::unordered_map<size_t, int> leafLits;
  leafLits.reserve(symbols.size());
  for (const auto symbol : symbols) {
    if (symbol < 2) {
      continue;
    }
    auto it = symbolFrameLits_.find(symbol);
    if (it == symbolFrameLits_.end() || frame >= it->second.size()) {
      throw std::runtime_error("Missing frame variable for symbol " +
                               std::to_string(symbol));
    }
    leafLits.emplace(symbol, it->second[frame]);
  }
  return leafLits;
}

FrameFormulaEncoder::FrameFormulaEncoder(
    SATSolverWrapper& solver,
    std::unordered_map<size_t, int> leafLits)
    : solver_(solver), leafLits_(std::move(leafLits)) {}

int FrameFormulaEncoder::getConstLit(bool value) {
  if (trueLit_.has_value()) {
    return value ? *trueLit_ : -*trueLit_;
  }
  int lit = newSolverLiteral(solver_);
  solver_.addClause({lit});
  trueLit_ = lit;
  return value ? lit : -lit;
}

bool FrameFormulaEncoder::isConstLit(int lit, bool value) {
  return lit == getConstLit(value);
}

int FrameFormulaEncoder::encode(BoolExpr* expr) {
  if (expr == nullptr) {
    throw std::invalid_argument("FrameFormulaEncoder::encode: null expr");
  }

  struct StackFrame {
    BoolExpr* expr = nullptr;
    bool visited = false;
  };

  // Encode iteratively so large BoolExpr DAGs do not rely on recursion depth.
  std::stack<StackFrame> stack;
  stack.push({expr, false});

  while (!stack.empty()) {
    auto current = stack.top();
    stack.pop();
    BoolExpr* node = current.expr;

    if (nodeToLit_.find(node) != nodeToLit_.end()) {
      continue;
    }

    if (node->getOp() == Op::VAR) {
      if (node->getId() == 0) {
        nodeToLit_.emplace(node, getConstLit(false));
      } else if (node->getId() == 1) {
        nodeToLit_.emplace(node, getConstLit(true));
      } else {
        auto it = leafLits_.find(node->getId());
        if (it == leafLits_.end()) {
          throw std::runtime_error("Missing leaf literal for symbol " +
                                   std::to_string(node->getId()));
        }
        nodeToLit_.emplace(node, it->second);
      }
      continue;
    }

    if (!current.visited) {
      stack.push({node, true});
      if (node->getRight()) {
        stack.push({node->getRight(), false});
      }
      if (node->getLeft()) {
        stack.push({node->getLeft(), false});
      }
      continue;
    }

    const int leftLit = node->getLeft() ? nodeToLit_.at(node->getLeft()) : 0;
    const int rightLit = node->getRight() ? nodeToLit_.at(node->getRight()) : 0;
    int lit = 0;

    // Standard Tseitin clauses for the BoolExpr node at this frame.  Before we
    // emit them, apply literal-level simplifications created by frame aliases
    // and constants.  Large SEC proofs intentionally alias state pairs that are
    // assumed equal in a frame; without these reductions, expressions such as
    // (a XOR a) still become full Tseitin cones and dominate CNF construction.
    switch (node->getOp()) {
      case Op::NOT:
        lit = -leftLit;
        break;
      case Op::AND:
        if (leftLit == rightLit || isConstLit(rightLit, true)) {
          lit = leftLit;
        } else if (isConstLit(leftLit, true)) {
          lit = rightLit;
        } else if (leftLit == -rightLit || isConstLit(leftLit, false) ||
                   isConstLit(rightLit, false)) {
          lit = getConstLit(false);
        } else {
          lit = newSolverLiteral(solver_);
          solver_.addClause({-lit, leftLit});
          solver_.addClause({-lit, rightLit});
          solver_.addClause({lit, -leftLit, -rightLit});
        }
        break;
      case Op::OR:
        if (leftLit == rightLit || isConstLit(rightLit, false)) {
          lit = leftLit;
        } else if (isConstLit(leftLit, false)) {
          lit = rightLit;
        } else if (leftLit == -rightLit || isConstLit(leftLit, true) ||
                   isConstLit(rightLit, true)) {
          lit = getConstLit(true);
        } else {
          lit = newSolverLiteral(solver_);
          solver_.addClause({-leftLit, lit});
          solver_.addClause({-rightLit, lit});
          solver_.addClause({-lit, leftLit, rightLit});
        }
        break;
      case Op::XOR:
        if (leftLit == rightLit) {
          lit = getConstLit(false);
        } else if (leftLit == -rightLit) {
          lit = getConstLit(true);
        } else if (isConstLit(leftLit, false)) {
          lit = rightLit;
        } else if (isConstLit(rightLit, false)) {
          lit = leftLit;
        } else if (isConstLit(leftLit, true)) {
          lit = -rightLit;
        } else if (isConstLit(rightLit, true)) {
          lit = -leftLit;
        } else {
          lit = newSolverLiteral(solver_);
          solver_.addClause({-lit, -leftLit, -rightLit});
          solver_.addClause({-lit, leftLit, rightLit});
          solver_.addClause({lit, -leftLit, rightLit});
          solver_.addClause({lit, leftLit, -rightLit});
        }
        break;
      case Op::VAR:
      case Op::NONE:
      default:
        throw std::runtime_error("Unsupported BoolExpr operator in frame encoder");
    }

    nodeToLit_.emplace(node, lit);
  }

  return nodeToLit_.at(expr);
}

void addLiteralEquivalence(SATSolverWrapper& solver, int lhs, int rhs) {
  solver.addClause({-lhs, rhs});
  solver.addClause({lhs, -rhs});
}

int createXorLiteral(SATSolverWrapper& solver, int lhs, int rhs) {
  const int lit = newSolverLiteral(solver);
  solver.addClause({-lit, -lhs, -rhs});
  solver.addClause({-lit, lhs, rhs});
  solver.addClause({lit, -lhs, rhs});
  solver.addClause({lit, lhs, -rhs});
  return lit;
}  // LCOV_EXCL_LINE

void addSimplePathConstraint(SATSolverWrapper& solver,
                             const FrameVariableStore& variables,
                             const std::vector<size_t>& stateSymbols,
                             size_t numFrames) {
  addSimplePathConstraint(solver, variables, stateSymbols, 0, numFrames);
}

void addSimplePathConstraint(SATSolverWrapper& solver,
                             const FrameVariableStore& variables,
                             const std::vector<size_t>& stateSymbols,
                             size_t firstFrame,
                             size_t numFrames) {
  if (stateSymbols.empty()) {
    return;
  }

  // Slide-48 refinement: every pair of frames must differ in at least one
  // state bit, which rules out cyclic paths in the induction step.
  const size_t lastFrame = firstFrame + numFrames;
  for (size_t i = firstFrame; i < lastFrame; ++i) {
    for (size_t j = i + 1; j < lastFrame; ++j) {
      std::vector<int> diffClause;
      diffClause.reserve(stateSymbols.size());
      for (const auto symbol : stateSymbols) {
        diffClause.push_back(createXorLiteral(
            solver,
            variables.getLiteral(symbol, i),
            variables.getLiteral(symbol, j)));
      }
      solver.addClause(diffClause);
    }
  }
}

}  // namespace KEPLER_FORMAL::SEC
