// Copyright 2024-2026 keplertech.io
// SPDX-License-Identifier: GPL-3.0-only

#include "kinduction/SatEncoding.h"

#include <algorithm>
#include <stdexcept>

namespace KEPLER_FORMAL::SEC {

namespace {

constexpr size_t kMaxSolverTseitinReserveHint = 65536;
constexpr size_t kLargeFormulaReserveLeafMultiplier = 64;

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
      // LCOV_EXCL_START
      return;  // LCOV_EXCL_LINE
      // LCOV_EXCL_STOP
    }
    const size_t lhsRoot = find(lhs);
    const size_t rhsRoot = find(rhs);
    if (lhsRoot == rhsRoot) {
      // LCOV_EXCL_START
      return;  // LCOV_EXCL_LINE
      // LCOV_EXCL_STOP
    }
    const size_t representative = std::min(lhsRoot, rhsRoot);
    const size_t merged = std::max(lhsRoot, rhsRoot);
    parent_[merged] = representative;
  }

  size_t find(size_t symbol) {
    auto it = parent_.find(symbol);
    if (it == parent_.end()) {
      // LCOV_EXCL_START
      throw std::runtime_error("Missing frame alias symbol " +  // LCOV_EXCL_LINE
                               std::to_string(symbol));  // LCOV_EXCL_LINE
                               // LCOV_EXCL_STOP
    }
    if (it->second != symbol) {
      it->second = find(it->second);
    }
    return it->second;
  // LCOV_EXCL_START
  }  // LCOV_EXCL_LINE
  // LCOV_EXCL_STOP

 private:
  std::unordered_map<size_t, size_t> parent_;
};

FrameSymbolAliases emptyAliases() {
  return {};
}

}  // namespace

// LCOV_EXCL_START
FrameVariableStore::FrameVariableStore(SATSolverWrapper& solver,
                                       const std::vector<size_t>& symbols,
                                       size_t numFrames)
    : FrameVariableStore(solver, symbols, numFrames, emptyAliases()) {}
// LCOV_EXCL_STOP

FrameVariableStore::FrameVariableStore(SATSolverWrapper& solver,
                                       const std::vector<size_t>& symbols,
                                       size_t numFrames,
                                       const FrameSymbolAliases& aliasesByFrame) {
  // The store knows the frame-variable count before any clause is emitted.
  // Reserving it up front is especially helpful for PDR, which creates many
  // small solvers and otherwise makes Kissat repeatedly grow its variable
  // arrays while transition Tseitin clauses are being streamed in.
  solver.reserveVars(symbols.size() * numFrames);

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
      // LCOV_EXCL_START
      throw std::runtime_error("Missing frame variable for symbol " +  // LCOV_EXCL_LINE
                               std::to_string(symbol));  // LCOV_EXCL_LINE
                               // LCOV_EXCL_STOP
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
      // LCOV_EXCL_START
      throw std::runtime_error("Missing frame variable for symbol " +  // LCOV_EXCL_LINE
                               std::to_string(symbol));  // LCOV_EXCL_LINE
                               // LCOV_EXCL_STOP
    }
    leafLits.emplace(symbol, it->second[frame]);
  }
  return leafLits;
}

// LCOV_EXCL_START
FrameFormulaEncoder::FrameFormulaEncoder(  // LCOV_EXCL_LINE
    SATSolverWrapper& solver,
    std::unordered_map<size_t, int> leafLits)
    : FrameFormulaEncoder(solver, std::move(leafLits), false, 0) {}
// LCOV_EXCL_STOP

// LCOV_EXCL_START
// LCOV_DISABLED_START
FrameFormulaEncoder::FrameFormulaEncoder(
// LCOV_DISABLED_STOP
    SATSolverWrapper& solver,
    std::unordered_map<size_t, int> leafLits,
    size_t expectedNodeHint)
    // LCOV_DISABLED_START
    : FrameFormulaEncoder(solver, std::move(leafLits), false, expectedNodeHint) {}
    // LCOV_DISABLED_STOP
// LCOV_EXCL_STOP

// LCOV_EXCL_START
// LCOV_DISABLED_START
FrameFormulaEncoder::FrameFormulaEncoder(
// LCOV_DISABLED_STOP
    SATSolverWrapper& solver,
    std::unordered_map<size_t, int> leafLits,
    bool createMissingLeaves)
    // LCOV_DISABLED_START
    : FrameFormulaEncoder(solver, std::move(leafLits), createMissingLeaves, 0) {}
    // LCOV_DISABLED_STOP
// LCOV_EXCL_STOP

FrameFormulaEncoder::FrameFormulaEncoder(  // LCOV_EXCL_LINE
    SATSolverWrapper& solver,
    std::unordered_map<size_t, int> leafLits,
    bool createMissingLeaves,
    size_t expectedNodeHint)
    : FrameFormulaEncoder(
          solver, std::move(leafLits), nullptr, createMissingLeaves,
          expectedNodeHint) {}

FrameFormulaEncoder::FrameFormulaEncoder(
    SATSolverWrapper& solver,
    std::unordered_map<size_t, int> leafLits,
    const std::unordered_map<size_t, size_t>* symbolMap,
    bool createMissingLeaves,
    size_t expectedNodeHint)
    : solver_(solver),
      leafLits_(std::move(leafLits)),
      symbolMap_(symbolMap),
      createMissingLeaves_(createMissingLeaves),
      expectedNodeHint_(expectedNodeHint),
      nodeArena_(nodeArenaBuffer_.data(), nodeArenaBuffer_.size()),
      nodeToLit_(&nodeArena_) {
  reserveNodeCache();
}

const std::unordered_map<size_t, int>& FrameFormulaEncoder::leafLits() const {
  return leafLits_;
}

size_t FrameFormulaEncoder::mappedSymbol(size_t symbol) const {
  if (symbolMap_ == nullptr || symbol < 2) {
    return symbol;
  }
  // LCOV_EXCL_START
  const auto mappedIt = symbolMap_->find(symbol);  // LCOV_EXCL_LINE
  if (mappedIt == symbolMap_->end()) {  // LCOV_EXCL_LINE
    throw std::runtime_error(  // LCOV_EXCL_LINE
        "Missing frame encoder symbol remap for variable " +  // LCOV_EXCL_LINE
        std::to_string(symbol));  // LCOV_EXCL_LINE
        // LCOV_EXCL_STOP
  }
  // LCOV_EXCL_START
  return mappedIt->second;  // LCOV_EXCL_LINE
  // LCOV_EXCL_STOP
}

void FrameFormulaEncoder::reserveNodeCache() {
  // The support leaf count is a useful lower bound for the number of formula
  // DAG nodes this encoder will touch. Wide reset-prefix and dual-rail
  // transition encodings share many leaves but still create much larger DAGs,
  // so reserve generously up front and keep small unit-test encoders compact.
  size_t expectedNodes =
      leafLits_.size() < 80
          ? 256
          : leafLits_.size() * kLargeFormulaReserveLeafMultiplier;
  if (expectedNodeHint_ != 0) {
    // PDR often encodes deep transition cones with a relatively small leaf
    // support.  When the caller already knows the DAG size, reserve for that
    // shape up front so the monotonic per-query arena does not accumulate old
    // bucket arrays through repeated unordered_map rehashes.
    const size_t hintedNodes =
        expectedNodeHint_ + std::max(expectedNodeHint_ / 8, static_cast<size_t>(256));
    expectedNodes = std::max(expectedNodes, hintedNodes);
  }
  nodeToLit_.reserve(expectedNodes);
  nodeMapReservedEntries_ = expectedNodes;
  // Do not mirror this full DAG estimate into Kissat.  A PDR predecessor query
  // creates a fresh solver for one local cube, and Kissat's reserve call zeros
  // several internal arrays up to the requested variable count.  On wide ASIC
  // transition cones the estimate can be millions of nodes, so eager solver
  // reservation spent more time clearing memory than proving the query.
  //
  // Still give Kissat a bounded Tseitin head start.  BlackParrot PDR profiles
  // showed the opposite extreme after removing the full reserve: the encoder
  // spent most of its time growing Kissat vectors one variable at a time while
  // streaming a large-but-local transition cone.  Capping the hint preserves
  // the memory fix while avoiding the hottest incremental-growth path.
  solver_.reserveAdditionalVars(
      std::min(expectedNodes, kMaxSolverTseitinReserveHint));
}

void FrameFormulaEncoder::cacheEncodedLiteral(BoolExpr* node, int lit) {
  const size_t desiredEntries = nodeToLit_.size() + 1;
  if (desiredEntries > nodeMapReservedEntries_) {
    // Grow the encoder DAG cache geometrically. This keeps large memory
    // transition encodings from rehashing on every small increment while also
    // avoiding a separate full-DAG prepass before every PDR target.
    // LCOV_EXCL_START
    nodeMapReservedEntries_ =  // LCOV_EXCL_LINE
        desiredEntries +  // LCOV_EXCL_LINE
        std::max(desiredEntries / 2, static_cast<size_t>(4096));  // LCOV_EXCL_LINE
    nodeToLit_.reserve(nodeMapReservedEntries_);  // LCOV_EXCL_LINE
  }  // LCOV_EXCL_LINE
  // LCOV_EXCL_STOP
  nodeToLit_.emplace(node, lit);
}

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
  std::vector<StackFrame> stack;
  stack.reserve(256);
  stack.push_back({expr, false});

  while (!stack.empty()) {
    auto current = stack.back();
    stack.pop_back();
    BoolExpr* node = current.expr;

    if (nodeToLit_.find(node) != nodeToLit_.end()) {
      continue;
    }

    if (node->getOp() == Op::VAR) {
      if (node->getId() == 0) {
        cacheEncodedLiteral(node, getConstLit(false));
      } else if (node->getId() == 1) {
        cacheEncodedLiteral(node, getConstLit(true));
      } else {
        const size_t symbol = mappedSymbol(node->getId());
        auto it = leafLits_.find(symbol);
        if (it == leafLits_.end()) {
          if (!createMissingLeaves_) {
            throw std::runtime_error("Missing leaf literal for symbol " +
                                     std::to_string(symbol));
          }
          it = leafLits_.emplace(symbol, newSolverLiteral(solver_)).first;
        }
        cacheEncodedLiteral(node, it->second);
      }
      continue;
    }

    if (!current.visited) {
      stack.push_back({node, true});
      if (node->getRight()) {
        stack.push_back({node->getRight(), false});
      }
      if (node->getLeft()) {
        stack.push_back({node->getLeft(), false});
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
          // LCOV_EXCL_START
          lit = leftLit;  // LCOV_EXCL_LINE
          // LCOV_EXCL_STOP
        } else if (isConstLit(leftLit, false)) {
          // LCOV_EXCL_START
          lit = rightLit;  // LCOV_EXCL_LINE
          // LCOV_EXCL_STOP
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
          // LCOV_EXCL_START
          lit = rightLit;  // LCOV_EXCL_LINE
          // LCOV_EXCL_STOP
        } else if (isConstLit(rightLit, false)) {
          // LCOV_EXCL_START
          lit = leftLit;  // LCOV_EXCL_LINE
          // LCOV_EXCL_STOP
        } else if (isConstLit(leftLit, true)) {
          // LCOV_EXCL_START
          lit = -rightLit;  // LCOV_EXCL_LINE
          // LCOV_EXCL_STOP
        } else if (isConstLit(rightLit, true)) {
          // LCOV_EXCL_START
          lit = -leftLit;  // LCOV_EXCL_LINE
        } else {  // LCOV_EXCL_LINE
        // LCOV_EXCL_STOP
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

    cacheEncodedLiteral(node, lit);
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
