// Copyright 2024-2026 keplertech.io
// SPDX-License-Identifier: GPL-3.0-only

#pragma once

#include <optional>
#include <set>
#include <unordered_map>
#include <vector>

#include "BoolExpr.h"
#include "../../sat/SATSolverWrapper.h"

namespace KEPLER_FORMAL::SEC {

// Frame-local equality assumptions can be encoded more efficiently by making
// both symbolic names point at the same SAT literal in that frame. This is a
// quotienting of an assumption already present in the proof obligation, not a
// structural shortcut: if the equality is not assumed for a frame, no alias is
// installed for that frame.
using FrameSymbolAliases =
    std::vector<std::vector<std::pair<size_t, size_t>>>;

// Owns the SAT literals that represent each symbolic SEC variable in each time
// frame of the unrolled problem.
class FrameVariableStore {
 public:
  FrameVariableStore(SATSolverWrapper& solver,
                     const std::vector<size_t>& symbols,
                     size_t numFrames);
  FrameVariableStore(SATSolverWrapper& solver,
                     const std::vector<size_t>& symbols,
                     size_t numFrames,
                     const FrameSymbolAliases& aliasesByFrame);

  bool hasSymbol(size_t symbol) const;
  int getLiteral(size_t symbol, size_t frame) const;
  std::unordered_map<size_t, int> makeLeafLits(size_t frame) const;
  std::unordered_map<size_t, int> makeLeafLits(
      size_t frame,
      const std::vector<size_t>& symbols) const;
  std::unordered_map<size_t, int> makeLeafLits(
      size_t frame,
      const std::set<size_t>& symbols) const;

 private:
  std::unordered_map<size_t, std::vector<int>> symbolFrameLits_;
};

// Converts a BoolExpr DAG into SAT clauses over one specific frame using a
// Tseitin-style encoding.
class FrameFormulaEncoder {
 public:
  FrameFormulaEncoder(SATSolverWrapper& solver,
                      std::unordered_map<size_t, int> leafLits);

  int encode(BoolExpr* expr);

 private:
  int getConstLit(bool value);
  bool isConstLit(int lit, bool value);

  SATSolverWrapper& solver_;
  std::unordered_map<size_t, int> leafLits_;
  std::unordered_map<BoolExpr*, int> nodeToLit_;
  std::optional<int> trueLit_;
};

void addLiteralEquivalence(SATSolverWrapper& solver, int lhs, int rhs);
int createXorLiteral(SATSolverWrapper& solver, int lhs, int rhs);
// Enforces the noncyclic-path refinement from k-induction by requiring every
// pair of frames to differ in at least one state bit.
void addSimplePathConstraint(SATSolverWrapper& solver,
                             const FrameVariableStore& variables,
                             const std::vector<size_t>& stateSymbols,
                             size_t numFrames);
void addSimplePathConstraint(SATSolverWrapper& solver,
                             const FrameVariableStore& variables,
                             const std::vector<size_t>& stateSymbols,
                             size_t firstFrame,
                             size_t numFrames);

}  // namespace KEPLER_FORMAL::SEC
