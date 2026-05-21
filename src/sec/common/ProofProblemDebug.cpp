// Copyright 2024-2026 keplertech.io
// SPDX-License-Identifier: GPL-3.0-only

#include "common/ProofProblemDebug.h"

#include <sstream>
#include <unordered_map>

#include "BoolExpr.h"
#include "proof/ProofEngineShared.h"

namespace KEPLER_FORMAL::SEC {

namespace {

std::string formatProofSymbol(size_t symbol) {
  if (symbol == 0) {
    return "FALSE";  // LCOV_EXCL_LINE
  }
  if (symbol == 1) {
    return "TRUE";  // LCOV_EXCL_LINE
  }
  return "x" + std::to_string(symbol);
}

const char* formatBoolOpForDebug(KEPLER_FORMAL::Op op) {
  switch (op) {
    case KEPLER_FORMAL::Op::AND:
      return "AND";
    case KEPLER_FORMAL::Op::OR:
      return "OR";  // LCOV_EXCL_LINE
    case KEPLER_FORMAL::Op::XOR:
      return "XOR";
    default:
      return "?";  // LCOV_EXCL_LINE
  }
}

void appendBoolExprForDebug(std::ostringstream& oss, const BoolExpr* expr) {
  if (expr == nullptr) {
    oss << "<null>";
    return;
  }

  switch (expr->getOp()) {
    case KEPLER_FORMAL::Op::VAR:
      oss << expr->getName();
      return;
    case KEPLER_FORMAL::Op::NOT:
      oss << "~";
      if (expr->getLeft()->getOp() != KEPLER_FORMAL::Op::VAR) {
        oss << "(";
      }
      appendBoolExprForDebug(oss, expr->getLeft());
      if (expr->getLeft()->getOp() != KEPLER_FORMAL::Op::VAR) {
        oss << ")";
      }
      return;
    case KEPLER_FORMAL::Op::AND:
    case KEPLER_FORMAL::Op::OR:
    case KEPLER_FORMAL::Op::XOR:
      if (expr->getLeft()->getOp() != KEPLER_FORMAL::Op::VAR) {
        oss << "(";
      }
      appendBoolExprForDebug(oss, expr->getLeft());
      if (expr->getLeft()->getOp() != KEPLER_FORMAL::Op::VAR) {
        oss << ")";
      }
      oss << " " << formatBoolOpForDebug(expr->getOp()) << " ";
      if (expr->getRight()->getOp() != KEPLER_FORMAL::Op::VAR) {
        oss << "(";
      }
      appendBoolExprForDebug(oss, expr->getRight());
      if (expr->getRight()->getOp() != KEPLER_FORMAL::Op::VAR) {
        oss << ")";
      }
      return;
    default:
      oss << "<invalid>";  // LCOV_EXCL_LINE
      return;  // LCOV_EXCL_LINE
  }
}

std::string formatBoolExprForDebug(BoolExpr* expr) {
  std::ostringstream oss;
  appendBoolExprForDebug(oss, expr);
  return oss.str();
}

std::string formatSymbolVector(const std::vector<size_t>& symbols) {
  std::ostringstream oss;
  oss << "[";
  for (size_t i = 0; i < symbols.size(); ++i) {
    if (i != 0) {
      oss << ", ";
    }
    oss << formatProofSymbol(symbols[i]);
  }
  oss << "]";
  return oss.str();
}

std::string formatEqualityPairs(const std::vector<std::pair<size_t, size_t>>& pairs) {
  std::ostringstream oss;
  oss << "[";
  for (size_t i = 0; i < pairs.size(); ++i) {
    if (i != 0) {
      oss << ", ";  // LCOV_EXCL_LINE
    }  // LCOV_EXCL_LINE
    oss << formatProofSymbol(pairs[i].first) << "=" << formatProofSymbol(pairs[i].second);
  }
  oss << "]";
  return oss.str();
}

std::string formatAssignedSymbols(const std::vector<std::pair<size_t, bool>>& assignments) {
  std::ostringstream oss;
  oss << "[";
  for (size_t i = 0; i < assignments.size(); ++i) {
    if (i != 0) {  // LCOV_EXCL_LINE
      oss << ", ";  // LCOV_EXCL_LINE
    }  // LCOV_EXCL_LINE
    oss << formatProofSymbol(assignments[i].first) << "=" << (assignments[i].second ? "1" : "0");  // LCOV_EXCL_LINE
  }  // LCOV_EXCL_LINE
  oss << "]";
  return oss.str();
}

std::string formatTransitionList(
    const std::vector<std::pair<size_t, BoolExpr*>>& transitions) {
  std::ostringstream oss;
  for (const auto& [stateSymbol, expr] : transitions) {
    oss << "    " << formatProofSymbol(stateSymbol) << "' = "
        << formatBoolExprForDebug(expr) << "\n";
  }
  return oss.str();
}

std::string formatNextStateSymbolMap(
    const std::vector<size_t>& currentSymbols,
    const std::unordered_map<size_t, size_t>& nextStateSymbols) {
  std::ostringstream oss;
  oss << "[";
  for (size_t i = 0; i < currentSymbols.size(); ++i) {
    if (i != 0) {
      oss << ", ";
    }
    const auto current = currentSymbols[i];
    oss << formatProofSymbol(current) << "->"
        << formatProofSymbol(nextStateSymbols.at(current));
  }
  oss << "]";
  return oss.str();
}

}  // namespace

std::string formatKInductionProblemForDebug(const KInductionProblem& problem) {
  std::ostringstream oss;
  oss << "description: "
      << (problem.description.empty() ? "<none>" : problem.description) << "\n";
  oss << "input_symbols: " << formatSymbolVector(problem.inputSymbols) << "\n";
  oss << "state0_symbols: " << formatSymbolVector(problem.state0Symbols) << "\n";
  oss << "state1_symbols: " << formatSymbolVector(problem.state1Symbols) << "\n";
  oss << "all_symbols: " << formatSymbolVector(problem.allSymbols) << "\n";
  oss << "reset_bootstrap_cycles: " << problem.resetBootstrapCycles << "\n";
  oss << "reset_bootstrap_inputs: "
      << formatAssignedSymbols(problem.resetBootstrapInputs) << "\n";
  oss << "initial_state_equalities: "
      << formatEqualityPairs(problem.initialStateEqualityPairs) << "\n";
  oss << "bootstrap_state_assignments: "
      << formatAssignedSymbols(problem.bootstrapStateAssignments) << "\n";
  oss << "bootstrap_state_equalities: "
      << formatEqualityPairs(problem.bootstrapStateEqualityPairs) << "\n";
  oss << "inductive_state_equalities: "
      << formatEqualityPairs(problem.inductiveStateEqualityPairs) << "\n";
  oss << "complemented_state_pairs0: "
      << formatEqualityPairs(problem.complementedStatePairs0) << "\n";
  oss << "complemented_state_pairs1: "
      << formatEqualityPairs(problem.complementedStatePairs1) << "\n";
  oss << "initial_condition: " << formatBoolExprForDebug(problem.initialCondition) << "\n";
  oss << "init_formula: " << formatBoolExprForDebug(buildProofInitFormula(problem)) << "\n";
  oss << "property: " << formatBoolExprForDebug(problem.property) << "\n";
  oss << "bad: " << formatBoolExprForDebug(problem.bad) << "\n";
  oss << "induction_property: " << formatBoolExprForDebug(problem.inductionProperty) << "\n";
  oss << "induction_bad: " << formatBoolExprForDebug(problem.inductionBad) << "\n";
  oss << "legality_formula: "
      << formatBoolExprForDebug(buildCurrentStateLegalityFormula(problem)) << "\n";

  size_t nextSymbol = nextFreshProofSymbol(problem);
  const auto combinedStateSymbols = problem.combinedStateSymbols();
  const auto nextStateSymbols =
      allocateFreshProofSymbols(combinedStateSymbols, nextSymbol);
  oss << "next_state_symbol_map: "
      << formatNextStateSymbolMap(combinedStateSymbols, nextStateSymbols) << "\n";
  oss << "transition_formula: "
      << formatBoolExprForDebug(buildOneStepTransitionFormula(problem, nextStateSymbols))
      << "\n";
  oss << "transitions0:\n" << formatTransitionList(problem.transitions0);
  oss << "transitions1:\n" << formatTransitionList(problem.transitions1);
  return oss.str();
}

}  // namespace KEPLER_FORMAL::SEC
