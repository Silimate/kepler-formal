// Copyright 2024-2026 keplertech.io
// SPDX-License-Identifier: GPL-3.0-only

#include "common/BoolExprUtils.h"

#include <optional>
#include <stdexcept>
#include <vector>

#include "kinduction/SatEncoding.h"

namespace KEPLER_FORMAL::SEC {

namespace {

bool isBoolConst(BoolExpr* expr, bool value) {
  return expr != nullptr && expr->getOp() == Op::VAR &&
         expr->getId() == static_cast<size_t>(value ? 1 : 0);
}

SATSolverWrapper::SolveStatus solveBoolFormulaStatus(
    BoolExpr* formula,
    KEPLER_FORMAL::Config::SolverType solverType,
    std::optional<unsigned> conflictLimit) {
  if (formula == nullptr || isBoolConst(formula, false)) {
    return SATSolverWrapper::SolveStatus::Unsat;
  }
  if (isBoolConst(formula, true)) {
    return SATSolverWrapper::SolveStatus::Sat;
  }

  SATSolverWrapper solver(solverType);
  const auto support = formula->getSupportVars();
  solver.configureForSecLocalBooleanCheck(support.size());
  std::unordered_map<size_t, int> leafLits;
  leafLits.reserve(support.size());
  for (const auto symbol : support) {
    if (symbol < 2) {
      continue;
    }
    leafLits.emplace(symbol, solver.newVar() + 2);
  }

  FrameFormulaEncoder encoder(solver, std::move(leafLits));
  solver.addClause({encoder.encode(formula)});
  if (solverType == KEPLER_FORMAL::Config::SolverType::KISSAT &&
      conflictLimit.has_value()) {
    return solver.solveWithKissatResourceLimits(
        *conflictLimit, *conflictLimit);
  }
  return solver.solveStatus();
}

}  // namespace

BoolExpr* remapBoolExprVariables(
    BoolExpr* root,
    const std::unordered_map<size_t, size_t>& varMap,
    std::unordered_map<BoolExpr*, BoolExpr*>& memo) {
  if (root == nullptr) {
    return nullptr;
  }

  if (auto it = memo.find(root); it != memo.end()) {
    return it->second;
  }

  struct StackFrame {
    BoolExpr* expr = nullptr;
    bool visited = false;
  };

  // Large gate-level SEC formulas are often long, hash-consed DAGs.  A
  // recursive remap is semantically simple, but profiling on BlackParrot-sized
  // designs showed it consuming substantial time and stack depth before the
  // SAT engine even sees a query.  This iterative post-order traversal keeps
  // the same memoized remapping while making the pass linear in the reached
  // DAG and robust for very deep cones.
  std::vector<StackFrame> stack;
  stack.push_back({root, false});
  while (!stack.empty()) {
    const StackFrame current = stack.back();
    stack.pop_back();
    BoolExpr* node = current.expr;
    // LCOV_EXCL_START
    if (node == nullptr || memo.find(node) != memo.end()) {
      continue;
    }
    // LCOV_EXCL_STOP

    if (node->getOp() == Op::VAR) {
      const size_t id = node->getId();
      if (id < 2) {
        memo.emplace(node, BoolExpr::Var(id));
      } else {
        auto it = varMap.find(id);
        if (it == varMap.end()) {
          throw std::runtime_error("Missing BoolExpr remap for variable " +
                                   std::to_string(id));
        }
        memo.emplace(node, BoolExpr::Var(it->second));
      }
      continue;
    }

    if (node->getOp() == Op::NONE) {
      throw std::runtime_error("Unsupported BoolExpr operator in remap");
    }

    if (!current.visited) {
      stack.push_back({node, true});
      if (node->getRight() != nullptr &&
          memo.find(node->getRight()) == memo.end()) {
        stack.push_back({node->getRight(), false});
      }
      if (node->getLeft() != nullptr &&
          memo.find(node->getLeft()) == memo.end()) {
        stack.push_back({node->getLeft(), false});
      }
      continue;
    }

    BoolExpr* remapped = nullptr;
    switch (node->getOp()) {
      case Op::NOT:
        remapped = BoolExpr::Not(memo.at(node->getLeft()));
        break;
      case Op::AND:
        remapped = BoolExpr::And(memo.at(node->getLeft()), memo.at(node->getRight()));
        break;
      case Op::OR:
        remapped = BoolExpr::Or(memo.at(node->getLeft()), memo.at(node->getRight()));
        break;
      case Op::XOR:
        remapped = BoolExpr::Xor(memo.at(node->getLeft()), memo.at(node->getRight()));
        break;
      // LCOV_EXCL_START
      case Op::VAR:
      case Op::NONE:
      default:
        throw std::runtime_error("Unsupported BoolExpr operator in remap");
      // LCOV_EXCL_STOP
    }
    memo.emplace(node, remapped);
  }

  return memo.at(root);
}

BoolExpr* remapBoolExprVariables(
    BoolExpr* root,
    const std::unordered_map<size_t, size_t>& varMap) {
  std::unordered_map<BoolExpr*, BoolExpr*> memo;
  return remapBoolExprVariables(root, varMap, memo);
}

BoolExpr* substituteBoolExprVariables(
    BoolExpr* root,
    const std::unordered_map<size_t, bool>& assignments,
    std::unordered_map<BoolExpr*, BoolExpr*>& memo) {
  if (root == nullptr) {
    return nullptr;
  }

  if (auto it = memo.find(root); it != memo.end()) {
    return it->second;
  }

  BoolExpr* substituted = nullptr;
  switch (root->getOp()) {
    case Op::VAR: {
      const size_t id = root->getId();
      if (id < 2) {
        substituted = BoolExpr::Var(id);
        break;
      }
      auto it = assignments.find(id);
      substituted =
          it == assignments.end() ? BoolExpr::Var(id)
                                  : (it->second ? BoolExpr::createTrue()
                                                : BoolExpr::createFalse());
      break;
    }
    case Op::NOT:
      substituted = BoolExpr::Not(
          substituteBoolExprVariables(root->getLeft(), assignments, memo));
      break;
    case Op::AND:
      substituted = BoolExpr::And(
          substituteBoolExprVariables(root->getLeft(), assignments, memo),
          substituteBoolExprVariables(root->getRight(), assignments, memo));
      break;
    case Op::OR:
      substituted = BoolExpr::Or(
          substituteBoolExprVariables(root->getLeft(), assignments, memo),
          substituteBoolExprVariables(root->getRight(), assignments, memo));
      break;
    case Op::XOR:
      substituted = BoolExpr::Xor(
          substituteBoolExprVariables(root->getLeft(), assignments, memo),
          substituteBoolExprVariables(root->getRight(), assignments, memo));
      break;
    case Op::NONE:
    default:
      throw std::runtime_error("Unsupported BoolExpr operator in substitution");
  }

  memo.emplace(root, substituted);
  return substituted;
}

BoolExpr* substituteBoolExprVariables(
    BoolExpr* root,
    const std::unordered_map<size_t, bool>& assignments) {
  std::unordered_map<BoolExpr*, BoolExpr*> memo;
  return substituteBoolExprVariables(root, assignments, memo);
}

bool isBoolFormulaSatisfiable(
    BoolExpr* formula,
    KEPLER_FORMAL::Config::SolverType solverType) {
  return solveBoolFormulaStatus(formula, solverType, std::nullopt) ==
         SATSolverWrapper::SolveStatus::Sat;
}

bool boolFormulaImplies(
    BoolExpr* assumptions,
    BoolExpr* conclusion,
    KEPLER_FORMAL::Config::SolverType solverType) {
  if (conclusion == nullptr) {
    return false;  // LCOV_EXCL_LINE
  }
  if (isBoolConst(conclusion, true) || isBoolConst(assumptions, false)) {
    return true;
  }

  // Ask SAT for an assignment that satisfies the assumptions and violates the
  // conclusion. If no such assignment exists, the implication is a theorem.
  return !isBoolFormulaSatisfiable(
      BoolExpr::And(assumptions, BoolExpr::Not(conclusion)), solverType);
}

std::optional<bool> boolFormulaImpliesWithConflictLimit(
    BoolExpr* assumptions,
    BoolExpr* conclusion,
    KEPLER_FORMAL::Config::SolverType solverType,
    unsigned conflictLimit) {
  if (conclusion == nullptr) {
    return false;  // LCOV_EXCL_LINE
  }
  if (isBoolConst(conclusion, true) || isBoolConst(assumptions, false)) {
    return true;
  }

  const auto status = solveBoolFormulaStatus(
      BoolExpr::And(assumptions, BoolExpr::Not(conclusion)),
      solverType,
      conflictLimit);
  if (status == SATSolverWrapper::SolveStatus::Unknown) {
    return std::nullopt;
  }
  return status == SATSolverWrapper::SolveStatus::Unsat;
}

}  // namespace KEPLER_FORMAL::SEC
