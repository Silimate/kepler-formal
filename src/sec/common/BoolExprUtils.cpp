// Copyright 2024-2026 keplertech.io
// SPDX-License-Identifier: GPL-3.0-only

#include "common/BoolExprUtils.h"

#include <stdexcept>

namespace KEPLER_FORMAL::SEC {

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

  BoolExpr* remapped = nullptr;
  switch (root->getOp()) {
    case Op::VAR: {
      const size_t id = root->getId();
      if (id < 2) {
        remapped = BoolExpr::Var(id);
        break;
      }
      auto it = varMap.find(id);
      if (it == varMap.end()) {
        throw std::runtime_error("Missing BoolExpr remap for variable " +
                                 std::to_string(id));
      }
      remapped = BoolExpr::Var(it->second);
      break;
    }
    case Op::NOT:
      remapped = BoolExpr::Not(
          remapBoolExprVariables(root->getLeft(), varMap, memo));
      break;
    case Op::AND:
      remapped = BoolExpr::And(
          remapBoolExprVariables(root->getLeft(), varMap, memo),
          remapBoolExprVariables(root->getRight(), varMap, memo));
      break;
    case Op::OR:
      remapped = BoolExpr::Or(
          remapBoolExprVariables(root->getLeft(), varMap, memo),
          remapBoolExprVariables(root->getRight(), varMap, memo));
      break;
    case Op::XOR:
      remapped = BoolExpr::Xor(
          remapBoolExprVariables(root->getLeft(), varMap, memo),
          remapBoolExprVariables(root->getRight(), varMap, memo));
      break;
    case Op::NONE:
    default:
      throw std::runtime_error("Unsupported BoolExpr operator in remap");
  }

  memo.emplace(root, remapped);
  return remapped;
}

BoolExpr* remapBoolExprVariables(
    BoolExpr* root,
    const std::unordered_map<size_t, size_t>& varMap) {
  std::unordered_map<BoolExpr*, BoolExpr*> memo;
  return remapBoolExprVariables(root, varMap, memo);
}

}  // namespace KEPLER_FORMAL::SEC
