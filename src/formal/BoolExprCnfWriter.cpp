// Copyright 2024-2026 keplertech.io
// SPDX-License-Identifier: GPL-3.0-only

#include "BoolExprCnfWriter.h"

#include "BoolExpr.h"

#include <fstream>
#include <stack>
#include <stdexcept>
#include <unordered_set>

namespace KEPLER_FORMAL {

namespace {

struct Frame {
  BoolExpr* expr = nullptr;
  bool visited = false;
  int leftLit = 0;
  int rightLit = 0;
};

}  // namespace

CnfFormula encodeBoolExprToCnf(BoolExpr* root) {
  if (!root) {
    throw std::invalid_argument("encodeBoolExprToCnf: root is null");
  }

  CnfFormula cnf;
  std::unordered_map<BoolExpr*, int> node2lit;
  std::unordered_set<std::string> forcedConstants;

  int nextVar = 0; // DIMACS variables are 1-based.

  auto allocVar = [&]() -> int {
    return ++nextVar;
  };

  auto getOrCreateVar = [&](const std::string& key) -> int {
    auto it = cnf.varNameToDimacs.find(key);
    if (it != cnf.varNameToDimacs.end()) {
      return it->second;
    }
    int v = allocVar();
    cnf.varNameToDimacs.emplace(key, v);
    return v;
  };

  auto constVar = [&](bool value) -> int {
    const std::string key = value ? "$__CONST_TRUE__" : "$__CONST_FALSE__";
    int v = getOrCreateVar(key);
    if (forcedConstants.insert(key).second) {
      cnf.clauses.push_back({value ? v : -v});
    }
    return v;
  };

  std::stack<Frame> stk;
  stk.push({root, false, 0, 0});

  while (!stk.empty()) {
    Frame& fr = stk.top();
    BoolExpr* e = fr.expr;

    if (node2lit.count(e)) {
      stk.pop();
      continue;
    }

    if (!fr.visited && e->getOp() == Op::VAR) {
      int lit = 0;
      if (e->getId() == 0) {
        lit = constVar(false);
      } else if (e->getId() == 1) {
        lit = constVar(true);
      } else {
        lit = getOrCreateVar(e->getName());
      }
      node2lit[e] = lit;
      stk.pop();
      continue;
    }

    if (!fr.visited) {
      fr.visited = true;
      if (e->getRight()) {
        stk.push({e->getRight(), false, 0, 0});
      }
      if (e->getLeft()) {
        stk.push({e->getLeft(), false, 0, 0});
      }
      continue;
    }

    if (e->getLeft()) {
      fr.leftLit = node2lit[e->getLeft()];
    }
    if (e->getRight()) {
      fr.rightLit = node2lit[e->getRight()];
    }

    int v = allocVar();
    int lit = v;
    node2lit[e] = lit;

    switch (e->getOp()) {
      case Op::NOT:
        cnf.clauses.push_back({-lit, -fr.leftLit});
        cnf.clauses.push_back({ lit,  fr.leftLit});
        break;

      case Op::AND:
        cnf.clauses.push_back({-lit, fr.leftLit});
        cnf.clauses.push_back({-lit, fr.rightLit});
        cnf.clauses.push_back({ lit, -fr.leftLit, -fr.rightLit});
        break;

      case Op::OR:
        cnf.clauses.push_back({-fr.leftLit,  lit});
        cnf.clauses.push_back({-fr.rightLit, lit});
        cnf.clauses.push_back({-lit,         fr.leftLit, fr.rightLit});
        break;

      case Op::XOR:
        cnf.clauses.push_back({-lit, -fr.leftLit, -fr.rightLit});
        cnf.clauses.push_back({-lit,  fr.leftLit,  fr.rightLit});
        cnf.clauses.push_back({ lit, -fr.leftLit,  fr.rightLit});
        cnf.clauses.push_back({ lit,  fr.leftLit, -fr.rightLit});
        break;

      case Op::VAR:
      case Op::NONE:
      default:
        throw std::runtime_error("encodeBoolExprToCnf: unsupported op");
    }

    stk.pop();
  }

  cnf.numVars = nextVar;
  cnf.rootLit = node2lit[root];
  return cnf;
}

bool writeDimacsCnf(const CnfFormula& cnf, std::ostream& out, bool assertRoot) {
  if (!out.good()) {
    return false;
  }
  int extraClauses = assertRoot ? 1 : 0;
  out << "p cnf " << cnf.numVars << " " << (cnf.clauses.size() + extraClauses) << "\n";
  for (const auto& clause : cnf.clauses) {
    for (int lit : clause) {
      out << lit << " ";
    }
    out << "0\n";
  }
  if (assertRoot) {
    out << cnf.rootLit << " 0\n";
  }
  return out.good();
}

bool dumpDimacsCnf(const CnfFormula& cnf, const std::string& path, bool assertRoot) {
  std::ofstream out(path);
  if (!out.is_open()) {
    return false;
  }
  return writeDimacsCnf(cnf, out, assertRoot);
}

bool dumpBoolExprToDimacs(BoolExpr* root, const std::string& path, bool assertRoot) {
  CnfFormula cnf = encodeBoolExprToCnf(root);
  return dumpDimacsCnf(cnf, path, assertRoot);
}

}  // namespace KEPLER_FORMAL
