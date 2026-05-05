// Copyright 2024-2026 keplertech.io
// SPDX-License-Identifier: GPL-3.0-only

#include "proof/ProofEngineShared.h"

#include <algorithm>
#include <unordered_set>

#include "common/BoolExprUtils.h"
#include "kinduction/SatEncoding.h"

namespace KEPLER_FORMAL::SEC {

namespace {

BoolExpr* buildEqualityFormula(size_t lhs, size_t rhs) {
  return makeEqualityExpr(BoolExpr::Var(lhs), BoolExpr::Var(rhs));
}

void addComplementedStateRelations(
    SATSolverWrapper& solver,
    const FrameVariableStore& variables,
    const std::vector<std::pair<size_t, size_t>>& complementedStatePairs,
    size_t numFrames) {
  for (size_t frame = 0; frame < numFrames; ++frame) {
    for (const auto& [primarySymbol, complementedSymbol] : complementedStatePairs) {
      addLiteralEquivalence(
          solver,
          variables.getLiteral(complementedSymbol, frame),
          -variables.getLiteral(primarySymbol, frame));
    }
  }
}

std::unordered_map<size_t, BoolExpr*> buildTransitionExprByStateSymbol(
    const KInductionProblem& problem) {
  std::unordered_map<size_t, BoolExpr*> transitionExprByStateSymbol;
  transitionExprByStateSymbol.reserve(
      problem.transitions0.size() + problem.transitions1.size());
  for (const auto& [stateSymbol, expr] : problem.transitions0) {
    transitionExprByStateSymbol.emplace(stateSymbol, expr);
  }
  for (const auto& [stateSymbol, expr] : problem.transitions1) {
    transitionExprByStateSymbol.emplace(stateSymbol, expr);
  }
  return transitionExprByStateSymbol;
}

std::unordered_map<size_t, size_t> buildComplementPrimaryByStateSymbol(
    const KInductionProblem& problem) {
  std::unordered_map<size_t, size_t> primaryByComplement;
  primaryByComplement.reserve(
      problem.complementedStatePairs0.size() +
      problem.complementedStatePairs1.size());
  for (const auto& [primarySymbol, complementedSymbol] :
       problem.complementedStatePairs0) {
    primaryByComplement.emplace(complementedSymbol, primarySymbol);
  }
  for (const auto& [primarySymbol, complementedSymbol] :
       problem.complementedStatePairs1) {
    primaryByComplement.emplace(complementedSymbol, primarySymbol);
  }
  return primaryByComplement;
}

std::unordered_set<size_t> buildCombinedStateSymbolSet(
    const KInductionProblem& problem) {
  std::unordered_set<size_t> stateSymbols;
  stateSymbols.reserve(problem.state0Symbols.size() + problem.state1Symbols.size());
  stateSymbols.insert(problem.state0Symbols.begin(), problem.state0Symbols.end());
  stateSymbols.insert(problem.state1Symbols.begin(), problem.state1Symbols.end());
  return stateSymbols;
}

std::vector<size_t> collectStateSupportSymbols(
    const KInductionProblem& problem,
    BoolExpr* formula) {
  std::vector<size_t> support;
  if (formula == nullptr) {
    return support;  // LCOV_EXCL_LINE
  }

  const auto stateSymbolSet = buildCombinedStateSymbolSet(problem);
  for (const auto symbol : formula->getSupportVars()) {
    if (stateSymbolSet.find(symbol) != stateSymbolSet.end()) {
      support.push_back(symbol);
    }
  }
  std::sort(support.begin(), support.end());
  support.erase(std::unique(support.begin(), support.end()), support.end());
  return support;
}

std::vector<size_t> expandTransitionTargets(
    const KInductionProblem& problem,
    const std::vector<size_t>& requestedTargets,
    const std::unordered_map<size_t, BoolExpr*>& transitionExprByStateSymbol) {
  const auto primaryByComplement = buildComplementPrimaryByStateSymbol(problem);
  std::vector<size_t> targets;
  targets.reserve(requestedTargets.size());

  for (const auto symbol : requestedTargets) {
    if (transitionExprByStateSymbol.find(symbol) !=
        transitionExprByStateSymbol.end()) {
      targets.push_back(symbol);
      continue;
    }
    if (const auto primaryIt = primaryByComplement.find(symbol);  // LCOV_EXCL_LINE
        primaryIt != primaryByComplement.end() &&  // LCOV_EXCL_LINE
        transitionExprByStateSymbol.find(primaryIt->second) !=  // LCOV_EXCL_LINE
            transitionExprByStateSymbol.end()) {  // LCOV_EXCL_LINE
      targets.push_back(primaryIt->second);  // LCOV_EXCL_LINE
    }  // LCOV_EXCL_LINE
  }

  std::sort(targets.begin(), targets.end());
  targets.erase(std::unique(targets.begin(), targets.end()), targets.end());
  return targets;
}

void addTransitionRelationForTargets(
    SATSolverWrapper& solver,
    const FrameVariableStore& variables,
    const KInductionProblem& problem,
    size_t frame,
    const std::vector<size_t>& requestedTargets) {
  const auto transitionExprByStateSymbol =
      buildTransitionExprByStateSymbol(problem);
  const auto encodedTargets = expandTransitionTargets(
      problem, requestedTargets, transitionExprByStateSymbol);

  FrameFormulaEncoder encoder(solver, variables.makeLeafLits(frame));
  for (const auto stateSymbol : encodedTargets) {
    addLiteralEquivalence(
        solver,
        variables.getLiteral(stateSymbol, frame + 1),
        encoder.encode(transitionExprByStateSymbol.at(stateSymbol)));
  }
}

}  // namespace

BoolExpr* buildProofInitFormula(const KInductionProblem& problem) {
  BoolExpr* init = BoolExpr::createTrue();
  bool hasConstraint = false;

  if (problem.resetBootstrapCycles != 0) {
    for (const auto& [symbol, value] : problem.bootstrapStateAssignments) {
      init = BoolExpr::And(
          init, value ? BoolExpr::Var(symbol) : BoolExpr::Not(BoolExpr::Var(symbol)));
      hasConstraint = true;
    }
    for (const auto& [lhsSymbol, rhsSymbol] : problem.bootstrapStateEqualityPairs) {
      init = BoolExpr::And(init, buildEqualityFormula(lhsSymbol, rhsSymbol));
      hasConstraint = true;
    }
  } else {
    if (problem.initialCondition != nullptr) {
      init = BoolExpr::And(init, problem.initialCondition);
      hasConstraint = true;
    }
    for (const auto& [lhsSymbol, rhsSymbol] : problem.initialStateEqualityPairs) {
      init = BoolExpr::And(init, buildEqualityFormula(lhsSymbol, rhsSymbol));
      hasConstraint = true;
    }
  }

  if (!hasConstraint) {
    return nullptr;
  }
  return BoolExpr::simplify(init);
}

size_t nextFreshProofSymbol(const KInductionProblem& problem) {
  size_t nextSymbol = 2;
  for (const auto symbol : problem.allSymbols) {
    nextSymbol = std::max(nextSymbol, symbol + 1);
  }
  return nextSymbol;
}

std::unordered_map<size_t, size_t> allocateFreshProofSymbols(
    const std::vector<size_t>& originalSymbols,
    size_t& nextSymbol) {
  std::unordered_map<size_t, size_t> symbolMap;
  symbolMap.reserve(originalSymbols.size());
  for (const auto symbol : originalSymbols) {
    symbolMap.emplace(symbol, nextSymbol++);
  }
  return symbolMap;
}

BoolExpr* buildOneStepTransitionFormula(
    const KInductionProblem& problem,
    const std::unordered_map<size_t, size_t>& nextStateSymbols) {
  BoolExpr* transition = BoolExpr::createTrue();
  for (const auto& [stateSymbol, expr] : problem.transitions0) {
    transition = BoolExpr::And(
        transition,
        makeEqualityExpr(BoolExpr::Var(nextStateSymbols.at(stateSymbol)), expr));
  }
  for (const auto& [stateSymbol, expr] : problem.transitions1) {
    transition = BoolExpr::And(
        transition,
        makeEqualityExpr(BoolExpr::Var(nextStateSymbols.at(stateSymbol)), expr));
  }
  for (const auto& [primarySymbol, complementedSymbol] : problem.complementedStatePairs0) {
    transition = BoolExpr::And(
        transition,
        makeEqualityExpr(
            BoolExpr::Var(nextStateSymbols.at(complementedSymbol)),
            BoolExpr::Not(BoolExpr::Var(nextStateSymbols.at(primarySymbol)))));
  }
  for (const auto& [primarySymbol, complementedSymbol] : problem.complementedStatePairs1) {
    transition = BoolExpr::And(
        transition,
        makeEqualityExpr(
            BoolExpr::Var(nextStateSymbols.at(complementedSymbol)),
            BoolExpr::Not(BoolExpr::Var(nextStateSymbols.at(primarySymbol)))));
  }
  return BoolExpr::simplify(transition);
}

BoolExpr* buildCurrentStateLegalityFormula(const KInductionProblem& problem) {
  BoolExpr* legality = BoolExpr::createTrue();
  for (const auto& [primarySymbol, complementedSymbol] : problem.complementedStatePairs0) {
    legality = BoolExpr::And(  // LCOV_EXCL_LINE
        legality,  // LCOV_EXCL_LINE
        makeEqualityExpr(  // LCOV_EXCL_LINE
            BoolExpr::Var(complementedSymbol), BoolExpr::Not(BoolExpr::Var(primarySymbol))));  // LCOV_EXCL_LINE
  }
  for (const auto& [primarySymbol, complementedSymbol] : problem.complementedStatePairs1) {
    legality = BoolExpr::And(
        legality,
        makeEqualityExpr(
            BoolExpr::Var(complementedSymbol), BoolExpr::Not(BoolExpr::Var(primarySymbol))));
  }
  return BoolExpr::simplify(legality);
}

BoolExpr* remapProofFormula(
    BoolExpr* formula,
    const std::unordered_map<size_t, size_t>& symbolMap) {
  std::unordered_map<BoolExpr*, BoolExpr*> memo;
  return remapBoolExprVariables(formula, symbolMap, memo);
}

bool isProofFormulaSatisfiable(
    BoolExpr* formula,
    KEPLER_FORMAL::Config::SolverType solverType) {
  if (formula == nullptr) {
    return false;  // LCOV_EXCL_LINE
  }

  SATSolverWrapper solver(solverType);
  const auto support = formula->getSupportVars();
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
  return solver.solve();
}

bool initialFrontierImplies(
    BoolExpr* initFormula,
    BoolExpr* invariant,
    KEPLER_FORMAL::Config::SolverType solverType) {
  if (initFormula == nullptr || invariant == nullptr) {
    return false;  // LCOV_EXCL_LINE
  }
  return !isProofFormulaSatisfiable(
      BoolExpr::And(initFormula, BoolExpr::Not(invariant)), solverType);
}

BoolExpr* selectValidatedStrengtheningInvariant(
    const KInductionProblem& problem,
    BoolExpr* initFormula,
    KEPLER_FORMAL::Config::SolverType solverType) {
  if (problem.inductionProperty == nullptr || initFormula == nullptr ||
      problem.inductionProperty == problem.property) {
    return nullptr;
  }

  if (!initialFrontierImplies(initFormula, problem.inductionProperty, solverType)) {
    return nullptr;
  }
  return problem.inductionProperty;
}

bool invariantExcludesBadStates(
    const KInductionProblem& problem,
    BoolExpr* invariant,
    KEPLER_FORMAL::Config::SolverType solverType) {
  if (invariant == nullptr || problem.bad == nullptr) {
    return false;  // LCOV_EXCL_LINE
  }
  return !isProofFormulaSatisfiable(
      BoolExpr::And(invariant, problem.bad), solverType);
}

bool isInductiveInvariant(
    const KInductionProblem& problem,
    BoolExpr* invariant,
    KEPLER_FORMAL::Config::SolverType solverType) {
  if (invariant == nullptr) {
    return false;  // LCOV_EXCL_LINE
  }

  SATSolverWrapper solver(solverType);
  FrameVariableStore variables(solver, problem.allSymbols, 2);
  addComplementedStateRelations(solver, variables, problem.complementedStatePairs0, 2);
  addComplementedStateRelations(solver, variables, problem.complementedStatePairs1, 2);
  // Only next-state symbols read by the candidate invariant need transition
  // equations. Encoding every flop transition here made PDR's immediate
  // invariant validation scale like a full-design induction proof even when
  // the candidate touched a small cone.
  addTransitionRelationForTargets(
      solver, variables, problem, 0, collectStateSupportSymbols(problem, invariant));

  FrameFormulaEncoder currentEncoder(solver, variables.makeLeafLits(0));
  FrameFormulaEncoder nextEncoder(solver, variables.makeLeafLits(1));
  solver.addClause({currentEncoder.encode(invariant)});
  solver.addClause({nextEncoder.encode(BoolExpr::Not(invariant))});
  return !solver.solve();
}

}  // namespace KEPLER_FORMAL::SEC
