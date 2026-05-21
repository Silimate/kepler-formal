// Copyright 2024-2026 keplertech.io
// SPDX-License-Identifier: GPL-3.0-only

#include "kinduction/InductionStepSolver.h"

#include <algorithm>
#include <unordered_map>
#include <unordered_set>

#include "kinduction/SatEncoding.h"
#include "proof/TransitionExprResolver.h"

namespace KEPLER_FORMAL::SEC {

namespace {

constexpr size_t kMaxSimplePathStateSymbols = 4096;

struct InductionCoi {
  std::vector<std::vector<size_t>> transitionTargetsByFrame;
  std::vector<size_t> relevantStateSymbols;
  std::vector<size_t> solverSymbols;
  std::unordered_set<size_t> solverSymbolSet;
};

std::unordered_set<size_t> buildStateSymbolSet(const KInductionProblem& problem) {
  std::unordered_set<size_t> stateSymbols;
  stateSymbols.reserve(problem.state0Symbols.size() + problem.state1Symbols.size());
  stateSymbols.insert(problem.state0Symbols.begin(), problem.state0Symbols.end());
  stateSymbols.insert(problem.state1Symbols.begin(), problem.state1Symbols.end());
  return stateSymbols;
}

std::unordered_map<size_t, size_t> buildPrimaryByComplementSymbol(
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

std::vector<size_t> sortedSymbols(const std::unordered_set<size_t>& symbols) {
  std::vector<size_t> sorted(symbols.begin(), symbols.end());
  std::sort(sorted.begin(), sorted.end());
  return sorted;
}

void addFormulaStateSupport(BoolExpr* formula,
                            const std::unordered_set<size_t>& stateSymbols,
                            std::unordered_set<size_t>& output) {
  if (formula == nullptr) {
    return;  // LCOV_EXCL_LINE
  }
  for (const auto symbol : formula->getSupportVars()) {
    if (stateSymbols.find(symbol) != stateSymbols.end()) {
      output.insert(symbol);
    }
  }
}

void addFormulaSupport(BoolExpr* formula, std::unordered_set<size_t>& output) {
  if (formula == nullptr) {
    return;  // LCOV_EXCL_LINE
  }
  for (const auto symbol : formula->getSupportVars()) {
    if (symbol >= 2) {
      output.insert(symbol);
    }
  }
}

void addEqualityAliasesForFrame(
    FrameSymbolAliases& aliasesByFrame,
    const std::vector<std::pair<size_t, size_t>>& equalityPairs,
    const std::unordered_set<size_t>& solverSymbols,
    size_t frame) {
  if (frame >= aliasesByFrame.size()) {
    return;  // LCOV_EXCL_LINE
  }
  auto& frameAliases = aliasesByFrame[frame];
  for (const auto& [lhsSymbol, rhsSymbol] : equalityPairs) {
    if (solverSymbols.find(lhsSymbol) == solverSymbols.end() ||
        solverSymbols.find(rhsSymbol) == solverSymbols.end()) {
      continue;  // LCOV_EXCL_LINE
    }
    frameAliases.emplace_back(lhsSymbol, rhsSymbol);
  }
}

FrameSymbolAliases buildInductionFrameAliases(
    const KInductionProblem& problem,
    const InductionCoi& coi,
    size_t numFrames,
    bool aliasInductiveStateEqualities) {
  FrameSymbolAliases aliasesByFrame(numFrames);
  if (!aliasInductiveStateEqualities) {
    return aliasesByFrame;
  }

  // The induction hypothesis assumes the selected state correspondences on
  // frames 0..k-1. Sharing SAT literals for those frame-local equalities gives
  // Kissat the quotient transition system directly while leaving the final bad
  // frame unaliased unless the proof explicitly assumes equality there too.
  for (size_t frame = 0; frame + 1 < numFrames; ++frame) {
    addEqualityAliasesForFrame(
        aliasesByFrame,
        problem.inductiveStateEqualityPairs,
        coi.solverSymbolSet,
        frame);
  }
  return aliasesByFrame;
}

std::vector<size_t> expandTransitionTargets(
    const std::unordered_set<size_t>& requestedTargets,
    const TransitionExprResolver& transitionByState,
    const std::unordered_map<size_t, size_t>& primaryByComplement) {
  std::unordered_set<size_t> expanded;
  expanded.reserve(requestedTargets.size());
  for (const auto symbol : requestedTargets) {
    if (transitionByState.contains(symbol)) {
      expanded.insert(symbol);
      continue;
    }
    if (const auto primaryIt = primaryByComplement.find(symbol);  // LCOV_EXCL_LINE
        primaryIt != primaryByComplement.end() &&  // LCOV_EXCL_LINE
        transitionByState.contains(primaryIt->second)) {  // LCOV_EXCL_LINE
      expanded.insert(primaryIt->second);  // LCOV_EXCL_LINE
    }  // LCOV_EXCL_LINE
  }
  return sortedSymbols(expanded);
}

void addRelevantComplementPartners(
    const std::vector<std::pair<size_t, size_t>>& complementedStatePairs,
    std::unordered_set<size_t>& solverSymbols) {
  for (const auto& [primarySymbol, complementedSymbol] : complementedStatePairs) {
    if (solverSymbols.find(primarySymbol) != solverSymbols.end() ||
        solverSymbols.find(complementedSymbol) != solverSymbols.end()) {  // LCOV_EXCL_LINE
      solverSymbols.insert(primarySymbol);
      solverSymbols.insert(complementedSymbol);
    }
  }
}

InductionCoi buildInductionCoi(const KInductionProblem& problem,
                               BoolExpr* inductionProperty,
                               BoolExpr* inductionBad,
                               bool addExtraInductiveEqualities,
                               size_t k) {
  // Cone-of-influence reduction for the actual k-induction SAT problem:
  // start from the formulas that are asserted at each frame, then walk
  // backwards through only the transition equations needed to define those
  // state bits. Large ASICs can have hundreds of thousands of modeled memory
  // and flop bits; leaving unconstrained, irrelevant bits in the solver makes
  // Kissat spend time deciding variables that cannot affect the proof.
  const auto stateSymbols = buildStateSymbolSet(problem);
  const TransitionExprResolver transitionByState(problem);
  const auto primaryByComplement = buildPrimaryByComplementSymbol(problem);

  std::vector<std::unordered_set<size_t>> requiredStates(k + 1);
  for (size_t frame = 0; frame < k; ++frame) {
    addFormulaStateSupport(inductionProperty, stateSymbols, requiredStates[frame]);
    if (addExtraInductiveEqualities) {
      for (const auto& [lhsSymbol, rhsSymbol] : problem.inductiveStateEqualityPairs) {
        requiredStates[frame].insert(lhsSymbol);
        requiredStates[frame].insert(rhsSymbol);
      }
    }
  }
  addFormulaStateSupport(inductionBad, stateSymbols, requiredStates[k]);

  std::vector<std::vector<size_t>> transitionTargetsByFrame(k);
  for (size_t frame = k; frame > 0; --frame) {
    auto targets = expandTransitionTargets(
        requiredStates[frame],
        transitionByState,
        primaryByComplement);
    transitionTargetsByFrame[frame - 1] = targets;
    for (const auto target : targets) {
      addFormulaStateSupport(
          transitionByState.at(target), stateSymbols, requiredStates[frame - 1]);
    }
  }

  std::unordered_set<size_t> solverSymbols;
  solverSymbols.reserve(1024);
  addFormulaSupport(inductionProperty, solverSymbols);
  addFormulaSupport(inductionBad, solverSymbols);
  if (addExtraInductiveEqualities) {
    for (const auto& [lhsSymbol, rhsSymbol] : problem.inductiveStateEqualityPairs) {
      solverSymbols.insert(lhsSymbol);
      solverSymbols.insert(rhsSymbol);
    }
  }

  std::unordered_set<size_t> relevantStateSymbols;
  for (const auto& frameStates : requiredStates) {
    relevantStateSymbols.insert(frameStates.begin(), frameStates.end());
    solverSymbols.insert(frameStates.begin(), frameStates.end());
  }
  for (const auto& targets : transitionTargetsByFrame) {
    for (const auto target : targets) {
      relevantStateSymbols.insert(target);
      solverSymbols.insert(target);
      addFormulaSupport(transitionByState.at(target), solverSymbols);
    }
  }
  addRelevantComplementPartners(problem.complementedStatePairs0, solverSymbols);
  addRelevantComplementPartners(problem.complementedStatePairs1, solverSymbols);

  InductionCoi coi;
  coi.transitionTargetsByFrame = std::move(transitionTargetsByFrame);
  coi.relevantStateSymbols = sortedSymbols(relevantStateSymbols);
  coi.solverSymbols = sortedSymbols(solverSymbols);
  coi.solverSymbolSet.insert(coi.solverSymbols.begin(), coi.solverSymbols.end());
  return coi;
}

void addComplementedStateRelations(
    SATSolverWrapper& solver,
    const FrameVariableStore& variables,
    const std::vector<std::pair<size_t, size_t>>& complementedStatePairs,
    const std::unordered_set<size_t>& solverSymbols,
    size_t numFrames) {
  for (size_t frame = 0; frame < numFrames; ++frame) {
    for (const auto& [primarySymbol, complementedSymbol] : complementedStatePairs) {
      if (solverSymbols.find(primarySymbol) == solverSymbols.end() ||
          solverSymbols.find(complementedSymbol) == solverSymbols.end()) {
        continue;  // LCOV_EXCL_LINE
      }
      addLiteralEquivalence(
          solver,
          variables.getLiteral(complementedSymbol, frame),
          -variables.getLiteral(primarySymbol, frame));
    }
  }
}

void addTransitionRelation(SATSolverWrapper& solver,
                           const FrameVariableStore& variables,
                           const TransitionExprResolver& transitionByState,
                           const std::vector<size_t>& targets,
                           size_t frame) {
  // The targets of a single frame often share most of their input cone. Keep a
  // frame-local encoder so common BoolExpr nodes are Tseitin-encoded once and
  // reused by every next-state equality in this frame.
  FrameFormulaEncoder encoder(solver, variables.makeLeafLits(frame));
  for (const auto stateSymbol : targets) {
    BoolExpr* expr = transitionByState.at(stateSymbol);
    addLiteralEquivalence(
        solver,
        variables.getLiteral(stateSymbol, frame + 1),
        encoder.encode(expr));
  }
}

void addInductiveStateEqualities(SATSolverWrapper& solver,
                                 const FrameVariableStore& variables,
                                 const KInductionProblem& problem,
                                 const std::unordered_set<size_t>& solverSymbols,
                                 size_t firstFrame,
                                 size_t lastFrame) {
  if (problem.inductiveStateEqualityPairs.empty() || firstFrame > lastFrame) {
    return;
  }

  for (size_t frame = firstFrame; frame <= lastFrame; ++frame) {
    for (const auto& [lhsSymbol, rhsSymbol] : problem.inductiveStateEqualityPairs) {
      if (solverSymbols.find(lhsSymbol) == solverSymbols.end() ||
          solverSymbols.find(rhsSymbol) == solverSymbols.end()) {
        continue;  // LCOV_EXCL_LINE
      }
      const int lhs = variables.getLiteral(lhsSymbol, frame);
      const int rhs = variables.getLiteral(rhsSymbol, frame);
      if (lhs == rhs) {
        continue;
      }
      addLiteralEquivalence(  // LCOV_EXCL_LINE
          solver,  // LCOV_EXCL_LINE
          lhs,  // LCOV_EXCL_LINE
          rhs);  // LCOV_EXCL_LINE
    }
  }
}

}  // namespace

bool provesByInduction(const KInductionProblem& problem,
                       KEPLER_FORMAL::Config::SolverType solverType,
                       size_t k) {
  const bool hasExplicitInductionInvariant = problem.inductionProperty != nullptr;
  BoolExpr* inductionProperty =
      hasExplicitInductionInvariant ? problem.inductionProperty : problem.property;
  BoolExpr* inductionBad =
      problem.inductionBad != nullptr ? problem.inductionBad : problem.bad;
  const bool addExtraInductiveEqualities = !hasExplicitInductionInvariant;
  const bool aliasInductiveStateEqualities =
      addExtraInductiveEqualities ||
      problem.inductionPropertyAssumesInductiveStateEqualities;
  const InductionCoi coi = buildInductionCoi(
      problem,
      inductionProperty,
      inductionBad,
      addExtraInductiveEqualities,
      k);
  const TransitionExprResolver transitionByState(problem);
  const FrameSymbolAliases aliasesByFrame = buildInductionFrameAliases(
      problem, coi, k + 1, aliasInductiveStateEqualities);

  SATSolverWrapper solver(solverType);
  solver.configureForSecConeProof(coi.solverSymbols.size());
  FrameVariableStore variables(solver, coi.solverSymbols, k + 1, aliasesByFrame);
  addComplementedStateRelations(
      solver, variables, problem.complementedStatePairs0, coi.solverSymbolSet, k + 1);
  addComplementedStateRelations(
      solver, variables, problem.complementedStatePairs1, coi.solverSymbolSet, k + 1);

  for (size_t frame = 0; frame < k; ++frame) {
    addTransitionRelation(
        solver, variables, transitionByState, coi.transitionTargetsByFrame[frame], frame);
  }

  for (size_t frame = 0; frame < k; ++frame) {
    FrameFormulaEncoder encoder(
        solver, variables.makeLeafLits(frame, inductionProperty->getSupportVars()));
    solver.addClause({encoder.encode(inductionProperty)});
  }
  if (addExtraInductiveEqualities && k > 0) {
    addInductiveStateEqualities(solver, variables, problem, coi.solverSymbolSet, 0, k - 1);
  }

  if (coi.relevantStateSymbols.size() <= kMaxSimplePathStateSymbols) {
    // The simple-path refinement is a completeness aid, not a soundness
    // requirement for classic k-induction. On large gate-level SEC problems it
    // creates one XOR per state bit per frame-pair, which can dominate the SAT
    // instance and drown the actual proof. Keep it for small pedagogical/unit
    // cases where it helps convergence, but avoid it for large ASIC designs.
    addSimplePathConstraint(solver, variables, coi.relevantStateSymbols, k + 1);
  }

  FrameFormulaEncoder lastFrameEncoder(
      solver, variables.makeLeafLits(k, inductionBad->getSupportVars()));
  solver.addClause({lastFrameEncoder.encode(inductionBad)});
  return !solver.solve();
}

}  // namespace KEPLER_FORMAL::SEC
