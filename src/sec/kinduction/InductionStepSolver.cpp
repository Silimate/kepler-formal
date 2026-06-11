// Copyright 2024-2026 keplertech.io
// SPDX-License-Identifier: GPL-3.0-only

#include "kinduction/InductionStepSolver.h"

#include <algorithm>
#include <cstdlib>
#include <limits>
#include <optional>
#include <unordered_map>
#include <unordered_set>

#include "common/SecDiag.h"
#include "kinduction/SatEncoding.h"
#include "proof/TransitionExprResolver.h"

namespace KEPLER_FORMAL::SEC {

namespace {

constexpr size_t kMaxSimplePathStateSymbols = 4096;
// Keep direct dual-rail leaf proofs bounded like KInductionEngine's localized
// path.  Hard resetless-state outputs should be reported as uncovered quickly.
constexpr unsigned kDefaultDualRailLeafInductionDecisionLimit = 5000;

struct InductionCoi {
  std::vector<std::vector<size_t>> transitionTargetsByFrame;
  std::vector<size_t> relevantStateSymbols;
  std::vector<size_t> solverSymbols;
  std::unordered_set<size_t> solverSymbolSet;
};

KEPLER_FORMAL::Config::SolverType inductionStepSolverType(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType) {
  (void)problem;
  return solverType;
}

std::optional<unsigned> readUnsignedEnv(const char* name) {
  const char* value = std::getenv(name);
  if (value == nullptr || *value == '\0') {
    return std::nullopt;
  }
  char* end = nullptr;
  const unsigned long parsed = std::strtoul(value, &end, 10);
  if (end == value || *end != '\0' ||
      parsed > std::numeric_limits<unsigned>::max()) {
    return std::nullopt;  // LCOV_EXCL_LINE
  }
  return static_cast<unsigned>(parsed);
}

bool isInductionStepCoiDiagEnabled() {
  return std::getenv("KEPLER_SEC_KI_COI_DIAG") != nullptr || isSecDiagEnabled();
}

std::optional<unsigned> directInductionDecisionLimit(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType) {
  if (!problem.usesDualRailStateEncoding ||
      problem.observedOutputExprs0.size() > 1 ||
      solverType != KEPLER_FORMAL::Config::SolverType::KISSAT) {
    return std::nullopt;
  }
  if (const auto limit =
          readUnsignedEnv("KEPLER_SEC_KI_DUAL_RAIL_LEAF_DECISION_LIMIT");
      limit.has_value()) {
    return limit;
  }
  // IMC calls the lower-level induction helper directly after output
  // localization. Keep those dual-rail leaf obligations bounded the same way
  // KInductionEngine does, so one hard output cannot stall the workflow.
  return kDefaultDualRailLeafInductionDecisionLimit;
}

size_t countTransitionTargets(
    const std::vector<std::vector<size_t>>& transitionTargetsByFrame) {
  size_t count = 0;
  for (const auto& targets : transitionTargetsByFrame) {
    count += targets.size();
  }
  return count;
}

size_t countStateEqualityPairsInCoi(
    const std::vector<std::pair<size_t, size_t>>& equalityPairs,
    const std::unordered_set<size_t>& solverSymbols) {
  size_t count = 0;
  for (const auto& [lhsSymbol, rhsSymbol] : equalityPairs) {
    if (solverSymbols.find(lhsSymbol) != solverSymbols.end() &&
        solverSymbols.find(rhsSymbol) != solverSymbols.end()) {
      ++count;
    }
  }
  return count;
}

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

void addRelevantDualRailPartners(
    const std::vector<DualRailSymbolPair>& railPairs,
    std::unordered_set<size_t>& solverSymbols) {
  for (const auto& rails : railPairs) {
    if (solverSymbols.find(rails.mayBeOne) != solverSymbols.end() ||
        solverSymbols.find(rails.mayBeZero) != solverSymbols.end()) {  // LCOV_EXCL_LINE
      solverSymbols.insert(rails.mayBeOne);
      solverSymbols.insert(rails.mayBeZero);
    }
  }
}

void addPostBootstrapResetInputSymbols(
    const KInductionProblem& problem,
    std::unordered_set<size_t>& solverSymbols) {
  if (problem.resetBootstrapCycles == 0) {
    return;
  }
  for (const auto& [symbol, _] : problem.resetBootstrapInputs) {
    solverSymbols.insert(symbol);
  }
}

void closeStateEqualityDependencies(
    const std::vector<std::pair<size_t, size_t>>& equalityPairs,
    std::unordered_set<size_t>& stateSymbols) {
  bool changed = true;
  while (changed) {
    changed = false;
    for (const auto& [lhsSymbol, rhsSymbol] : equalityPairs) {
      const bool lhsNeeded = stateSymbols.find(lhsSymbol) != stateSymbols.end();
      const bool rhsNeeded = stateSymbols.find(rhsSymbol) != stateSymbols.end();
      if (!lhsNeeded && !rhsNeeded) {
        continue;
      }
      changed |= stateSymbols.insert(lhsSymbol).second;
      changed |= stateSymbols.insert(rhsSymbol).second;
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
  std::unordered_set<size_t> transitionSupportSymbols;
  transitionSupportSymbols.reserve(1024);
  for (size_t frame = 0; frame < k; ++frame) {
    addFormulaStateSupport(inductionProperty, stateSymbols, requiredStates[frame]);
  }
  addFormulaStateSupport(inductionBad, stateSymbols, requiredStates[k]);

  std::vector<std::vector<size_t>> transitionTargetsByFrame(k);
  for (size_t frame = k; frame > 0; --frame) {
    if (addExtraInductiveEqualities && frame < k) {
      // Output-batched SEC should not carry every design-wide state relation into
      // a local proof.  Close only relations touched by this frame's real output
      // cone before walking one transition step backward.
      closeStateEqualityDependencies(
          problem.inductiveStateEqualityPairs, requiredStates[frame]);
    }
    auto targets = expandTransitionTargets(
        requiredStates[frame],
        transitionByState,
        primaryByComplement);
    transitionTargetsByFrame[frame - 1] = targets;
    // Wide dual-rail buses share large transition cones.  Ask the resolver for
    // the whole frame target set at once so KI/IMC reuse the same DAG walk
    // while still collecting exactly the symbols needed by the proof.
    transitionByState.collectSupportForTargets(
        targets,
        stateSymbols,
        requiredStates[frame - 1],
        transitionSupportSymbols);
  }
  if (addExtraInductiveEqualities) {
    closeStateEqualityDependencies(
        problem.inductiveStateEqualityPairs, requiredStates[0]);
  }

  std::unordered_set<size_t> solverSymbols;
  solverSymbols.reserve(1024);
  addFormulaSupport(inductionProperty, solverSymbols);
  addFormulaSupport(inductionBad, solverSymbols);

  std::unordered_set<size_t> relevantStateSymbols;
  for (const auto& frameStates : requiredStates) {
    relevantStateSymbols.insert(frameStates.begin(), frameStates.end());
    solverSymbols.insert(frameStates.begin(), frameStates.end());
  }
  for (const auto& targets : transitionTargetsByFrame) {
    for (const auto target : targets) {
      relevantStateSymbols.insert(target);
      solverSymbols.insert(target);
    }
  }
  solverSymbols.insert(
      transitionSupportSymbols.begin(), transitionSupportSymbols.end());
  addRelevantComplementPartners(problem.complementedStatePairs0, solverSymbols);
  addRelevantComplementPartners(problem.complementedStatePairs1, solverSymbols);
  addRelevantDualRailPartners(problem.dualRailStatePairs, solverSymbols);
  addPostBootstrapResetInputSymbols(problem, solverSymbols);

  InductionCoi coi;
  coi.transitionTargetsByFrame = std::move(transitionTargetsByFrame);
  coi.relevantStateSymbols = sortedSymbols(relevantStateSymbols);
  coi.solverSymbols = sortedSymbols(solverSymbols);
  coi.solverSymbolSet.insert(coi.solverSymbols.begin(), coi.solverSymbols.end());
  return coi;
}

void emitInductionStepCoiDiag(const KInductionProblem& problem,
                              const InductionCoi& coi,
                              size_t k) {
  if (!isInductionStepCoiDiagEnabled()) {
    return;
  }
  emitSecDiag(
      "SEC diag: k-induction step coi k=", k,
      " solver_symbols=", coi.solverSymbols.size(),
      " transition_targets=", countTransitionTargets(coi.transitionTargetsByFrame),
      " relevant_states=", coi.relevantStateSymbols.size(),
      " inductive_equalities_in_coi=",
      countStateEqualityPairsInCoi(
          problem.inductiveStateEqualityPairs, coi.solverSymbolSet));
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

void addDualRailStateValidity(
    SATSolverWrapper& solver,
    const FrameVariableStore& variables,
    const std::vector<DualRailSymbolPair>& railPairs,
    const std::unordered_set<size_t>& solverSymbols,
    size_t numFrames) {
  for (size_t frame = 0; frame < numFrames; ++frame) {
    for (const auto& rails : railPairs) {
      if (solverSymbols.find(rails.mayBeOne) == solverSymbols.end() ||
          solverSymbols.find(rails.mayBeZero) == solverSymbols.end()) {
        continue;  // LCOV_EXCL_LINE
      }
      // Dual-rail encodes a non-empty possible-value set.  The empty set
      // (may1=0, may0=0) is not a legal ternary value and must not be available
      // to induction as a synthetic predecessor.
      solver.addClause({
          variables.getLiteral(rails.mayBeOne, frame),
          variables.getLiteral(rails.mayBeZero, frame)});
    }
  }
}

void addPostBootstrapResetInputConstraints(
    SATSolverWrapper& solver,
    const FrameVariableStore& variables,
    const KInductionProblem& problem,
    size_t numFrames) {
  if (problem.resetBootstrapCycles == 0) {
    return;
  }

  for (const auto& [symbol, assertedValue] : problem.resetBootstrapInputs) {
    if (!variables.hasSymbol(symbol)) {  // LCOV_EXCL_LINE
      continue;  // LCOV_EXCL_LINE
    }
    for (size_t frame = 0; frame < numFrames; ++frame) {
      // The induction query starts at the post-bootstrap frontier.  Match the
      // base-case/PDR environment by keeping reset controls deasserted
      // throughout this window instead of proving across arbitrary reset
      // reassertion.
      solver.addClause(
          {assertedValue ? -variables.getLiteral(symbol, frame)
                         : variables.getLiteral(symbol, frame)});  // LCOV_EXCL_LINE
    }
  }
}

}  // namespace

InductionProofStatus proveByInductionStatus(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    size_t k,
    std::optional<unsigned> kissatDecisionLimit) {
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
  emitInductionStepCoiDiag(problem, coi, k);
  const auto inductionPropertySupport = inductionProperty->getSupportVars();
  const auto inductionBadSupport = inductionBad->getSupportVars();
  const TransitionExprResolver transitionByState(problem);
  const FrameSymbolAliases aliasesByFrame = buildInductionFrameAliases(
      problem, coi, k + 1, aliasInductiveStateEqualities);

  const auto localSolverType = inductionStepSolverType(problem, solverType);
  SATSolverWrapper solver(localSolverType);
  if (problem.usesDualRailStateEncoding) {
    solver.configureForSecDualRailConeProof(coi.solverSymbols.size());
  } else {
    solver.configureForSecConeProof(coi.solverSymbols.size());
  }
  FrameVariableStore variables(solver, coi.solverSymbols, k + 1, aliasesByFrame);
  addComplementedStateRelations(
      solver, variables, problem.complementedStatePairs0, coi.solverSymbolSet, k + 1);
  addComplementedStateRelations(
      solver, variables, problem.complementedStatePairs1, coi.solverSymbolSet, k + 1);
  addDualRailStateValidity(
      solver, variables, problem.dualRailStatePairs, coi.solverSymbolSet, k + 1);
  addPostBootstrapResetInputConstraints(solver, variables, problem, k + 1);

  for (size_t frame = 0; frame < k; ++frame) {
    addTransitionRelation(
        solver, variables, transitionByState, coi.transitionTargetsByFrame[frame], frame);
  }

  for (size_t frame = 0; frame < k; ++frame) {
    FrameFormulaEncoder encoder(
        solver, variables.makeLeafLits(frame, inductionPropertySupport));
    solver.addClause({encoder.encode(inductionProperty)});
  }
  if (addExtraInductiveEqualities && k > 0) {
    addInductiveStateEqualities(solver, variables, problem, coi.solverSymbolSet, 0, k - 1);
  }

  if (!problem.usesDualRailStateEncoding &&
      coi.relevantStateSymbols.size() <= kMaxSimplePathStateSymbols) {
    // The simple-path refinement is a completeness aid, not a soundness
    // requirement for classic k-induction. On large gate-level SEC problems it
    // creates one XOR per state bit per frame-pair, which can dominate the SAT
    // instance and drown the actual proof. Dual-rail already doubles each state
    // bit into may-one/may-zero rails, so skip this optional refinement there.
    addSimplePathConstraint(solver, variables, coi.relevantStateSymbols, k + 1);
  }

  FrameFormulaEncoder lastFrameEncoder(
      solver, variables.makeLeafLits(k, inductionBadSupport));
  solver.addClause({lastFrameEncoder.encode(inductionBad)});
  SATSolverWrapper::SolveStatus solveStatus;
  if (localSolverType == KEPLER_FORMAL::Config::SolverType::KISSAT &&
      kissatDecisionLimit.has_value()) {
    solveStatus = solver.solveWithKissatResourceLimits(
        std::numeric_limits<unsigned>::max(), *kissatDecisionLimit);
  } else if (localSolverType == KEPLER_FORMAL::Config::SolverType::CADICAL &&
             kissatDecisionLimit.has_value()) {  // LCOV_EXCL_LINE
    solveStatus = solver.solveWithAssumptionsStatus(  // LCOV_EXCL_LINE
        {},  // LCOV_EXCL_LINE
        *kissatDecisionLimit,  // LCOV_EXCL_LINE
        *kissatDecisionLimit);  // LCOV_EXCL_LINE
  } else {  // LCOV_EXCL_LINE
    solveStatus = solver.solveStatus();
  }
  switch (solveStatus) {
    case SATSolverWrapper::SolveStatus::Unsat:
      return InductionProofStatus::Proved;
    case SATSolverWrapper::SolveStatus::Sat:
      return InductionProofStatus::NotProved;
    case SATSolverWrapper::SolveStatus::Unknown:
      return InductionProofStatus::Unknown;  // LCOV_EXCL_LINE
  }
  return InductionProofStatus::Unknown;  // LCOV_EXCL_LINE
}

bool provesByInduction(const KInductionProblem& problem,
                       KEPLER_FORMAL::Config::SolverType solverType,
                       size_t k) {
  return proveByInductionStatus(
             problem,
             solverType,
             k,
             directInductionDecisionLimit(problem, solverType)) ==
         InductionProofStatus::Proved;
}

}  // namespace KEPLER_FORMAL::SEC
