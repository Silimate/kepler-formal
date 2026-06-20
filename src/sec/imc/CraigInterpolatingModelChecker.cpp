// Copyright 2024-2026 keplertech.io
// SPDX-License-Identifier: GPL-3.0-only

#include "imc/CraigInterpolatingModelChecker.h"

#include <algorithm>
#include <chrono>
#include <cstdlib>
#include <optional>
#include <stdexcept>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/SecDiag.h"
#include "kinduction/SatEncoding.h"
#include "proof/TransitionExprResolver.h"

namespace KEPLER_FORMAL::SEC {

namespace {

using VariablePartition = SATSolverWrapper::CraigVariablePartition;
using ClausePartition = SATSolverWrapper::CraigClausePartition;
using SteadyClock = std::chrono::steady_clock;

int64_t elapsedMilliseconds(SteadyClock::time_point start) {
  return std::chrono::duration_cast<std::chrono::milliseconds>(
             SteadyClock::now() - start)
      .count();
}

struct RegionLiteral {
  bool isState = false;
  size_t index = 0;
  bool positive = true;
};

struct InterpolantRegion {
  enum class Type {
    False,
    True,
    Normal,
  };

  Type type = Type::False;
  size_t auxiliaryCount = 0;
  std::vector<std::vector<RegionLiteral>> definitionClauses;
  RegionLiteral root;
};

struct TransitionEncodingResult {
  std::unordered_map<size_t, int> currentLits;
};

int instantiateRegionLiteral(
    const RegionLiteral& literal,
    const std::unordered_map<size_t, int>& stateLits,
    const std::vector<int>& auxiliaryLits) {
  const int positive = literal.isState
                           ? stateLits.at(literal.index)
                           : auxiliaryLits.at(literal.index);
  return literal.positive ? positive : -positive;
}

std::unordered_set<size_t> stateSymbolSet(
    const KInductionProblem& problem) {
  std::unordered_set<size_t> states;
  states.reserve(problem.state0Symbols.size() + problem.state1Symbols.size());
  states.insert(problem.state0Symbols.begin(), problem.state0Symbols.end());
  states.insert(problem.state1Symbols.begin(), problem.state1Symbols.end());
  return states;
}

void closePairDependencies(
    const std::vector<std::pair<size_t, size_t>>& pairs,
    std::unordered_set<size_t>& symbols) {
  bool changed = true;
  while (changed) {
    changed = false;
    for (const auto& [lhs, rhs] : pairs) {
      if (!symbols.contains(lhs) && !symbols.contains(rhs)) {
        continue;
      }
      changed |= symbols.insert(lhs).second;
      changed |= symbols.insert(rhs).second;
    }
  }
}

void closeSameDesignStateSemantics(
    const KInductionProblem& problem,
    std::unordered_set<size_t>& symbols) {
  closePairDependencies(problem.complementedStatePairs0, symbols);
  closePairDependencies(problem.complementedStatePairs1, symbols);
  closePairDependencies(problem.sameFrameStateEqualityPairs0, symbols);
  closePairDependencies(problem.sameFrameStateEqualityPairs1, symbols);
  for (const auto& rails : problem.dualRailStatePairs) {
    if (symbols.contains(rails.mayBeOne) ||
        symbols.contains(rails.mayBeZero)) {
      symbols.insert(rails.mayBeOne);
      symbols.insert(rails.mayBeZero);
    }
  }
}

std::vector<size_t> sortedSymbols(
    const std::unordered_set<size_t>& symbols) {
  std::vector<size_t> sorted(symbols.begin(), symbols.end());
  std::sort(sorted.begin(), sorted.end());
  return sorted;
}

std::unordered_set<size_t> initialTrackedStates(
    const KInductionProblem& problem) {
  const auto states = stateSymbolSet(problem);
  std::unordered_set<size_t> tracked;
  for (const size_t symbol : problem.bad->getSupportVars()) {
    if (states.contains(symbol)) {
      tracked.insert(symbol);
    }
  }
  closeSameDesignStateSemantics(problem, tracked);
  return tracked;
}

std::unordered_map<size_t, int> allocateLeafLits(
    SATSolverWrapper& solver,
    const std::vector<size_t>& symbols,
    VariablePartition partition) {
  solver.setCraigVariablePartition(partition);
  std::unordered_map<size_t, int> leaves;
  leaves.reserve(symbols.size());
  for (const size_t symbol : symbols) {
    leaves.emplace(symbol, solver.newVar() + 2);
  }
  return leaves;
}

void addLiteralEquivalenceForPartition(
    SATSolverWrapper& solver,
    int lhs,
    int rhs,
    ClausePartition partition) {
  solver.setCraigClausePartition(partition);
  addLiteralEquivalence(solver, lhs, rhs);
}

void addPairEqualities(
    SATSolverWrapper& solver,
    const std::unordered_map<size_t, int>& leaves,
    const std::vector<std::pair<size_t, size_t>>& pairs,
    bool complemented,
    ClausePartition partition) {
  for (const auto& [lhsSymbol, rhsSymbol] : pairs) {
    const auto lhs = leaves.find(lhsSymbol);
    const auto rhs = leaves.find(rhsSymbol);
    if (lhs == leaves.end() || rhs == leaves.end()) {
      continue;
    }
    addLiteralEquivalenceForPartition(
        solver,
        rhs->second,
        complemented ? -lhs->second : lhs->second,
        partition);
  }
}

void addStateSemantics(
    SATSolverWrapper& solver,
    const KInductionProblem& problem,
    const std::unordered_map<size_t, int>& leaves,
    ClausePartition partition) {
  addPairEqualities(
      solver, leaves, problem.complementedStatePairs0, true, partition);
  addPairEqualities(
      solver, leaves, problem.complementedStatePairs1, true, partition);
  addPairEqualities(
      solver, leaves, problem.sameFrameStateEqualityPairs0, false, partition);
  addPairEqualities(
      solver, leaves, problem.sameFrameStateEqualityPairs1, false, partition);
  solver.setCraigClausePartition(partition);
  for (const auto& rails : problem.dualRailStatePairs) {
    const auto mayOne = leaves.find(rails.mayBeOne);
    const auto mayZero = leaves.find(rails.mayBeZero);
    if (mayOne != leaves.end() && mayZero != leaves.end()) {
      solver.addClause({mayOne->second, mayZero->second});
    }
  }
}

void addResetInputValue(
    SATSolverWrapper& solver,
    const KInductionProblem& problem,
    std::unordered_map<size_t, int>& leaves,
    bool asserted,
    VariablePartition variablePartition,
    ClausePartition clausePartition) {
  solver.setCraigVariablePartition(variablePartition);
  solver.setCraigClausePartition(clausePartition);
  for (const auto& [symbol, assertedValue] : problem.resetBootstrapInputs) {
    auto [it, inserted] = leaves.emplace(symbol, 0);
    if (inserted) {
      it->second = solver.newVar() + 2;
    }
    const bool value = asserted ? assertedValue : !assertedValue;
    solver.addClause({value ? it->second : -it->second});
  }
}

std::unordered_map<size_t, size_t> primaryByComplement(
    const KInductionProblem& problem) {
  std::unordered_map<size_t, size_t> result;
  for (const auto& [primary, complement] : problem.complementedStatePairs0) {
    result.emplace(complement, primary);
  }
  for (const auto& [primary, complement] : problem.complementedStatePairs1) {
    result.emplace(complement, primary);
  }
  return result;
}

size_t transitionTargetFor(
    size_t symbol,
    const TransitionExprResolver& resolver,
    const std::unordered_map<size_t, size_t>& complementPrimary) {
  if (resolver.contains(symbol)) {
    return symbol;
  }
  const auto primary = complementPrimary.find(symbol);
  if (primary != complementPrimary.end() && resolver.contains(primary->second)) {
    return primary->second;
  }
  return symbol;
}

TransitionEncodingResult addProjectedTransition(
    SATSolverWrapper& solver,
    const KInductionProblem& problem,
    const TransitionExprResolver& resolver,
    const std::unordered_map<size_t, size_t>& complementPrimary,
    const std::unordered_set<size_t>& trackedStates,
    std::unordered_map<size_t, int> currentLits,
    const std::unordered_map<size_t, int>& nextStateLits) {
  solver.setCraigVariablePartition(VariablePartition::ALocal);
  for (const size_t symbol : problem.inputSymbols) {
    if (!currentLits.contains(symbol)) {
      currentLits.emplace(symbol, solver.newVar() + 2);
    }
  }

  FrameFormulaEncoder encoder(
      solver, std::move(currentLits), /*createMissingLeaves=*/true);
  std::unordered_set<size_t> encodedTargets;
  for (const size_t requested : trackedStates) {
    const size_t target =
        transitionTargetFor(requested, resolver, complementPrimary);
    if (!resolver.contains(target) || !encodedTargets.insert(target).second) {
      continue;
    }
    const auto next = nextStateLits.find(target);
    if (next == nextStateLits.end()) {
      continue;
    }
    solver.setCraigVariablePartition(VariablePartition::ALocal);
    const int transitionLit = encoder.encode(resolver.at(target));
    addLiteralEquivalenceForPartition(
        solver, next->second, transitionLit, ClausePartition::A);
  }

  auto leaves = encoder.leafLits();
  addResetInputValue(
      solver,
      problem,
      leaves,
      /*asserted=*/false,
      VariablePartition::ALocal,
      ClausePartition::A);
  addStateSemantics(solver, problem, leaves, ClausePartition::A);
  return {std::move(leaves)};
}

RegionLiteral convertInterpolantLiteral(
    int literal,
    const std::unordered_map<int, size_t>& stateByVariable,
    int firstAuxiliaryVariable,
    std::unordered_map<int, size_t>& auxiliaryByVariable) {
  const int variable = std::abs(literal);
  if (const auto state = stateByVariable.find(variable);
      state != stateByVariable.end()) {
    return {true, state->second, literal > 0};
  }
  if (variable < firstAuxiliaryVariable) {
    throw std::runtime_error(
        "Craig interpolant contains a non-global original variable");
  }
  auto [auxiliary, inserted] =
      auxiliaryByVariable.emplace(variable, auxiliaryByVariable.size());
  (void)inserted;
  return {false, auxiliary->second, literal > 0};
}

InterpolantRegion convertInterpolant(
    const SATSolverWrapper::CraigInterpolantCnf& cnf,
    const std::unordered_map<int, size_t>& stateByVariable) {
  if (cnf.type ==
      SATSolverWrapper::CraigInterpolantCnf::Type::ConstantFalse) {
    return {InterpolantRegion::Type::False};
  }
  if (cnf.type ==
      SATSolverWrapper::CraigInterpolantCnf::Type::ConstantTrue) {
    return {InterpolantRegion::Type::True};
  }
  if (cnf.type != SATSolverWrapper::CraigInterpolantCnf::Type::Normal ||
      cnf.clauses.empty() || cnf.clauses.back().size() != 1) {
    throw std::runtime_error("CaDiCaL returned an invalid Craig interpolant CNF");
  }

  InterpolantRegion region;
  region.type = InterpolantRegion::Type::Normal;
  std::unordered_map<int, size_t> auxiliaryByVariable;
  region.definitionClauses.reserve(cnf.clauses.size() - 1);
  for (size_t clauseIndex = 0; clauseIndex + 1 < cnf.clauses.size();
       ++clauseIndex) {
    std::vector<RegionLiteral> clause;
    clause.reserve(cnf.clauses[clauseIndex].size());
    for (const int literal : cnf.clauses[clauseIndex]) {
      clause.push_back(convertInterpolantLiteral(
          literal,
          stateByVariable,
          cnf.firstAuxiliaryVariable,
          auxiliaryByVariable));
    }
    region.definitionClauses.push_back(std::move(clause));
  }
  region.root = convertInterpolantLiteral(
      cnf.clauses.back().front(),
      stateByVariable,
      cnf.firstAuxiliaryVariable,
      auxiliaryByVariable);
  region.auxiliaryCount = auxiliaryByVariable.size();
  return region;
}

int instantiateRegion(
    SATSolverWrapper& solver,
    const InterpolantRegion& region,
    const std::unordered_map<size_t, int>& stateLits,
    VariablePartition variablePartition,
    ClausePartition clausePartition) {
  if (region.type == InterpolantRegion::Type::True) {
    solver.setCraigVariablePartition(variablePartition);
    const int literal = solver.newVar() + 2;
    solver.setCraigClausePartition(clausePartition);
    solver.addClause({literal});
    return literal;
  }
  if (region.type == InterpolantRegion::Type::False) {
    solver.setCraigVariablePartition(variablePartition);
    const int literal = solver.newVar() + 2;
    solver.setCraigClausePartition(clausePartition);
    solver.addClause({-literal});
    return literal;
  }

  solver.setCraigVariablePartition(variablePartition);
  std::vector<int> auxiliaryLits;
  auxiliaryLits.reserve(region.auxiliaryCount);
  for (size_t index = 0; index < region.auxiliaryCount; ++index) {
    auxiliaryLits.push_back(solver.newVar() + 2);
  }

  solver.setCraigClausePartition(clausePartition);
  for (const auto& abstractClause : region.definitionClauses) {
    std::vector<int> clause;
    clause.reserve(abstractClause.size());
    for (const auto& literal : abstractClause) {
      clause.push_back(
          instantiateRegionLiteral(literal, stateLits, auxiliaryLits));
    }
    solver.addClause(clause);
  }
  return instantiateRegionLiteral(region.root, stateLits, auxiliaryLits);
}

void addBadFormula(
    SATSolverWrapper& solver,
    const KInductionProblem& problem,
    std::unordered_map<size_t, int> nextLeaves) {
  solver.setCraigVariablePartition(VariablePartition::BLocal);
  for (const size_t symbol : problem.inputSymbols) {
    if (!nextLeaves.contains(symbol)) {
      nextLeaves.emplace(symbol, solver.newVar() + 2);
    }
  }
  addResetInputValue(
      solver,
      problem,
      nextLeaves,
      /*asserted=*/false,
      VariablePartition::BLocal,
      ClausePartition::B);
  FrameFormulaEncoder encoder(
      solver, std::move(nextLeaves), /*createMissingLeaves=*/true);
  solver.setCraigVariablePartition(VariablePartition::BLocal);
  const int bad = encoder.encode(problem.bad);
  solver.setCraigClausePartition(ClausePartition::B);
  solver.addClause({bad});
}

void addInitialFrontierConstraint(
    SATSolverWrapper& solver,
    const KInductionProblem& problem,
    std::unordered_map<size_t, int> leaves) {
  BoolExpr* initial = BoolExpr::createTrue();
  bool hasInitialConstraint = false;
  for (const auto& [symbol, value] : problem.initialStateAssignments) {
    initial = BoolExpr::And(
        initial,
        value ? BoolExpr::Var(symbol)
              : BoolExpr::Not(BoolExpr::Var(symbol)));
    hasInitialConstraint = true;
  }
  if (!problem.hasExplicitInitialState() && !hasInitialConstraint) {
    // Resetless SEC observes both designs from an already-matching top-level
    // frontier. This is an interface property, not an internal state relation.
    initial = problem.property;
    hasInitialConstraint = initial != nullptr;
  }
  if (!hasInitialConstraint) {
    return;
  }

  solver.setCraigVariablePartition(VariablePartition::ALocal);
  FrameFormulaEncoder encoder(
      solver, std::move(leaves), /*createMissingLeaves=*/true);
  const int initialLiteral = encoder.encode(initial);
  solver.setCraigClausePartition(ClausePartition::A);
  solver.addClause({initialLiteral});
}

struct FrontierResult {
  std::optional<InterpolantRegion> region;
  std::unordered_set<size_t> transitionStateSupport;
};

struct InductivenessResult {
  bool isInductive = false;
  std::unordered_set<size_t> transitionStateSupport;
};

void addStateAssignments(
    SATSolverWrapper& solver,
    const std::unordered_map<size_t, int>& leaves,
    const std::vector<std::pair<size_t, bool>>& assignments) {
  solver.setCraigClausePartition(ClausePartition::A);
  for (const auto& [symbol, value] : assignments) {
    if (const auto literal = leaves.find(symbol); literal != leaves.end()) {
      solver.addClause({value ? literal->second : -literal->second});
    }
  }
}

FrontierResult deriveBoundedFrontierRegion(
    const KInductionProblem& problem,
    const std::unordered_set<size_t>& trackedStates,
    size_t proofDepth) {
  SATSolverWrapper solver(KEPLER_FORMAL::Config::SolverType::CADICAL);
  solver.enableCraigInterpolation();
  solver.configureForSecLocalBooleanCheck(trackedStates.size());
  const TransitionExprResolver resolver(problem);
  const auto complementPrimary = primaryByComplement(problem);
  const bool startsAtConcreteBootstrapFrontier =
      problem.resetBootstrapCycles != 0 &&
      !problem.bootstrapStateAssignments.empty();
  // Concrete bootstrap assignments are independently derived for each design
  // by reset simulation. Starting from that post-reset frontier avoids
  // rebuilding the reset transition cone and introduces no cross-design state
  // relation.
  const size_t bootstrapDepth =
      startsAtConcreteBootstrapFrontier ? 0 : problem.resetBootstrapCycles;
  const size_t depth = bootstrapDepth + proofDepth;

  std::vector<std::unordered_map<size_t, int>> frameLits(depth + 1);
  frameLits[depth] = allocateLeafLits(
      solver, sortedSymbols(trackedStates), VariablePartition::Global);
  std::unordered_map<int, size_t> stateByVariable;
  for (const auto& [symbol, literal] : frameLits[depth]) {
    stateByVariable.emplace(std::abs(literal), symbol);
  }

  FrontierResult result;
  if (depth == 0 && !startsAtConcreteBootstrapFrontier) {
    addInitialFrontierConstraint(solver, problem, frameLits[0]);
  }

  std::unordered_set<size_t> required = trackedStates;
  for (size_t reverseFrame = depth; reverseFrame > 0; --reverseFrame) {
    const size_t frame = reverseFrame - 1;
    frameLits[frame] = allocateLeafLits(
        solver, problem.inputSymbols, VariablePartition::ALocal);
    FrameFormulaEncoder encoder(
        solver, std::move(frameLits[frame]), /*createMissingLeaves=*/true);
    std::unordered_set<size_t> encodedTargets;
    for (const size_t requested : required) {
      const size_t target =
          transitionTargetFor(requested, resolver, complementPrimary);
      if (!resolver.contains(target) || !encodedTargets.insert(target).second) {
        continue;
      }
      const auto next = frameLits[frame + 1].find(target);
      if (next == frameLits[frame + 1].end()) {
        continue;
      }
      solver.setCraigVariablePartition(VariablePartition::ALocal);
      const int transition = encoder.encode(resolver.at(target));
      addLiteralEquivalenceForPartition(
          solver, next->second, transition, ClausePartition::A);
    }
    frameLits[frame] = encoder.leafLits();
    addResetInputValue(
        solver,
        problem,
        frameLits[frame],
        /*asserted=*/frame < bootstrapDepth,
        VariablePartition::ALocal,
        ClausePartition::A);
    addStateSemantics(
        solver, problem, frameLits[frame], ClausePartition::A);

    required.clear();
    const auto states = stateSymbolSet(problem);
    for (const auto& [symbol, literal] : frameLits[frame]) {
      (void)literal;
      if (states.contains(symbol)) {
        required.insert(symbol);
      }
    }
    closeSameDesignStateSemantics(problem, required);
    if (frame > 0) {
      for (const size_t symbol : required) {
        if (!frameLits[frame].contains(symbol)) {
          solver.setCraigVariablePartition(VariablePartition::ALocal);
          frameLits[frame].emplace(symbol, solver.newVar() + 2);
        }
      }
    }
  }

  if (!startsAtConcreteBootstrapFrontier) {
    addStateAssignments(
        solver, frameLits[0], problem.initialStateAssignments);
  }
  if (bootstrapDepth <= depth) {
    addStateAssignments(
        solver,
        frameLits[bootstrapDepth],
        problem.bootstrapStateAssignments);
  }
  if (startsAtConcreteBootstrapFrontier && proofDepth == 0) {
    emitSecDiag(
        "SEC diag: imc Craig starts at concrete post-reset frontier "
        "assignments=",
        problem.bootstrapStateAssignments.size(),
        " reset_cycles=", problem.resetBootstrapCycles);
  }
  addStateSemantics(
      solver, problem, frameLits[depth], ClausePartition::A);
  const auto states = stateSymbolSet(problem);
  for (const auto& leaves : frameLits) {
    for (const auto& [symbol, literal] : leaves) {
      (void)literal;
      if (states.contains(symbol)) {
        result.transitionStateSupport.insert(symbol);
      }
    }
  }
  closeSameDesignStateSemantics(problem, result.transitionStateSupport);
  addBadFormula(solver, problem, frameLits[depth]);

  // Keep phase timing diagnostic-only. It identifies whether a difficult IMC
  // batch is dominated by SAT or by Craig-interpolant materialization.
  emitSecDiag(
      "SEC diag: imc Craig bounded solve begin depth=", proofDepth,
      " tracked_states=", trackedStates.size(),
      " transition_states=", result.transitionStateSupport.size());
  const auto solveStart = SteadyClock::now();
  const auto solveStatus = solver.solveStatus();
  emitSecDiag(
      "SEC diag: imc Craig bounded solve end depth=", proofDepth,
      " status=", static_cast<int>(solveStatus),
      " elapsed_ms=", elapsedMilliseconds(solveStart));
  if (solveStatus != SATSolverWrapper::SolveStatus::Unsat) {
    return result;
  }
  const auto interpolationStart = SteadyClock::now();
  result.region =
      convertInterpolant(solver.createCraigInterpolant(), stateByVariable);
  emitSecDiag(
      "SEC diag: imc Craig interpolant built depth=", proofDepth,
      " elapsed_ms=", elapsedMilliseconds(interpolationStart));
  return result;
}

InductivenessResult reachableSetIsInductive(
    const KInductionProblem& problem,
    const std::unordered_set<size_t>& trackedStates,
    const std::vector<InterpolantRegion>& reachableRegions) {
  SATSolverWrapper solver(KEPLER_FORMAL::Config::SolverType::CADICAL);
  const auto tracked = sortedSymbols(trackedStates);
  auto currentLits = allocateLeafLits(
      solver, sortedSymbols(trackedStates), VariablePartition::ALocal);
  const auto nextLits =
      allocateLeafLits(solver, tracked, VariablePartition::ALocal);
  addStateSemantics(solver, problem, currentLits, ClausePartition::A);

  std::vector<int> currentRegionRoots;
  currentRegionRoots.reserve(reachableRegions.size());
  for (const auto& region : reachableRegions) {
    currentRegionRoots.push_back(instantiateRegion(
        solver,
        region,
        currentLits,
        VariablePartition::ALocal,
        ClausePartition::A));
  }
  solver.addClause(currentRegionRoots);

  const TransitionExprResolver resolver(problem);
  const TransitionEncodingResult transition = addProjectedTransition(
      solver,
      problem,
      resolver,
      primaryByComplement(problem),
      trackedStates,
      currentLits,
      nextLits);
  InductivenessResult result;
  const auto stateSymbols = stateSymbolSet(problem);
  for (const auto& [symbol, literal] : transition.currentLits) {
    (void)literal;
    if (stateSymbols.contains(symbol)) {
      result.transitionStateSupport.insert(symbol);
    }
  }
  closeSameDesignStateSemantics(problem, result.transitionStateSupport);
  addStateSemantics(solver, problem, nextLits, ClausePartition::A);

  // Negating a union requires every member region to be false in the successor
  // frame. UNSAT therefore proves that the accumulated reachable over-
  // approximation is closed under the concrete transition relation.
  for (const auto& region : reachableRegions) {
    const int nextRoot = instantiateRegion(
        solver,
        region,
        nextLits,
        VariablePartition::ALocal,
        ClausePartition::A);
    solver.addClause({-nextRoot});
  }
  emitSecDiag(
      "SEC diag: imc Craig inductiveness solve begin regions=",
      reachableRegions.size(), " tracked_states=", trackedStates.size());
  const auto solveStart = SteadyClock::now();
  const auto status = solver.solveStatus();
  emitSecDiag(
      "SEC diag: imc Craig inductiveness solve end status=",
      static_cast<int>(status),
      " elapsed_ms=", elapsedMilliseconds(solveStart));
  result.isInductive =
      status == SATSolverWrapper::SolveStatus::Unsat;
  return result;
}

CraigImcResult runWithProjection(
    const KInductionProblem& problem,
    std::unordered_set<size_t>& trackedStates,
    size_t maxIterations) {
  std::vector<InterpolantRegion> reachableRegions;
  for (size_t depth = 0; depth <= maxIterations; ++depth) {
    FrontierResult frontier =
        deriveBoundedFrontierRegion(problem, trackedStates, depth);
    if (!frontier.region.has_value()) {
      const size_t oldSize = trackedStates.size();
      trackedStates.insert(
          frontier.transitionStateSupport.begin(),
          frontier.transitionStateSupport.end());
      closeSameDesignStateSemantics(problem, trackedStates);
      if (trackedStates.size() == oldSize) {
        return {CraigImcStatus::NoProgress, depth + 1};
      }
      return {CraigImcStatus::NoProgress, 0};
    }
    reachableRegions.push_back(std::move(*frontier.region));
    const InductivenessResult inductiveness =
        reachableSetIsInductive(problem, trackedStates, reachableRegions);
    if (inductiveness.isInductive) {
      return {CraigImcStatus::Equivalent, depth + 1};
    }

    // A SAT inductiveness query may be caused only by state variables omitted
    // from the projection. Refine with same-design transition support before
    // adding more time frames; no cross-design correspondence is introduced.
    const size_t oldSize = trackedStates.size();
    trackedStates.insert(
        inductiveness.transitionStateSupport.begin(),
        inductiveness.transitionStateSupport.end());
    closeSameDesignStateSemantics(problem, trackedStates);
    if (trackedStates.size() != oldSize) {
      emitSecDiag(
          "SEC diag: imc Craig refines transition projection states=",
          oldSize, "->", trackedStates.size());
      return {CraigImcStatus::NoProgress, 0};
    }
  }
  return {CraigImcStatus::NoProgress, maxIterations};
}

}  // namespace

CraigInterpolatingModelChecker::CraigInterpolatingModelChecker(
    const KInductionProblem& problem)
    : problem_(problem) {}

CraigImcResult CraigInterpolatingModelChecker::run(
    size_t maxIterations) const {
  std::unordered_set<size_t> trackedStates = initialTrackedStates(problem_);
  if (trackedStates.empty()) {
    return {CraigImcStatus::Equivalent, 0};
  }

  for (size_t projectionRound = 0;
       projectionRound <= problem_.state0Symbols.size() +
                              problem_.state1Symbols.size();
       ++projectionRound) {
    const size_t projectionSize = trackedStates.size();
    emitSecDiag(
        "SEC diag: imc Craig projection round=", projectionRound,
        " states=", projectionSize);
    const CraigImcResult result =
        runWithProjection(problem_, trackedStates, maxIterations);
    if (result.status == CraigImcStatus::Equivalent ||
        result.iterations != 0 ||
        trackedStates.size() == projectionSize) {
      return result;
    }
  }
  return {};
}

}  // namespace KEPLER_FORMAL::SEC
