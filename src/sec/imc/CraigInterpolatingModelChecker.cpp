// Copyright 2024-2026 keplertech.io
// SPDX-License-Identifier: GPL-3.0-only

#include "imc/CraigInterpolatingModelChecker.h"

#include <algorithm>
#include <chrono>
#include <cstring>
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
using AuxiliaryStateInvariants = std::vector<std::pair<size_t, bool>>;

constexpr size_t kAuxiliaryInvariantSupportLimit = 256;

bool imcAuxiliaryInvariantsEnabled() {
  const char* enabled = std::getenv("KEPLER_SEC_IMC_AUX_INVARIANTS");
  return enabled != nullptr && std::strcmp(enabled, "1") == 0;
}

bool imcDirectCubeSourceEnabled() {
  const char* enabled = std::getenv("KEPLER_SEC_IMC_DIRECT_CUBE_SOURCE");
  return enabled != nullptr && std::strcmp(enabled, "1") == 0;
}

int64_t elapsedMilliseconds(SteadyClock::time_point start) {
  return std::chrono::duration_cast<std::chrono::milliseconds>(
             SteadyClock::now() - start)
      .count();
}

struct TransitionEncodingResult {
  std::unordered_map<size_t, int> currentLits;
};

size_t regionClauseCount(const InterpolantRegion& region) {
  return region.definitionClauseEnds.size();
}

size_t regionLiteralCount(const InterpolantRegion& region) {
  return region.definitionLiterals.size();
}

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

void addAuxiliaryStateInvariants(
    SATSolverWrapper& solver,
    const std::unordered_map<size_t, int>& leaves,
    const AuxiliaryStateInvariants& invariants,
    ClausePartition partition) {
  if (invariants.empty()) {
    return;
  }
  solver.setCraigClausePartition(partition);
  for (const auto& [symbol, value] : invariants) {
    if (const auto leaf = leaves.find(symbol); leaf != leaves.end()) {
      solver.addClause({value ? leaf->second : -leaf->second});
    }
  }
}

std::unordered_map<size_t, bool> bootstrapStateConstants(
    const KInductionProblem& problem) {
  std::unordered_map<size_t, bool> constants;
  constants.reserve(problem.bootstrapStateAssignments.size());
  const auto states = stateSymbolSet(problem);
  for (const auto& [symbol, value] : problem.bootstrapStateAssignments) {
    if (states.contains(symbol)) {
      constants[symbol] = value;
    }
  }
  return constants;
}

bool transitionPreservesStateConstant(
    const TransitionExprResolver& resolver,
    size_t symbol,
    bool value,
    const std::unordered_map<size_t, bool>& constants) {
  if (!resolver.contains(symbol)) {
    return false;
  }
  const auto& support = resolver.support(symbol);
  if (support.size() > kAuxiliaryInvariantSupportLimit) {
    return false;
  }

  SATSolverWrapper solver(KEPLER_FORMAL::Config::SolverType::KISSAT);
  std::unordered_map<size_t, int> leaves;
  leaves.reserve(support.size());
  for (const size_t supportSymbol : support) {
    if (supportSymbol >= 2) {
      leaves.emplace(supportSymbol, solver.newVar() + 2);
    }
  }

  for (const auto& [constantSymbol, constantValue] : constants) {
    const auto leaf = leaves.find(constantSymbol);
    if (leaf != leaves.end()) {
      solver.addClause({constantValue ? leaf->second : -leaf->second});
    }
  }

  FrameFormulaEncoder encoder(
      solver, std::move(leaves), /*createMissingLeaves=*/true);
  const int nextValue = encoder.encode(resolver.at(symbol));
  solver.addClause({value ? -nextValue : nextValue});
  return solver.solveStatus() == SATSolverWrapper::SolveStatus::Unsat;
}

AuxiliaryStateInvariants deriveAuxiliaryStateInvariants(
    const KInductionProblem& problem) {
  if (!imcAuxiliaryInvariantsEnabled() ||
      problem.bootstrapStateAssignments.empty()) {
    return {};
  }

  const TransitionExprResolver resolver(problem);
  auto constants = bootstrapStateConstants(problem);
  const size_t candidateCount = constants.size();
  bool changed = true;
  while (changed) {
    changed = false;
    for (auto it = constants.begin(); it != constants.end();) {
      if (transitionPreservesStateConstant(
              resolver, it->first, it->second, constants)) {
        ++it;
        continue;
      }
      it = constants.erase(it);
      changed = true;
    }
  }

  AuxiliaryStateInvariants invariants(
      constants.begin(), constants.end());
  std::sort(invariants.begin(), invariants.end());
  emitSecDiag(
      "SEC diag: imc Craig auxiliary constants=", invariants.size(),
      " candidates=", candidateCount,
      " support_limit=", kAuxiliaryInvariantSupportLimit);
  return invariants;
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

std::unordered_set<size_t> transitionProjectionSupport(
    const KInductionProblem& problem,
    const TransitionExprResolver& resolver,
    const std::unordered_map<size_t, size_t>& complementPrimary,
    const std::unordered_set<size_t>& trackedStates) {
  const auto states = stateSymbolSet(problem);
  std::unordered_set<size_t> support = trackedStates;
  for (const size_t requested : sortedSymbols(trackedStates)) {
    const size_t target =
        transitionTargetFor(requested, resolver, complementPrimary);
    // addProjectedTransition only encodes targets that also have a next-state
    // leaf in the current projection. Match that behavior here so batching
    // sees the same closure Craig IMC will later refine toward.
    if (!trackedStates.contains(target) || !resolver.contains(target)) {
      continue;
    }
    for (const size_t symbol : resolver.support(target)) {
      if (states.contains(symbol)) {
        support.insert(symbol);
      }
    }
  }
  closeSameDesignStateSemantics(problem, support);
  return support;
}

TransitionEncodingResult addProjectedTransition(
    SATSolverWrapper& solver,
    const KInductionProblem& problem,
    const TransitionExprResolver& resolver,
    const std::unordered_map<size_t, size_t>& complementPrimary,
    const std::unordered_set<size_t>& trackedStates,
    const AuxiliaryStateInvariants& auxiliaryInvariants,
    std::unordered_map<size_t, int> currentLits,
    const std::unordered_map<size_t, int>& nextStateLits,
    VariablePartition localVariablePartition,
    ClausePartition clausePartition) {
  solver.setCraigVariablePartition(localVariablePartition);
  // FrameFormulaEncoder emits Tseitin clauses while encoding each transition.
  // Select the transition's Craig side before encoding, not only before adding
  // the final next-state equivalence.
  solver.setCraigClausePartition(clausePartition);
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
    solver.setCraigVariablePartition(localVariablePartition);
    solver.setCraigClausePartition(clausePartition);
    const int transitionLit = encoder.encode(resolver.at(target));
    addLiteralEquivalenceForPartition(
        solver, next->second, transitionLit, clausePartition);
  }

  auto leaves = encoder.leafLits();
  addResetInputValue(
      solver,
      problem,
      leaves,
      /*asserted=*/false,
      localVariablePartition,
      clausePartition);
  addStateSemantics(solver, problem, leaves, clausePartition);
  addAuxiliaryStateInvariants(
      solver, leaves, auxiliaryInvariants, clausePartition);
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
  region.definitionClauseEnds.reserve(cnf.clauses.size() - 1);
  size_t inputLiteralCount = 0;
  for (size_t clauseIndex = 0; clauseIndex + 1 < cnf.clauses.size();
       ++clauseIndex) {
    inputLiteralCount += cnf.clauses[clauseIndex].size();
    for (const int literal : cnf.clauses[clauseIndex]) {
      region.definitionLiterals.push_back(convertInterpolantLiteral(
          literal,
          stateByVariable,
          cnf.firstAuxiliaryVariable,
          auxiliaryByVariable));
    }
    region.definitionClauseEnds.push_back(region.definitionLiterals.size());
  }
  region.root = convertInterpolantLiteral(
      cnf.clauses.back().front(),
      stateByVariable,
      cnf.firstAuxiliaryVariable,
      auxiliaryByVariable);
  region.auxiliaryCount = auxiliaryByVariable.size();
  emitSecDiag(
      "SEC diag: imc Craig interpolant converted clauses=",
      regionClauseCount(region),
      " literals=", regionLiteralCount(region),
      " input_literals=", inputLiteralCount,
      " auxiliaries=", region.auxiliaryCount);
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
  size_t clauseBegin = 0;
  for (const size_t clauseEnd : region.definitionClauseEnds) {
    std::vector<int> clause;
    clause.reserve(clauseEnd - clauseBegin);
    for (size_t index = clauseBegin; index < clauseEnd; ++index) {
      clause.push_back(
          instantiateRegionLiteral(
              region.definitionLiterals[index], stateLits, auxiliaryLits));
    }
    solver.addClause(clause);
    clauseBegin = clauseEnd;
  }
  return instantiateRegionLiteral(region.root, stateLits, auxiliaryLits);
}

void addRegionUnionConstraint(
    SATSolverWrapper& solver,
    const std::vector<InterpolantRegion>& regions,
    const std::unordered_map<size_t, int>& stateLits,
    VariablePartition auxiliaryVariablePartition,
    ClausePartition clausePartition) {
  if (regions.empty()) {
    return;
  }
  std::vector<int> roots;
  roots.reserve(regions.size());
  for (const InterpolantRegion& region : regions) {
    roots.push_back(instantiateRegion(
        solver, region, stateLits, auxiliaryVariablePartition, clausePartition));
  }
  solver.setCraigClausePartition(clausePartition);
  solver.addClause(roots);
}

std::optional<InterpolantRegion> buildConcreteAssignmentRegion(
    const std::vector<std::pair<size_t, bool>>& assignments,
    const std::unordered_set<size_t>& trackedStates) {
  std::unordered_map<size_t, bool> assignmentBySymbol;
  assignmentBySymbol.reserve(assignments.size());
  for (const auto& [symbol, value] : assignments) {
    assignmentBySymbol.emplace(symbol, value);
  }

  std::vector<RegionLiteral> cubeLiterals;
  cubeLiterals.reserve(trackedStates.size());
  for (const size_t symbol : sortedSymbols(trackedStates)) {
    const auto assignment = assignmentBySymbol.find(symbol);
    if (assignment == assignmentBySymbol.end()) {
      // A partial assignment is an over-approximation, not the exact concrete
      // post-reset cube required by the bounded counterexample fast path.
      return std::nullopt;
    }
    cubeLiterals.push_back({true, symbol, assignment->second});
  }
  if (cubeLiterals.empty()) {
    return std::nullopt;
  }

  InterpolantRegion region;
  region.type = InterpolantRegion::Type::Normal;
  region.auxiliaryCount = 1;
  region.root = {false, 0, true};
  region.definitionLiterals.reserve(cubeLiterals.size() * 2 + 1);
  region.definitionClauseEnds.reserve(cubeLiterals.size() + 1);

  // Encode root <-> conjunction(assignments). Both directions are required:
  // the positive root selects the exact initial cube, while a negated root in
  // an inductiveness query denotes the exact complement of that cube.
  for (const RegionLiteral& literal : cubeLiterals) {
    region.definitionLiterals.push_back({false, 0, false});
    region.definitionLiterals.push_back(literal);
    region.definitionClauseEnds.push_back(region.definitionLiterals.size());
  }
  region.definitionLiterals.push_back(region.root);
  for (RegionLiteral literal : cubeLiterals) {
    literal.positive = !literal.positive;
    region.definitionLiterals.push_back(literal);
  }
  region.definitionClauseEnds.push_back(region.definitionLiterals.size());
  return region;
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
  SATSolverWrapper::SolveStatus solveStatus =
      SATSolverWrapper::SolveStatus::Unknown;
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

void addConcreteCubeOrRegionRoots(
    SATSolverWrapper& solver,
    const std::unordered_map<size_t, int>& leaves,
    const std::vector<std::pair<size_t, bool>>& cubeAssignments,
    const std::vector<int>& regionRoots) {
  solver.setCraigClausePartition(ClausePartition::A);
  for (const auto& [symbol, value] : cubeAssignments) {
    const auto leaf = leaves.find(symbol);
    if (leaf == leaves.end()) {
      continue;
    }
    std::vector<int> clause = regionRoots;
    clause.push_back(value ? leaf->second : -leaf->second);
    solver.addClause(clause);
  }
}

FrontierResult deriveBoundedFrontierRegion(
    const KInductionProblem& problem,
    const std::unordered_set<size_t>& trackedStates,
    const AuxiliaryStateInvariants& auxiliaryInvariants,
    size_t proofDepth) {
  SATSolverWrapper solver(KEPLER_FORMAL::Config::SolverType::CADICAL);
  solver.enableCraigInterpolation();
  // This is the main IMC proof, not a small disposable validator. Keep
  // CaDiCaL's proof-compatible preprocessing and inprocessing enabled so the
  // large transition relation is simplified before the UNSAT search.
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
  const auto buildStart = SteadyClock::now();
  emitSecDiag(
      "SEC diag: imc Craig bounded build begin depth=", proofDepth,
      " tracked_states=", trackedStates.size(),
      " total_depth=", depth);
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
    addAuxiliaryStateInvariants(
        solver, frameLits[frame], auxiliaryInvariants, ClausePartition::A);

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
  emitSecDiag(
      "SEC diag: imc Craig bounded build after_unroll depth=", proofDepth,
      " elapsed_ms=", elapsedMilliseconds(buildStart));

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
  addAuxiliaryStateInvariants(
      solver, frameLits[depth], auxiliaryInvariants, ClausePartition::A);
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
  emitSecDiag(
      "SEC diag: imc Craig bounded build end depth=", proofDepth,
      " transition_states=", result.transitionStateSupport.size(),
      " elapsed_ms=", elapsedMilliseconds(buildStart));

  // Keep phase timing diagnostic-only. It identifies whether a difficult IMC
  // batch is dominated by SAT or by Craig-interpolant materialization.
  emitSecDiag(
      "SEC diag: imc Craig bounded solve begin depth=", proofDepth,
      " tracked_states=", trackedStates.size(),
      " transition_states=", result.transitionStateSupport.size());
  const auto solveStart = SteadyClock::now();
  result.solveStatus = solver.solveStatus();
  emitSecDiag(
      "SEC diag: imc Craig bounded solve end depth=", proofDepth,
      " status=", static_cast<int>(result.solveStatus),
      " elapsed_ms=", elapsedMilliseconds(solveStart));
  if (result.solveStatus != SATSolverWrapper::SolveStatus::Unsat) {
    return result;
  }
  const auto interpolationStart = SteadyClock::now();
  result.region =
      convertInterpolant(solver.createCraigInterpolant(), stateByVariable);
  emitSecDiag(
      "SEC diag: imc Craig interpolant built depth=", proofDepth,
      " type=", static_cast<int>(result.region->type),
      " clauses=", regionClauseCount(*result.region),
      " literals=", regionLiteralCount(*result.region),
      " auxiliaries=", result.region->auxiliaryCount,
      " elapsed_ms=", elapsedMilliseconds(interpolationStart));
  return result;
}

FrontierResult deriveLookaheadFrontierRegion(
    const KInductionProblem& problem,
    const std::unordered_set<size_t>& trackedStates,
    const std::vector<InterpolantRegion>& reachableRegions,
    const std::vector<InterpolantRegion>& helperInvariantRegions,
    const AuxiliaryStateInvariants& auxiliaryInvariants,
    bool sourceIncludesConcreteBootstrapCube,
    size_t lookahead,
    size_t iteration) {
  SATSolverWrapper solver(KEPLER_FORMAL::Config::SolverType::CADICAL);
  solver.enableCraigInterpolation();

  const std::vector<size_t> tracked = sortedSymbols(trackedStates);
  std::vector<std::unordered_map<size_t, int>> frameLits(lookahead + 1);
  frameLits[0] = allocateLeafLits(
      solver, tracked, VariablePartition::ALocal);
  frameLits[1] = allocateLeafLits(
      solver, tracked, VariablePartition::Global);
  for (size_t frame = 2; frame <= lookahead; ++frame) {
    frameLits[frame] = allocateLeafLits(
        solver, tracked, VariablePartition::BLocal);
  }
  addRegionUnionConstraint(
      solver,
      helperInvariantRegions,
      frameLits[0],
      VariablePartition::ALocal,
      ClausePartition::A);
  addRegionUnionConstraint(
      solver,
      helperInvariantRegions,
      frameLits[1],
      VariablePartition::ALocal,
      ClausePartition::A);
  for (size_t frame = 2; frame <= lookahead; ++frame) {
    addRegionUnionConstraint(
        solver,
        helperInvariantRegions,
        frameLits[frame],
        VariablePartition::BLocal,
        ClausePartition::B);
  }
  addAuxiliaryStateInvariants(
      solver, frameLits[0], auxiliaryInvariants, ClausePartition::A);
  addAuxiliaryStateInvariants(
      solver, frameLits[1], auxiliaryInvariants, ClausePartition::A);
  for (size_t frame = 2; frame <= lookahead; ++frame) {
    addAuxiliaryStateInvariants(
        solver, frameLits[frame], auxiliaryInvariants, ClausePartition::B);
  }
  std::unordered_map<int, size_t> stateByVariable;
  for (const auto& [symbol, literal] : frameLits[1]) {
    stateByVariable.emplace(std::abs(literal), symbol);
  }

  const bool useDirectConcreteCube =
      sourceIncludesConcreteBootstrapCube && imcDirectCubeSourceEnabled();
  if (useDirectConcreteCube) {
    std::vector<int> regionRoots;
    regionRoots.reserve(
        reachableRegions.empty() ? 0 : reachableRegions.size() - 1);
    for (size_t index = 1; index < reachableRegions.size(); ++index) {
      regionRoots.push_back(instantiateRegion(
          solver,
          reachableRegions[index],
          frameLits[0],
          VariablePartition::ALocal,
          ClausePartition::A));
    }
    // The concrete post-reset cube is always the first source region. Encode
    // cube OR other_regions directly instead of rebuilding an auxiliary cube
    // root and then OR'ing that root with the interpolant roots.
    addConcreteCubeOrRegionRoots(
        solver,
        frameLits[0],
        problem.bootstrapStateAssignments,
        regionRoots);
  } else {
    std::vector<int> currentRegionRoots;
    currentRegionRoots.reserve(reachableRegions.size());
    for (const auto& region : reachableRegions) {
      currentRegionRoots.push_back(instantiateRegion(
          solver,
          region,
          frameLits[0],
          VariablePartition::ALocal,
          ClausePartition::A));
    }
    solver.setCraigClausePartition(ClausePartition::A);
    solver.addClause(currentRegionRoots);
  }

  const TransitionExprResolver resolver(problem);
  const auto complementPrimary = primaryByComplement(problem);
  const auto buildStart = SteadyClock::now();
  emitSecDiag(
      "SEC diag: imc Craig image build begin lookahead=", lookahead,
      " iteration=", iteration,
      " regions=", reachableRegions.size(),
      " tracked_states=", trackedStates.size(),
      " direct_cube_source=", useDirectConcreteCube ? 1 : 0);
  const TransitionEncodingResult transition = addProjectedTransition(
      solver,
      problem,
      resolver,
      complementPrimary,
      trackedStates,
      auxiliaryInvariants,
      frameLits[0],
      frameLits[1],
      VariablePartition::ALocal,
      ClausePartition::A);
  emitSecDiag(
      "SEC diag: imc Craig image build after_a_transition lookahead=",
      lookahead,
      " iteration=", iteration,
      " elapsed_ms=", elapsedMilliseconds(buildStart));

  FrontierResult result;
  const auto states = stateSymbolSet(problem);
  for (const auto& [symbol, literal] : transition.currentLits) {
    (void)literal;
    if (states.contains(symbol)) {
      result.transitionStateSupport.insert(symbol);
    }
  }
  for (size_t frame = 1; frame < lookahead; ++frame) {
    const TransitionEncodingResult suffixTransition = addProjectedTransition(
        solver,
        problem,
        resolver,
        complementPrimary,
        trackedStates,
        auxiliaryInvariants,
        frameLits[frame],
        frameLits[frame + 1],
        VariablePartition::BLocal,
        ClausePartition::B);
    for (const auto& [symbol, literal] : suffixTransition.currentLits) {
      (void)literal;
      if (states.contains(symbol)) {
        result.transitionStateSupport.insert(symbol);
      }
    }
  }
  emitSecDiag(
      "SEC diag: imc Craig image build after_b_suffix lookahead=",
      lookahead,
      " iteration=", iteration,
      " suffix_frames=", lookahead > 0 ? lookahead - 1 : 0,
      " elapsed_ms=", elapsedMilliseconds(buildStart));
  closeSameDesignStateSemantics(problem, result.transitionStateSupport);
  addStateSemantics(solver, problem, frameLits[1], ClausePartition::A);
  addAuxiliaryStateInvariants(
      solver, frameLits[1], auxiliaryInvariants, ClausePartition::A);
  addStateSemantics(
      solver, problem, frameLits[lookahead], ClausePartition::B);
  addAuxiliaryStateInvariants(
      solver, frameLits[lookahead], auxiliaryInvariants, ClausePartition::B);
  addBadFormula(solver, problem, frameLits[lookahead]);
  emitSecDiag(
      "SEC diag: imc Craig image build end lookahead=", lookahead,
      " iteration=", iteration,
      " transition_states=", result.transitionStateSupport.size(),
      " elapsed_ms=", elapsedMilliseconds(buildStart));

  emitSecDiag(
      "SEC diag: imc Craig image solve begin lookahead=", lookahead,
      " iteration=", iteration,
      " regions=", reachableRegions.size(),
      " tracked_states=", trackedStates.size());
  const auto solveStart = SteadyClock::now();
  result.solveStatus = solver.solveStatus();
  emitSecDiag(
      "SEC diag: imc Craig image solve end lookahead=", lookahead,
      " iteration=", iteration,
      " status=", static_cast<int>(result.solveStatus),
      " elapsed_ms=", elapsedMilliseconds(solveStart));
  if (result.solveStatus != SATSolverWrapper::SolveStatus::Unsat) {
    return result;
  }

  const auto interpolationStart = SteadyClock::now();
  result.region =
      convertInterpolant(solver.createCraigInterpolant(), stateByVariable);
  emitSecDiag(
      "SEC diag: imc Craig image interpolant built lookahead=", lookahead,
      " iteration=", iteration,
      " type=", static_cast<int>(result.region->type),
      " clauses=", regionClauseCount(*result.region),
      " literals=", regionLiteralCount(*result.region),
      " auxiliaries=", result.region->auxiliaryCount,
      " elapsed_ms=", elapsedMilliseconds(interpolationStart));
  return result;
}

class IncrementalInductivenessChecker {
 public:
  IncrementalInductivenessChecker(
      const KInductionProblem& problem,
      const std::unordered_set<size_t>& trackedStates,
      const std::vector<InterpolantRegion>& helperInvariantRegions,
      const AuxiliaryStateInvariants& auxiliaryInvariants)
      : problem_(problem),
        solver_(KEPLER_FORMAL::Config::SolverType::CADICAL),
        trackedStates_(trackedStates),
        helperInvariantRegions_(helperInvariantRegions),
        auxiliaryInvariants_(auxiliaryInvariants) {
    // This solver keeps growing after assumption solves. Disable CaDiCaL
    // variable-introducing preprocessing so later interpolant auxiliaries do
    // not collide with solver-internal extension variables.
    solver_.configureForSecLocalBooleanCheck(trackedStates_.size());
    const std::vector<size_t> tracked = sortedSymbols(trackedStates);
    currentLits_ = allocateLeafLits(
        solver_, tracked, VariablePartition::ALocal);
    nextLits_ = allocateLeafLits(
        solver_, tracked, VariablePartition::ALocal);
    addRegionUnionConstraint(
        solver_,
        helperInvariantRegions_,
        currentLits_,
        VariablePartition::ALocal,
        ClausePartition::A);
    addRegionUnionConstraint(
        solver_,
        helperInvariantRegions_,
        nextLits_,
        VariablePartition::ALocal,
        ClausePartition::A);
    addStateSemantics(
        solver_, problem_, currentLits_, ClausePartition::A);
    addAuxiliaryStateInvariants(
        solver_, currentLits_, auxiliaryInvariants_, ClausePartition::A);
    const TransitionExprResolver resolver(problem_);
    const TransitionEncodingResult transition = addProjectedTransition(
        solver_,
        problem_,
        resolver,
        primaryByComplement(problem_),
        trackedStates_,
        auxiliaryInvariants_,
        currentLits_,
        nextLits_,
        VariablePartition::ALocal,
        ClausePartition::A);
    currentLits_ = transition.currentLits;

    const auto stateSymbols = stateSymbolSet(problem_);
    for (const auto& [symbol, literal] : currentLits_) {
      (void)literal;
      if (stateSymbols.contains(symbol)) {
        transitionStateSupport_.insert(symbol);
      }
    }
    closeSameDesignStateSemantics(problem_, transitionStateSupport_);
    addStateSemantics(solver_, problem_, nextLits_, ClausePartition::A);
    addAuxiliaryStateInvariants(
        solver_, nextLits_, auxiliaryInvariants_, ClausePartition::A);
  }

  void addRegion(const InterpolantRegion& region) {
    const auto addStart = SteadyClock::now();
    currentRegionRoots_.push_back(instantiateRegion(
        solver_,
        region,
        currentLits_,
        VariablePartition::ALocal,
        ClausePartition::A));
    const int nextRoot = instantiateRegion(
        solver_,
        region,
        nextLits_,
        VariablePartition::ALocal,
        ClausePartition::A);
    // The reachable approximation only grows. Its successor complement
    // therefore strengthens monotonically and can remain in the solver.
    solver_.addClause({-nextRoot});
    emitSecDiag(
        "SEC diag: imc Craig incremental add_region regions=",
        currentRegionRoots_.size(),
        " clauses=", regionClauseCount(region),
        " literals=", regionLiteralCount(region),
        " auxiliaries=", region.auxiliaryCount,
        " elapsed_ms=", elapsedMilliseconds(addStart));
  }

  bool isInductive() {
    emitSecDiag(
        "SEC diag: imc Craig incremental inductiveness begin regions=",
        currentRegionRoots_.size(),
        " tracked_states=", trackedStates_.size());
    const auto solveStart = SteadyClock::now();
    size_t sourceChecks = 0;
    // The newest interpolant is the only source added since the previous
    // closure check. Test it first so a non-inductive region returns after one
    // SAT query instead of re-proving every older source region UNSAT.
    for (auto root = currentRegionRoots_.rbegin();
         root != currentRegionRoots_.rend();
         ++root) {
      ++sourceChecks;
      const auto status =
          solver_.solveWithAssumptionsStatus({*root});
      if (status != SATSolverWrapper::SolveStatus::Unsat) {
        emitSecDiag(
            "SEC diag: imc Craig incremental inductiveness end status=",
            static_cast<int>(status),
            " source_checks=", sourceChecks,
            " elapsed_ms=", elapsedMilliseconds(solveStart));
        return false;
      }
    }
    emitSecDiag(
        "SEC diag: imc Craig incremental inductiveness end status=",
        static_cast<int>(SATSolverWrapper::SolveStatus::Unsat),
        " source_checks=", sourceChecks,
        " elapsed_ms=", elapsedMilliseconds(solveStart));
    return true;
  }

  bool addRegionAndCheck(const InterpolantRegion& region) {
    addRegion(region);
    return isInductive();
  }

  const std::unordered_set<size_t>& transitionStateSupport() const {
    return transitionStateSupport_;
  }

 private:
  const KInductionProblem& problem_;
  SATSolverWrapper solver_;
  const std::unordered_set<size_t>& trackedStates_;
  const std::vector<InterpolantRegion>& helperInvariantRegions_;
  const AuxiliaryStateInvariants& auxiliaryInvariants_;
  std::unordered_map<size_t, int> currentLits_;
  std::unordered_map<size_t, int> nextLits_;
  std::unordered_set<size_t> transitionStateSupport_;
  std::vector<int> currentRegionRoots_;
};

CraigImcResult runWithProjection(
    const KInductionProblem& problem,
    std::unordered_set<size_t>& trackedStates,
    const std::vector<InterpolantRegion>& helperInvariantRegions,
    const AuxiliaryStateInvariants& auxiliaryInvariants,
    size_t maxIterations) {
  FrontierResult frontier;
  std::optional<InterpolantRegion> initialRegion =
      buildConcreteAssignmentRegion(
          problem.bootstrapStateAssignments, trackedStates);
  const bool hasConcreteInitialCube = initialRegion.has_value();
  if (!initialRegion.has_value()) {
    frontier = deriveBoundedFrontierRegion(
        problem, trackedStates, auxiliaryInvariants, 0);
    initialRegion = std::move(frontier.region);
    if (!initialRegion.has_value()) {
      const size_t oldSize = trackedStates.size();
      trackedStates.insert(
          frontier.transitionStateSupport.begin(),
          frontier.transitionStateSupport.end());
      closeSameDesignStateSemantics(problem, trackedStates);
      return {
          CraigImcStatus::NoProgress,
          trackedStates.size() == oldSize ? 1u : 0u};
    }
  } else {
    emitSecDiag(
        "SEC diag: imc Craig uses exact post-reset initial cube states=",
        trackedStates.size(),
        " reset_cycles=", problem.resetBootstrapCycles);
  }
  const InterpolantRegion concreteInitialRegion = std::move(*initialRegion);
  if (!craigInvariantExcludesBad(
          problem, trackedStates, {concreteInitialRegion},
          auxiliaryInvariants)) {
    return {
        hasConcreteInitialCube ? CraigImcStatus::CounterexampleCandidate
                               : CraigImcStatus::NoProgress,
        hasConcreteInitialCube ? 0u : 1u};
  }
  IncrementalInductivenessChecker initialInductivenessChecker(
      problem, trackedStates, helperInvariantRegions, auxiliaryInvariants);
  if (initialInductivenessChecker.addRegionAndCheck(concreteInitialRegion)) {
    return {
        CraigImcStatus::Equivalent,
        1,
        {concreteInitialRegion},
        trackedStates};
  }

  size_t oldSize = trackedStates.size();
  trackedStates.insert(
      initialInductivenessChecker.transitionStateSupport().begin(),
      initialInductivenessChecker.transitionStateSupport().end());
  closeSameDesignStateSemantics(problem, trackedStates);
  if (trackedStates.size() != oldSize) {
    emitSecDiag(
        "SEC diag: imc Craig refines transition projection states=",
        oldSize, "->", trackedStates.size());
    return {CraigImcStatus::NoProgress, 0};
  }

  for (size_t lookahead = 1; lookahead <= maxIterations; ++lookahead) {
    std::vector<InterpolantRegion> reachableRegions{concreteInitialRegion};
    IncrementalInductivenessChecker inductivenessChecker(
        problem, trackedStates, helperInvariantRegions, auxiliaryInvariants);
    inductivenessChecker.addRegion(concreteInitialRegion);

    for (size_t iteration = 1; iteration <= maxIterations; ++iteration) {
      frontier = deriveLookaheadFrontierRegion(
          problem,
          trackedStates,
          reachableRegions,
          helperInvariantRegions,
          auxiliaryInvariants,
          hasConcreteInitialCube,
          lookahead,
          iteration);
      if (!frontier.region.has_value()) {
        oldSize = trackedStates.size();
        trackedStates.insert(
            frontier.transitionStateSupport.begin(),
            frontier.transitionStateSupport.end());
        closeSameDesignStateSemantics(problem, trackedStates);
        if (trackedStates.size() != oldSize) {
          emitSecDiag(
              "SEC diag: imc Craig refines transition projection states=",
              oldSize, "->", trackedStates.size());
          return {CraigImcStatus::NoProgress, 0};
        }
        if (hasConcreteInitialCube &&
            iteration == 1 &&
            frontier.solveStatus == SATSolverWrapper::SolveStatus::Sat) {
          // At the first iteration the source region is the exact concrete
          // post-reset cube, so this SAT path is a real bounded candidate at
          // this lookahead. Later iterations start from over-approximations and
          // remain refinement signals only.
          return {
              CraigImcStatus::CounterexampleCandidate,
              lookahead};
        }
        // The current approximation reaches B's suffix. Increase the bounded
        // lookahead and restart from the concrete initial interpolant.
        break;
      }
      reachableRegions.push_back(std::move(*frontier.region));
      if (inductivenessChecker.addRegionAndCheck(reachableRegions.back())) {
        return {
            CraigImcStatus::Equivalent,
            lookahead,
            reachableRegions,
            trackedStates};
      }

      // A SAT inductiveness query may be caused only by state variables omitted
      // from the projection. Refine with same-design transition support before
      // continuing the interpolation sequence.
      oldSize = trackedStates.size();
      trackedStates.insert(
          inductivenessChecker.transitionStateSupport().begin(),
          inductivenessChecker.transitionStateSupport().end());
      closeSameDesignStateSemantics(problem, trackedStates);
      if (trackedStates.size() != oldSize) {
        emitSecDiag(
            "SEC diag: imc Craig refines transition projection states=",
            oldSize, "->", trackedStates.size());
        return {CraigImcStatus::NoProgress, 0};
      }
    }
  }
  return {
      hasConcreteInitialCube ? CraigImcStatus::ConcreteNoProgress
                             : CraigImcStatus::NoProgress,
      maxIterations};
}

}  // namespace

CraigInterpolatingModelChecker::CraigInterpolatingModelChecker(
    const KInductionProblem& problem,
    const std::vector<InterpolantRegion>* helperInvariantRegions,
    const std::unordered_set<size_t>* initialTrackedStates)
    : problem_(problem),
      helperInvariantRegions_(helperInvariantRegions),
      initialTrackedStates_(initialTrackedStates) {}

CraigImcResult CraigInterpolatingModelChecker::run(
    size_t maxIterations) const {
  std::unordered_set<size_t> trackedStates = initialTrackedStates(problem_);
  if (initialTrackedStates_ != nullptr) {
    const auto states = stateSymbolSet(problem_);
    for (const size_t symbol : *initialTrackedStates_) {
      if (states.contains(symbol)) {
        trackedStates.insert(symbol);
      }
    }
    closeSameDesignStateSemantics(problem_, trackedStates);
  }
  if (trackedStates.empty()) {
    return {CraigImcStatus::Equivalent, 0};
  }
  const std::vector<InterpolantRegion> emptyHelperRegions;
  const std::vector<InterpolantRegion>& helperRegions =
      helperInvariantRegions_ == nullptr ? emptyHelperRegions
                                         : *helperInvariantRegions_;
  const AuxiliaryStateInvariants auxiliaryInvariants =
      deriveAuxiliaryStateInvariants(problem_);

  for (size_t projectionRound = 0;
       projectionRound <= problem_.state0Symbols.size() +
                              problem_.state1Symbols.size();
       ++projectionRound) {
    const size_t projectionSize = trackedStates.size();
    emitSecDiag(
        "SEC diag: imc Craig projection round=", projectionRound,
        " states=", projectionSize);
    const CraigImcResult result =
        runWithProjection(
            problem_,
            trackedStates,
            helperRegions,
            auxiliaryInvariants,
            maxIterations);
    if (result.status == CraigImcStatus::Equivalent ||
        result.iterations != 0 ||
        trackedStates.size() == projectionSize) {
      return result;
    }
  }
  return {};
}

bool craigInvariantExcludesBad(
    const KInductionProblem& problem,
    const std::unordered_set<size_t>& trackedStates,
    const std::vector<InterpolantRegion>& invariantRegions,
    const AuxiliaryStateInvariants& auxiliaryStateInvariants) {
  if (trackedStates.empty() || invariantRegions.empty()) {
    return false;
  }

  SATSolverWrapper solver(KEPLER_FORMAL::Config::SolverType::CADICAL);
  auto stateLits = allocateLeafLits(
      solver, sortedSymbols(trackedStates), VariablePartition::ALocal);
  addStateSemantics(solver, problem, stateLits, ClausePartition::A);
  addAuxiliaryStateInvariants(
      solver, stateLits, auxiliaryStateInvariants, ClausePartition::A);

  std::vector<int> regionRoots;
  regionRoots.reserve(invariantRegions.size());
  for (const auto& region : invariantRegions) {
    regionRoots.push_back(instantiateRegion(
        solver,
        region,
        stateLits,
        VariablePartition::ALocal,
        ClausePartition::A));
  }
  solver.setCraigClausePartition(ClausePartition::A);
  solver.addClause(regionRoots);
  addBadFormula(solver, problem, stateLits);

  // Reusing a Craig IMC invariant is sound because it is already proven
  // reachable-frontier inductive for the concrete transition system.  This
  // query only asks whether the new top-level bad predicate intersects that
  // invariant; it does not add cross-design state assumptions.
  return solver.solveStatus() == SATSolverWrapper::SolveStatus::Unsat;
}

bool craigInvariantConjunctionExcludesBad(
    const KInductionProblem& problem,
    const std::vector<CraigInvariantRegionSet>& invariantSets,
    const AuxiliaryStateInvariants& auxiliaryStateInvariants) {
  if (invariantSets.empty()) {
    return false;
  }

  std::unordered_set<size_t> trackedStates;
  for (const CraigInvariantRegionSet& invariantSet : invariantSets) {
    if (invariantSet.regions.empty()) {
      return false;
    }
    trackedStates.insert(
        invariantSet.trackedStates.begin(), invariantSet.trackedStates.end());
  }
  const auto states = stateSymbolSet(problem);
  for (const size_t symbol : problem.bad->getSupportVars()) {
    if (states.contains(symbol)) {
      trackedStates.insert(symbol);
    }
  }
  closeSameDesignStateSemantics(problem, trackedStates);
  if (trackedStates.empty()) {
    return false;
  }

  SATSolverWrapper solver(KEPLER_FORMAL::Config::SolverType::CADICAL);
  auto stateLits = allocateLeafLits(
      solver, sortedSymbols(trackedStates), VariablePartition::ALocal);
  addStateSemantics(solver, problem, stateLits, ClausePartition::A);
  addAuxiliaryStateInvariants(
      solver, stateLits, auxiliaryStateInvariants, ClausePartition::A);

  // Each set is one proved Craig invariant encoded as OR(regions).  Adding one
  // clause per set conjoins those proved invariants; the intersection is still
  // inductive and contains the reset frontier, but is often strong enough to
  // rule out later sibling outputs without another image computation.
  for (const CraigInvariantRegionSet& invariantSet : invariantSets) {
    std::vector<int> regionRoots;
    regionRoots.reserve(invariantSet.regions.size());
    for (const InterpolantRegion& region : invariantSet.regions) {
      regionRoots.push_back(instantiateRegion(
          solver,
          region,
          stateLits,
          VariablePartition::ALocal,
          ClausePartition::A));
    }
    solver.setCraigClausePartition(ClausePartition::A);
    solver.addClause(regionRoots);
  }
  addBadFormula(solver, problem, stateLits);
  return solver.solveStatus() == SATSolverWrapper::SolveStatus::Unsat;
}

std::unordered_set<size_t> computeCraigImcProjectionClosure(
    const KInductionProblem& problem,
    const std::unordered_set<size_t>& seedSupport) {
  const auto states = stateSymbolSet(problem);
  std::unordered_set<size_t> trackedStates;
  for (const size_t symbol : seedSupport) {
    if (states.contains(symbol)) {
      trackedStates.insert(symbol);
    }
  }
  closeSameDesignStateSemantics(problem, trackedStates);
  if (trackedStates.empty()) {
    return trackedStates;
  }

  const TransitionExprResolver resolver(problem);
  const auto complementPrimary = primaryByComplement(problem);
  for (size_t round = 0; round <= states.size(); ++round) {
    const size_t oldSize = trackedStates.size();
    const auto support = transitionProjectionSupport(
        problem, resolver, complementPrimary, trackedStates);
    trackedStates.insert(support.begin(), support.end());
    closeSameDesignStateSemantics(problem, trackedStates);
    if (trackedStates.size() == oldSize) {
      break;
    }
  }
  return trackedStates;
}

}  // namespace KEPLER_FORMAL::SEC
