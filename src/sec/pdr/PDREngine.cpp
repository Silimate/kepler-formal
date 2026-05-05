// Copyright 2024-2026 keplertech.io
// SPDX-License-Identifier: GPL-3.0-only

#include "pdr/PDREngine.h"

#include <algorithm>
#include <cstdlib>
#include <optional>
#include <sstream>
#include <unordered_map>
#include <string_view>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/ProofProblemDebug.h"
#include "common/SecDiag.h"
#include "proof/ProofEngineShared.h"
#include "kinduction/SatEncoding.h"

namespace KEPLER_FORMAL::SEC {

// Overall PDR algorithm:
// 1. Build Init from the SEC startup constraints and reuse any already
//    validated strengthening invariant when it is sound to do so.
// 2. Maintain frames F[0], F[1], ... where each frame stores clauses known to
//    hold for all states reachable within that many steps.
// 3. At each level, ask whether a bad state still survives the current frame.
// 4. If so, recursively search for predecessors until either Init is reached
//    (real counterexample) or the bad cube is blocked by a learned clause.
// 5. Generalize learned blocking clauses, add them to all earlier frames, and
//    then propagate them forward when the transition relation preserves them.
// 6. Stop once two adjacent frames converge, when a real bug is found, or when
//    the requested frame budget is exhausted.

namespace {

// Cubes represent a concrete bad/predecessor state, while clauses are the
// blocked generalization of such a state stored in a PDR frame.
struct CubeLiteral {
  size_t symbol = 0;
  bool value = false;

  bool operator==(const CubeLiteral& other) const {
    return symbol == other.symbol && value == other.value;
  }
};

struct ClauseLiteral {
  size_t symbol = 0;
  bool positive = false;

  bool operator==(const ClauseLiteral& other) const {
    return symbol == other.symbol && positive == other.positive;
  }
};

using StateCube = std::vector<CubeLiteral>;
using StateClause = std::vector<ClauseLiteral>;

struct FrameClauses {
  // F[i] stores clauses known to hold for all states reachable within i steps.
  std::vector<StateClause> clauses;
};

struct ProofObligation {
  // "cube is bad at level" requests either a predecessor or a blocking clause.
  StateCube cube;
  size_t level = 0;
  size_t badFrame = 0;
};

void addComplementedStateRelations(
    SATSolverWrapper& solver,
    const FrameVariableStore& variables,
    const std::vector<std::pair<size_t, size_t>>& complementedStatePairs,
    size_t numFrames);

void addTransitionRelation(SATSolverWrapper& solver,
                           const FrameVariableStore& variables,
                           const KInductionProblem& problem,
                           size_t frame);

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
    primaryByComplement.emplace(complementedSymbol, primarySymbol);  // LCOV_EXCL_LINE
  }
  for (const auto& [primarySymbol, complementedSymbol] :
       problem.complementedStatePairs1) {
    primaryByComplement.emplace(complementedSymbol, primarySymbol);  // LCOV_EXCL_LINE
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

std::vector<size_t> sortUniqueSymbols(std::unordered_set<size_t> symbols) {
  std::vector<size_t> ordered(symbols.begin(), symbols.end());
  std::sort(ordered.begin(), ordered.end());
  ordered.erase(std::unique(ordered.begin(), ordered.end()), ordered.end());
  return ordered;
}

std::vector<size_t> collectStateSupportSymbols(
    const KInductionProblem& problem,
    BoolExpr* formula) {
  if (formula == nullptr) {
    return {};  // LCOV_EXCL_LINE
  }

  const auto stateSymbolSet = buildCombinedStateSymbolSet(problem);
  std::unordered_set<size_t> support;
  for (const auto symbol : formula->getSupportVars()) {
    if (stateSymbolSet.find(symbol) != stateSymbolSet.end()) {
      support.insert(symbol);
    }
  }
  return sortUniqueSymbols(std::move(support));
}

std::vector<size_t> expandTransitionTargets(
    const KInductionProblem& problem,
    const std::vector<size_t>& requestedTargets,
    const std::unordered_map<size_t, BoolExpr*>& transitionExprByStateSymbol) {
  const auto primaryByComplement = buildComplementPrimaryByStateSymbol(problem);
  std::unordered_set<size_t> targets;
  targets.reserve(requestedTargets.size());

  for (const auto symbol : requestedTargets) {
    if (transitionExprByStateSymbol.find(symbol) !=
        transitionExprByStateSymbol.end()) {
      targets.insert(symbol);
      continue;
    }

    // Complemented flop outputs are constrained through the primary flop. If a
    // cube talks only about the complemented bit, encode the primary transition
    // and let the complemented-state relation connect the two next-frame bits.
    if (const auto primaryIt = primaryByComplement.find(symbol);  // LCOV_EXCL_LINE
        primaryIt != primaryByComplement.end() &&  // LCOV_EXCL_LINE
        transitionExprByStateSymbol.find(primaryIt->second) !=  // LCOV_EXCL_LINE
            transitionExprByStateSymbol.end()) {  // LCOV_EXCL_LINE
      targets.insert(primaryIt->second);  // LCOV_EXCL_LINE
    }
  }

  return sortUniqueSymbols(std::move(targets));
}

std::vector<size_t> cubeStateSymbols(const StateCube& cube) {
  std::unordered_set<size_t> symbols;
  symbols.reserve(cube.size());
  for (const auto& literal : cube) {
    symbols.insert(literal.symbol);
  }
  return sortUniqueSymbols(std::move(symbols));
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

std::vector<size_t> predecessorProjectionSymbols(
    const KInductionProblem& problem,
    const StateCube& targetCube) {
  const auto transitionExprByStateSymbol =
      buildTransitionExprByStateSymbol(problem);
  const auto encodedTargets = expandTransitionTargets(
      problem, cubeStateSymbols(targetCube), transitionExprByStateSymbol);
  const auto stateSymbolSet = buildCombinedStateSymbolSet(problem);

  std::unordered_set<size_t> projection;
  for (const auto target : encodedTargets) {
    for (const auto symbol :
         transitionExprByStateSymbol.at(target)->getSupportVars()) {
      if (stateSymbolSet.find(symbol) != stateSymbolSet.end()) {
        projection.insert(symbol);
      }
    }
  }
  return sortUniqueSymbols(std::move(projection));
}

void addComplementedStateRelations(
    SATSolverWrapper& solver,
    const FrameVariableStore& variables,
    const std::vector<std::pair<size_t, size_t>>& complementedStatePairs,
    size_t numFrames) {
  for (size_t frame = 0; frame < numFrames; ++frame) {
    for (const auto& [primarySymbol, complementedSymbol] : complementedStatePairs) {  // LCOV_EXCL_LINE
      addLiteralEquivalence(  // LCOV_EXCL_LINE
          solver,  // LCOV_EXCL_LINE
          variables.getLiteral(complementedSymbol, frame),  // LCOV_EXCL_LINE
          -variables.getLiteral(primarySymbol, frame));  // LCOV_EXCL_LINE
    }
  }
}

void addTransitionRelation(SATSolverWrapper& solver,
                           const FrameVariableStore& variables,
                           const KInductionProblem& problem,
                           size_t frame) {
  FrameFormulaEncoder encoder(solver, variables.makeLeafLits(frame));
  for (const auto& [stateSymbol, expr] : problem.transitions0) {
    addLiteralEquivalence(
        solver,
        variables.getLiteral(stateSymbol, frame + 1),
        encoder.encode(expr));
  }
  for (const auto& [stateSymbol, expr] : problem.transitions1) {
    addLiteralEquivalence(
        solver,
        variables.getLiteral(stateSymbol, frame + 1),
        encoder.encode(expr));
  }
}

void normalizeCube(StateCube& cube) {
  // Canonical ordering lets us compare cubes structurally and avoid learning
  // the same obligation more than once with a different literal order.
  std::sort(cube.begin(), cube.end(), [](const CubeLiteral& lhs, const CubeLiteral& rhs) {
    if (lhs.symbol != rhs.symbol) {
      return lhs.symbol < rhs.symbol;
    }
    return lhs.value < rhs.value;  // LCOV_EXCL_LINE
  });
  cube.erase(std::unique(cube.begin(), cube.end()), cube.end());
}

void normalizeClause(StateClause& clause) {
  // Clauses are canonicalized for the same reason: later subsumption and
  // convergence checks depend on stable ordering and deduplication.
  std::sort(
      clause.begin(), clause.end(), [](const ClauseLiteral& lhs, const ClauseLiteral& rhs) {
        if (lhs.symbol != rhs.symbol) {
          return lhs.symbol < rhs.symbol;
        }
        return lhs.positive < rhs.positive;  // LCOV_EXCL_LINE
      });
  clause.erase(std::unique(clause.begin(), clause.end()), clause.end());
}

StateClause clauseFromCube(const StateCube& cube) {
  StateClause clause;
  clause.reserve(cube.size());
  for (const auto& literal : cube) {
    clause.push_back({literal.symbol, !literal.value});
  }
  normalizeClause(clause);
  return clause;
}

StateCube cubeFromClauseNegation(const StateClause& clause) {
  StateCube cube;
  cube.reserve(clause.size());
  for (const auto& literal : clause) {
    cube.push_back({literal.symbol, !literal.positive});
  }
  normalizeCube(cube);
  return cube;
}

bool clauseSubsumes(const StateClause& lhs, const StateClause& rhs) {
  return std::includes(rhs.begin(), rhs.end(), lhs.begin(), lhs.end(),
                       [](const ClauseLiteral& a, const ClauseLiteral& b) {
                         if (a.symbol != b.symbol) {
                           return a.symbol < b.symbol;
                         }
                         return a.positive < b.positive;
                       });
}

bool frameHasSubsumingClause(const FrameClauses& frame, const StateClause& clause) {
  for (const auto& existingClause : frame.clauses) {
    if (clauseSubsumes(existingClause, clause)) {
      return true;
    }
  }
  return false;
}

void addClauseToFrame(FrameClauses& frame, StateClause clause) {
  normalizeClause(clause);
  if (frameHasSubsumingClause(frame, clause)) {
    return;
  }

  // Keep each frame minimal so later SAT queries do not carry redundant facts.
  frame.clauses.erase(
      std::remove_if(
          frame.clauses.begin(),
          frame.clauses.end(),
          [&](const StateClause& existingClause) {
            return clauseSubsumes(clause, existingClause);
          }),
      frame.clauses.end());
  frame.clauses.push_back(std::move(clause));
}

void addClauseToFrames(std::vector<FrameClauses>& frames,
                       const StateClause& clause,
                       size_t maxLevel) {
  for (size_t level = 1; level <= maxLevel; ++level) {
    addClauseToFrame(frames[level], clause);
  }
}

void addStateClause(SATSolverWrapper& solver,
                    const FrameVariableStore& variables,
                    const StateClause& clause,
                    size_t frame) {
  std::vector<int> satClause;
  satClause.reserve(clause.size());
  for (const auto& literal : clause) {
    const int satLiteral = variables.getLiteral(literal.symbol, frame);
    satClause.push_back(literal.positive ? satLiteral : -satLiteral);
  }
  solver.addClause(satClause);
}

void addCubeAssumptions(SATSolverWrapper& solver,
                        const FrameVariableStore& variables,
                        const StateCube& cube,
                        size_t frame) {
  for (const auto& literal : cube) {
    solver.addClause(
        {literal.value ? variables.getLiteral(literal.symbol, frame)
                       : -variables.getLiteral(literal.symbol, frame)});
  }
}

void addNegatedCubeClause(SATSolverWrapper& solver,
                          const FrameVariableStore& variables,
                          const StateCube& cube,
                          size_t frame) {
  std::vector<int> satClause;
  satClause.reserve(cube.size());
  for (const auto& literal : cube) {
    const int satLiteral = variables.getLiteral(literal.symbol, frame);
    satClause.push_back(literal.value ? -satLiteral : satLiteral);
  }
  solver.addClause(satClause);
}

void addFrameConstraints(SATSolverWrapper& solver,
                         const FrameVariableStore& variables,
                         BoolExpr* initFormula,
                         BoolExpr* frameInvariant,
                         const std::vector<FrameClauses>& frames,
                         size_t level,
                         size_t frame) {
  if (level == 0) {
    // F[0] is Init, so the SAT query is anchored directly in the startup
    // frontier rather than in learned blocking clauses.
    FrameFormulaEncoder encoder(solver, variables.makeLeafLits(frame));
    solver.addClause({encoder.encode(initFormula)});
    return;
  }

  // For higher frames, materialize the currently learned blocking clauses and
  // any validated strengthening invariant the strategy handed to PDR.
  for (const auto& clause : frames[level].clauses) {
    addStateClause(solver, variables, clause, frame);
  }
  if (frameInvariant != nullptr) {
    // The optional strengthening is treated exactly like a frame fact, but it
    // is validated before we allow the engine to rely on it.
    FrameFormulaEncoder encoder(solver, variables.makeLeafLits(frame));  // LCOV_EXCL_LINE
    solver.addClause({encoder.encode(frameInvariant)});  // LCOV_EXCL_LINE
  }
}

StateCube extractStateCube(const SATSolverWrapper& solver,
                           const FrameVariableStore& variables,
                           const std::vector<size_t>& stateSymbols,
                           size_t frame) {
  StateCube cube;
  cube.reserve(stateSymbols.size());
  for (const auto symbol : stateSymbols) {
    cube.push_back({symbol, solver.getLiteralValue(variables.getLiteral(symbol, frame))});
  }
  normalizeCube(cube);
  return cube;
}

std::optional<StateCube> findBadCube(const KInductionProblem& problem,
                                     KEPLER_FORMAL::Config::SolverType solverType,
                                     BoolExpr* initFormula,
                                     BoolExpr* frameInvariant,
                                     const std::vector<FrameClauses>& frames,
                                     size_t level) {
  // Search the current frame for a concrete state that still satisfies bad
  // after all learned blocking clauses and optional strengthening are applied.
  SATSolverWrapper solver(solverType);
  FrameVariableStore variables(solver, problem.allSymbols, 1);
  addComplementedStateRelations(solver, variables, problem.complementedStatePairs0, 1);
  addComplementedStateRelations(solver, variables, problem.complementedStatePairs1, 1);
  addFrameConstraints(
      solver, variables, initFormula, frameInvariant, frames, level, 0);
  FrameFormulaEncoder encoder(solver, variables.makeLeafLits(0));
  solver.addClause({encoder.encode(problem.bad)});
  if (!solver.solve()) {
    return std::nullopt;
  }

  // A PDR cube only needs to mention the state bits that the bad predicate
  // actually observes. Extracting every state bit is sound but disastrous on
  // memory-rich designs such as CVA6 because every later blocking query would
  // carry a full-register snapshot.
  return extractStateCube(
      solver, variables, collectStateSupportSymbols(problem, problem.bad), 0);
}

std::optional<StateCube> findPredecessorCube(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    BoolExpr* initFormula,
    BoolExpr* frameInvariant,
    const std::vector<FrameClauses>& frames,
    size_t level,
    const StateCube& targetCube,
    bool excludeTargetOnCurrentFrame) {
  // This is the one-step predecessor query at the heart of PDR: does some
  // state in F[level] transition into the target cube on the next frame?
  SATSolverWrapper solver(solverType);
  FrameVariableStore variables(solver, problem.allSymbols, 2);
  addComplementedStateRelations(solver, variables, problem.complementedStatePairs0, 2);
  addComplementedStateRelations(solver, variables, problem.complementedStatePairs1, 2);
  addFrameConstraints(
      solver, variables, initFormula, frameInvariant, frames, level, 0);
  // Encode only the next-state equations needed to decide the requested target
  // cube. This keeps one local PDR obligation from materializing the entire
  // design transition relation.
  addTransitionRelationForTargets(
      solver, variables, problem, 0, cubeStateSymbols(targetCube));
  addCubeAssumptions(solver, variables, targetCube, 1);
  if (excludeTargetOnCurrentFrame) {
    addNegatedCubeClause(solver, variables, targetCube, 0);
  }
  if (!solver.solve()) {
    return std::nullopt;
  }

  // The predecessor cube is projected onto the current-state support of the
  // target transitions. Inputs stay existential, and unrelated flops stay out
  // of the learned obligation instead of ballooning every clause.
  return extractStateCube(
      solver, variables, predecessorProjectionSymbols(problem, targetCube), 0);
}

bool cubeIntersectsInit(const KInductionProblem& problem,
                        KEPLER_FORMAL::Config::SolverType solverType,
                        BoolExpr* initFormula,
                        const StateCube& cube) {
  // A clause is only safe to learn if its negated cube stays outside Init.
  SATSolverWrapper solver(solverType);
  FrameVariableStore variables(solver, problem.allSymbols, 1);
  addComplementedStateRelations(solver, variables, problem.complementedStatePairs0, 1);
  addComplementedStateRelations(solver, variables, problem.complementedStatePairs1, 1);
  FrameFormulaEncoder encoder(solver, variables.makeLeafLits(0));
  solver.addClause({encoder.encode(initFormula)});
  addCubeAssumptions(solver, variables, cube, 0);
  return solver.solve();
}

StateCube generalizeBlockedCube(const KInductionProblem& problem,
                                KEPLER_FORMAL::Config::SolverType solverType,
                                BoolExpr* initFormula,
                                BoolExpr* frameInvariant,
                                const std::vector<FrameClauses>& frames,
                                size_t level,
                                const StateCube& cube) {
  // Greedy clause generalization: drop literals that are unnecessary for
  // blocking and not needed to keep the cube outside Init.
  StateCube candidate = cube;
  size_t index = 0;
  while (index < candidate.size()) {
    StateCube reduced = candidate;
    reduced.erase(reduced.begin() + static_cast<std::ptrdiff_t>(index));
    if (cubeIntersectsInit(problem, solverType, initFormula, reduced)) {
      ++index;
      continue;
    }
    if (!findPredecessorCube(
             problem,
             solverType,
             initFormula,
             frameInvariant,
             frames,
             level - 1,
             reduced,
             true)
             .has_value()) {
      candidate = std::move(reduced);
      continue;
    }
    ++index;
  }
  return candidate;
}

bool framesConverged(const FrameClauses& lhs, const FrameClauses& rhs) {
  if (lhs.clauses.size() != rhs.clauses.size()) {
    return false;
  }
  for (const auto& clause : lhs.clauses) {
    if (!frameHasSubsumingClause(rhs, clause)) {
      return false;  // LCOV_EXCL_LINE
    }
  }
  for (const auto& clause : rhs.clauses) {
    if (!frameHasSubsumingClause(lhs, clause)) {
      return false;  // LCOV_EXCL_LINE
    }
  }
  return true;
}

bool obligationAlreadyBlocked(const std::vector<FrameClauses>& frames,
                              const ProofObligation& obligation) {
  return frameHasSubsumingClause(frames[obligation.level], clauseFromCube(obligation.cube));  // LCOV_EXCL_LINE
}

size_t popNextObligationIndex(const std::vector<ProofObligation>& queue) {
  size_t bestIndex = 0;
  for (size_t i = 1; i < queue.size(); ++i) {
    if (queue[i].level < queue[bestIndex].level ||
        (queue[i].level == queue[bestIndex].level &&
         queue[i].badFrame < queue[bestIndex].badFrame)) {
      bestIndex = i;
    }
  }
  return bestIndex;
}

bool blockProofObligations(const KInductionProblem& problem,
                           KEPLER_FORMAL::Config::SolverType solverType,
                           BoolExpr* initFormula,
                           BoolExpr* frameInvariant,
                           std::vector<FrameClauses>& frames,
                           const StateCube& rootCube,
                           size_t rootLevel,
                           size_t& badFrame) {
  // This is the paper's recursive blocking idea expressed as an explicit queue
  // so we do not depend on deep recursion for large obligation stacks.
  std::vector<ProofObligation> queue = {{{rootCube, rootLevel, rootLevel}}};

  while (!queue.empty()) {
    const size_t obligationIndex = popNextObligationIndex(queue);
    const ProofObligation obligation = queue[obligationIndex];
    queue.erase(queue.begin() + static_cast<std::ptrdiff_t>(obligationIndex));

    if (obligationAlreadyBlocked(frames, obligation)) {
      continue;
    }

    if (obligation.level == 0) {
      badFrame = obligation.badFrame;
      return false;
    }

    if (const auto predecessor = findPredecessorCube(
            problem,
            solverType,
            initFormula,
            frameInvariant,
            frames,
            obligation.level - 1,
            obligation.cube,
            false);
        predecessor.has_value()) {
      queue.push_back(obligation);
      queue.push_back({*predecessor, obligation.level - 1, obligation.badFrame});
      continue;
    }

    // No predecessor survives F[level-1], so the cube can be blocked at every
    // frame up to "level" after a small literal-dropping generalization pass.
    const StateCube generalizedCube = generalizeBlockedCube(
        problem,
        solverType,
        initFormula,
        frameInvariant,
        frames,
        obligation.level,
        obligation.cube);
    addClauseToFrames(frames, clauseFromCube(generalizedCube), obligation.level);
    if (obligation.level < obligation.badFrame) {
      queue.push_back({generalizedCube, obligation.level + 1, obligation.badFrame});
    }
  }

  return true;
}

std::vector<StateClause> buildSeedClauses(const KInductionProblem& problem,
                                          KEPLER_FORMAL::Config::SolverType solverType,
                                          BoolExpr* initFormula) {
  std::vector<StateClause> seedClauses;
  // Seed the first learned frame with state equalities that are already
  // guaranteed by Init/bootstrap, so PDR starts from facts that are known
  // reachable-state invariants instead of rediscovering them from scratch.
  for (const auto& [lhsSymbol, rhsSymbol] : problem.inductiveStateEqualityPairs) {
    StateClause clause0 = {{lhsSymbol, false}, {rhsSymbol, true}};  // LCOV_EXCL_LINE
    StateClause clause1 = {{lhsSymbol, true}, {rhsSymbol, false}};  // LCOV_EXCL_LINE
    normalizeClause(clause0);  // LCOV_EXCL_LINE
    normalizeClause(clause1);  // LCOV_EXCL_LINE

    // Promote already-anchored state equalities into initial frame facts when
    // they are guaranteed by Init/bootstrap instead of guessed from structure.
    if (!cubeIntersectsInit(problem, solverType, initFormula, cubeFromClauseNegation(clause0))) {  // LCOV_EXCL_LINE
      seedClauses.push_back(clause0);  // LCOV_EXCL_LINE
    }  // LCOV_EXCL_LINE
    if (!cubeIntersectsInit(problem, solverType, initFormula, cubeFromClauseNegation(clause1))) {  // LCOV_EXCL_LINE
      seedClauses.push_back(clause1);  // LCOV_EXCL_LINE
    }  // LCOV_EXCL_LINE
  }
  return seedClauses;
}

void propagateClauses(const KInductionProblem& problem,
                      KEPLER_FORMAL::Config::SolverType solverType,
                      BoolExpr* initFormula,
                      BoolExpr* frameInvariant,
                      std::vector<FrameClauses>& frames,
                      size_t maxLevel) {
  // Standard PDR propagation: if F[i] /\ T implies a clause on the next frame,
  // move that clause forward into F[i+1].
  for (size_t level = 1; level <= maxLevel; ++level) {
    const auto snapshot = frames[level].clauses;
    for (const auto& clause : snapshot) {
      // Only propagate clauses that are not already known to hold on the next frame,
      // otherwise we would be doing redundant work and risking over-blocking by
      // adding the same clause again after generalization.
      if (frameHasSubsumingClause(frames[level + 1], clause)) {
        continue;
      }
      const StateCube violatingCube = cubeFromClauseNegation(clause);
      // A clause is only safe to propagate if it does not block a real bad path, so check
      // whether any predecessor of the negated cube survives in the current frame. If not, the
      // clause can be added to the next frame without risking over-blocking.
      if (!findPredecessorCube(
               problem,
               solverType,
               initFormula,
               frameInvariant,
               frames,
               level,
               violatingCube,
               false)
               .has_value()) {
        addClauseToFrame(frames[level + 1], clause);
      }
    }
  }
}

bool isSecPdrTraceEnabled() {
  return std::getenv("KEPLER_SEC_PDR_TRACE") != nullptr;
}

std::string formatSymbolForPdrTrace(size_t symbol) {
  if (symbol == 0) {
    return "FALSE";  // LCOV_EXCL_LINE
  }
  if (symbol == 1) {
    return "TRUE";  // LCOV_EXCL_LINE
  }
  return "x" + std::to_string(symbol);
}

std::string formatCubeForPdrTrace(const StateCube& cube) {
  std::ostringstream oss;
  oss << "{";
  for (size_t i = 0; i < cube.size(); ++i) {
    if (i != 0) {
      oss << ", ";
    }
    oss << formatSymbolForPdrTrace(cube[i].symbol) << "=" << (cube[i].value ? "1" : "0");
  }
  oss << "}";
  return oss.str();
}

std::string formatClauseForPdrTrace(const StateClause& clause) {
  std::ostringstream oss;
  oss << "(";
  for (size_t i = 0; i < clause.size(); ++i) {
    if (i != 0) {
      oss << " OR ";
    }
    if (!clause[i].positive) {
      oss << "!";
    }
    oss << formatSymbolForPdrTrace(clause[i].symbol);
  }
  oss << ")";
  return oss.str();
}

std::string formatFramesForPdrTrace(const std::vector<FrameClauses>& frames) {
  std::ostringstream oss;
  for (size_t level = 0; level < frames.size(); ++level) {
    oss << "  F[" << level << "]: ";
    if (level == 0) {
      oss << "Init";
    }
    oss << "\n";
    if (frames[level].clauses.empty()) {
      oss << "    <empty>\n";
      continue;
    }
    for (const auto& clause : frames[level].clauses) {
      oss << "    " << formatClauseForPdrTrace(clause) << "\n";
    }
  }
  return oss.str();
}

void emitPdrTrace(std::string_view label, const std::string& body) {
  if (!isSecPdrTraceEnabled()) {
    return;
  }
  emitSecDiag("SEC PDR trace: ", label, "\n", body);
}

void emitPdrTraceProblem(const KInductionProblem& problem) {
  emitPdrTrace("problem", formatKInductionProblemForDebug(problem));
}

void emitPdrTraceFrames(std::string_view label,
                        const std::vector<FrameClauses>& frames) {
  emitPdrTrace(label, formatFramesForPdrTrace(frames));
}

std::optional<PDRResult> tryImmediatePdrProofCandidate(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    BoolExpr* initFormula,
    BoolExpr* candidate,
    BoolExpr*& frameInvariant) {
  if (candidate == nullptr ||
      !initialFrontierImplies(initFormula, candidate, solverType) ||
      !isInductiveInvariant(problem, candidate, solverType)) {
    return std::nullopt;
  }

  if (invariantExcludesBadStates(problem, candidate, solverType)) {
    // If the strategy already synthesized a sound inductive strengthening, the
    // new engine can accept that proof immediately instead of rediscovering it.
    return PDRResult{PDRStatus::Equivalent, 1};
  }

  // Otherwise the candidate is a safe frame fact, even if it is not by itself
  // enough to prove the full SEC property.
  if (frameInvariant == nullptr) {  // LCOV_EXCL_LINE
    frameInvariant = candidate;  // LCOV_EXCL_LINE
  }
  return std::nullopt;
}

std::optional<PDRResult> runPdrImmediateChecks(const KInductionProblem& problem,
                                               KEPLER_FORMAL::Config::SolverType solverType,
                                               BoolExpr* initFormula,
                                               BoolExpr*& frameInvariant) {
  // Before entering the clause loop, try any reusable proof candidates the SEC
  // strategy already built. A candidate is only safe to inject into every PDR
  // frame once it is known to be inductive; otherwise it would over-constrain
  // the search and could hide a real counterexample.
  if (const auto proof = tryImmediatePdrProofCandidate(
          problem,
          solverType,
          initFormula,
          selectValidatedStrengtheningInvariant(problem, initFormula, solverType),
          frameInvariant);
      proof.has_value()) {
    return proof;  // LCOV_EXCL_LINE
  }

  // Keep PDR aligned with IMC: if the plain SEC property is already inductive
  // from the startup frontier, there is no reason to spend time blocking cubes.
  if (const auto proof = tryImmediatePdrProofCandidate(
          problem, solverType, initFormula, problem.property, frameInvariant);
      proof.has_value()) {
    return proof;
  }

  return std::nullopt;
}

}  // namespace

PDREngine::PDREngine(const KInductionProblem& problem,
                     KEPLER_FORMAL::Config::SolverType solverType)
    : problem_(problem), solverType_(solverType) {}

PDRResult PDREngine::run(size_t maxFrames) const {
  // Build the SEC startup frontier once so every frame query shares the same
  // interpretation of reset/bootstrap and frame-0 equality constraints.
  emitPdrTraceProblem(problem_);
  BoolExpr* initFormula = buildProofInitFormula(problem_);
  if (initFormula == nullptr) {
    return {PDRStatus::Inconclusive, 0};
  }

  BoolExpr* frameInvariant = nullptr;
  if (const auto proof =
          runPdrImmediateChecks(problem_, solverType_, initFormula, frameInvariant);
      proof.has_value()) {
    return *proof;
  }

  std::vector<FrameClauses> frames(1);
  emitPdrTraceFrames("initial_frames", frames);

  // Before growing any frame sequence, check whether Init itself already
  // contains a bad state.
  if (auto badCube = findBadCube(
          problem_, solverType_, initFormula, frameInvariant, frames, 0);
      badCube.has_value()) {
    emitPdrTrace("bad_cube@F0", formatCubeForPdrTrace(*badCube));  // LCOV_EXCL_LINE
    return {PDRStatus::Different, 0};  // LCOV_EXCL_LINE
  }

  if (maxFrames == 0) {
    return {PDRStatus::Inconclusive, 0};  // LCOV_EXCL_LINE
  }

  const auto seedClauses = buildSeedClauses(problem_, solverType_, initFormula);
  frames.emplace_back(FrameClauses{seedClauses});
  emitPdrTraceFrames("seeded_frames", frames);
  for (size_t level = 1; level <= maxFrames; ++level) {
    // Phase 1: exhaust the proof obligations created by bad states that still
    // survive in the current frontier.
    while (true) {
      const auto badCube =
          findBadCube(
              problem_, solverType_, initFormula, frameInvariant, frames, level);
      if (!badCube.has_value()) {
        break;
      }
      emitPdrTrace(("bad_cube@F" + std::to_string(level)).c_str(),
                   formatCubeForPdrTrace(*badCube));
      size_t badFrame = level;
      if (!blockProofObligations(
              problem_,
              solverType_,
              initFormula,
              frameInvariant,
              frames,
              *badCube,
              level,
              badFrame)) {
        emitPdrTraceFrames("frames_before_counterexample", frames);  // LCOV_EXCL_LINE
        return {PDRStatus::Different, badFrame};  // LCOV_EXCL_LINE
      }
      emitPdrTraceFrames("frames_after_blocking", frames);
    }

    // Phase 2: create the next frame, seed it with already-known startup
    // facts
    frames.emplace_back(FrameClauses{seedClauses});
    // and then try to push learned clauses forward.
    // We push in order to reach covergence and the condition is that that 
    // the clause is not preventing an actual bad path
    propagateClauses(
        problem_, solverType_, initFormula, frameInvariant, frames, level);
    emitPdrTraceFrames(("frames_after_propagation@F" + std::to_string(level)).c_str(),
                       frames);

    // Phase 3: convergence means F[i] == F[i+1], so the frame has become an
    // inductive invariant and the SEC property is proved.
    for (size_t convergenceLevel = 1; convergenceLevel <= level; ++convergenceLevel) {
      if (framesConverged(frames[convergenceLevel], frames[convergenceLevel + 1])) {
        emitPdrTraceFrames(
            ("frames_converged@F" + std::to_string(convergenceLevel)).c_str(), frames);
        return {PDRStatus::Equivalent, convergenceLevel};
      }
    }
  }

  return {PDRStatus::Inconclusive, maxFrames};  // LCOV_EXCL_LINE
}

}  // namespace KEPLER_FORMAL::SEC
