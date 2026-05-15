// Copyright 2024-2026 keplertech.io
// SPDX-License-Identifier: GPL-3.0-only

#include "kinduction/KInductionEngine.h"

#include <algorithm>
#include <cstdlib>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/BoolExprUtils.h"
#include "common/SecDiag.h"
#include "kinduction/BaseCaseSolver.h"
#include "kinduction/InductionStepSolver.h"

namespace KEPLER_FORMAL::SEC {

namespace {

// SEC properties are a conjunction of observed-output equalities.  A single
// monolithic OR-of-all-bads query can still be too wide for ASIC netlists, but
// proving one output per solver call repeats the same problem copy, invariant
// setup, and SAT encoder startup hundreds of times.  The engine therefore uses
// bounded batches: combine nearby outputs while their direct property support
// stays small, and recursively split a batch if the combined k-induction query
// is inconclusive.  That keeps the proof obligation real while avoiding both
// extremes.
constexpr size_t kMaxOutputBatchSize = 32;
constexpr size_t kOutputBatchSupportLimit = 512;

bool isKInductionDiagEnabled() {
  return std::getenv("KEPLER_SEC_KI_DIAG") != nullptr || isSecDiagEnabled();
}

void emitKInductionProblemDiag(const KInductionProblem& problem,
                               size_t maxK) {
  if (!isKInductionDiagEnabled()) {
    return;
  }
  emitSecDiag(
      "SEC diag: k-induction problem outputs=",
      problem.observedOutputExprs0.size(),
      " state0=", problem.state0Symbols.size(),
      " state1=", problem.state1Symbols.size(),
      " initial_equalities=", problem.initialStateEqualityPairs.size(),
      " bootstrap_equalities=", problem.bootstrapStateEqualityPairs.size(),
      " inductive_equalities=", problem.inductiveStateEqualityPairs.size(),
      " reset_bootstrap_cycles=", problem.resetBootstrapCycles,
      " max_k=", maxK);
}

void configureOutputBatchProblem(KInductionProblem& batch,
                                 const KInductionProblem& source,
                                 size_t firstOutput,
                                 size_t endOutput) {
  if (source.observedOutputs.size() == source.observedOutputExprs0.size()) {
    batch.observedOutputs.assign(
        source.observedOutputs.begin() + firstOutput,
        source.observedOutputs.begin() + endOutput);
  } else {
    batch.observedOutputs.clear();
  }
  batch.observedOutputNames.assign(
      source.observedOutputNames.begin() + firstOutput,
      source.observedOutputNames.begin() + endOutput);
  batch.observedOutputExprs0.assign(
      source.observedOutputExprs0.begin() + firstOutput,
      source.observedOutputExprs0.begin() + endOutput);
  batch.observedOutputExprs1.assign(
      source.observedOutputExprs1.begin() + firstOutput,
      source.observedOutputExprs1.begin() + endOutput);

  // SEC output equality is a conjunction.  Proving smaller conjunctions and
  // combining the results is logically equivalent to one monolithic property,
  // while allowing the base/induction encoders to run COI on much smaller
  // output cones. This is especially important for gate-level ASICs with many
  // memory-backed state bits, where one OR-of-all-bads SAT query can drown
  // Kissat preprocessing in irrelevant equivalence classes.
  BoolExpr* property = BoolExpr::createTrue();
  for (size_t i = 0; i < batch.observedOutputExprs0.size(); ++i) {
    property = BoolExpr::And(
        property,
        makeEqualityExpr(batch.observedOutputExprs0[i], batch.observedOutputExprs1[i]));
  }
  batch.property = BoolExpr::simplify(property);
  batch.bad = BoolExpr::simplify(BoolExpr::Not(batch.property));

  // Recompute the induction obligation from the batch property.  The shared
  // structural/startup invariants stay in the problem as inductive equality
  // pairs, but output-specific SAT/abstract-map pruning from the monolithic
  // problem is intentionally not reused across a smaller property.
  batch.inductionProperty = nullptr;
  batch.inductionBad = nullptr;
  batch.description = source.description + " output batch";
}

void appendOutputSupport(const KInductionProblem& problem,
                         size_t outputIndex,
                         std::unordered_set<size_t>& support) {
  for (const auto symbol : problem.observedOutputExprs0[outputIndex]->getSupportVars()) {
    support.insert(symbol);
  }
  for (const auto symbol : problem.observedOutputExprs1[outputIndex]->getSupportVars()) {
    support.insert(symbol);
  }
}

std::vector<std::pair<size_t, size_t>> buildSupportBoundedOutputBatches(
    const KInductionProblem& problem) {
  std::vector<std::pair<size_t, size_t>> batches;
  size_t firstOutput = 0;
  std::unordered_set<size_t> batchSupport;
  batchSupport.reserve(kOutputBatchSupportLimit);

  while (firstOutput < problem.observedOutputExprs0.size()) {
    size_t endOutput = firstOutput;
    batchSupport.clear();
    while (endOutput < problem.observedOutputExprs0.size()) {
      std::unordered_set<size_t> candidateSupport = batchSupport;
      appendOutputSupport(problem, endOutput, candidateSupport);

      const bool batchAlreadyHasOutput = endOutput > firstOutput;
      const bool exceedsCount =
          endOutput - firstOutput + 1 > kMaxOutputBatchSize;
      const bool exceedsSupport =
          candidateSupport.size() > kOutputBatchSupportLimit;
      if (batchAlreadyHasOutput && (exceedsCount || exceedsSupport)) {
        break;
      }

      batchSupport = std::move(candidateSupport);
      ++endOutput;
    }
    batches.emplace_back(firstOutput, endOutput);
    firstOutput = endOutput;
  }

  return batches;
}

KInductionResult runMonolithicKInduction(const KInductionProblem& problem,
                                         KEPLER_FORMAL::Config::SolverType solverType,
                                         size_t maxK) {
  // Handle the purely combinational mismatch case before any unrolling.
  if (isKInductionDiagEnabled()) {
    emitSecDiag("SEC diag: k-induction base k=0 begin");
  }
  if (auto witness = SEC::findBaseCounterexample(problem, solverType, 0);
      witness.has_value()) {
    if (isKInductionDiagEnabled()) {
      emitSecDiag("SEC diag: k-induction base k=0 found cex");
    }
    return {KInductionStatus::Different, witness->badFrame, std::move(witness)};
  }
  if (isKInductionDiagEnabled()) {
    emitSecDiag("SEC diag: k-induction base k=0 unsat");
  }

  // If there is no state, the base check already decided the whole problem.
  if (problem.combinedStateSymbols().empty()) {
    return {KInductionStatus::Equivalent, 0};
  }

  // At the start of iteration k, all frames < k have already been proved safe
  // by the base checks below.  That is exactly the base obligation needed for
  // the k-step induction query "P[0]..P[k-1] => P[k]"; if the step closes, the
  // property is invariant and there is no reason to spend time on the frontier
  // BMC query for frame k. Only when the step is inconclusive do we extend the
  // concrete base horizon by checking the new frontier for a real counterexample.
  for (size_t k = 1; k <= maxK; ++k) {
    if (isKInductionDiagEnabled()) {
      emitSecDiag("SEC diag: k-induction step k=", k, " begin");
    }

    if (SEC::provesByInduction(problem, solverType, k)) {
      if (isKInductionDiagEnabled()) {
        emitSecDiag("SEC diag: k-induction step k=", k, " proved");
      }
      return {KInductionStatus::Equivalent, k};
    }
    if (isKInductionDiagEnabled()) {
      emitSecDiag("SEC diag: k-induction step k=", k, " inconclusive");
      emitSecDiag("SEC diag: k-induction base k=", k, " begin");
    }

    // Earlier base checks have already ruled out bad states on frames < k.
    // Check only the newly exposed frontier instead of re-solving an
    // OR-of-all-previous-bads query at every depth.
    if (auto witness = SEC::findBaseCounterexampleAtFrontier(
            problem, solverType, k);
        witness.has_value()) {
      if (isKInductionDiagEnabled()) {
        emitSecDiag("SEC diag: k-induction base k=", k, " found cex");
      }
      return {KInductionStatus::Different, witness->badFrame, std::move(witness)};
    }
    if (isKInductionDiagEnabled()) {
      emitSecDiag("SEC diag: k-induction base k=", k, " unsat");
    }
  }

  // Frontier checks are an optimization over the classic cumulative base case:
  // each iteration checks only the newly exposed bad frame because earlier
  // frames were already ruled out.  Before reporting inconclusive, run one
  // cumulative base query as a safety net so any interaction with reset
  // bootstrap offsets or observation-only startup semantics cannot hide a real
  // bounded counterexample.
  if (auto witness = SEC::findBaseCounterexample(problem, solverType, maxK);
      witness.has_value()) {
    return {KInductionStatus::Different, witness->badFrame, std::move(witness)};
  }

  return {KInductionStatus::Inconclusive, maxK};
}

KInductionResult combineBatchResults(KInductionResult lhs,
                                     const KInductionResult& rhs) {
  if (lhs.status == KInductionStatus::Different) {
    return lhs;  // LCOV_EXCL_LINE
  }
  if (rhs.status == KInductionStatus::Different) {
    return rhs;
  }
  if (rhs.status == KInductionStatus::Inconclusive) {
    lhs.status = KInductionStatus::Inconclusive;
  }
  lhs.bound = std::max(lhs.bound, rhs.bound);
  return lhs;
}

KInductionResult runOutputRangeKInduction(
    KInductionProblem& batchProblem,
    const KInductionProblem& sourceProblem,
    KEPLER_FORMAL::Config::SolverType solverType,
    size_t maxK,
    size_t firstOutput,
    size_t endOutput) {
  configureOutputBatchProblem(batchProblem, sourceProblem, firstOutput, endOutput);
  const KInductionResult result =
      runMonolithicKInduction(batchProblem, solverType, maxK);
  if (result.status != KInductionStatus::Inconclusive ||
      endOutput - firstOutput <= 1) {
    return result;
  }

  // A conjunction can occasionally be harder for k-induction than its pieces.
  // Split only on inconclusive batches, so successful wide proofs stay fast and
  // difficult cases fall back to the previous fine-grained behavior.
  const size_t middle = firstOutput + (endOutput - firstOutput) / 2;
  KInductionResult combined =
      runOutputRangeKInduction(
          batchProblem, sourceProblem, solverType, maxK, firstOutput, middle);
  if (combined.status == KInductionStatus::Different) {
    return combined;
  }
  return combineBatchResults(
      std::move(combined),
      runOutputRangeKInduction(
          batchProblem, sourceProblem, solverType, maxK, middle, endOutput));
}

KInductionResult runOutputBatchedKInduction(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    size_t maxK) {
  emitKInductionProblemDiag(problem, maxK);
  KInductionResult combined{KInductionStatus::Equivalent, 0};
  // Copy the large shared SEC problem once, then mutate only the small
  // output/property slice for each batch.  The previous implementation copied
  // hundreds of thousands of state symbols and equality pairs per batch, which
  // became visible on BlackParrot even after SAT-side batching was effective.
  KInductionProblem batchProblem = problem;
  for (const auto& [firstOutput, endOutput] :
       buildSupportBoundedOutputBatches(problem)) {
    const KInductionResult result = runOutputRangeKInduction(
        batchProblem, problem, solverType, maxK, firstOutput, endOutput);
    if (result.status == KInductionStatus::Different) {
      return result;
    }
    if (result.status == KInductionStatus::Inconclusive) {
      combined.status = KInductionStatus::Inconclusive;
    }
    combined.bound = std::max(combined.bound, result.bound);
  }
  return combined;
}

}  // namespace

// Overall k-induction algorithm:
// 1. Check frame 0 immediately for a purely combinational mismatch.
// 2. If the SEC problem has no state, that base check fully decides it.
// 3. For k = 1..maxK, first ask whether the k-step induction rule closes from
//    the already-proved safe prefix.
// 4. If the step is inconclusive, extend the safe prefix by checking the next
//    concrete base frontier for a counterexample.
// 5. Return the first counterexample, the first successful proof bound, or
//    "inconclusive" if neither happens within the requested budget.

KInductionEngine::KInductionEngine(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType)
    : problem_(problem), solverType_(solverType) {}

KInductionResult KInductionEngine::run(size_t maxK) const {
  if (problem_.observedOutputExprs0.size() <= 1) {
    emitKInductionProblemDiag(problem_, maxK);
  }
  if (problem_.observedOutputExprs0.size() > 1) {
    return runOutputBatchedKInduction(problem_, solverType_, maxK);
  }
  return runMonolithicKInduction(problem_, solverType_, maxK);
}

std::optional<KInductionResult::CounterexampleWitness>
KInductionEngine::findBaseCounterexample(size_t k) const {
  // The base case is delegated to the shared SEC BMC solver so every engine
  // reports the same witness shape and frame numbering.
  return SEC::findBaseCounterexample(problem_, solverType_, k);
}

bool KInductionEngine::provesByInduction(size_t k) const {
  // The induction step is delegated as well so all k-induction-based engines
  // rely on one simple-path SAT encoding.
  return SEC::provesByInduction(problem_, solverType_, k);
}

}  // namespace KEPLER_FORMAL::SEC
