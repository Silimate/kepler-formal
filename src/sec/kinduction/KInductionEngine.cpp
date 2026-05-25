// Copyright 2024-2026 keplertech.io
// SPDX-License-Identifier: GPL-3.0-only

#include "kinduction/KInductionEngine.h"

#include <algorithm>
#include <cstdlib>
#include <utility>

#include "common/SecDiag.h"
#include "kinduction/BaseCaseSolver.h"
#include "kinduction/InductionStepSolver.h"
#include "kinduction/OutputBatching.h"

namespace KEPLER_FORMAL::SEC {

namespace {

bool isKInductionDiagEnabled() {
  return std::getenv("KEPLER_SEC_KI_DIAG") != nullptr || isSecDiagEnabled();
}

bool isFrontierFirstEnabled() {
  return std::getenv("KEPLER_SEC_KI_FRONTIER_FIRST") != nullptr;
}

// Batching protects very wide designs from one enormous OR-of-output-bads SAT
// query, but medium designs can be faster monolithically because every batch
// repeats the same reset/bootstrap COI.  Keep AES/BlackParrot-style wide cases
// batched while allowing sky130hs_ibex-sized designs to close in one proof.
constexpr size_t kMinOutputsForBatchedProof = 129;

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

KInductionResult runMonolithicKInduction(const KInductionProblem& problem,
                                         KEPLER_FORMAL::Config::SolverType solverType,
                                         size_t maxK) {
  const bool frontierFirst = isFrontierFirstEnabled();
  // Handle the purely combinational mismatch case before any unrolling.
  if (isKInductionDiagEnabled()) {
    emitSecDiag("SEC diag: k-induction base k=0 begin");
  }
  auto baseZeroWitness = frontierFirst
      ? SEC::findFastBaseCounterexampleAtFrontier(problem, solverType, 0)
      : SEC::findBaseCounterexample(problem, solverType, 0);
  if (baseZeroWitness.has_value()) {
    if (isKInductionDiagEnabled()) {
      emitSecDiag("SEC diag: k-induction base k=0 found cex");
    }
    return {
        KInductionStatus::Different,
        baseZeroWitness->badFrame,
        std::move(baseZeroWitness)};
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
    bool frontierAlreadyChecked = false;
    if (frontierFirst) {
      if (isKInductionDiagEnabled()) {
        emitSecDiag("SEC diag: k-induction base k=", k, " begin");
      }
      if (auto witness = SEC::findFastBaseCounterexampleAtFrontier(
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
      frontierAlreadyChecked = true;
      // The regression helper enables frontier-first only for cases expected
      // to produce a counterexample.  In that mode, spending time on the
      // induction proof can only delay the desired CEX search; if all checked
      // frontiers are safe, the run should end inconclusive rather than prove
      // equivalence.
      continue;
    }

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
      if (!frontierAlreadyChecked) {
        emitSecDiag("SEC diag: k-induction base k=", k, " begin");
      }
    }

    // Earlier base checks have already ruled out bad states on frames < k.
    // Check only the newly exposed frontier instead of re-solving an
    // OR-of-all-previous-bads query at every depth.
    if (!frontierAlreadyChecked) {
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
  }

  if (frontierFirst) {
    return {KInductionStatus::Inconclusive, maxK};
  }

  // Frontier checks are an optimization over the classic cumulative base case:
  // each iteration checks only the newly exposed bad frame because earlier
  // frames were already ruled out.  Before reporting inconclusive, run one
  // cumulative base query as a safety net so any interaction with reset
  // bootstrap offsets or observation-only startup semantics cannot hide a real
  // bounded counterexample.
  if (auto witness = SEC::findBaseCounterexample(problem, solverType, maxK);
      witness.has_value()) {
    return {KInductionStatus::Different, witness->badFrame, std::move(witness)};  // LCOV_EXCL_LINE
  }

  return {KInductionStatus::Inconclusive, maxK};
}

KInductionResult combineBatchResults(KInductionResult lhs,
                                     const KInductionResult& rhs) {
  if (lhs.status == KInductionStatus::Different) {
    return lhs;  // LCOV_EXCL_LINE
  }
  if (rhs.status == KInductionStatus::Different) {
    return rhs;  // LCOV_EXCL_LINE
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
    return combined;  // LCOV_EXCL_LINE
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
  if (isFrontierFirstEnabled()) {
    emitKInductionProblemDiag(problem_, maxK);
    return runMonolithicKInduction(problem_, solverType_, maxK);
  }
  if (problem_.observedOutputExprs0.size() <= 1) {
    emitKInductionProblemDiag(problem_, maxK);
  }
  if (problem_.observedOutputExprs0.size() >= kMinOutputsForBatchedProof) {
    return runOutputBatchedKInduction(problem_, solverType_, maxK);
  }
  return runMonolithicKInduction(problem_, solverType_, maxK);
}

}  // namespace KEPLER_FORMAL::SEC
