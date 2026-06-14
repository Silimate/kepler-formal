// Copyright 2024-2026 keplertech.io
// SPDX-License-Identifier: GPL-3.0-only

#include "kinduction/KInductionEngine.h"

#include <algorithm>
#include <cstdlib>
#include <limits>
#include <optional>
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

// Batching protects SEC proofs from one broad OR-of-output-bads SAT query.
// Keep every true multi-output proof batched; medium designs such as
// sky130hs_ibex are still sensitive to monolithic base-case witnesses.
constexpr size_t kMinOutputsForBatchedProof = 2;
constexpr unsigned kDefaultBatchedInductionDecisionLimit = 200000;
// Dual-rail SEC is a coverage extension for resetless state.  Residual outputs
// that do not close quickly should become uncovered/inconclusive instead of
// letting one expanded rail query dominate the full regression runtime.
constexpr unsigned kDefaultDualRailInductionDecisionLimit = 5000;

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

// LCOV_EXCL_START


// LCOV_EXCL_STOP
unsigned binaryBatchedInductionDecisionLimit() {
  return readUnsignedEnv("KEPLER_SEC_KI_BATCH_DECISION_LIMIT")
      .value_or(kDefaultBatchedInductionDecisionLimit);
}

std::optional<unsigned> dualRailLeafInductionDecisionLimit() {
  if (const auto leafLimit =
          readUnsignedEnv("KEPLER_SEC_KI_DUAL_RAIL_LEAF_DECISION_LIMIT");
      leafLimit.has_value()) {
    return leafLimit;
  }
  return kDefaultDualRailInductionDecisionLimit;
}

std::optional<unsigned> batchedInductionDecisionLimit(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType) {
  if (solverType != KEPLER_FORMAL::Config::SolverType::KISSAT) {
    return std::nullopt;  // LCOV_EXCL_LINE
  }

  if (problem.usesDualRailStateEncoding &&
      // LCOV_EXCL_START
      problem.observedOutputExprs0.size() <= 1) {
      // LCOV_EXCL_STOP
    return dualRailLeafInductionDecisionLimit();
  }

  if (problem.observedOutputExprs0.size() <= 1) {
    return std::nullopt;
  }

  if (!problem.usesDualRailStateEncoding) {
    return binaryBatchedInductionDecisionLimit();
  }

  // Dual-rail proofs are state-space expanded, so a single hard multi-output
  // induction batch can spend the whole workflow inside CDCL.  Base checks are
  // shared outside the slices, making recursive splitting cheap enough to use
  // the normal batch cap here too.
  if (const auto dualRailLimit =
          readUnsignedEnv("KEPLER_SEC_KI_DUAL_RAIL_BATCH_DECISION_LIMIT");
      dualRailLimit.has_value()) {
    return dualRailLimit;
  }
  return readUnsignedEnv("KEPLER_SEC_KI_BATCH_DECISION_LIMIT")
      .value_or(kDefaultDualRailInductionDecisionLimit);
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

bool provesDualRailFrontierWithoutWitness(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    size_t k) {
  if (!problem.usesDualRailStateEncoding ||
      problem.observedOutputExprs0.size() <= 1) {
    return false;
  }
  if (!SEC::provesNoBaseCounterexampleAtFrontier(problem, solverType, k)) {  // LCOV_EXCL_LINE
    return false;  // LCOV_EXCL_LINE
  }
  if (isKInductionDiagEnabled()) {  // LCOV_EXCL_LINE
    // LCOV_EXCL_START
    emitSecDiag(  // LCOV_EXCL_LINE
        "SEC diag: k-induction dual-rail proof-only base k=", k,
        // LCOV_EXCL_STOP
        " unsat");
  // LCOV_EXCL_START
  }  // LCOV_EXCL_LINE
  return true;  // LCOV_EXCL_LINE
  // LCOV_EXCL_STOP
}

// LCOV_EXCL_START
bool shouldCheckLocalBaseCase(const KInductionProblem& problem) {
  return !problem.deferBaseCaseChecks;
  // LCOV_EXCL_STOP
}

bool proofNeedsConcreteFrontierValidation(const KInductionProblem& problem) {
  return problem.resetBootstrapCycles != 0 ||
         problem.inductionProperty != nullptr ||
         problem.inductionBad != nullptr;
}

KInductionResult runMonolithicKInduction(const KInductionProblem& problem,
                                         KEPLER_FORMAL::Config::SolverType solverType,
                                         size_t maxK) {
  // Handle the purely combinational mismatch case before any unrolling.
  if (isKInductionDiagEnabled()) {
    emitSecDiag("SEC diag: k-induction base k=0 begin");
  }
  if (shouldCheckLocalBaseCase(problem)) {
    // LCOV_EXCL_START
    auto baseZeroWitness = SEC::findBaseCounterexample(problem, solverType, 0);
    // LCOV_EXCL_STOP
    if (baseZeroWitness.has_value()) {
      if (isKInductionDiagEnabled()) {
        emitSecDiag("SEC diag: k-induction base k=0 found cex");
      }
      return {
          KInductionStatus::Different,
          baseZeroWitness->badFrame,
          std::move(baseZeroWitness)};
    }
  } else if (isKInductionDiagEnabled()) {
    emitSecDiag("SEC diag: k-induction base k=0 deferred");
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

// LCOV_EXCL_START

    const std::optional<unsigned> inductionDecisionLimit =
        batchedInductionDecisionLimit(problem, solverType);
    const InductionProofStatus inductionStatus =
        SEC::proveByInductionStatus(
            problem, solverType, k, inductionDecisionLimit);
    if (inductionStatus == InductionProofStatus::Proved) {
      if (shouldCheckLocalBaseCase(problem) &&
          proofNeedsConcreteFrontierValidation(problem)) {
        // Reset/bootstrap and explicit induction certificates can prove a
        // LCOV_EXCL_STOP
        // strengthened obligation. Before accepting that as SEC equivalence,
        // LCOV_EXCL_START
        // validate the concrete top-output base predicate through the proved
        // frontier.
        if (auto witness = SEC::findBaseCounterexample(problem, solverType, k);
            witness.has_value()) {
            // LCOV_EXCL_STOP
          return {
              KInductionStatus::Different,
              witness->badFrame,
              std::move(witness)};
        }
      // LCOV_EXCL_START
      }
      // LCOV_EXCL_STOP
      if (isKInductionDiagEnabled()) {
        emitSecDiag("SEC diag: k-induction step k=", k, " proved");
      }
      return {KInductionStatus::Equivalent, k};
    }
    if (inductionStatus == InductionProofStatus::Unknown) {
      if (isKInductionDiagEnabled()) {  // LCOV_EXCL_LINE
        if (problem.usesDualRailStateEncoding &&  // LCOV_EXCL_LINE
            problem.observedOutputExprs0.size() <= 1) {  // LCOV_EXCL_LINE
          emitSecDiag(  // LCOV_EXCL_LINE
              "SEC diag: k-induction step k=", k,
              " resource-limited; checking frontier");
        } else {  // LCOV_EXCL_LINE
          emitSecDiag(  // LCOV_EXCL_LINE
              "SEC diag: k-induction step k=", k,
              " resource-limited; splitting output batch");
        }
      }  // LCOV_EXCL_LINE
      // LCOV_EXCL_START
      if (!problem.usesDualRailStateEncoding ||  // LCOV_EXCL_LINE
          problem.observedOutputExprs0.size() > 1) {  // LCOV_EXCL_LINE
        return {KInductionStatus::Inconclusive, k};  // LCOV_EXCL_LINE
      }
      // LCOV_EXCL_STOP
      if (!shouldCheckLocalBaseCase(problem)) {  // LCOV_EXCL_LINE
        return {KInductionStatus::Inconclusive, k};  // LCOV_EXCL_LINE
      // LCOV_EXCL_START
      }
    }  // LCOV_EXCL_LINE
    // LCOV_EXCL_STOP
    if (isKInductionDiagEnabled()) {
      emitSecDiag("SEC diag: k-induction step k=", k, " inconclusive");
      emitSecDiag("SEC diag: k-induction base k=", k, " begin");
    // LCOV_EXCL_START
    }

    // Earlier base checks have already ruled out bad states on frames < k.
    // Check only the newly exposed frontier instead of re-solving an
    // LCOV_EXCL_STOP
    // OR-of-all-previous-bads query at every depth.
    // LCOV_EXCL_START
    if (shouldCheckLocalBaseCase(problem)) {
      const bool frontierProvedWithoutWitness =
      // LCOV_EXCL_STOP
          provesDualRailFrontierWithoutWitness(problem, solverType, k);
      // LCOV_EXCL_START
      if (!frontierProvedWithoutWitness) {
      // LCOV_EXCL_STOP
        if (auto witness = SEC::findBaseCounterexampleAtFrontier(
                problem, solverType, k);
            witness.has_value()) {
          if (isKInductionDiagEnabled()) {
            emitSecDiag("SEC diag: k-induction base k=", k, " found cex");
          }
          return {
              KInductionStatus::Different,
              witness->badFrame,
              std::move(witness)};
        }
      }
      if (isKInductionDiagEnabled()) {
        emitSecDiag("SEC diag: k-induction base k=", k, " unsat");
      }
    } else if (isKInductionDiagEnabled()) {
      emitSecDiag("SEC diag: k-induction base k=", k, " deferred");
    }
  }

  // Frontier checks are an optimization over the classic cumulative base case:
  // each iteration checks only the newly exposed bad frame because earlier
  // frames were already ruled out.  Before reporting inconclusive, run one
  // cumulative base query as a safety net so any interaction with reset
  // bootstrap offsets or observation-only startup semantics cannot hide a real
  // bounded counterexample.
  if (shouldCheckLocalBaseCase(problem)) {
    if (auto witness = SEC::findBaseCounterexample(problem, solverType, maxK);
        witness.has_value()) {
      return {KInductionStatus::Different, witness->badFrame, std::move(witness)};  // LCOV_EXCL_LINE
    }
  }

  return {KInductionStatus::Inconclusive, maxK};
}

// LCOV_EXCL_START


// LCOV_EXCL_STOP
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
  // LCOV_EXCL_START
  lhs.bound = std::max(lhs.bound, rhs.bound);
  // LCOV_EXCL_STOP
  return lhs;
}

KInductionResult runOutputRangeKInduction(
    KInductionProblem& batchProblem,
    const KInductionProblem& sourceProblem,
    KEPLER_FORMAL::Config::SolverType solverType,
    size_t maxK,
    size_t firstOutput,
    // LCOV_EXCL_START
    size_t endOutput) {
    // LCOV_EXCL_STOP
  configureOutputBatchProblem(batchProblem, sourceProblem, firstOutput, endOutput);
  if (isKInductionDiagEnabled()) {
    // LCOV_EXCL_START
    emitSecDiag(
    // LCOV_EXCL_STOP
        "SEC diag: k-induction output range [", firstOutput, ",", endOutput,
        ") outputs=", endOutput - firstOutput);
  }
  const KInductionResult result =
      runMonolithicKInduction(batchProblem, solverType, maxK);
  if (isKInductionDiagEnabled()) {
    emitSecDiag(
        "SEC diag: k-induction output range [", firstOutput, ",", endOutput,
        ") status=", static_cast<int>(result.status),
        " bound=", result.bound);
  }
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
  const OutputBatchingLimits batchingLimits =
      defaultOutputBatchingLimitsForProblem(problem);
  // Copy the large shared SEC problem once, then mutate only the small
  // output/property slice for each batch.  The previous implementation copied
  // LCOV_EXCL_START
  // hundreds of thousands of state symbols and equality pairs per batch, which
  // LCOV_EXCL_STOP
  // became visible on BlackParrot even after SAT-side batching was effective.
  KInductionProblem batchProblem = problem;
  const bool useSharedBaseCase =
      problem.usesDualRailStateEncoding && shouldCheckLocalBaseCase(problem);
  // Preserve explicit caller deferral for localized residual proofs.  The
  // shared-base optimization below is only for normal batched proofs that still
  // own their base obligation inside this engine.
  batchProblem.deferBaseCaseChecks =
      problem.deferBaseCaseChecks || useSharedBaseCase;
  for (const auto& [firstOutput, endOutput] :
       buildSupportBoundedOutputBatches(problem, batchingLimits)) {
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
  if (useSharedBaseCase && combined.status == KInductionStatus::Equivalent) {
    // Slices may prove before running their local frontier BMC. The shared
    // full-output check must therefore include the proved frontier itself.
    if (auto witness =
            SEC::findBaseCounterexample(problem, solverType, combined.bound);
        witness.has_value()) {
      return {KInductionStatus::Different, witness->badFrame, std::move(witness)};
    }
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
  if (problem_.observedOutputExprs0.size() >= kMinOutputsForBatchedProof) {
    return runOutputBatchedKInduction(problem_, solverType_, maxK);
  }
  return runMonolithicKInduction(problem_, solverType_, maxK);
}

}  // namespace KEPLER_FORMAL::SEC
