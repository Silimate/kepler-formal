// Copyright 2024-2026 keplertech.io
// SPDX-License-Identifier: GPL-3.0-only

#include "imc/IMCEngine.h"

#include <algorithm>
#include <string>
#include <unordered_set>
#include <vector>

#include "common/SecDiag.h"
#include "kinduction/BaseCaseSolver.h"
#include "imc/CraigInterpolatingModelChecker.h"
#include "imc/ExactInterpolantSynthesizer.h"
#include "kinduction/OutputBatching.h"
#include "kinduction/SatEncoding.h"
#include "proof/ProofEngineShared.h"

namespace KEPLER_FORMAL::SEC {

// Overall IMC algorithm:
// 1. Reuse the shared SEC base-case search to detect concrete counterexamples.
// 2. Build the startup frontier from init/reset/bootstrap constraints.
// 3. Try any already-validated strengthening plus the one-step exact
//    interpolant as an immediate inductive proof.
// 4. If that is not enough, grow the exact reachable frontier with depth k.
// 5. At each k, conjoin the frontier with the validated strengthening and ask
//    whether the result is now inductive and excludes bad.
// 6. Return the first counterexample, the first proof depth, or inconclusive.

namespace {

constexpr OutputBatchingLimits kLargeDualRailCraigBatchingLimits{
    /*maxOutputBatchSize=*/4,
    /*outputBatchSupportLimit=*/8192};

constexpr size_t kCraigBatchMinOverlapPercent = 90;
constexpr size_t kCraigBatchMinMarginalSupportLimit = 64;
constexpr size_t kCraigBatchMarginalSupportDivisor = 10;
constexpr size_t kCraigBatchSingleOutputSupportLimit = 1024;

std::unordered_set<size_t> observedOutputSupport(
    const KInductionProblem& problem,
    size_t outputIndex) {
  std::unordered_set<size_t> support;
  const auto support0 =
      problem.observedOutputExprs0[outputIndex]->getSupportVars();
  const auto support1 =
      problem.observedOutputExprs1[outputIndex]->getSupportVars();
  support.reserve(support0.size() + support1.size());
  support.insert(support0.begin(), support0.end());
  support.insert(support1.begin(), support1.end());
  return support;
}

size_t supportIntersectionSize(const std::unordered_set<size_t>& lhs,
                               const std::unordered_set<size_t>& rhs) {
  const auto& smaller = lhs.size() <= rhs.size() ? lhs : rhs;
  const auto& larger = lhs.size() <= rhs.size() ? rhs : lhs;
  size_t count = 0;
  for (const size_t symbol : smaller) {
    if (larger.find(symbol) != larger.end()) {
      ++count;
    }
  }
  return count;
}

void mergeSupport(std::unordered_set<size_t>& batchSupport,
                  const std::unordered_set<size_t>& outputSupport) {
  batchSupport.insert(outputSupport.begin(), outputSupport.end());
}

size_t marginalSupportLimit(size_t batchSupportSize) {
  return std::max(
      kCraigBatchMinMarginalSupportLimit,
      batchSupportSize / kCraigBatchMarginalSupportDivisor);
}

bool canAddOutputToCraigBatch(
    const std::unordered_set<size_t>& batchSupport,
    const std::unordered_set<size_t>& outputSupport,
    const OutputBatchingLimits& limits,
    size_t batchOutputCount,
    const char** rejectReason,
    size_t* marginalSupport,
    size_t* overlapPercent) {
  if (batchOutputCount == 0) {
    return true;
  }
  if (batchOutputCount + 1 > limits.maxOutputBatchSize) {
    *rejectReason = "count_limit";
    return false;
  }
  // Large frontiers make Craig interpolants grow with the OR'ed bad predicate;
  // keep those outputs single even when their raw supports overlap heavily.
  if (batchSupport.size() > kCraigBatchSingleOutputSupportLimit ||
      outputSupport.size() > kCraigBatchSingleOutputSupportLimit) {
    *rejectReason = "large_support";
    return false;
  }

  const size_t overlap = supportIntersectionSize(batchSupport, outputSupport);
  const size_t marginal = outputSupport.size() - overlap;
  const size_t unionSupport = batchSupport.size() + marginal;
  *marginalSupport = marginal;
  *overlapPercent =
      outputSupport.empty() ? 100 : (overlap * 100) / outputSupport.size();

  if (unionSupport > limits.outputBatchSupportLimit) {
    *rejectReason = "support_limit";
    return false;
  }
  if (*overlapPercent < kCraigBatchMinOverlapPercent) {
    *rejectReason = "low_overlap";
    return false;
  }
  if (marginal > marginalSupportLimit(batchSupport.size())) {
    *rejectReason = "marginal_support";
    return false;
  }
  return true;
}

void addComplementedStateRelations(
    SATSolverWrapper& solver,
    const FrameVariableStore& variables,
    const std::vector<std::pair<size_t, size_t>>& complementedStatePairs,
    size_t numFrames) {
  // Complemented outputs such as Q/QN are modeled as hard equalities between
  // the primary and inverted state views in every explored frame.
  for (size_t frame = 0; frame < numFrames; ++frame) {
    for (const auto& [primarySymbol, complementedSymbol] : complementedStatePairs) {
      // LCOV_EXCL_START
      addLiteralEquivalence(  // LCOV_EXCL_LINE
          solver,  // LCOV_EXCL_LINE
          variables.getLiteral(complementedSymbol, frame),  // LCOV_EXCL_LINE
          -variables.getLiteral(primarySymbol, frame));  // LCOV_EXCL_LINE
          // LCOV_EXCL_STOP
    }
  }
}

void addTransitionRelation(SATSolverWrapper& solver,
                           const FrameVariableStore& variables,
                           const KInductionProblem& problem,
                           size_t frame) {
  // Encode one SEC transition step for both designs into the local SAT frame.
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

BoolExpr* buildStateAssignmentCube(const std::vector<size_t>& symbols, size_t assignment) {
  // Turn one concrete state assignment into a BoolExpr cube so exact frontier
  // enumeration can reuse the common proof-formula helpers.
  BoolExpr* cube = BoolExpr::createTrue();
  for (size_t bit = 0; bit < symbols.size(); ++bit) {
    BoolExpr* literal = BoolExpr::Var(symbols[bit]);
    cube = BoolExpr::And(
        cube,
        (assignment & (size_t{1} << bit)) != 0 ? literal : BoolExpr::Not(literal));
  }
  return BoolExpr::simplify(cube);
}

bool isStateReachableAtDepth(const KInductionProblem& problem,
                             KEPLER_FORMAL::Config::SolverType solverType,
                             BoolExpr* initFormula,
                             const std::vector<size_t>& stateSymbols,
                             size_t assignment,
                             size_t depth) {
  // Ask whether one concrete combined SEC state is reachable at exactly this
  // depth from the init/reset frontier.
  SATSolverWrapper solver(solverType);
  FrameVariableStore variables(solver, problem.allSymbols, depth + 1);
  addComplementedStateRelations(solver, variables, problem.complementedStatePairs0, depth + 1);
  addComplementedStateRelations(solver, variables, problem.complementedStatePairs1, depth + 1);
  for (size_t frame = 0; frame < depth; ++frame) {
    addTransitionRelation(solver, variables, problem, frame);
  }

  FrameFormulaEncoder initEncoder(solver, variables.makeLeafLits(0));
  solver.addClause({initEncoder.encode(initFormula)});

  FrameFormulaEncoder targetEncoder(solver, variables.makeLeafLits(depth));
  solver.addClause({targetEncoder.encode(buildStateAssignmentCube(stateSymbols, assignment))});
  return solver.solve();
}

BoolExpr* buildExactReachableStateInvariant(const KInductionProblem& problem,
                                            KEPLER_FORMAL::Config::SolverType solverType,
                                            BoolExpr* initFormula,
                                            size_t depth,
                                            size_t maxStateBits = 12) {
  const std::vector<size_t> combinedStateSymbols = problem.combinedStateSymbols();
  if (initFormula == nullptr || combinedStateSymbols.empty() ||
      combinedStateSymbols.size() > maxStateBits) {
    // LCOV_EXCL_START
    return nullptr;  // LCOV_EXCL_LINE
    // LCOV_EXCL_STOP
  }

  const size_t assignmentCount = size_t{1} << combinedStateSymbols.size();
  BoolExpr* reachable = BoolExpr::createFalse();
  bool foundReachableState = false;

  // Build the exact set of states reachable within the bounded frontier. IMC
  // can then stop as soon as this frontier becomes inductive and excludes bad.
  for (size_t assignment = 0; assignment < assignmentCount; ++assignment) {
    bool reachableWithinDepth = false;
    for (size_t frame = 0; frame <= depth; ++frame) {
      if (isStateReachableAtDepth(
              problem, solverType, initFormula, combinedStateSymbols, assignment, frame)) {
        reachableWithinDepth = true;
        break;
      }
    }

    if (!reachableWithinDepth) {
      continue;
    }

    foundReachableState = true;
    reachable = BoolExpr::Or(
        reachable, buildStateAssignmentCube(combinedStateSymbols, assignment));
  }

  if (!foundReachableState) {
    // LCOV_EXCL_START
    return nullptr;  // LCOV_EXCL_LINE
    // LCOV_EXCL_STOP
  }
  return BoolExpr::simplify(reachable);
}

BoolExpr* buildInitialImcStrengthening(const KInductionProblem& problem,
                                       KEPLER_FORMAL::Config::SolverType solverType,
                                       BoolExpr* initFormula) {
  if (initFormula == nullptr) {
    return nullptr;  // LCOV_EXCL_LINE
  }

  // Reuse any already validated SEC strengthening and then sharpen it with the
  // exact one-step interpolant when that derivation is affordable.
  BoolExpr* sharedStrengthening =
      selectValidatedStrengtheningInvariant(problem, initFormula, solverType);
  ExactInterpolantSynthesizer interpolantSynthesizer(problem, solverType);
  if (auto interpolant =
          interpolantSynthesizer.deriveOneStepReachableStateInvariant();
      interpolant.has_value()) {
    sharedStrengthening =
        sharedStrengthening == nullptr
            ? *interpolant
            : BoolExpr::simplify(BoolExpr::And(sharedStrengthening, *interpolant));
  }
  return sharedStrengthening == nullptr ? problem.property : sharedStrengthening;
}

bool provesImcInvariant(const KInductionProblem& problem,
                        KEPLER_FORMAL::Config::SolverType solverType,
                        BoolExpr* initFormula,
                        BoolExpr* invariant) {
  return invariant != nullptr &&
         initialFrontierImplies(initFormula, invariant, solverType) &&
         isInductiveInvariant(problem, invariant, solverType) &&
         invariantExcludesBadStates(problem, invariant, solverType);
}

std::optional<IMCResult> findImcCounterexample(const ImcBaseCounterexampleCache& cache,
                                               KEPLER_FORMAL::Config::SolverType solverType,
                                               size_t depth) {
  // IMC checks depths monotonically.  Only the newly exposed frontier can hold
  // a fresh counterexample, so avoid rebuilding a cumulative BMC query that
  // re-walks already-cleared frames and all earlier output bad clauses.
  if (auto witness = findImcBaseCounterexampleAtFrontier(cache, solverType, depth);
      witness.has_value()) {
    return IMCResult{IMCStatus::Different, witness->badFrame, std::move(witness)};
  }
  return std::nullopt;
}

void removeCrossDesignStateCandidates(KInductionProblem& problem) {
  // IMC must derive every relation between the two designs from the encoded
  // reset and transition formulas. Candidate correspondences mined elsewhere
  // are intentionally unavailable to both interpolation and witness search.
  problem.initialStateEqualityPairs.clear();
  problem.bootstrapStateEqualityPairs.clear();
  problem.inductiveStateEqualityPairs.clear();
  problem.inductionPropertyAssumesInductiveStateEqualities = false;
}

struct ReusableCraigInvariant {
  std::vector<InterpolantRegion> regions;
  std::unordered_set<size_t> trackedStates;
  size_t proofBound = 0;
};

IMCResult runCraigOutputRange(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    size_t maxK,
    size_t firstOutput,
    size_t endOutput,
    ReusableCraigInvariant& reusableInvariant) {
  KInductionProblem batchProblem = problem;
  configureOutputBatchProblem(
      batchProblem, problem, firstOutput, endOutput);
  removeCrossDesignStateCandidates(batchProblem);
  emitSecDiag(
      "SEC diag: imc Craig output batch first=", firstOutput,
      " end=", endOutput,
      " first_name=",
      firstOutput < problem.observedOutputNames.size()
          ? problem.observedOutputNames[firstOutput]
          : std::string("<unknown>"),
      " bad_support=", batchProblem.bad->getSupportVars().size());

  if (!reusableInvariant.regions.empty() &&
      craigInvariantExcludesBad(
          batchProblem,
          reusableInvariant.trackedStates,
          reusableInvariant.regions)) {
    emitSecDiag(
        "SEC diag: imc Craig reused invariant for output batch first=",
        firstOutput, " end=", endOutput);
    return {IMCStatus::Equivalent, reusableInvariant.proofBound};
  }

  CraigInterpolatingModelChecker checker(batchProblem);
  const CraigImcResult proof = checker.run(maxK);
  if (proof.status == CraigImcStatus::Equivalent) {
    if (!proof.invariantRegions.empty()) {
      reusableInvariant.regions = proof.invariantRegions;
      reusableInvariant.trackedStates = proof.trackedStates;
      reusableInvariant.proofBound = proof.iterations;
    }
    return {IMCStatus::Equivalent, proof.iterations};
  }
  if (proof.status == CraigImcStatus::CounterexampleCandidate) {
    // Craig found SAT from the exact concrete post-reset frontier. Reconstruct
    // only that lookahead with the exact bounded witness encoder; this is
    // counterexample validation inside IMC, not a different proof engine.
    const auto cache = makeImcBaseCounterexampleCache(batchProblem);
    if (const auto counterexample =
            findImcCounterexample(*cache, solverType, proof.iterations);
        counterexample.has_value()) {
      return *counterexample;
    }
    return {IMCStatus::Inconclusive, maxK};
  }

  if (endOutput > firstOutput + 1) {
    const size_t midpoint = firstOutput + (endOutput - firstOutput) / 2;
    const IMCResult left = runCraigOutputRange(
        problem, solverType, maxK, firstOutput, midpoint, reusableInvariant);
    const IMCResult right = runCraigOutputRange(
        problem, solverType, maxK, midpoint, endOutput, reusableInvariant);
    if (left.status == IMCStatus::Different) {
      return left;
    }
    if (right.status == IMCStatus::Different) {
      return right;
    }
    if (left.status == IMCStatus::Equivalent &&
        right.status == IMCStatus::Equivalent) {
      return {
          IMCStatus::Equivalent, std::max(left.bound, right.bound)};
    }
    return {IMCStatus::Inconclusive, maxK};
  }

  if (proof.status == CraigImcStatus::ConcreteNoProgress) {
    // Every first-iteration lookahead already started from the complete
    // concrete post-reset cube. Repeating all bounded SAT queries here would
    // rebuild the same transition prefixes without adding proof information.
    return {IMCStatus::Inconclusive, maxK};
  }

  // Partial or implicit initial frontiers are over-approximations. Preserve the
  // exact bounded localization sweep for those cases so a reachable mismatch
  // is never hidden by an abstract Craig SAT result.
  const auto cache = makeImcBaseCounterexampleCache(batchProblem);
  for (size_t depth = 0; depth <= maxK; ++depth) {
    if (const auto counterexample =
            findImcCounterexample(*cache, solverType, depth);
        counterexample.has_value()) {
      return *counterexample;
    }
  }
  return {IMCStatus::Inconclusive, maxK};
}

IMCResult runLargeDualRailCraigImc(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    size_t maxK) {
  // Craig IMC derives proof regions from the selected output slice. When one
  // bus bit already pulls a wide rail-state cone, nearby bits usually reuse the
  // same transition surface. Batch those bits here so classic IMC proves one
  // conjunction instead of rebuilding the same Craig query per bit. This limit
  // is IMC-local and does not change KI/PDR batching.
  const auto batches = buildLargeDualRailCraigImcOutputBatches(
      problem, kLargeDualRailCraigBatchingLimits);
  size_t proofBound = 0;
  bool inconclusive = false;
  ReusableCraigInvariant reusableInvariant;
  for (const auto& [firstOutput, endOutput] : batches) {
    const IMCResult batch = runCraigOutputRange(
        problem, solverType, maxK, firstOutput, endOutput, reusableInvariant);
    if (batch.status == IMCStatus::Different) {
      return batch;
    }
    if (batch.status == IMCStatus::Inconclusive) {
      inconclusive = true;
    } else {
      proofBound = std::max(proofBound, batch.bound);
    }
  }
  return inconclusive ? IMCResult{IMCStatus::Inconclusive, maxK}
                      : IMCResult{IMCStatus::Equivalent, proofBound};
}

bool shouldBuildExplicitImcInitFormula(const KInductionProblem& problem) {
  if (!problem.usesDualRailStateEncoding) {
    return true;
  }
  // Exact IMC enumerates reachable combined states only for tiny systems.
  // Large dual-rail ASIC problems use proof-derived Craig interpolation instead
  // of materializing a full rail-init formula.
  return problem.totalStateCount <= 12;
}

}  // namespace

std::vector<std::pair<size_t, size_t>> buildLargeDualRailCraigImcOutputBatches(
    const KInductionProblem& problem,
    const OutputBatchingLimits& limits) {
  std::vector<std::unordered_set<size_t>> outputSupports;
  outputSupports.reserve(problem.observedOutputExprs0.size());
  for (size_t output = 0; output < problem.observedOutputExprs0.size();
       ++output) {
    outputSupports.push_back(observedOutputSupport(problem, output));
  }

  std::vector<std::pair<size_t, size_t>> batches;
  size_t firstOutput = 0;
  while (firstOutput < outputSupports.size()) {
    size_t endOutput = firstOutput;
    std::unordered_set<size_t> batchSupport;
    while (endOutput < outputSupports.size()) {
      const char* rejectReason = nullptr;
      size_t marginalSupport = 0;
      size_t overlapPercent = 100;
      const size_t batchOutputCount = endOutput - firstOutput;
      if (!canAddOutputToCraigBatch(
              batchSupport,
              outputSupports[endOutput],
              limits,
              batchOutputCount,
              &rejectReason,
              &marginalSupport,
              &overlapPercent)) {
        emitSecDiag(
            "SEC diag: imc Craig batch closes before output=", endOutput,
            " reason=", rejectReason,
            " batch_first=", firstOutput,
            " batch_support=", batchSupport.size(),
            " output_support=", outputSupports[endOutput].size(),
            " marginal_support=", marginalSupport,
            " overlap_percent=", overlapPercent);
        break;
      }
      mergeSupport(batchSupport, outputSupports[endOutput]);
      ++endOutput;
    }
    if (endOutput == firstOutput) {
      // Always make progress: an oversized single output still deserves one
      // exact IMC attempt rather than being silently skipped by the scheduler.
      ++endOutput;  // LCOV_EXCL_LINE
    }
    batches.emplace_back(firstOutput, endOutput);
    firstOutput = endOutput;
  }
  return batches;
}

IMCEngine::IMCEngine(const KInductionProblem& problem,
                     KEPLER_FORMAL::Config::SolverType solverType)
    : problem_(problem), solverType_(solverType) {}

IMCResult IMCEngine::run(size_t maxK) const {
  if (problem_.combinedStateSymbols().empty()) {
    // Stateless SEC is still a real IMC base query: a combinational mismatch
    // at frame 0 must be reported before declaring equivalence.
    const auto baseCache = makeImcBaseCounterexampleCache(problem_);
    if (const auto counterexample =
            findImcCounterexample(*baseCache, solverType_, 0);
        counterexample.has_value()) {
      return *counterexample;
    }
    return {IMCStatus::Equivalent, 0};
  }

  if (problem_.usesDualRailStateEncoding &&
      problem_.effectiveTotalStateCount() > 12 &&
      !problem_.observedOutputExprs0.empty() &&
      problem_.observedOutputExprs0.size() ==
          problem_.observedOutputExprs1.size()) {
    return runLargeDualRailCraigImc(problem_, solverType_, maxK);
  }

  const auto baseCache = makeImcBaseCounterexampleCache(problem_);
  // Keep counterexample discovery on the same bounded base-case machinery as
  // the rest of SEC so witnesses and reported cycles stay consistent.
  if (const auto counterexample =
          findImcCounterexample(*baseCache, solverType_, 0);
      counterexample.has_value()) {
    return *counterexample;  // LCOV_EXCL_LINE
  }

  BoolExpr* initFormula =
      shouldBuildExplicitImcInitFormula(problem_) ? buildProofInitFormula(problem_)
                                                  : nullptr;
  const BoolExpr* sharedStrengthening =
      buildInitialImcStrengthening(problem_, solverType_, initFormula);
  if (initFormula != nullptr &&
      provesImcInvariant(problem_, solverType_, initFormula,
                         const_cast<BoolExpr*>(sharedStrengthening))) {
    // Before spending time on deeper frontiers, see whether the startup
    // strengthening is already a complete inductive proof.
    return {IMCStatus::Equivalent, 1};
  }

  for (size_t k = 1; k <= maxK; ++k) {
    if (const auto counterexample =
            findImcCounterexample(*baseCache, solverType_, k);
        counterexample.has_value()) {
      return *counterexample;
    }

    if (initFormula == nullptr) {
      // LCOV_EXCL_START
      continue;  // LCOV_EXCL_LINE
      // LCOV_EXCL_STOP
    }

    BoolExpr* frontierInvariant =
        buildExactReachableStateInvariant(problem_, solverType_, initFormula, k);
    if (frontierInvariant == nullptr) {
      // LCOV_EXCL_START
      continue;  // LCOV_EXCL_LINE
      // LCOV_EXCL_STOP
    }

    // Keep the explicit IMC engine centered on the reachable frontier, but
    // reuse any already validated strengthening to reduce the SAT work needed
    // to establish inductiveness on compact transition systems.
    BoolExpr* proofInvariant =
        sharedStrengthening == nullptr
            // LCOV_EXCL_START
            ? frontierInvariant  // LCOV_EXCL_LINE
            // LCOV_EXCL_STOP
            : BoolExpr::simplify(
                  BoolExpr::And(frontierInvariant, const_cast<BoolExpr*>(sharedStrengthening)));

    if (provesImcInvariant(problem_, solverType_, initFormula, proofInvariant)) {
      // LCOV_EXCL_START
      return {IMCStatus::Equivalent, k};  // LCOV_EXCL_LINE
      // LCOV_EXCL_STOP
    }
  }

  // We exhausted the requested depth without finding either a counterexample
  // or an inductive frontier.
  return {IMCStatus::Inconclusive, maxK};
}

}  // namespace KEPLER_FORMAL::SEC
