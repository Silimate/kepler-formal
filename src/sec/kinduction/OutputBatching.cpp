// Copyright 2024-2026 keplertech.io
// SPDX-License-Identifier: GPL-3.0-only

#include "kinduction/OutputBatching.h"

#include <algorithm>
#include <unordered_set>

#include "common/BoolExprUtils.h"

namespace KEPLER_FORMAL::SEC {

namespace {

// A single monolithic OR-of-all-bads query can be too wide for ASIC netlists,
// but proving one output per solver call repeats setup work hundreds of times.
// These limits keep nearby outputs together while preventing one batch from
// dragging most of the design into one SAT cone.
constexpr OutputBatchingLimits kDefaultOutputBatchingLimits;
constexpr OutputBatchingLimits kDualRailOutputBatchingLimits{16, 512};

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

}  // namespace

std::vector<std::pair<size_t, size_t>> buildSupportBoundedOutputBatches(
    const KInductionProblem& problem) {
  return buildSupportBoundedOutputBatches(
      problem, defaultOutputBatchingLimitsForProblem(problem));
}

std::vector<std::pair<size_t, size_t>> buildSupportBoundedOutputBatches(
    const KInductionProblem& problem,
    const OutputBatchingLimits& limits) {
  std::vector<std::pair<size_t, size_t>> batches;
  size_t firstOutput = 0;
  std::unordered_set<size_t> batchSupport;
  batchSupport.reserve(limits.outputBatchSupportLimit);

  while (firstOutput < problem.observedOutputExprs0.size()) {
    size_t endOutput = firstOutput;
    batchSupport.clear();
    while (endOutput < problem.observedOutputExprs0.size()) {
      std::unordered_set<size_t> candidateSupport = batchSupport;
      appendOutputSupport(problem, endOutput, candidateSupport);

      const bool batchAlreadyHasOutput = endOutput > firstOutput;
      const bool exceedsCount =
          endOutput - firstOutput + 1 > limits.maxOutputBatchSize;
      const bool exceedsSupport =
          candidateSupport.size() > limits.outputBatchSupportLimit;
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

OutputBatchingLimits defaultOutputBatchingLimitsForProblem(
    const KInductionProblem& problem) {
  if (problem.usesDualRailStateEncoding) {
    // Dual-rail output obligations already carry both may-one/may-zero rails.
    // Start with moderate shared-cone batches, then let KI's recursive
    // splitter localize only the conjunctions that are actually hard.
    return kDualRailOutputBatchingLimits;
  }
  return kDefaultOutputBatchingLimits;
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
  if (source.outputImpliedByInductionCore.size() ==
      source.observedOutputExprs0.size()) {
    batch.outputImpliedByInductionCore.assign(
        source.outputImpliedByInductionCore.begin() + firstOutput,
        source.outputImpliedByInductionCore.begin() + endOutput);
  } else {
    batch.outputImpliedByInductionCore.clear();
  }

  // SEC output equality is a conjunction. Proving smaller conjunctions and
  // combining the results is logically equivalent to one monolithic property,
  // while allowing the base/induction encoders to run COI on much smaller
  // output cones.
  BoolExpr* property = BoolExpr::createTrue();
  for (size_t i = 0; i < batch.observedOutputExprs0.size(); ++i) {
    property = BoolExpr::And(
        property,
        makeEqualityExpr(batch.observedOutputExprs0[i], batch.observedOutputExprs1[i]));
  }
  batch.property = BoolExpr::simplify(property);
  batch.bad = BoolExpr::simplify(BoolExpr::Not(batch.property));

  // Keep the shared state-equality strengthening as KI hypotheses for sliced
  // output proofs.  Rebuilding the monolithic induction property here would ask
  // every tiny output batch to prove all shared state equalities as goals; large
  // reset-heavy ASICs then spend the run chasing unrelated equality failures
  // instead of proving the selected output cone.
  batch.inductionProperty = nullptr;
  batch.inductionBad = nullptr;
  batch.inductionPropertyAssumesInductiveStateEqualities = false;
  batch.description = source.description + " output batch";
}

}  // namespace KEPLER_FORMAL::SEC
