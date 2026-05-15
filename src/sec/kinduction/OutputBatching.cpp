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
constexpr size_t kMaxOutputBatchSize = 32;
constexpr size_t kOutputBatchSupportLimit = 512;

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

  // Recompute the induction obligation from the batch property.  The shared
  // structural/startup invariants stay in the problem as inductive equality
  // pairs, but output-specific pruning from the monolithic property is not
  // reused across a narrower output slice.
  batch.inductionProperty = nullptr;
  batch.inductionBad = nullptr;
  batch.description = source.description + " output batch";
}

}  // namespace KEPLER_FORMAL::SEC
