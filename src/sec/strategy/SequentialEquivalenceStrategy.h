// Copyright 2024-2026 keplertech.io
// SPDX-License-Identifier: GPL-3.0-only

#pragma once

#include <cstddef>
#include <string>
#include <vector>

#include "../../config/Config.h"

namespace naja::NL {
class SNLDesign;
}

namespace KEPLER_FORMAL::SEC {

enum class SecEngine {
  Legacy,
  KInduction,
  Imc,
  Pdr,
};

enum class SecEncoding {
  Binary,
  DualRailSteady,
};

enum class SequentialEquivalenceStatus {
  Equivalent,
  Different,
  Inconclusive,
  Unsupported,
};

struct ExtractedBoundaryReportEntry {  // LCOV_EXCL_LINE
  std::string design;
  std::string signal;
  std::vector<std::string> roles;
  std::string connectivitySkip;
};

struct SequentialEquivalenceResult {  // LCOV_EXCL_LINE
  SequentialEquivalenceStatus status = SequentialEquivalenceStatus::Unsupported;
  size_t bound = 0;
  std::string reason;
  size_t coveredOutputs = 0;
  size_t totalOutputs = 0;
  std::vector<std::string> skippedObservedOutputs;
  std::vector<std::string> resetUnanchoredSkippedOutputs;
  std::vector<std::string> multiClockDomainSkippedOutputs;
  std::vector<std::string> abstractedSequentialBoundaries;
  std::vector<ExtractedBoundaryReportEntry> extractedBoundaryReports;

  double outputCoveragePercent() const {
    if (totalOutputs == 0) {
      // LCOV_EXCL_START
      return 0.0;
      // LCOV_EXCL_STOP
    }
    return (100.0 * static_cast<double>(coveredOutputs)) /
           static_cast<double>(totalOutputs);
  }
};

struct SequentialDesignModel;

// Builds a combined SEC problem from two sequential designs and discharges it
// with the selected SEC proof engine. "Legacy" preserves the historical hybrid
// path, while K_INDUCTION, IMC, and PDR expose distinct top-level engines over
// the same extracted transition system.
class SequentialEquivalenceStrategy {
 public:
  SequentialEquivalenceStrategy(
      naja::NL::SNLDesign* top0,
      naja::NL::SNLDesign* top1,
      KEPLER_FORMAL::Config::SolverType solverType =
          KEPLER_FORMAL::Config::getSolverType(),
      SecEngine secEngine = SecEngine::Legacy,
      SecEncoding encoding = SecEncoding::DualRailSteady);

  SequentialEquivalenceResult run(size_t maxK) const;
  SequentialEquivalenceResult runExtractedModels(
      const SequentialDesignModel& model0,
      const SequentialDesignModel& model1,
      size_t maxK) const;

 private:
  naja::NL::SNLDesign* top0_;
  naja::NL::SNLDesign* top1_;
  KEPLER_FORMAL::Config::SolverType solverType_;
  SecEngine secEngine_;
  SecEncoding encoding_;
};

namespace detail {

constexpr size_t kMaxPdrInductiveStateEqualityOutputs = 64;
constexpr size_t kMinPdrDualRailFrameZeroValidationOutputs = 256;
constexpr size_t kMaxPdrDualRailFrameZeroValidationOutputs = 384;
constexpr size_t kMaxPdrDualRailFrameZeroValidationStateSymbols = 1000000;
constexpr size_t kMaxDualRailGlobalBootstrapEqualityOutputs = 384;

inline bool shouldInferPdrInductiveStateEqualities(
    SecEngine secEngine,
    size_t observedOutputSurface) {
  // Classic IMC should derive its reachable over-approximation from Craig
  // interpolants, not from pre-mined cross-design internal state equalities.
  if (secEngine == SecEngine::Imc) {
    return false;
  }
  return secEngine != SecEngine::Pdr ||
         observedOutputSurface <= kMaxPdrInductiveStateEqualityOutputs;
}

inline bool shouldAcceptDualRailResetFrontierCoverageAsFinalResult(
    SecEngine secEngine) {
  return secEngine != SecEngine::Pdr;
}

inline bool shouldSkipDualRailGlobalBootstrapEqualityMining(
    SecEngine secEngine,
    SecEncoding encoding,
    size_t observedOutputSurface) {
  return (secEngine == SecEngine::KInduction ||
          secEngine == SecEngine::Imc) &&
         encoding == SecEncoding::DualRailSteady &&
         observedOutputSurface > kMaxDualRailGlobalBootstrapEqualityOutputs;
}

inline bool shouldDeferPdrDualRailFrameZeroValidation(
    size_t observedOutputSurface,
    size_t railStateSymbolSurface) {
  if (observedOutputSurface > kMaxPdrDualRailFrameZeroValidationOutputs) {
    return true;
  }
  // A mid-wide output bus can still be too expensive when compact extraction
  // expands the rail state into a very large surface.  Keep small probe designs
  // on the exact validation path, but let PDR own huge SoC surfaces directly.
  return observedOutputSurface >= kMinPdrDualRailFrameZeroValidationOutputs &&
         railStateSymbolSurface >
             kMaxPdrDualRailFrameZeroValidationStateSymbols;
}

}  // namespace detail

}  // namespace KEPLER_FORMAL::SEC
