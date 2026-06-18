

#pragma once

#include <mutex>

namespace KEPLER_FORMAL {

class Config {
public:
  enum SolverType {
    KISSAT,
    GLUCOSE,
    CADICAL
  };

  // Delete copy/move to enforce singleton semantics
  Config(const Config&) = delete;
  Config& operator=(const Config&) = delete;
  Config(Config&&) = delete;
  Config& operator=(Config&&) = delete;

  // Static configuration API
  // LCOV_EXCL_START
  static void setSolverType(SolverType type) {
    solverType_ = type;
  }
  // LCOV_EXCL_STOP

  static SolverType getSolverType() {
    return solverType_;
  }

  static void setReportSkippedPOs(bool enabled) {
    reportSkippedPOs_ = enabled;
  }

  static bool getReportSkippedPOs() {
    return reportSkippedPOs_;
  }

  static void setSecTreatUncomputableSeqAsBoundary(bool enabled) {
    secTreatUncomputableSeqAsBoundary_ = enabled;
  }

  static bool getSecTreatUncomputableSeqAsBoundary() {  // LCOV_EXCL_LINE
    return secTreatUncomputableSeqAsBoundary_;  // LCOV_EXCL_LINE
  }

  static void setSecSteadyFrontierGuard(bool enabled) {
    secSteadyFrontierGuard_ = enabled;
  }

  static bool getSecSteadyFrontierGuard() {
    return secSteadyFrontierGuard_;
  }

private:
  Config() = default;
  ~Config() = default;

  inline static SolverType solverType_ = KISSAT;
  inline static bool reportSkippedPOs_ = false;
  inline static bool secTreatUncomputableSeqAsBoundary_ = true;
  inline static bool secSteadyFrontierGuard_ = false;
};

} // namespace kepler
