// Copyright 2024-2026 keplertech.io
// SPDX-License-Identifier: GPL-3.0-only

#include "strategy/SequentialEquivalenceStrategy.h"

#include <algorithm>
#include <cctype>
#include <cstdio>
#include <cstdlib>
#include <iterator>
#include <map>
#include <optional>
#include <set>
#include <sstream>
#include <stdexcept>
#include <unordered_map>
#include <unordered_set>

#include "DNL.h"
#include "NLUniverse.h"
#include "SNLPath.h"
#include "common/BoolExprUtils.h"
#include "common/AlignedSignals.h"
#include "imc/ExactInterpolantSynthesizer.h"
#include "imc/IMCEngine.h"
#include "kinduction/KInductionEngine.h"
#include "model/SequentialDesignModel.h"
#include "pdr/PDREngine.h"
#include "strategy/ReachableStateInvariant.h"
#include "strategy/StructuralStateInvariant.h"

namespace KEPLER_FORMAL::SEC {

// Overall SEC strategy pipeline:
// 1. Extract both designs into the normalized sequential model used by SEC.
// 2. Align environment inputs and observed outputs by stable external names.
// 3. Infer internal state correspondences structurally, not by register names.
// 4. Build reset/init reachable-state strengthening for startup anchoring.
// 5. Remap both designs into one shared SAT symbol space.
// 6. Build the checked SEC property and the stronger proof invariant.
// 7. Hand the combined transition system to the selected top-level engine and
//    translate its result back into user-facing SEC diagnostics.

namespace {

std::string joinReasons(const std::vector<std::string>& reasons) {
  std::ostringstream oss;
  for (size_t i = 0; i < reasons.size(); ++i) {
    if (i) {
      oss << " | ";
    }
    oss << reasons[i];
  }
  return oss.str();
}

std::string describeMismatchedNames(const std::vector<std::string>& lhs,
                                    const std::vector<std::string>& rhs,
                                    const char* label) {
  std::ostringstream oss;
  oss << "Mismatched " << label << " sets";
  if (!lhs.empty()) {
    oss << " lhs=[";
    for (size_t i = 0; i < lhs.size(); ++i) {
      if (i) {
        oss << ", ";
      }
      oss << lhs[i];
    }
    oss << "]";
  }
  if (!rhs.empty()) {
    oss << " rhs=[";
    for (size_t i = 0; i < rhs.size(); ++i) {
      if (i) {
        oss << ", ";
      }
      oss << rhs[i];
    }
    oss << "]";
  }
  return oss.str();
}

std::string formatBoolValue(bool value) {
  return value ? "1" : "0";
}

std::string normalizeSignalBaseName(const std::string& name) {
  std::string base = name;
  const auto bracket = base.find('[');
  if (bracket != std::string::npos) {
    base = base.substr(0, bracket);
  }
  std::transform(base.begin(), base.end(), base.begin(), [](unsigned char ch) {
    return static_cast<char>(std::toupper(ch));
  });
  return base;
}

std::optional<bool> getResetAssertionValue(const std::string& displayName) {
  const std::string normalized = normalizeSignalBaseName(displayName);
  if (normalized == "RESET" || normalized == "RST") {
    return true;
  }
  if (normalized == "RESET_N" || normalized == "RESETN" ||
      normalized == "RST_N" || normalized == "RSTN") {
    return false;
  }
  return std::nullopt;
}

SignalKey getTerminalPathKey(const naja::DNL::DNLTerminalFull& terminal) {
  SignalKey key;
  const auto pathNames = terminal.getDNLInstance().getPath().getPathNames();
  key.first.reserve(pathNames.size() + 1);
  for (const auto& name : pathNames) {
    key.first.push_back(name.getID());  // LCOV_EXCL_LINE
  }
  key.first.push_back(terminal.getSnlBitTerm()->getName().getID());
  key.second.push_back(
      static_cast<naja::NL::NLID::DesignObjectID>(terminal.getSnlBitTerm()->getBit()));
  return key;
}

std::string getTerminalDisplayName(const naja::DNL::DNLTerminalFull& terminal) {
  std::ostringstream oss;
  const auto pathNames = terminal.getDNLInstance().getPath().getPathNames();
  for (const auto& name : pathNames) {
    oss << name.getString() << ".";
  }
  oss << terminal.getSnlBitTerm()->getName().getString() << "["
      << terminal.getSnlBitTerm()->getBit() << "]";
  return oss.str();
}

std::string formatStringList(const std::vector<std::string>& values, size_t limit) {
  if (values.empty()) {
    return "<none>";
  }

  std::ostringstream oss;
  const size_t printed = std::min(values.size(), limit);
  for (size_t i = 0; i < printed; ++i) {
    if (i) {
      oss << ", ";
    }
    oss << values[i];
  }
  if (values.size() > printed) {
    oss << ", ... +" << (values.size() - printed) << " more";  // LCOV_EXCL_LINE
  }  // LCOV_EXCL_LINE
  return oss.str();
}

std::vector<std::string> setDifference(const std::set<std::string>& lhs,
                                       const std::set<std::string>& rhs) {
  std::vector<std::string> diff;
  std::set_difference(
      lhs.begin(), lhs.end(), rhs.begin(), rhs.end(), std::back_inserter(diff));
  return diff;
}

std::string describeConnectivitySkipOrigin(ConnectivitySkipOrigin origin) {
  switch (origin) {
    case ConnectivitySkipOrigin::NoDriver:
      return "no-driver";
    case ConnectivitySkipOrigin::MultiDriver:
      return "multi-driver";
    case ConnectivitySkipOrigin::LogicalLoop:
      return "logical-loop";
  }
  return "connectivity";  // LCOV_EXCL_LINE
}

std::string describeConnectivitySkipInfo(const ConnectivitySkipInfo& info) {
  std::ostringstream oss;
  oss << describeConnectivitySkipOrigin(info.origin) << " connectivity: "
      << info.detail;
  return oss.str();
}

std::string describeSecSignalKey(const SequentialDesignModel& model,
                                 const SignalKey& key) {
  if (const auto it = model.displayNameByKey.find(key);
      it != model.displayNameByKey.end()) {
    return it->second;
  }
  return signalKeyToString(key);  // LCOV_EXCL_LINE
}

void appendUniqueRole(std::vector<std::string>& roles, const char* role) {
  if (std::find(roles.begin(), roles.end(), role) == roles.end()) {
    roles.push_back(role);
  }
}

struct OutputCoverageSelection {
  AlignedSignals checkedOutputs;
  std::vector<std::string> skippedOutputs;
  size_t totalOutputs = 0;
};

struct AlignedSecInterface {
  AlignedSignals inputs;
  AlignedSignals outputs;
  AlignedSignals inductiveStateEqualities;
  OutputCoverageSelection outputCoverage;
};

struct SharedSecSymbolSpace {
  KInductionProblem problem;
  std::unordered_map<SignalKey, size_t, SignalKeyHash> inputSymbols0;
  std::unordered_map<SignalKey, size_t, SignalKeyHash> inputSymbols1;
  std::unordered_map<SignalKey, size_t, SignalKeyHash> state0Symbols;
  std::unordered_map<SignalKey, size_t, SignalKeyHash> state1Symbols;
  std::unordered_map<size_t, size_t> localToCombined0;
  std::unordered_map<size_t, size_t> localToCombined1;
};

struct RemappedSecExpressions {
  std::unordered_map<SignalKey, BoolExpr*, SignalKeyHash> next0;
  std::unordered_map<SignalKey, BoolExpr*, SignalKeyHash> next1;
};

struct ScopedDnlContext {
  explicit ScopedDnlContext(naja::NL::SNLDesign* top)
      : universe_(naja::NL::NLUniverse::get()),
        previousTop_(universe_ ? universe_->getTopDesign() : nullptr) {
    if (universe_ == nullptr) {
      throw std::runtime_error("NLUniverse not created for SEC cone tracing");  // LCOV_EXCL_LINE
    }

    naja::DNL::destroy();
    universe_->setTopDesign(top);
    dnl_ = naja::DNL::get();
  }

  ~ScopedDnlContext() {
    naja::DNL::destroy();
    if (universe_ != nullptr && previousTop_ != nullptr) {
      universe_->setTopDesign(previousTop_);
    }
  }

  naja::DNL::DNLFull* dnl() const {
    return dnl_;
  }

 private:
  naja::NL::NLUniverse* universe_ = nullptr;
  naja::NL::SNLDesign* previousTop_ = nullptr;
  naja::DNL::DNLFull* dnl_ = nullptr;
};

std::optional<naja::DNL::DNLID> findTermByDisplayName(
    naja::DNL::DNLFull* dnl,
    const std::string& signalName) {
  for (naja::DNL::DNLID termID = 0; termID < dnl->getDNLTerms().size(); ++termID) {
    const auto& term = dnl->getDNLTerminalFromID(termID);
    if (term.isNull()) {
      continue;  // LCOV_EXCL_LINE
    }
    if (getTerminalDisplayName(term) == signalName) {
      return termID;
    }
  }
  return std::nullopt;  // LCOV_EXCL_LINE
}

std::optional<naja::DNL::DNLID> findTermByKey(naja::DNL::DNLFull* dnl,
                                              const SignalKey& key) {
  for (naja::DNL::DNLID termID = 0; termID < dnl->getDNLTerms().size(); ++termID) {
    const auto& term = dnl->getDNLTerminalFromID(termID);
    if (term.isNull()) {
      continue;  // LCOV_EXCL_LINE
    }
    if (getTerminalPathKey(term) == key) {
      return termID;
    }
  }
  return std::nullopt;  // LCOV_EXCL_LINE
}

std::vector<naja::DNL::DNLID> resolveTermsByKey(
    naja::DNL::DNLFull* dnl,
    const std::vector<SignalKey>& keys) {
  std::vector<naja::DNL::DNLID> resolved;
  resolved.reserve(keys.size());
  for (const auto& key : keys) {
    if (auto termID = findTermByKey(dnl, key); termID.has_value()) {
      resolved.push_back(*termID);
    }
  }
  return resolved;
}

std::string formatConeTerm(naja::DNL::DNLFull* dnl, naja::DNL::DNLID termID) {
  const auto& term = dnl->getDNLTerminalFromID(termID);
  if (term.isNull()) {
    return "<null>";  // LCOV_EXCL_LINE
  }
  if (term.getIsoID() == naja::DNL::DNLID_MAX) {
    return getTerminalDisplayName(term);  // LCOV_EXCL_LINE
  }

  const auto& iso = dnl->getDNLIsoDB().getIsoFromIsoIDconst(term.getIsoID());
  if (iso.isConstant0()) {
    return "Constant 0";  // LCOV_EXCL_LINE
  }
  if (iso.isConstant1()) {
    return "Constant 1";  // LCOV_EXCL_LINE
  }
  return getTerminalDisplayName(term);
}

struct ConeTrace {
  std::vector<std::vector<std::string>> levels;
  std::set<std::string> allTerms;
};

ConeTrace buildConeTrace(naja::DNL::DNLFull* dnl,
                         naja::DNL::DNLID seedTermID,
                         const std::vector<naja::DNL::DNLID>& environmentInputs) {
  ConeTrace trace;
  std::vector<bool> isEnvironmentInput(dnl->getDNLTerms().size(), false);
  for (const auto termID : environmentInputs) {
    if (termID < isEnvironmentInput.size()) {
      isEnvironmentInput[termID] = true;
    }
  }

  const auto seedIsoID = dnl->getDNLTerminalFromID(seedTermID).getIsoID();
  if (seedIsoID == naja::DNL::DNLID_MAX) {
    return trace;  // LCOV_EXCL_LINE
  }

  std::vector<naja::DNL::DNLID> currentIsos = {seedIsoID};
  std::unordered_set<naja::DNL::DNLID> visitedIsos;
  while (!currentIsos.empty()) {
    std::set<std::string> levelTerms;
    std::vector<naja::DNL::DNLID> nextIsos;

    for (const auto isoID : currentIsos) {
      if (isoID == naja::DNL::DNLID_MAX || !visitedIsos.insert(isoID).second) {
        continue;
      }

      const auto& iso = dnl->getDNLIsoDB().getIsoFromIsoIDconst(isoID);
      if (iso.isConstant0()) {
        levelTerms.insert("Constant 0");  // LCOV_EXCL_LINE
        continue;  // LCOV_EXCL_LINE
      }
      if (iso.isConstant1()) {
        levelTerms.insert("Constant 1");  // LCOV_EXCL_LINE
        continue;  // LCOV_EXCL_LINE
      }

      for (const auto driver : iso.getDrivers()) {
        if (driver == naja::DNL::DNLID_MAX) {
          continue;  // LCOV_EXCL_LINE
        }

        const auto& driverTerm = dnl->getDNLTerminalFromID(driver);
        if (driverTerm.isNull()) {
          continue;  // LCOV_EXCL_LINE
        }

        levelTerms.insert(formatConeTerm(dnl, driver));
        if (driver < isEnvironmentInput.size() && isEnvironmentInput[driver]) {
          continue;
        }

        const auto& inst = driverTerm.getDNLInstance();
        for (naja::DNL::DNLID termID = inst.getTermIndexes().first;
             termID != naja::DNL::DNLID_MAX && termID <= inst.getTermIndexes().second;
             ++termID) {
          const auto& term = dnl->getDNLTerminalFromID(termID);
          if (term.isNull()) {
            continue;  // LCOV_EXCL_LINE
          }
          if (term.getSnlBitTerm()->getDirection() ==
              naja::NL::SNLBitTerm::Direction::Output) {
            continue;
          }
          if (term.getIsoID() != naja::DNL::DNLID_MAX) {
            nextIsos.push_back(term.getIsoID());
          }
        }
      }
    }

    if (!levelTerms.empty()) {
      std::vector<std::string> orderedTerms(levelTerms.begin(), levelTerms.end());
      trace.allTerms.insert(orderedTerms.begin(), orderedTerms.end());
      trace.levels.push_back(std::move(orderedTerms));
    }

    std::sort(nextIsos.begin(), nextIsos.end());
    nextIsos.erase(std::unique(nextIsos.begin(), nextIsos.end()), nextIsos.end());
    currentIsos = std::move(nextIsos);
  }

  return trace;
}

std::string formatConeLevels(const ConeTrace& trace) {
  constexpr size_t kMaxLevels = 12;
  constexpr size_t kMaxTermsPerLevel = 12;

  if (trace.levels.empty()) {
    return "    <no traced cone terms>\n";  // LCOV_EXCL_LINE
  }

  std::ostringstream oss;
  const size_t printedLevels = std::min(trace.levels.size(), kMaxLevels);
  for (size_t level = 0; level < printedLevels; ++level) {
    oss << "    step " << level << ": "
        << formatStringList(trace.levels[level], kMaxTermsPerLevel) << "\n";
  }
  if (trace.levels.size() > printedLevels) {
    oss << "    ... +" << (trace.levels.size() - printedLevels)  // LCOV_EXCL_LINE
        << " more trace steps\n";  // LCOV_EXCL_LINE
  }  // LCOV_EXCL_LINE
  return oss.str();
}

struct ConeDiffReport {
  ConeTrace trace;
  std::string error;
};

ConeDiffReport buildConeDiffReport(naja::NL::SNLDesign* top,
                                   const std::string& differenceSignal,
                                   const std::vector<SignalKey>& environmentInputs) {
  ConeDiffReport report;
  ScopedDnlContext dnlContext(top);
  auto* dnl = dnlContext.dnl();

  const auto seedTermID = findTermByDisplayName(dnl, differenceSignal);
  if (!seedTermID.has_value()) {
    report.error =  // LCOV_EXCL_LINE
        "could not resolve the differing SEC signal back into the DNL";
    return report;  // LCOV_EXCL_LINE
  }

  report.trace = buildConeTrace(
      dnl, *seedTermID, resolveTermsByKey(dnl, environmentInputs));
  return report;
}

std::string formatConeTraceback(const KInductionResult::CounterexampleWitness& witness,
                                const SequentialDesignModel& model0,
                                const SequentialDesignModel& model1,
                                naja::NL::SNLDesign* top0,
                                naja::NL::SNLDesign* top1) {
  if (witness.outputMismatches.empty()) {
    return "";  // LCOV_EXCL_LINE
  }
  const auto& differencePoint = witness.outputMismatches.front();

  std::ostringstream oss;
  oss << "Traceback for first differing point `" << differencePoint.signal
      << "` at cycle " << witness.badFrame << ":\n";

  if (top0 == nullptr || top1 == nullptr) {
    oss << "  Cone traceback unavailable: compact SEC released the "
           "elaborated designs after model extraction.\n";
    return oss.str();
  }

  try {
    const auto report0 = buildConeDiffReport(
        top0, differencePoint.signal, model0.environmentInputs);
    const auto report1 = buildConeDiffReport(
        top1, differencePoint.signal, model1.environmentInputs);

    if (!report0.error.empty() || !report1.error.empty()) {
      oss << "  Cone traceback unavailable: ";  // LCOV_EXCL_LINE
      if (!report0.error.empty()) {  // LCOV_EXCL_LINE
        oss << "design0 " << report0.error;  // LCOV_EXCL_LINE
      }  // LCOV_EXCL_LINE
      if (!report0.error.empty() && !report1.error.empty()) {  // LCOV_EXCL_LINE
        oss << "; ";  // LCOV_EXCL_LINE
      }  // LCOV_EXCL_LINE
      if (!report1.error.empty()) {  // LCOV_EXCL_LINE
        oss << "design1 " << report1.error;  // LCOV_EXCL_LINE
      }  // LCOV_EXCL_LINE
      oss << "\n";  // LCOV_EXCL_LINE
      return oss.str();  // LCOV_EXCL_LINE
    }

    oss << "  design0 cone to environment inputs:\n"
        << formatConeLevels(report0.trace);
    oss << "  design1 cone to environment inputs:\n"
        << formatConeLevels(report1.trace);

    constexpr size_t kMaxDiffTerms = 20;
    const auto onlyInDesign0 =
        setDifference(report0.trace.allTerms, report1.trace.allTerms);
    const auto onlyInDesign1 =
        setDifference(report1.trace.allTerms, report0.trace.allTerms);
    oss << "  cone terms only in design0: "
        << formatStringList(onlyInDesign0, kMaxDiffTerms) << "\n";
    oss << "  cone terms only in design1: "
        << formatStringList(onlyInDesign1, kMaxDiffTerms) << "\n";
  } catch (const std::exception& e) {
    oss << "  Cone traceback unavailable: " << e.what() << "\n";  // LCOV_EXCL_LINE
  }  // LCOV_EXCL_LINE

  return oss.str();
}

std::string formatCounterexampleWitness(const KInductionResult& result,
                                        const SequentialDesignModel& model0,
                                        const SequentialDesignModel& model1,
                                        naja::NL::SNLDesign* top0,
                                        naja::NL::SNLDesign* top1) {
  if (!result.witness.has_value()) {
    return "";  // LCOV_EXCL_LINE
  }

  const auto& witness = *result.witness;
  std::ostringstream oss;
  oss << "Counterexample reaches the first bad frame at cycle "
      << witness.badFrame << ".\n";

  if (witness.inputTrace.empty()) {
    oss << "Input trace: <none>\n";  // LCOV_EXCL_LINE
  } else {  // LCOV_EXCL_LINE
    oss << "Input trace:\n";
    for (const auto& frame : witness.inputTrace) {
      oss << "  cycle " << frame.frame << ": ";
      if (frame.assignments.empty()) {
        oss << "<no environment inputs>";  // LCOV_EXCL_LINE
      } else {  // LCOV_EXCL_LINE
        for (size_t i = 0; i < frame.assignments.size(); ++i) {
          if (i) {
            oss << ", ";
          }
          oss << frame.assignments[i].signal << "="
              << formatBoolValue(frame.assignments[i].value);
        }
      }
      oss << "\n";
    }
  }

  if (!witness.outputMismatches.empty()) {
    oss << "Observed output mismatches at cycle " << witness.badFrame << ":\n";
    for (const auto& mismatch : witness.outputMismatches) {
      oss << "  " << mismatch.signal << ": design0="
          << formatBoolValue(mismatch.design0Value)
          << ", design1=" << formatBoolValue(mismatch.design1Value) << "\n";
    }
  }

  oss << formatConeTraceback(witness, model0, model1, top0, top1);

  return oss.str();
}

std::map<SignalKey, std::string, SignalKeyLess> buildKeyToNameMap(
    const std::vector<SignalKey>& keys,
    const std::unordered_map<SignalKey, std::string, SignalKeyHash>& displayNames,
    const char* label) {
  std::map<SignalKey, std::string, SignalKeyLess> byKey;
  for (const auto& key : keys) {
    const auto nameIt = displayNames.find(key);
    if (nameIt == displayNames.end()) {
      throw std::runtime_error(  // LCOV_EXCL_LINE
          std::string("Missing display name for SEC ") + label);  // LCOV_EXCL_LINE
    }
    const auto [_, inserted] = byKey.emplace(key, nameIt->second);
    if (!inserted) {
      throw std::runtime_error(  // LCOV_EXCL_LINE
          std::string("Duplicate SEC ") + label + " key `" + signalKeyToString(key) + "`");  // LCOV_EXCL_LINE
    }
  }
  return byKey;
}

std::vector<std::string> sortedNames(
    const std::map<SignalKey, std::string, SignalKeyLess>& byKey) {
  std::vector<std::string> names;
  names.reserve(byKey.size());
  for (const auto& [_, name] : byKey) {
    names.push_back(name);
  }
  return names;
}

AlignedSignals alignSignalsByName(
    const std::vector<SignalKey>& keys0,
    const std::unordered_map<SignalKey, std::string, SignalKeyHash>& displayNames0,
    const std::vector<SignalKey>& keys1,
    const std::unordered_map<SignalKey, std::string, SignalKeyHash>& displayNames1,
    const char* label) {
  // Inputs/outputs are part of the user-visible contract, so SEC requires an
  // exact stable-key match before any proof engine is allowed to run.
  const auto byKey0 = buildKeyToNameMap(keys0, displayNames0, label);
  const auto byKey1 = buildKeyToNameMap(keys1, displayNames1, label);
  if (byKey0.size() != byKey1.size()) {
    throw std::runtime_error(
        describeMismatchedNames(sortedNames(byKey0), sortedNames(byKey1), label));
  }

  auto it0 = byKey0.begin();
  auto it1 = byKey1.begin();
  for (; it0 != byKey0.end() && it1 != byKey1.end(); ++it0, ++it1) {
    if (it0->first != it1->first) {
      throw std::runtime_error(
          describeMismatchedNames(sortedNames(byKey0), sortedNames(byKey1), label));
    }
  }

  AlignedSignals aligned;
  aligned.names.reserve(byKey0.size());
  aligned.keys0.reserve(byKey0.size());
  aligned.keys1.reserve(byKey0.size());
  for (const auto& [key, displayName] : byKey0) {
    aligned.names.push_back(displayName);
    aligned.keys0.push_back(key);
    aligned.keys1.push_back(key);
  }
  return aligned;
}

OutputCoverageSelection selectCoveredObservedOutputs(
    const AlignedSignals& allObservedOutputs,
    const SequentialDesignModel& model0,
    const SequentialDesignModel& model1) {
  // Connectivity skips are the only SEC skips we allow here. Unsupported
  // primitive semantics should already have stopped extraction earlier.
  OutputCoverageSelection selection;
  selection.totalOutputs = allObservedOutputs.names.size();
  selection.checkedOutputs.names.reserve(allObservedOutputs.names.size());
  selection.checkedOutputs.keys0.reserve(allObservedOutputs.names.size());
  selection.checkedOutputs.keys1.reserve(allObservedOutputs.names.size());

  for (size_t i = 0; i < allObservedOutputs.names.size(); ++i) {
    const auto& key0 = allObservedOutputs.keys0[i];
    const auto& key1 = allObservedOutputs.keys1[i];
    const auto& name = allObservedOutputs.names[i];

    const auto skip0 = model0.connectivitySkipInfoByKey.find(key0);
    const auto skip1 = model1.connectivitySkipInfoByKey.find(key1);
    if (skip0 != model0.connectivitySkipInfoByKey.end() ||
        skip1 != model1.connectivitySkipInfoByKey.end()) {
      std::vector<std::string> reasons;
      if (skip0 != model0.connectivitySkipInfoByKey.end()) {
        reasons.push_back(
            "design0 " + describeConnectivitySkipInfo(skip0->second));
      }
      if (skip1 != model1.connectivitySkipInfoByKey.end()) {
        reasons.push_back(
            "design1 " + describeConnectivitySkipInfo(skip1->second));
      }
      selection.skippedOutputs.push_back(
          name + ": " + joinReasons(reasons));
      continue;
    }

    if (model0.observedOutputExprByKey.find(key0) ==
            model0.observedOutputExprByKey.end() ||
        model1.observedOutputExprByKey.find(key1) ==
            model1.observedOutputExprByKey.end()) {
      throw std::runtime_error(
          "Missing observed output expression for aligned SEC output `" +
          name + "`");
    }

    selection.checkedOutputs.names.push_back(name);
    selection.checkedOutputs.keys0.push_back(key0);
    selection.checkedOutputs.keys1.push_back(key1);
  }

  return selection;
}

SequentialEquivalenceResult makeSecResult(
    SequentialEquivalenceStatus status,
    size_t bound,
    std::string reason,
    const OutputCoverageSelection& coverage,
    std::vector<std::string> abstractedSequentialBoundaries = {},
    std::vector<ExtractedBoundaryReportEntry> extractedBoundaryReports = {}) {
  SequentialEquivalenceResult result;
  result.status = status;
  result.bound = bound;
  result.reason = std::move(reason);
  result.coveredOutputs = coverage.checkedOutputs.names.size();
  result.totalOutputs = coverage.totalOutputs;
  result.skippedObservedOutputs = coverage.skippedOutputs;
  result.abstractedSequentialBoundaries =
      std::move(abstractedSequentialBoundaries);
  result.extractedBoundaryReports = std::move(extractedBoundaryReports);
  return result;
}

template <typename MapT>
void assignSymbols(const std::vector<SignalKey>& keys,
                   MapT& output,
                   std::vector<size_t>& allSymbols,
                   size_t& nextSymbol);

std::unordered_map<size_t, size_t> buildLocalToCombinedMap(
    const SequentialDesignModel& model,
    const std::unordered_map<SignalKey, size_t, SignalKeyHash>& inputSymbols,
    const std::unordered_map<SignalKey, size_t, SignalKeyHash>& stateSymbols);

void logSecDiagLine(bool secDiagEnabled, const char* message) {
  if (!secDiagEnabled) {
    return;
  }
  fprintf(stderr, "%s\n", message);
  fflush(stderr);
}

void appendAbstractedSequentialBoundaries(
    const SequentialDesignModel& model,
    const char* designPrefix,
    std::vector<std::string>& abstractedSequentialBoundaries) {
  abstractedSequentialBoundaries.reserve(
      abstractedSequentialBoundaries.size() +
      model.abstractedSequentialBoundaries.size());
  for (const auto& description : model.abstractedSequentialBoundaries) {
    abstractedSequentialBoundaries.push_back(
        std::string(designPrefix) + " " + description);
  }
}

void appendExtractedBoundaryReports(
    const SequentialDesignModel& model,
    const char* designPrefix,
    std::vector<ExtractedBoundaryReportEntry>& reports) {
  std::map<std::string, ExtractedBoundaryReportEntry> reportsBySignal;

  auto ensureEntry = [&](const SignalKey& key) -> ExtractedBoundaryReportEntry& {
    const auto signal = describeSecSignalKey(model, key);
    auto [it, _] = reportsBySignal.try_emplace(signal);
    it->second.design = designPrefix;
    it->second.signal = signal;
    if (const auto skipIt = model.connectivitySkipInfoByKey.find(key);
        skipIt != model.connectivitySkipInfoByKey.end()) {
      it->second.connectivitySkip = describeConnectivitySkipInfo(skipIt->second);
    }
    return it->second;
  };

  auto addRole = [&](const SignalKey& key, const char* role) {
    auto& entry = ensureEntry(key);
    appendUniqueRole(entry.roles, role);
  };

  // Boundary terms are the full exposed SEC cut surface:
  // - the original top interface
  // - opaque internal cut points from leaves SEC cannot model combinationally
  //   and does not recognize as sequential
  // - the interface exposed when an uncomputable sequential is abstracted
  for (const auto& key : model.topInputKeys) {
    addRole(key, "top_input");
  }
  for (const auto& key : model.topOutputKeys) {
    addRole(key, "top_output");
  }
  for (const auto& key : model.internalBoundaryInputKeys) {
    addRole(key, "opaque_internal_input");
  }
  for (const auto& key : model.internalBoundaryOutputKeys) {
    addRole(key, "opaque_internal_output");
  }
  for (const auto& detail : model.abstractedSequentialBoundaryDetails) {
    for (const auto& key : detail.stateKeys) {
      addRole(key, "abstracted_sequential_state");
    }
    for (const auto& key : detail.observedKeys) {
      addRole(key, "abstracted_sequential_observed");
    }
  }

  reports.reserve(reports.size() + reportsBySignal.size());
  for (auto& [_, entry] : reportsBySignal) {
    reports.push_back(std::move(entry));
  }
}

SequentialDesignModel extractSecDesign(naja::NL::SNLDesign* top,
                                       const char* extractedMessage,
                                       bool secDiagEnabled) {
  SequentialDesignModel model = SequentialDesignModel::extract(top);
  logSecDiagLine(secDiagEnabled, extractedMessage);
  return model;
}

AlignedSecInterface alignSecInterface(const SequentialDesignModel& model0,
                                      const SequentialDesignModel& model1,
                                      bool secDiagEnabled) {
  AlignedSecInterface aligned;
  logSecDiagLine(secDiagEnabled, "SEC diag: aligning inputs/outputs");

  aligned.inputs = alignSignalsByName(
      model0.environmentInputs,
      model0.displayNameByKey,
      model1.environmentInputs,
      model1.displayNameByKey,
      "environment input");
  const auto alignedAllOutputs = alignSignalsByName(
      model0.allObservedOutputs,
      model0.displayNameByKey,
      model1.allObservedOutputs,
      model1.displayNameByKey,
      "observed output");
  aligned.outputCoverage =
      selectCoveredObservedOutputs(alignedAllOutputs, model0, model1);
  aligned.outputs = aligned.outputCoverage.checkedOutputs;
  if (aligned.outputs.names.empty()) {
    return aligned;
  }

  if (secDiagEnabled) {
    fprintf(
        stderr,
        "SEC diag: checked_outputs=%zu total_outputs=%zu skipped=%zu\n",
        aligned.outputs.names.size(),
        aligned.outputCoverage.totalOutputs,
        aligned.outputCoverage.skippedOutputs.size());
    fflush(stderr);
  }

  aligned.outputs = alignSignalsByName(
      model0.observedOutputs,
      model0.displayNameByKey,
      model1.observedOutputs,
      model1.displayNameByKey,
      "observed output");
  if (aligned.outputs.names.size() != aligned.outputCoverage.checkedOutputs.names.size()) {
    throw std::runtime_error(
        "Internal SEC error: checked observed outputs and extractor-visible observed "
        "outputs disagree after connectivity skipping");
  }

  logSecDiagLine(secDiagEnabled, "SEC diag: inferring inductive state equalities");
  aligned.inductiveStateEqualities = inferStructurallyEquivalentStatePairs(
      model0, model1, aligned.inputs);
  logSecDiagLine(secDiagEnabled, "SEC diag: inferred inductive state equalities");
  return aligned;
}

SharedSecSymbolSpace buildSharedSecSymbolSpace(
    const SequentialDesignModel& model0,
    const SequentialDesignModel& model1,
    const AlignedSignals& alignedInputs,
    const AlignedSignals& alignedOutputs) {
  SharedSecSymbolSpace symbolSpace;
  symbolSpace.problem.environmentInputNames = alignedInputs.names;
  symbolSpace.problem.observedOutputNames = alignedOutputs.names;

  size_t nextSymbol = 2;
  assignSymbols(
      model0.stateBits,
      symbolSpace.state0Symbols,
      symbolSpace.problem.allSymbols,
      nextSymbol);
  assignSymbols(
      model1.stateBits,
      symbolSpace.state1Symbols,
      symbolSpace.problem.allSymbols,
      nextSymbol);

  for (size_t i = 0; i < alignedInputs.names.size(); ++i) {
    const size_t symbol = nextSymbol++;
    symbolSpace.inputSymbols0.emplace(alignedInputs.keys0[i], symbol);
    symbolSpace.inputSymbols1.emplace(alignedInputs.keys1[i], symbol);
    symbolSpace.problem.allSymbols.push_back(symbol);
    symbolSpace.problem.inputSymbols.push_back(symbol);
    if (auto assertedValue = getResetAssertionValue(alignedInputs.names[i]);
        assertedValue.has_value()) {
      symbolSpace.problem.resetBootstrapInputs.emplace_back(symbol, *assertedValue);
    }
  }

  for (const auto& key : model0.stateBits) {
    symbolSpace.problem.state0Symbols.push_back(symbolSpace.state0Symbols.at(key));
  }
  for (const auto& key : model1.stateBits) {
    symbolSpace.problem.state1Symbols.push_back(symbolSpace.state1Symbols.at(key));
  }

  for (const auto& relation : model0.complementedStateRelations) {
    if (symbolSpace.state0Symbols.find(relation.primaryKey) !=
            symbolSpace.state0Symbols.end() &&
        symbolSpace.state0Symbols.find(relation.complementedKey) !=
            symbolSpace.state0Symbols.end()) {
      symbolSpace.problem.complementedStatePairs0.emplace_back(
          symbolSpace.state0Symbols.at(relation.primaryKey),
          symbolSpace.state0Symbols.at(relation.complementedKey));
    }
  }
  for (const auto& relation : model1.complementedStateRelations) {
    if (symbolSpace.state1Symbols.find(relation.primaryKey) !=
            symbolSpace.state1Symbols.end() &&
        symbolSpace.state1Symbols.find(relation.complementedKey) !=
            symbolSpace.state1Symbols.end()) {
      symbolSpace.problem.complementedStatePairs1.emplace_back(
          symbolSpace.state1Symbols.at(relation.primaryKey),
          symbolSpace.state1Symbols.at(relation.complementedKey));
    }
  }

  symbolSpace.localToCombined0 = buildLocalToCombinedMap(
      model0, symbolSpace.inputSymbols0, symbolSpace.state0Symbols);
  symbolSpace.localToCombined1 = buildLocalToCombinedMap(
      model1, symbolSpace.inputSymbols1, symbolSpace.state1Symbols);
  return symbolSpace;
}

RemappedSecExpressions remapSecExpressions(
    const SequentialDesignModel& model0,
    const SequentialDesignModel& model1,
    const AlignedSignals& alignedOutputs,
    const SharedSecSymbolSpace& symbolSpace,
    KInductionProblem& problem,
    bool secDiagEnabled) {
  RemappedSecExpressions remapped;
  std::unordered_map<BoolExpr*, BoolExpr*> remapMemo0;
  std::unordered_map<BoolExpr*, BoolExpr*> remapMemo1;

  for (size_t i = 0; i < alignedOutputs.names.size(); ++i) {
    const auto& key0 = alignedOutputs.keys0[i];
    const auto& key1 = alignedOutputs.keys1[i];
    const auto remappedOutput0 = remapBoolExprVariables(
        model0.observedOutputExprByKey.at(key0),
        symbolSpace.localToCombined0,
        remapMemo0);
    const auto remappedOutput1 = remapBoolExprVariables(
        model1.observedOutputExprByKey.at(key1),
        symbolSpace.localToCombined1,
        remapMemo1);
    problem.observedOutputExprs0.push_back(remappedOutput0);
    problem.observedOutputExprs1.push_back(remappedOutput1);
  }
  logSecDiagLine(secDiagEnabled, "SEC diag: remapped observed outputs");

  for (const auto& key : model0.stateBits) {
    remapped.next0.emplace(
        key,
        remapBoolExprVariables(
            model0.nextStateExprByStateKey.at(key),
            symbolSpace.localToCombined0,
            remapMemo0));
  }
  for (const auto& key : model1.stateBits) {
    remapped.next1.emplace(
        key,
        remapBoolExprVariables(
            model1.nextStateExprByStateKey.at(key),
            symbolSpace.localToCombined1,
            remapMemo1));
  }
  logSecDiagLine(secDiagEnabled, "SEC diag: remapped next-state formulas");
  return remapped;
}

void applyInitialStateAssignments(
    const std::unordered_map<SignalKey, bool, SignalKeyHash>& initialValues,
    const std::unordered_map<SignalKey, size_t, SignalKeyHash>& stateSymbols,
    BoolExpr*& initialCondition,
    KInductionProblem& problem) {
  for (const auto& [key, value] : initialValues) {
    const auto symbolIt = stateSymbols.find(key);
    if (symbolIt == stateSymbols.end()) {
      continue;  // LCOV_EXCL_LINE
    }
    BoolExpr* literal = BoolExpr::Var(symbolIt->second);
    initialCondition = BoolExpr::And(
        initialCondition, value ? literal : BoolExpr::Not(literal));
    ++problem.initializedStateCount;
  }
}

ReachableStateInvariant integrateReachableStateInvariant(
    const SequentialDesignModel& model0,
    const SequentialDesignModel& model1,
    const AlignedSignals& alignedInputs,
    const AlignedSignals& inductiveStateEqualities,
    const std::unordered_map<SignalKey, size_t, SignalKeyHash>& state0Symbols,
    const std::unordered_map<SignalKey, size_t, SignalKeyHash>& state1Symbols,
    KInductionProblem& problem,
    bool secDiagEnabled) {
  BoolExpr* initialCondition = BoolExpr::createTrue();
  applyInitialStateAssignments(
      model0.initialStateValueByKey, state0Symbols, initialCondition, problem);
  applyInitialStateAssignments(
      model1.initialStateValueByKey, state1Symbols, initialCondition, problem);
  problem.totalStateCount =
      problem.state0Symbols.size() + problem.state1Symbols.size();
  if (problem.hasExplicitInitialState()) {
    problem.initialCondition = BoolExpr::simplify(initialCondition);
  }

  const ReachableStateInvariant reachableInvariant = buildReachableStateInvariant(
      model0, model1, alignedInputs, inductiveStateEqualities, secDiagEnabled);
  for (size_t i = 0; i < reachableInvariant.initialStateCorrespondence.names.size(); ++i) {
    problem.initialStateEqualityPairs.emplace_back(
        state0Symbols.at(reachableInvariant.initialStateCorrespondence.keys0[i]),
        state1Symbols.at(reachableInvariant.initialStateCorrespondence.keys1[i]));
  }

  for (const auto& [key, value] : reachableInvariant.bootstrapValues0) {
    if (state0Symbols.find(key) != state0Symbols.end()) {
      problem.bootstrapStateAssignments.emplace_back(state0Symbols.at(key), value);
    }
  }
  for (const auto& [key, value] : reachableInvariant.bootstrapValues1) {
    if (state1Symbols.find(key) != state1Symbols.end()) {
      problem.bootstrapStateAssignments.emplace_back(state1Symbols.at(key), value);
    }
  }

  problem.resetBootstrapCycles = reachableInvariant.bootstrapCycles;
  for (size_t i = 0; i < reachableInvariant.anchoredStateEqualities.names.size(); ++i) {
    problem.inductiveStateEqualityPairs.emplace_back(
        state0Symbols.at(reachableInvariant.anchoredStateEqualities.keys0[i]),
        state1Symbols.at(reachableInvariant.anchoredStateEqualities.keys1[i]));
    if (!problem.resetBootstrapInputs.empty()) {
      problem.bootstrapStateEqualityPairs.emplace_back(
          state0Symbols.at(reachableInvariant.anchoredStateEqualities.keys0[i]),
          state1Symbols.at(reachableInvariant.anchoredStateEqualities.keys1[i]));
    }
  }
  return reachableInvariant;
}

void buildSecPropertiesAndTransitions(
    const SequentialDesignModel& model0,
    const SequentialDesignModel& model1,
    const AlignedSignals& alignedInputs,
    const AlignedSignals& alignedOutputs,
    const ReachableStateInvariant& reachableInvariant,
    const std::unordered_map<SignalKey, size_t, SignalKeyHash>& state0Symbols,
    const std::unordered_map<SignalKey, size_t, SignalKeyHash>& state1Symbols,
    const RemappedSecExpressions& remapped,
    KInductionProblem& problem,
    bool secDiagEnabled) {
  const auto [abstractOutputMap0, abstractOutputMap1] = buildAbstractTransitionMaps(
      model0,
      model1,
      alignedInputs,
      reachableInvariant.anchoredStateEqualities);
  logSecDiagLine(secDiagEnabled, "SEC diag: built abstract transition maps");

  for (const auto& key : model0.stateBits) {
    problem.transitions0.emplace_back(state0Symbols.at(key), remapped.next0.at(key));
  }
  for (const auto& key : model1.stateBits) {
    problem.transitions1.emplace_back(state1Symbols.at(key), remapped.next1.at(key));
  }

  BoolExpr* property = BoolExpr::createTrue();
  BoolExpr* inductionProperty = BoolExpr::createTrue();
  for (size_t i = 0; i < reachableInvariant.anchoredStateEqualities.names.size(); ++i) {
    inductionProperty = BoolExpr::And(
        inductionProperty,
        makeEqualityExpr(
            BoolExpr::Var(
                state0Symbols.at(reachableInvariant.anchoredStateEqualities.keys0[i])),
            BoolExpr::Var(
                state1Symbols.at(reachableInvariant.anchoredStateEqualities.keys1[i]))));
  }

  for (size_t i = 0; i < problem.observedOutputExprs0.size(); ++i) {
    const auto outputEquality = makeEqualityExpr(
        problem.observedOutputExprs0[i], problem.observedOutputExprs1[i]);
    property = BoolExpr::And(property, outputEquality);

    const auto& key0 = alignedOutputs.keys0[i];
    const auto& key1 = alignedOutputs.keys1[i];
    if (areEquivalentUnderAbstractMaps(
            model0.observedOutputExprByKey.at(key0),
            model1.observedOutputExprByKey.at(key1),
            abstractOutputMap0,
            abstractOutputMap1)) {
      continue;
    }
    inductionProperty = BoolExpr::And(inductionProperty, outputEquality);
  }

  problem.property = BoolExpr::simplify(property);
  problem.bad = BoolExpr::simplify(BoolExpr::Not(problem.property));
  problem.inductionProperty = BoolExpr::simplify(inductionProperty);
  problem.inductionBad = BoolExpr::simplify(BoolExpr::Not(problem.inductionProperty));
  problem.description = "SEC property with aligned observed outputs";
  logSecDiagLine(secDiagEnabled, "SEC diag: built SEC and induction properties");

  if (secDiagEnabled) {
    printf(
        "SEC diag: property_is_true=%d induction_property_is_true=%d "
        "bad_is_false=%d induction_bad_is_false=%d reset_bootstrap_inputs=%zu "
        "bootstrap_cycles=%zu bootstrap_equalities=%zu inductive_equalities=%zu\n",
        problem.property == BoolExpr::createTrue(),
        problem.inductionProperty == BoolExpr::createTrue(),
        problem.bad == BoolExpr::createFalse(),
        problem.inductionBad == BoolExpr::createFalse(),
        problem.resetBootstrapInputs.size(),
        problem.resetBootstrapCycles,
        problem.bootstrapStateEqualityPairs.size(),
        problem.inductiveStateEqualityPairs.size());
    fflush(stdout);
  }
}

const char* describeSecEngine(SecEngine secEngine) {
  switch (secEngine) {
    case SecEngine::Pdr:
      return "pdr engine";
    case SecEngine::Imc:
      return "imc engine";
    case SecEngine::KInduction:
      return "classic k-induction engine";
    case SecEngine::Legacy:
    default:
      return "legacy engine";
  }
}

SequentialEquivalenceResult runPdrSecEngine(
    const KInductionProblem& problem,
    size_t maxK,
    KEPLER_FORMAL::Config::SolverType solverType,
    const SequentialDesignModel& model0,
    const SequentialDesignModel& model1,
    naja::NL::SNLDesign* top0,
    naja::NL::SNLDesign* top1,
    const OutputCoverageSelection& outputCoverage,
    const std::vector<std::string>& abstractedSequentialBoundaries,
    const std::vector<ExtractedBoundaryReportEntry>& extractedBoundaryReports) {
  KInductionEngine baseline(problem, solverType);
  const auto baselineResult = baseline.run(0);
  switch (baselineResult.status) {
    case KInductionStatus::Equivalent:
      return makeSecResult(
          SequentialEquivalenceStatus::Equivalent,
          baselineResult.bound,
          "",
          outputCoverage,
          abstractedSequentialBoundaries,
          extractedBoundaryReports);
    case KInductionStatus::Different:
      return makeSecResult(  // LCOV_EXCL_LINE
          SequentialEquivalenceStatus::Different,
          baselineResult.bound,  // LCOV_EXCL_LINE
          formatCounterexampleWitness(baselineResult, model0, model1, top0, top1),  // LCOV_EXCL_LINE
          outputCoverage,  // LCOV_EXCL_LINE
          abstractedSequentialBoundaries,  // LCOV_EXCL_LINE
          extractedBoundaryReports);  // LCOV_EXCL_LINE
    case KInductionStatus::Inconclusive:
    default:
      break;
  }

  PDREngine pdrEngine(problem, solverType);
  const auto pdrResult = pdrEngine.run(maxK);
  switch (pdrResult.status) {
    case PDRStatus::Equivalent:
      return makeSecResult(
          SequentialEquivalenceStatus::Equivalent,
          pdrResult.bound,
          "",
          outputCoverage,
          abstractedSequentialBoundaries,
          extractedBoundaryReports);
    case PDRStatus::Different: {
      KInductionEngine witnessEngine(problem, solverType);  // LCOV_EXCL_LINE
      const auto witnessResult = witnessEngine.run(pdrResult.bound);  // LCOV_EXCL_LINE
      const std::string details =
          witnessResult.status == KInductionStatus::Different  // LCOV_EXCL_LINE
              ? formatCounterexampleWitness(witnessResult, model0, model1, top0, top1)  // LCOV_EXCL_LINE
              : "PDR found a counterexample at k = " +  // LCOV_EXCL_LINE
                    std::to_string(pdrResult.bound);  // LCOV_EXCL_LINE
      return makeSecResult(  // LCOV_EXCL_LINE
          SequentialEquivalenceStatus::Different,
          pdrResult.bound,  // LCOV_EXCL_LINE
          details,  // LCOV_EXCL_LINE
          outputCoverage,  // LCOV_EXCL_LINE
          abstractedSequentialBoundaries,  // LCOV_EXCL_LINE
          extractedBoundaryReports);  // LCOV_EXCL_LINE
    }  // LCOV_EXCL_LINE
    case PDRStatus::Inconclusive:  // LCOV_EXCL_LINE
    default:
      return makeSecResult(  // LCOV_EXCL_LINE
          SequentialEquivalenceStatus::Inconclusive,
          pdrResult.bound,  // LCOV_EXCL_LINE
          "Reached max_k without a proof or counterexample",  // LCOV_EXCL_LINE
          outputCoverage,  // LCOV_EXCL_LINE
          abstractedSequentialBoundaries,  // LCOV_EXCL_LINE
          extractedBoundaryReports);  // LCOV_EXCL_LINE
  }
}

SequentialEquivalenceResult runKInductionSecEngine(
    const KInductionProblem& problem,
    size_t maxK,
    KEPLER_FORMAL::Config::SolverType solverType,
    const SequentialDesignModel& model0,
    const SequentialDesignModel& model1,
    naja::NL::SNLDesign* top0,
    naja::NL::SNLDesign* top1,
    const OutputCoverageSelection& outputCoverage,
    const std::vector<std::string>& abstractedSequentialBoundaries,
    const std::vector<ExtractedBoundaryReportEntry>& extractedBoundaryReports) {
  KInductionEngine engine(problem, solverType);
  const auto result = engine.run(maxK);
  switch (result.status) {
    case KInductionStatus::Equivalent:
      return makeSecResult(
          SequentialEquivalenceStatus::Equivalent,
          result.bound,
          "",
          outputCoverage,
          abstractedSequentialBoundaries,
          extractedBoundaryReports);
    case KInductionStatus::Different:
      return makeSecResult(
          SequentialEquivalenceStatus::Different,
          result.bound,
          result.witness.has_value()
              ? formatCounterexampleWitness(result, model0, model1, top0, top1)
              : "Classic k-induction found a counterexample at k = " +  // LCOV_EXCL_LINE
                    std::to_string(result.bound),  // LCOV_EXCL_LINE
          outputCoverage,
          abstractedSequentialBoundaries,
          extractedBoundaryReports);
    case KInductionStatus::Inconclusive:  // LCOV_EXCL_LINE
    default:
      return makeSecResult(  // LCOV_EXCL_LINE
          SequentialEquivalenceStatus::Inconclusive,
          result.bound,  // LCOV_EXCL_LINE
          "Reached max_k without a proof or counterexample",  // LCOV_EXCL_LINE
          outputCoverage,  // LCOV_EXCL_LINE
          abstractedSequentialBoundaries,  // LCOV_EXCL_LINE
          extractedBoundaryReports);  // LCOV_EXCL_LINE
  }
}

SequentialEquivalenceResult runImcSecEngine(
    const KInductionProblem& problem,
    size_t maxK,
    KEPLER_FORMAL::Config::SolverType solverType,
    const SequentialDesignModel& model0,
    const SequentialDesignModel& model1,
    naja::NL::SNLDesign* top0,
    naja::NL::SNLDesign* top1,
    const OutputCoverageSelection& outputCoverage,
    const std::vector<std::string>& abstractedSequentialBoundaries,
    const std::vector<ExtractedBoundaryReportEntry>& extractedBoundaryReports) {
  IMCEngine engine(problem, solverType);
  const auto result = engine.run(maxK);
  switch (result.status) {
    case IMCStatus::Equivalent:
      return makeSecResult(
          SequentialEquivalenceStatus::Equivalent,
          result.bound,
          "",
          outputCoverage,
          abstractedSequentialBoundaries,
          extractedBoundaryReports);
    case IMCStatus::Different: {
      const KInductionResult witnessResult{  // LCOV_EXCL_LINE
          KInductionStatus::Different, result.bound, result.witness};  // LCOV_EXCL_LINE
      return makeSecResult(  // LCOV_EXCL_LINE
          SequentialEquivalenceStatus::Different,
          result.bound,  // LCOV_EXCL_LINE
          result.witness.has_value()  // LCOV_EXCL_LINE
              ? formatCounterexampleWitness(witnessResult, model0, model1, top0, top1)  // LCOV_EXCL_LINE
              : "IMC found a counterexample at k = " +  // LCOV_EXCL_LINE
                    std::to_string(result.bound),  // LCOV_EXCL_LINE
          outputCoverage,  // LCOV_EXCL_LINE
          abstractedSequentialBoundaries,  // LCOV_EXCL_LINE
          extractedBoundaryReports);  // LCOV_EXCL_LINE
    }  // LCOV_EXCL_LINE
    case IMCStatus::Inconclusive:  // LCOV_EXCL_LINE
    default:
      return makeSecResult(  // LCOV_EXCL_LINE
          SequentialEquivalenceStatus::Inconclusive,
          result.bound,  // LCOV_EXCL_LINE
          "Reached max_k without a proof or counterexample",  // LCOV_EXCL_LINE
          outputCoverage,  // LCOV_EXCL_LINE
          abstractedSequentialBoundaries,  // LCOV_EXCL_LINE
          extractedBoundaryReports);  // LCOV_EXCL_LINE
  }
}

SequentialEquivalenceResult runLegacySecEngine(
    KInductionProblem problem,
    size_t maxK,
    KEPLER_FORMAL::Config::SolverType solverType,
    const SequentialDesignModel& model0,
    const SequentialDesignModel& model1,
    naja::NL::SNLDesign* top0,
    naja::NL::SNLDesign* top1,
    const OutputCoverageSelection& outputCoverage,
    const std::vector<std::string>& abstractedSequentialBoundaries,
    const std::vector<ExtractedBoundaryReportEntry>& extractedBoundaryReports) {
  ExactInterpolantSynthesizer interpolantSynthesizer(problem, solverType);
  if (auto interpolant =
          interpolantSynthesizer.deriveOneStepReachableStateInvariant();
      interpolant.has_value()) {
    problem.inductionProperty = BoolExpr::simplify(
        BoolExpr::And(problem.inductionProperty, *interpolant));
    problem.inductionBad =
        BoolExpr::simplify(BoolExpr::Not(problem.inductionProperty));
  }

  KInductionEngine engine(problem, solverType);
  const auto result = engine.run(maxK);
  switch (result.status) {
    case KInductionStatus::Equivalent:
      return makeSecResult(
          SequentialEquivalenceStatus::Equivalent,
          result.bound,
          "",
          outputCoverage,
          abstractedSequentialBoundaries,
          extractedBoundaryReports);
    case KInductionStatus::Different:
      return makeSecResult(
          SequentialEquivalenceStatus::Different,
          result.bound,
          formatCounterexampleWitness(result, model0, model1, top0, top1),
          outputCoverage,
          abstractedSequentialBoundaries,
          extractedBoundaryReports);
    case KInductionStatus::Inconclusive:
    default:
      return makeSecResult(
          SequentialEquivalenceStatus::Inconclusive,
          result.bound,
          "Reached max_k without a proof or counterexample",
          outputCoverage,
          abstractedSequentialBoundaries,
          extractedBoundaryReports);
  }
}

template <typename MapT>
void assignSymbols(const std::vector<SignalKey>& keys,
                   MapT& output,
                   std::vector<size_t>& allSymbols,
                   size_t& nextSymbol) {
  for (const auto& key : keys) {
    output.emplace(key, nextSymbol);
    allSymbols.push_back(nextSymbol);
    ++nextSymbol;
  }
}

std::unordered_map<size_t, size_t> buildLocalToCombinedMap(
    const SequentialDesignModel& model,
    const std::unordered_map<SignalKey, size_t, SignalKeyHash>& inputSymbols,
    const std::unordered_map<SignalKey, size_t, SignalKeyHash>& stateSymbols) {
  // Each design is extracted independently, so its BoolExpr variables must be
  // rewritten into a single shared symbol space before we can compare them.
  std::unordered_map<size_t, size_t> localToCombined;
  for (const auto& [key, localVar] : model.inputVarByKey) {
    if (auto it = inputSymbols.find(key); it != inputSymbols.end()) {
      localToCombined.emplace(localVar, it->second);
      continue;
    }
    if (auto it = stateSymbols.find(key); it != stateSymbols.end()) {
      localToCombined.emplace(localVar, it->second);
    }
  }
  return localToCombined;
}

}  // namespace

SequentialEquivalenceStrategy::SequentialEquivalenceStrategy(
    naja::NL::SNLDesign* top0,
    naja::NL::SNLDesign* top1,
    KEPLER_FORMAL::Config::SolverType solverType,
    SecEngine secEngine)
    : top0_(top0), top1_(top1), solverType_(solverType), secEngine_(secEngine) {}

SequentialEquivalenceResult SequentialEquivalenceStrategy::run(size_t maxK) const {
  const bool secDiagEnabled = std::getenv("KEPLER_SEC_DIAG") != nullptr;
  logSecDiagLine(secDiagEnabled, "SEC diag: start run");

  // Phase 1: extract both designs into the normalized SEC model used by every
  // downstream engine. If either side cannot be modeled soundly, stop before we
  // spend time aligning interfaces or building proof problems.
  const auto model0 =
      extractSecDesign(top0_, "SEC diag: extracted design0", secDiagEnabled);
  if (model0.hasUnsupportedFeatures()) {
    std::vector<std::string> abstractedSequentialBoundaries;
    std::vector<ExtractedBoundaryReportEntry> extractedBoundaryReports;
    appendAbstractedSequentialBoundaries(
        model0, "design0", abstractedSequentialBoundaries);
    appendExtractedBoundaryReports(model0, "design0", extractedBoundaryReports);
    return makeSecResult(
        SequentialEquivalenceStatus::Unsupported,
        0,
        joinReasons(model0.unsupportedReasons),
        OutputCoverageSelection{},
        abstractedSequentialBoundaries,
        extractedBoundaryReports);
  }

  const auto model1 =
      extractSecDesign(top1_, "SEC diag: extracted design1", secDiagEnabled);
  return runExtractedModels(model0, model1, maxK);
}

SequentialEquivalenceResult SequentialEquivalenceStrategy::runExtractedModels(
    const SequentialDesignModel& model0,
    const SequentialDesignModel& model1,
    size_t maxK) const {
  const bool secDiagEnabled = std::getenv("KEPLER_SEC_DIAG") != nullptr;
  logSecDiagLine(secDiagEnabled, "SEC diag: start run from extracted models");

  // Compact SEC can release the elaborated Naja DBs after extraction and run
  // entirely from these value-type models. Rebuilding the boundary summaries
  // here keeps normal and compact flows reporting the same coverage details.
  std::vector<std::string> abstractedSequentialBoundaries;
  std::vector<ExtractedBoundaryReportEntry> extractedBoundaryReports;
  appendAbstractedSequentialBoundaries(
      model0, "design0", abstractedSequentialBoundaries);
  appendExtractedBoundaryReports(model0, "design0", extractedBoundaryReports);
  if (model0.hasUnsupportedFeatures()) {
    return makeSecResult(
        SequentialEquivalenceStatus::Unsupported,
        0,
        joinReasons(model0.unsupportedReasons),
        OutputCoverageSelection{},
        abstractedSequentialBoundaries,
        extractedBoundaryReports);
  }
  appendAbstractedSequentialBoundaries(
      model1, "design1", abstractedSequentialBoundaries);
  appendExtractedBoundaryReports(model1, "design1", extractedBoundaryReports);
  if (model1.hasUnsupportedFeatures()) {
    return makeSecResult(
        SequentialEquivalenceStatus::Unsupported,
        0,
        joinReasons(model1.unsupportedReasons),
        OutputCoverageSelection{},
        abstractedSequentialBoundaries,
        extractedBoundaryReports);
  }

  // Phase 2: align the externally visible SEC interface, then drop any outputs
  // whose cones were already classified as skipped by extraction.
  AlignedSecInterface aligned;
  try {
    aligned = alignSecInterface(model0, model1, secDiagEnabled);
  } catch (const std::exception& e) {
    return makeSecResult(
        SequentialEquivalenceStatus::Unsupported,
        0,
        e.what(),
        aligned.outputCoverage,
        abstractedSequentialBoundaries,
        extractedBoundaryReports);
  }
  if (aligned.outputs.names.empty()) {
    return makeSecResult(
        SequentialEquivalenceStatus::Unsupported,
        0,
        "No aligned observed outputs remain after skipping cones with no-driver, "
        "multi-driver, or logical-loop connectivity.",
        aligned.outputCoverage,
        abstractedSequentialBoundaries,
        extractedBoundaryReports);
  }

  if (secDiagEnabled) {
    printf(
        "SEC diag: aligned_inputs=%zu aligned_outputs=%zu inductive_state_equalities=%zu "
        "state_bits0=%zu state_bits1=%zu\n",
        aligned.inputs.names.size(),
        aligned.outputs.names.size(),
        aligned.inductiveStateEqualities.names.size(),
        model0.stateBits.size(),
        model1.stateBits.size());
    fflush(stdout);
  }

  if (&model0 == &model1) {
    // Compact SEC can intentionally pass the same extracted value model for
    // both sides when the input specification is byte-for-byte identical.
    // After unsupported-feature checks and observed-output coverage selection,
    // the remaining SEC question is literally "does this model equal itself?",
    // so building two disjoint SAT symbol spaces would only recreate the
    // memory spike that compact mode is supposed to avoid.
    return makeSecResult(
        SequentialEquivalenceStatus::Equivalent,
        0,
        "",
        aligned.outputCoverage,
        abstractedSequentialBoundaries,
        extractedBoundaryReports);
  }

  // Phase 3: rewrite both designs into one shared symbol space, strengthen the
  // startup frontier with reset/bootstrap facts, and build the final SEC
  // property plus the induction-friendly variant that some engines consume.
  SharedSecSymbolSpace symbolSpace = buildSharedSecSymbolSpace(
      model0, model1, aligned.inputs, aligned.outputs);
  const auto remapped = remapSecExpressions(
      model0,
      model1,
      aligned.outputs,
      symbolSpace,
      symbolSpace.problem,
      secDiagEnabled);
  const auto reachableInvariant = integrateReachableStateInvariant(
      model0,
      model1,
      aligned.inputs,
      aligned.inductiveStateEqualities,
      symbolSpace.state0Symbols,
      symbolSpace.state1Symbols,
      symbolSpace.problem,
      secDiagEnabled);
  buildSecPropertiesAndTransitions(
      model0,
      model1,
      aligned.inputs,
      aligned.outputs,
      reachableInvariant,
      symbolSpace.state0Symbols,
      symbolSpace.state1Symbols,
      remapped,
      symbolSpace.problem,
      secDiagEnabled);

  // Phase 4: hand the fully normalized SEC transition system to the requested
  // top-level engine. From here on, every engine sees the same problem and only
  // differs in how it searches for proofs or counterexamples.
  if (secDiagEnabled) {
    fprintf(stderr, "SEC diag: entering %s\n", describeSecEngine(secEngine_));
    fflush(stderr);
  }

  switch (secEngine_) {
    case SecEngine::Pdr:
      return runPdrSecEngine(
          symbolSpace.problem,
          maxK,
          solverType_,
          model0,
          model1,
          top0_,
          top1_,
          aligned.outputCoverage,
          abstractedSequentialBoundaries,
          extractedBoundaryReports);
    case SecEngine::KInduction:
      return runKInductionSecEngine(
          symbolSpace.problem,
          maxK,
          solverType_,
          model0,
          model1,
          top0_,
          top1_,
          aligned.outputCoverage,
          abstractedSequentialBoundaries,
          extractedBoundaryReports);
    case SecEngine::Imc:
      return runImcSecEngine(
          symbolSpace.problem,
          maxK,
          solverType_,
          model0,
          model1,
          top0_,
          top1_,
          aligned.outputCoverage,
          abstractedSequentialBoundaries,
          extractedBoundaryReports);
    case SecEngine::Legacy:
    default:
      return runLegacySecEngine(
          symbolSpace.problem,
          maxK,
          solverType_,
          model0,
          model1,
          top0_,
          top1_,
          aligned.outputCoverage,
          abstractedSequentialBoundaries,
          extractedBoundaryReports);
  }
}

}  // namespace KEPLER_FORMAL::SEC
