// Copyright 2024-2026 keplertech.io
// SPDX-License-Identifier: GPL-3.0-only

#include "strategy/SequentialEquivalenceStrategy.h"

#include <algorithm>
#include <cctype>
#include <cstddef>
#include <cstdio>
#include <cstdlib>
#include <iterator>
#include <map>
#include <memory>
#include <optional>
#include <set>
#include <sstream>
#include <stdexcept>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "DNL.h"
#include "NLUniverse.h"
#include "SNLPath.h"
#include "common/BoolExprUtils.h"
#include "common/AlignedSignals.h"
#include "common/SecDiag.h"
#include "imc/ExactInterpolantSynthesizer.h"
#include "imc/IMCEngine.h"
#include "kinduction/BaseCaseSolver.h"
#include "kinduction/KInductionEngine.h"
#include "kinduction/OutputBatching.h"
#include "model/SequentialDesignModel.h"
#include "pdr/PDREngine.h"
#include "proof/TransitionExprResolver.h"
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

bool hasSuffix(const std::string& value, const std::string& suffix) {
  return value.size() >= suffix.size() &&
         value.compare(value.size() - suffix.size(), suffix.size(), suffix) == 0;
}

std::vector<std::string> resetNameCandidates(const std::string& displayName) {
  // The shared SEC symbol space sees user-visible top-input names such as
  // `reset_i[0]`.  Match the same reset spelling policy as the reachable-state
  // pass so a reset discovered during model analysis remains available when
  // bootstrap constraints are converted to shared SAT symbols.
  const std::string normalized = normalizeSignalBaseName(displayName);
  std::vector<std::string> candidates = {normalized};
  if (hasSuffix(normalized, "_I")) {
    candidates.push_back(normalized.substr(0, normalized.size() - 2));
  }
  if (hasSuffix(normalized, "_NI")) {
    candidates.push_back(normalized.substr(0, normalized.size() - 1));
  }
  return candidates;
}

std::optional<bool> getResetAssertionValue(const std::string& displayName) {
  for (const auto& candidate : resetNameCandidates(displayName)) {
    if (candidate == "RESET" || candidate == "RST") {
      return true;
    }
    if (candidate == "RESET_N" || candidate == "RESETN" ||
        candidate == "RST_N" || candidate == "RSTN") {
      return false;
    }
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

bool pdrStrategyStatsEnabled() {
  return std::getenv("KEPLER_SEC_PDR_STATS") != nullptr;
}

constexpr size_t kMaxPdrGlobalResetBootstrapEqualityStates = 100000;

void emitPdrStrategyStageStats(
    bool enabled,
    size_t batchIndex,
    size_t firstOutput,
    size_t endOutput,
    const char* stage,
    size_t transitionClosureLimit,
    size_t predecessorProjectionLimit,
    size_t badCubeLimit,
    const KInductionProblem& batch) {
  if (!enabled) {
    return;
  }

  // These stage markers are intentionally coarse: when a large SEC/PDR run is
  // sampled, they identify which CEGAR retry owns the following predecessor SAT
  // traffic without flooding the log with every query.
  emitSecDiag(
      "SEC PDR stats: strategy batch=", batchIndex,
      " outputs=[", firstOutput, ",", endOutput, ")",
      " stage=", stage,
      " closure_limit=", transitionClosureLimit,
      " projection_limit=", predecessorProjectionLimit,
      " bad_cube_limit=", badCubeLimit,
      " transitions=", batch.transitions0.size() + batch.transitions1.size(),
      " init_assignments=", batch.initialStateAssignments.size(),
      " bootstrap_assignments=", batch.bootstrapStateAssignments.size(),
      " init_equalities=", batch.initialStateEqualityPairs.size(),
      " bootstrap_equalities=", batch.bootstrapStateEqualityPairs.size(),
      " inductive_equalities=", batch.inductiveStateEqualityPairs.size(),
      " observed_outputs=", batch.observedOutputExprs0.size());
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
    bool remapTransitions,
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

  if (remapTransitions) {
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
  } else {
    logSecDiagLine(
        secDiagEnabled,
        "SEC diag: deferred next-state formula remapping for k-induction");
  }
  return remapped;
}

void attachLazyTransitions(
    const SequentialDesignModel& model0,
    const SequentialDesignModel& model1,
    const std::unordered_map<SignalKey, size_t, SignalKeyHash>& state0Symbols,
    const std::unordered_map<SignalKey, size_t, SignalKeyHash>& state1Symbols,
    std::unordered_map<size_t, size_t>&& localToCombined0,
    std::unordered_map<size_t, size_t>&& localToCombined1,
    KInductionProblem& problem) {
  auto store = std::make_shared<LazyTransitionStore>();
  store->localToCombinedByDesign[0] = std::move(localToCombined0);
  store->localToCombinedByDesign[1] = std::move(localToCombined1);
  store->sourceByStateSymbol.reserve(model0.stateBits.size() + model1.stateBits.size());
  store->remappedByStateSymbol.reserve(model0.stateBits.size() + model1.stateBits.size());
  store->remapMemoByDesign[0].reserve(model0.stateBits.size());
  store->remapMemoByDesign[1].reserve(model1.stateBits.size());

  for (const auto& key : model0.stateBits) {
    const auto symbolIt = state0Symbols.find(key);
    const auto exprIt = model0.nextStateExprByStateKey.find(key);
    if (symbolIt == state0Symbols.end() ||
        exprIt == model0.nextStateExprByStateKey.end()) {
      continue;  // LCOV_EXCL_LINE
    }
    store->sourceByStateSymbol.emplace(
        symbolIt->second, LazyTransitionSource{0, exprIt->second});
  }
  for (const auto& key : model1.stateBits) {
    const auto symbolIt = state1Symbols.find(key);
    const auto exprIt = model1.nextStateExprByStateKey.find(key);
    if (symbolIt == state1Symbols.end() ||
        exprIt == model1.nextStateExprByStateKey.end()) {
      continue;  // LCOV_EXCL_LINE
    }
    store->sourceByStateSymbol.emplace(
        symbolIt->second, LazyTransitionSource{1, exprIt->second});
  }
  problem.lazyTransitions = std::move(store);
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
    // Keep the unit reset/init facts separately from the monolithic
    // initial-condition formula.  The k-induction base solver can then encode
    // only the init values for state bits that are in the current COI, instead
    // of dragging the whole design reset cone into every output proof.
    problem.initialStateAssignments.emplace_back(symbolIt->second, value);
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
    KEPLER_FORMAL::Config::SolverType solverType,
    bool deriveResetBootstrapStrengthening,
    bool deriveResetBootstrapEqualities,
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
      model0,
      model1,
      alignedInputs,
      inductiveStateEqualities,
      deriveResetBootstrapStrengthening,
      secDiagEnabled,
      solverType,
      deriveResetBootstrapEqualities);
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
  if (problem.resetBootstrapInputs.empty()) {
    // The reachable-state pass works on each extracted model and can recognize
    // reset-looking local inputs before the final shared SEC symbol space is
    // assembled. PDR/KI/IMC can only run a reset-bootstrap proof when that
    // reset also exists as an aligned environment input with one shared symbol.
    // If no such symbol was created, keep the proof in normal initial-frontier
    // mode so the initial state/equality facts remain active instead of being
    // replaced by an unconstrained "bootstrap" frontier.
    problem.resetBootstrapCycles = 0;
    problem.bootstrapStateAssignments.clear();
    problem.bootstrapStateEqualityPairs.clear();
  }
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
    KEPLER_FORMAL::Config::SolverType solverType,
    bool secDiagEnabled) {
  const auto [abstractOutputMap0, abstractOutputMap1] = buildAbstractTransitionMaps(
      model0,
      model1,
      alignedInputs,
      reachableInvariant.anchoredStateEqualities);
  logSecDiagLine(secDiagEnabled, "SEC diag: built abstract transition maps");

  if (problem.lazyTransitions == nullptr) {
    for (const auto& key : model0.stateBits) {
      problem.transitions0.emplace_back(state0Symbols.at(key), remapped.next0.at(key));
    }
    for (const auto& key : model1.stateBits) {
      problem.transitions1.emplace_back(state1Symbols.at(key), remapped.next1.at(key));
    }
  }

  BoolExpr* property = BoolExpr::createTrue();
  BoolExpr* inductionCore = BoolExpr::createTrue();
  size_t abstractEquivalentOutputCount = 0;
  size_t satImpliedOutputCount = 0;
  for (size_t i = 0; i < reachableInvariant.anchoredStateEqualities.names.size(); ++i) {
    inductionCore = BoolExpr::And(
        inductionCore,
        makeEqualityExpr(
            BoolExpr::Var(
                state0Symbols.at(reachableInvariant.anchoredStateEqualities.keys0[i])),
            BoolExpr::Var(
                state1Symbols.at(reachableInvariant.anchoredStateEqualities.keys1[i]))));
  }

  BoolExpr* inductionProperty = inductionCore;
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
      ++abstractEquivalentOutputCount;
      continue;
    }
    // A proof obligation can omit an output equality only when the current
    // induction core already excludes every assignment that would violate it.
    // This catches Boolean-equivalent post-layout cones that are not
    // structurally identical under the fast abstract-map comparison.
    if (boolFormulaImplies(inductionCore, outputEquality, solverType)) {
      ++satImpliedOutputCount;
      continue;
    }

    inductionProperty = BoolExpr::And(inductionProperty, outputEquality);
  }

  problem.property = BoolExpr::simplify(property);
  problem.bad = BoolExpr::simplify(BoolExpr::Not(problem.property));
  problem.inductionProperty = BoolExpr::simplify(inductionProperty);
  problem.inductionBad = BoolExpr::simplify(BoolExpr::Not(problem.inductionProperty));
  problem.inductionPropertyAssumesInductiveStateEqualities =
      !problem.inductiveStateEqualityPairs.empty();
  problem.description = "SEC property with aligned observed outputs";
  logSecDiagLine(secDiagEnabled, "SEC diag: built SEC and induction properties");

  if (secDiagEnabled) {
    printf(
        "SEC diag: property_is_true=%d induction_property_is_true=%d "
        "bad_is_false=%d induction_bad_is_false=%d reset_bootstrap_inputs=%zu "
        "bootstrap_cycles=%zu initial_equalities=%zu bootstrap_equalities=%zu "
        "inductive_equalities=%zu abstract_equiv_outputs=%zu "
        "sat_implied_outputs=%zu\n",
        problem.property == BoolExpr::createTrue(),
        problem.inductionProperty == BoolExpr::createTrue(),
        problem.bad == BoolExpr::createFalse(),
        problem.inductionBad == BoolExpr::createFalse(),
        problem.resetBootstrapInputs.size(),
        problem.resetBootstrapCycles,
        problem.initialStateEqualityPairs.size(),
        problem.bootstrapStateEqualityPairs.size(),
        problem.inductiveStateEqualityPairs.size(),
        abstractEquivalentOutputCount,
        satImpliedOutputCount);
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
  // PDR still needs the cheap frame-0 mismatch check before growing frames, but
  // it should not invoke the full k-induction top engine with max_k=0.  A
  // bounded engine run at k=0 is necessarily inconclusive for sequential
  // problems, which made the output-batching fallback split every output and
  // repeat the same BMC setup hundreds of times before PDR even started.
  if (auto witness = SEC::findBaseCounterexample(problem, solverType, 0);
      witness.has_value()) {
    const KInductionResult witnessResult{
        KInductionStatus::Different, witness->badFrame, std::move(witness)};
    return makeSecResult(  // LCOV_EXCL_LINE
        SequentialEquivalenceStatus::Different,
        witnessResult.bound,  // LCOV_EXCL_LINE
        formatCounterexampleWitness(witnessResult, model0, model1, top0, top1),  // LCOV_EXCL_LINE
        outputCoverage,  // LCOV_EXCL_LINE
        abstractedSequentialBoundaries,  // LCOV_EXCL_LINE
        extractedBoundaryReports);  // LCOV_EXCL_LINE
  }

  if (problem.combinedStateSymbols().empty()) {
    return makeSecResult(
        SequentialEquivalenceStatus::Equivalent,
        0,
        "",
        outputCoverage,
        abstractedSequentialBoundaries,
        extractedBoundaryReports);
  }

  auto filterPairsToSupport =
      [](const std::vector<std::pair<size_t, size_t>>& source,
         std::vector<std::pair<size_t, size_t>>& target,
         const std::unordered_set<size_t>& support) {
        target.clear();
        for (const auto& pair : source) {
          if (support.find(pair.first) != support.end() ||
              support.find(pair.second) != support.end()) {
            target.push_back(pair);
          }
        }
      };

  auto filterAssignmentsToSupport =
      [](const std::vector<std::pair<size_t, bool>>& source,
         std::vector<std::pair<size_t, bool>>& target,
         const std::unordered_set<size_t>& support) {
        target.clear();
        for (const auto& assignment : source) {
          if (support.find(assignment.first) != support.end()) {
            target.push_back(assignment);
          }
        }
      };

  auto rebuildPdrBatchStrengthening = [](KInductionProblem& batch) {
    BoolExpr* inductionProperty = BoolExpr::createTrue();
    for (const auto& [lhsSymbol, rhsSymbol] : batch.inductiveStateEqualityPairs) {
      inductionProperty = BoolExpr::And(
          inductionProperty,
          makeEqualityExpr(BoolExpr::Var(lhsSymbol), BoolExpr::Var(rhsSymbol)));
    }
    for (size_t i = 0; i < batch.observedOutputExprs0.size(); ++i) {
      inductionProperty = BoolExpr::And(
          inductionProperty,
          makeEqualityExpr(
              batch.observedOutputExprs0[i], batch.observedOutputExprs1[i]));
    }

    // PDR consumes this only as a candidate frame-strengthening lemma. The
    // engine validates both Init => lemma and lemma /\ T => lemma' before the
    // formula can constrain any bad-cube or predecessor query.
    batch.inductionProperty = BoolExpr::simplify(inductionProperty);
    batch.inductionBad = BoolExpr::simplify(BoolExpr::Not(batch.inductionProperty));
    batch.inductionPropertyAssumesInductiveStateEqualities =
        !batch.inductiveStateEqualityPairs.empty();
  };

  TransitionExprResolver pdrBatchTransitionByState(problem);
  const auto& pdrBatchPrimaryByComplement =
      pdrBatchTransitionByState.primaryByComplement();

  auto computePdrBatchSupportClosure = [&](const KInductionProblem& batch,
                                           size_t transitionClosureLimit) {
    if (batch.property == nullptr) {
      return std::unordered_set<size_t>{};  // LCOV_EXCL_LINE
    }
    const auto propertySupport = batch.property->getSupportVars();
    std::unordered_set<size_t> support(propertySupport.begin(), propertySupport.end());
    std::unordered_set<size_t> expandedTransitionStates;
    std::vector<size_t> worklist;

    auto enqueueTransitionState = [&](size_t symbol) {
      if (!pdrBatchTransitionByState.contains(symbol)) {
        if (const auto primaryIt = pdrBatchPrimaryByComplement.find(symbol);
            primaryIt != pdrBatchPrimaryByComplement.end()) {
          symbol = primaryIt->second;
        } else {
          return;
        }
      }
      support.insert(symbol);
      if (expandedTransitionStates.insert(symbol).second) {
        worklist.push_back(symbol);
      }
    };

    for (const auto propertySymbol : propertySupport) {
      enqueueTransitionState(propertySymbol);
    }
    for (size_t cursor = 0;
         cursor < worklist.size() &&
         support.size() < transitionClosureLimit;
         ++cursor) {
      for (const auto dependency : pdrBatchTransitionByState.support(worklist[cursor])) {
        if (support.insert(dependency).second) {
          enqueueTransitionState(dependency);
        }
      }
    }
    return support;
  };

  auto prunePdrBatchStrengthening = [&](KInductionProblem& batch,
                                        size_t transitionClosureLimit) {
    auto support =
        computePdrBatchSupportClosure(batch, transitionClosureLimit);

    // A PDR output slice should not inherit every state-equality/reset fact in
    // an ASIC-size SEC problem. Keep only the relational startup and inductive
    // facts connected to the current property through a bounded transition
    // cone. One-step pruning is too weak for PDR because predecessor blocking
    // walks backwards through multiple transition layers; the bounded closure
    // keeps those real dependencies without reintroducing the full-design
    // million-symbol relational init surface.
    filterPairsToSupport(
        problem.initialStateEqualityPairs, batch.initialStateEqualityPairs, support);
    filterPairsToSupport(
        problem.bootstrapStateEqualityPairs, batch.bootstrapStateEqualityPairs, support);
    filterPairsToSupport(
        problem.inductiveStateEqualityPairs, batch.inductiveStateEqualityPairs, support);
    filterAssignmentsToSupport(
        problem.initialStateAssignments, batch.initialStateAssignments, support);
    filterAssignmentsToSupport(
        problem.bootstrapStateAssignments, batch.bootstrapStateAssignments, support);
    for (const auto& pair : batch.initialStateEqualityPairs) {
      support.insert(pair.first);
      support.insert(pair.second);
    }
    for (const auto& pair : batch.bootstrapStateEqualityPairs) {
      support.insert(pair.first);
      support.insert(pair.second);
    }
    for (const auto& pair : batch.inductiveStateEqualityPairs) {
      support.insert(pair.first);
      support.insert(pair.second);
    }
    for (const auto& assignment : batch.initialStateAssignments) {
      support.insert(assignment.first);
    }
    for (const auto& assignment : batch.bootstrapStateAssignments) {
      support.insert(assignment.first);
    }
    rebuildPdrBatchStrengthening(batch);

    if (batch.lazyTransitions != nullptr) {
      auto& store = *batch.lazyTransitions;
      batch.transitions0.clear();
      batch.transitions1.clear();
      constexpr size_t kMaxEagerRemappedPdrBatchTransitions = 1024;
      if (support.size() > kMaxEagerRemappedPdrBatchTransitions) {
        // Keep large ASIC batches lazy.  Sampling on BlackParrot showed that
        // eagerly remapping a 12k-symbol support closure built more than a
        // million transition DAG nodes before the first PDR SAT query.  The
        // transition resolver still has the exact support closure above, and
        // will remap only the transitions that PDR actually encodes.
        return;
      }
      batch.transitions0.reserve(support.size());
      batch.transitions1.reserve(support.size());

      // Sampling on BlackParrot showed the proof spending time lazily remapping
      // next-state expressions inside predecessor queries. Once the batch cone
      // is already pruned to the output support closure, remap those relevant
      // transitions eagerly here so PDR reuses them across all obligations in
      // the batch instead of materializing them piecemeal during SAT queries.
      for (const auto symbol : support) {
        const auto sourceIt = store.sourceByStateSymbol.find(symbol);
        if (sourceIt == store.sourceByStateSymbol.end()) {
          continue;
        }

        BoolExpr* remapped = nullptr;
        if (const auto cachedIt = store.remappedByStateSymbol.find(symbol);
            cachedIt != store.remappedByStateSymbol.end()) {
          remapped = cachedIt->second;
        } else {
          const LazyTransitionSource& source = sourceIt->second;
          remapped = remapBoolExprVariables(
              source.localExpr,
              store.localToCombinedByDesign[source.designIndex],
              store.remapMemoByDesign[source.designIndex]);
          store.remappedByStateSymbol.emplace(symbol, remapped);
        }

        if (sourceIt->second.designIndex == 0) {
          batch.transitions0.emplace_back(symbol, remapped);
        } else {
          batch.transitions1.emplace_back(symbol, remapped);
        }
      }
    }
  };

  auto prunePdrBatchRelations = [&](KInductionProblem& batch,
                                    size_t transitionClosureLimit) {
    prunePdrBatchStrengthening(batch, transitionClosureLimit);
  };

  // PDR is still proving real PDR obligations, but wide ASIC SEC properties are
  // better handled as output-cone slices. This keeps reset-bootstrap F[0]
  // strengthening and blocking queries local to a small property instead of
  // materializing every observed output in one frame.
  //
  // Keep each PDR batch bounded, but do not prove one output per engine run.
  // BlackParrot sampling showed the one-output mode repeating the same
  // reset-frontier and PDR blocking work hundreds of times.  A moderate batch
  // still proves a real conjunction slice. If projected PDR finds a
  // counterexample on a multi-output slice, escalate PDR precision first and
  // avoid broad concrete-BMC validation until the final exact retry.
  constexpr OutputBatchingLimits kPdrOutputBatchingLimits{16, 512};
  constexpr size_t kPdrBatchTransitionClosureLimit = 12000;
  constexpr size_t kRefinedPdrBatchTransitionClosureLimit = 60000;
  struct PdrOutputBatch {
    size_t firstOutput = 0;
    size_t endOutput = 0;
    bool startAtFinalExact = false;
  };
  std::vector<PdrOutputBatch> outputBatches;
  for (const auto& [firstOutput, endOutput] :
       buildSupportBoundedOutputBatches(problem, kPdrOutputBatchingLimits)) {
    outputBatches.push_back({firstOutput, endOutput, false});
  }
  KInductionProblem batchProblem = problem;
  size_t provedBound = 0;
  const bool emitPdrStageStats = pdrStrategyStatsEnabled();
  struct FinalPdrStageOutcome {
    bool equivalent = false;
    bool shouldSplit = false;
    std::optional<SequentialEquivalenceResult> terminalResult;
  };
  auto runFinalExactPdrStage =
      [&](size_t batchIndex,
          size_t firstOutput,
          size_t endOutput) -> FinalPdrStageOutcome {
    constexpr size_t kMaxPdrConcreteValidationOutputs = 1;
    constexpr size_t kMaxFinalExactPdrOutputBatchSize =
        kPdrOutputBatchingLimits.maxOutputBatchSize;
    constexpr size_t kFinalExactPdrPredecessorProjectionLimit = 32;
    constexpr size_t kFinalExactPdrBadCubeStateLimit = 32;
    constexpr size_t kFinalExactPdrRootGeneralizationAttempts = 0;
    if (endOutput - firstOutput > kMaxFinalExactPdrOutputBatchSize) {
      if (emitPdrStageStats) {
        emitSecDiag(
            "SEC PDR stats: splitting before final exact repair ",
            "outputs=[", firstOutput, ",", endOutput, ")",
            " limit=", kMaxFinalExactPdrOutputBatchSize);
      }
      FinalPdrStageOutcome outcome;
      outcome.shouldSplit = true;
      return outcome;
    }

    KInductionProblem validationProblem = problem;
    configureOutputBatchProblem(
        validationProblem, problem, firstOutput, endOutput);

    KInductionProblem fullExactBatchProblem = problem;
    configureOutputBatchProblem(
        fullExactBatchProblem, problem, firstOutput, endOutput);
    // Keep the full transition relation for this output slice during the
    // final exact retry, but do not reintroduce unrelated startup/induction
    // facts from the rest of the SEC problem. Those global relations are
    // useful for broad proofs, yet they can dominate SAT encoding once this
    // last retry is focused on a bounded slice.
    prunePdrBatchStrengthening(
        fullExactBatchProblem, kRefinedPdrBatchTransitionClosureLimit);
    const bool finalBatchCanValidateConcrete =
        endOutput - firstOutput <= kMaxPdrConcreteValidationOutputs;
    const bool finalBatchCanRefineProjectedCounterexamples = true;
    const bool finalSliceUsesBadFormulaValidation =
        endOutput - firstOutput <=
        kPdrOutputBatchingLimits.maxOutputBatchSize;
    // In SEC mode every reported difference is validated by a concrete
    // bounded-prefix check before it escapes this strategy. Keep final PDR over
    // the reset-frontier over-approximation instead of spending ASIC runtime in
    // per-cube exact reset-image queries; proving the over-approximation safe
    // is still sound for the concrete design pair.
    const bool finalSliceUsesResetFrontier = false;
    const size_t finalPdrPredecessorProjectionLimit =
        kFinalExactPdrPredecessorProjectionLimit;
    const size_t finalPdrBadCubeStateLimit =
        kFinalExactPdrBadCubeStateLimit;
    emitPdrStrategyStageStats(
        emitPdrStageStats,
        batchIndex,
        firstOutput,
        endOutput,
        "full_exact_strengthening_pruned",
        kRefinedPdrBatchTransitionClosureLimit,
        finalPdrPredecessorProjectionLimit,
        finalPdrBadCubeStateLimit,
        fullExactBatchProblem);
    PDREngine fullExactPdrEngine(
        fullExactBatchProblem,
        solverType,
        finalPdrPredecessorProjectionLimit,
        finalPdrBadCubeStateLimit,
        /*useExactFrameClauses=*/true,
        /*maxPredecessorQueries=*/0,
        /*refineProjectedCounterexamples=*/
            finalBatchCanRefineProjectedCounterexamples,
        /*maxBoundedRootGeneralizationAttempts=*/
            kFinalExactPdrRootGeneralizationAttempts,
        /*learnValidatedBadFormulaClauses=*/finalSliceUsesBadFormulaValidation,
        /*useExactResetFrontierChecks=*/finalSliceUsesResetFrontier);
    const auto fullExactPdrResult = fullExactPdrEngine.run(maxK, true);
    if (fullExactPdrResult.status == PDRStatus::Equivalent) {
      if (finalBatchCanValidateConcrete) {
        if (auto fullExactWitness = SEC::findBaseCounterexample(
                validationProblem, solverType, maxK);
            fullExactWitness.has_value()) {
          const KInductionResult witnessResult{
              KInductionStatus::Different,
              fullExactWitness->badFrame,
              std::move(fullExactWitness)};
          FinalPdrStageOutcome outcome;
          outcome.terminalResult = makeSecResult(
              SequentialEquivalenceStatus::Different,
              witnessResult.bound,
              formatCounterexampleWitness(
                  witnessResult, model0, model1, top0, top1),
              outputCoverage,
              abstractedSequentialBoundaries,
              extractedBoundaryReports);
          return outcome;
        }
      }
      provedBound = std::max(provedBound, fullExactPdrResult.bound);
      FinalPdrStageOutcome outcome;
      outcome.equivalent = true;
      return outcome;
    }
    if (fullExactPdrResult.status == PDRStatus::Different) {
      std::optional<KInductionResult::CounterexampleWitness>
          fullExactWitness;
      if (finalBatchCanValidateConcrete) {
        fullExactWitness = SEC::findBaseCounterexampleAtFrontier(
            validationProblem, solverType, fullExactPdrResult.bound);
      }
      if (fullExactWitness.has_value()) {
        const KInductionResult witnessResult{
            KInductionStatus::Different,
            fullExactPdrResult.bound,
            std::move(fullExactWitness)};
        FinalPdrStageOutcome outcome;
        outcome.terminalResult = makeSecResult(
            SequentialEquivalenceStatus::Different,
            fullExactPdrResult.bound,
            formatCounterexampleWitness(
                witnessResult, model0, model1, top0, top1),
            outputCoverage,
            abstractedSequentialBoundaries,
            extractedBoundaryReports);
        return outcome;
      }
    }
    if (endOutput - firstOutput > 1) {
      FinalPdrStageOutcome outcome;
      outcome.shouldSplit = true;
      return outcome;
    }
    const std::string outputName =
        firstOutput < problem.observedOutputNames.size()
            ? problem.observedOutputNames[firstOutput]
            : std::to_string(firstOutput);  // LCOV_EXCL_LINE
    FinalPdrStageOutcome outcome;
    outcome.terminalResult = makeSecResult(
        SequentialEquivalenceStatus::Inconclusive,
        fullExactPdrResult.bound,
        "PDR reached an abstract counterexample that concrete BMC did not "
        "validate for output `" +
            outputName + "` at k = " +
            std::to_string(fullExactPdrResult.bound),
        outputCoverage,
        abstractedSequentialBoundaries,
        extractedBoundaryReports);
    return outcome;
  };

  auto splitPdrBatchAtFinalStage =
      [&](size_t batchIndex, size_t firstOutput, size_t endOutput) {
    const size_t midOutput = firstOutput + (endOutput - firstOutput) / 2;
    outputBatches.insert(
        outputBatches.begin() + static_cast<std::ptrdiff_t>(batchIndex + 1),
        {PdrOutputBatch{firstOutput, midOutput, true},
         PdrOutputBatch{midOutput, endOutput, true}});
  };

  for (size_t batchIndex = 0; batchIndex < outputBatches.size(); ++batchIndex) {
    const auto [firstOutput, endOutput, startAtFinalExact] =
        outputBatches[batchIndex];
    if (startAtFinalExact) {
      const FinalPdrStageOutcome finalOutcome =
          runFinalExactPdrStage(batchIndex, firstOutput, endOutput);
      if (finalOutcome.terminalResult.has_value()) {
        return *finalOutcome.terminalResult;
      }
      if (finalOutcome.shouldSplit) {
        splitPdrBatchAtFinalStage(batchIndex, firstOutput, endOutput);
      }
      continue;
    }
    configureOutputBatchProblem(batchProblem, problem, firstOutput, endOutput);
    prunePdrBatchRelations(batchProblem, kPdrBatchTransitionClosureLimit);
    // ASIC SEC runs need smaller carried predecessor obligations than the
    // standalone PDR engine default.  This does not change the PDR proof rule:
    // every learned clause is still justified by an UNSAT predecessor query,
    // and every reported counterexample is still checked by concrete BMC.
    constexpr size_t kSecPdrPredecessorProjectionLimit = 4;
    constexpr size_t kProjectedPdrPredecessorQueryBudget = 5000;
    constexpr bool kValidateProjectedPdrCandidatesBeforeFinal = false;
    emitPdrStrategyStageStats(
        emitPdrStageStats,
        batchIndex,
        firstOutput,
        endOutput,
        "initial",
        kPdrBatchTransitionClosureLimit,
        kSecPdrPredecessorProjectionLimit,
        kSecPdrPredecessorProjectionLimit,
        batchProblem);
    PDREngine pdrEngine(
        batchProblem,
        solverType,
        kSecPdrPredecessorProjectionLimit,
        kSecPdrPredecessorProjectionLimit,
        /*useExactFrameClauses=*/false,
        kProjectedPdrPredecessorQueryBudget,
        /*refineProjectedCounterexamples=*/false,
        PDREngine::kDefaultBoundedRootGeneralizationAttempts,
        /*learnValidatedBadFormulaClauses=*/false,
        /*useExactResetFrontierChecks=*/false);
    const auto pdrResult = pdrEngine.run(maxK, true);
    switch (pdrResult.status) {
      case PDRStatus::Equivalent:
        provedBound = std::max(provedBound, pdrResult.bound);
        break;
      case PDRStatus::Different: {
        // Exact concrete validation remains a one-output leaf operation. The
        // final exact PDR retry can now repair a moderate batch by validating
        // each output-bad formula separately, so do not split the batch until
        // all precision stages have had that proof-preserving repair chance.
        constexpr size_t kMaxPdrConcreteValidationOutputs = 1;
        KInductionProblem validationProblem = problem;
        configureOutputBatchProblem(
            validationProblem, problem, firstOutput, endOutput);
        std::optional<KInductionResult::CounterexampleWitness> witness;
        if (kValidateProjectedPdrCandidatesBeforeFinal &&
            endOutput - firstOutput <= kMaxPdrConcreteValidationOutputs) {
          witness = SEC::findBaseCounterexampleAtFrontier(
              validationProblem, solverType, pdrResult.bound);
        }
        if (!witness.has_value()) {
          // ASIC cones can still produce an abstract trace when the local
          // relation slice is too small. Retry the same output batch with more
          // relation / predecessor context before concrete validation. This
          // keeps the proof as real PDR over the conjunction slice while
          // avoiding the measured 598-pass one-output loop on BlackParrot. Any
          // reported difference is still accepted only after concrete BMC
          // validation below.
          // The initial 4-literal projection can be too abstract on a widened
          // ASIC relation, but BlackParrot measurements showed that jumping
          // straight to 64 literals creates a large level-1 blocked-predecessor
          // enumeration loop. Use an intermediate precision step before the
          // later exact retries.
          constexpr size_t kModeratePdrPredecessorProjectionLimit = 16;
          // Exact-frame retries need more predecessor context than the
          // moderate projection to avoid abstract counterexamples, but fully
          // unbounded predecessor cubes were measured to enumerate thousands of
          // adjacent SAT models on BlackParrot. Use this bounded midpoint for
          // exact-frame passes.
          constexpr size_t kExactFramePdrPredecessorProjectionLimit = 32;
          // Projected CEGAR stages are allowed to be inconclusive. If they
          // keep finding abstract SAT predecessors without strengthening the
          // frames, stop that stage and move to the stronger exact-frame PDR
          // retry instead of enumerating the same projected space for minutes.
          KInductionProblem refinedBatchProblem = problem;
          configureOutputBatchProblem(
              refinedBatchProblem, problem, firstOutput, endOutput);
          prunePdrBatchRelations(
              refinedBatchProblem, kRefinedPdrBatchTransitionClosureLimit);

          // If concrete BMC rejects the first projected trace, first widen the
          // relation slice while keeping predecessor cubes small. Sampling on
          // BlackParrot showed that widening predecessor cubes before the
          // relation makes PDR enumerate thousands of exact level-1
          // predecessors. A wider relation can remove the abstraction that
          // produced the trace without abandoning the compact PDR obligation
          // shape that keeps ASIC proofs tractable.
          emitPdrStrategyStageStats(
              emitPdrStageStats,
              batchIndex,
              firstOutput,
              endOutput,
              "widened_relation",
              kRefinedPdrBatchTransitionClosureLimit,
              kSecPdrPredecessorProjectionLimit,
              kSecPdrPredecessorProjectionLimit,
              refinedBatchProblem);
          PDREngine refinedPdrEngine(
              refinedBatchProblem,
              solverType,
              kSecPdrPredecessorProjectionLimit,
              kSecPdrPredecessorProjectionLimit,
              /*useExactFrameClauses=*/false,
              kProjectedPdrPredecessorQueryBudget,
              /*refineProjectedCounterexamples=*/false,
              PDREngine::kDefaultBoundedRootGeneralizationAttempts,
              /*learnValidatedBadFormulaClauses=*/false,
              /*useExactResetFrontierChecks=*/false);
          const auto refinedPdrResult = refinedPdrEngine.run(maxK, true);
          if (refinedPdrResult.status == PDRStatus::Equivalent) {
            provedBound = std::max(provedBound, refinedPdrResult.bound);
            break;
          }
          if (refinedPdrResult.status == PDRStatus::Different) {
            std::optional<KInductionResult::CounterexampleWitness> refinedWitness;
            if (kValidateProjectedPdrCandidatesBeforeFinal &&
                endOutput - firstOutput <= kMaxPdrConcreteValidationOutputs) {
              refinedWitness = SEC::findBaseCounterexampleAtFrontier(
                  validationProblem, solverType, refinedPdrResult.bound);
            }
            if (refinedWitness.has_value()) {
              const KInductionResult witnessResult{
                  KInductionStatus::Different,
                  refinedPdrResult.bound,
                  std::move(refinedWitness)};
              return makeSecResult(
                  SequentialEquivalenceStatus::Different,
                  refinedPdrResult.bound,
                  formatCounterexampleWitness(
                      witnessResult, model0, model1, top0, top1),
                  outputCoverage,
                  abstractedSequentialBoundaries,
                  extractedBoundaryReports);
            }
          }
          // If the wider relation still finds only an abstract trace, grow the
          // predecessor projection moderately on that same relation.  This is
          // a precision refinement, not a proof shortcut; any reported
          // difference is still validated by concrete BMC below.
          KInductionProblem widenedBatchProblem = refinedBatchProblem;
          emitPdrStrategyStageStats(
              emitPdrStageStats,
              batchIndex,
              firstOutput,
              endOutput,
              "widened_relation_moderate_projection",
              kRefinedPdrBatchTransitionClosureLimit,
              kModeratePdrPredecessorProjectionLimit,
              kModeratePdrPredecessorProjectionLimit,
              widenedBatchProblem);
          PDREngine widenedPdrEngine(
              widenedBatchProblem,
              solverType,
              kModeratePdrPredecessorProjectionLimit,
              kModeratePdrPredecessorProjectionLimit,
              /*useExactFrameClauses=*/false,
              kProjectedPdrPredecessorQueryBudget,
              /*refineProjectedCounterexamples=*/false,
              PDREngine::kDefaultBoundedRootGeneralizationAttempts,
              /*learnValidatedBadFormulaClauses=*/false,
              /*useExactResetFrontierChecks=*/false);
          const auto widenedPdrResult = widenedPdrEngine.run(maxK, true);
          if (widenedPdrResult.status == PDRStatus::Equivalent) {
            provedBound = std::max(provedBound, widenedPdrResult.bound);
            break;
          }
          if (widenedPdrResult.status == PDRStatus::Different) {
            std::optional<KInductionResult::CounterexampleWitness> widenedWitness;
            if (kValidateProjectedPdrCandidatesBeforeFinal &&
                endOutput - firstOutput <= kMaxPdrConcreteValidationOutputs) {
              widenedWitness = SEC::findBaseCounterexampleAtFrontier(
                  validationProblem, solverType, widenedPdrResult.bound);
            }
            if (widenedWitness.has_value()) {
              const KInductionResult witnessResult{
                  KInductionStatus::Different,
                  widenedPdrResult.bound,
                  std::move(widenedWitness)};
              return makeSecResult(
                  SequentialEquivalenceStatus::Different,
                  widenedPdrResult.bound,
                  formatCounterexampleWitness(
                      witnessResult, model0, model1, top0, top1),
                  outputCoverage,
                  abstractedSequentialBoundaries,
                  extractedBoundaryReports);
            }
          }
          // Last retry on the widened relation slice: keep the complete
          // learned frame, but keep carried predecessor cubes bounded. Sampling
          // on BlackParrot showed that unbounded predecessor cubes made exact
          // PDR enumerate thousands of adjacent full SAT models; exact frame
          // clauses are the part that removes stale abstract predecessors.
          emitPdrStrategyStageStats(
              emitPdrStageStats,
              batchIndex,
              firstOutput,
              endOutput,
              "widened_relation_exact",
              kRefinedPdrBatchTransitionClosureLimit,
              kExactFramePdrPredecessorProjectionLimit,
              kExactFramePdrPredecessorProjectionLimit,
              widenedBatchProblem);
          PDREngine exactPdrEngine(
              widenedBatchProblem,
              solverType,
              kExactFramePdrPredecessorProjectionLimit,
              kExactFramePdrPredecessorProjectionLimit,
              /*useExactFrameClauses=*/true,
              /*maxPredecessorQueries=*/0,
              /*refineProjectedCounterexamples=*/false,
              PDREngine::kDefaultBoundedRootGeneralizationAttempts,
              /*learnValidatedBadFormulaClauses=*/false,
              /*useExactResetFrontierChecks=*/false);
          const auto exactPdrResult = exactPdrEngine.run(maxK, true);
          if (exactPdrResult.status == PDRStatus::Equivalent) {
            provedBound = std::max(provedBound, exactPdrResult.bound);
            break;
          }
          if (exactPdrResult.status == PDRStatus::Different) {
            std::optional<KInductionResult::CounterexampleWitness> exactWitness;
            if (kValidateProjectedPdrCandidatesBeforeFinal &&
                endOutput - firstOutput <= kMaxPdrConcreteValidationOutputs) {
              exactWitness = SEC::findBaseCounterexampleAtFrontier(
                  validationProblem, solverType, exactPdrResult.bound);
            }
            if (exactWitness.has_value()) {
              const KInductionResult witnessResult{
                  KInductionStatus::Different,
                  exactPdrResult.bound,
                  std::move(exactWitness)};
              return makeSecResult(
                  SequentialEquivalenceStatus::Different,
                  exactPdrResult.bound,
                  formatCounterexampleWitness(
                      witnessResult, model0, model1, top0, top1),
                  outputCoverage,
                  abstractedSequentialBoundaries,
                  extractedBoundaryReports);
            }
          }
          const FinalPdrStageOutcome finalOutcome =
              runFinalExactPdrStage(batchIndex, firstOutput, endOutput);
          if (finalOutcome.terminalResult.has_value()) {
            return *finalOutcome.terminalResult;
          }
          if (finalOutcome.equivalent) {
            break;
          }
          if (finalOutcome.shouldSplit) {
            splitPdrBatchAtFinalStage(batchIndex, firstOutput, endOutput);
            break;
          }
        }
        const KInductionResult witnessResult{
            KInductionStatus::Different, pdrResult.bound, std::move(witness)};
        return makeSecResult(
            SequentialEquivalenceStatus::Different,
            pdrResult.bound,
            formatCounterexampleWitness(witnessResult, model0, model1, top0, top1),
            outputCoverage,
            abstractedSequentialBoundaries,
            extractedBoundaryReports);
      }
      case PDRStatus::Inconclusive:
      default:
        return makeSecResult(
            SequentialEquivalenceStatus::Inconclusive,
            pdrResult.bound,
            "Reached max_k without a proof or counterexample",
            outputCoverage,
            abstractedSequentialBoundaries,
            extractedBoundaryReports);
    }
  }

  return makeSecResult(
      SequentialEquivalenceStatus::Equivalent,
      provedBound,
      "",
      outputCoverage,
      abstractedSequentialBoundaries,
      extractedBoundaryReports);
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
  // KI and PDR both work on small COI slices of a potentially huge SEC
  // problem. Keep next-state formulas in their extracted-model symbol space
  // until the proof engine actually asks for a transition; otherwise PDR
  // materializes the full ASIC transition relation before output batching can
  // prune it.
  const bool useLazyTransitionRemapping =
      secEngine_ == SecEngine::KInduction || secEngine_ == SecEngine::Pdr;
  const auto remapped = remapSecExpressions(
      model0,
      model1,
      aligned.outputs,
      symbolSpace,
      symbolSpace.problem,
      !useLazyTransitionRemapping,
      secDiagEnabled);
  // KI / IMC consume explicit post-reset state values directly. SEC/PDR keeps
  // the reset cycle/input model and validates startup candidates with concrete
  // BMC / reset-frontier checks, so it can avoid the sampled full-design sweep
  // that tries to constant-evaluate every state bit before the first PDR query.
  const bool deriveResetBootstrapStrengthening = secEngine_ != SecEngine::Pdr;
  const size_t totalStateBits = model0.stateBits.size() + model1.stateBits.size();
  const bool deriveResetBootstrapEqualities =
      secEngine_ != SecEngine::Pdr ||
      totalStateBits <= kMaxPdrGlobalResetBootstrapEqualityStates;
  if (secDiagEnabled && secEngine_ == SecEngine::Pdr &&
      !deriveResetBootstrapEqualities) {
    fprintf(
        stderr,
        "SEC diag: skipping global PDR reset-bootstrap equality mining for "
        "%zu state bits (limit=%zu)\n",
        totalStateBits,
        kMaxPdrGlobalResetBootstrapEqualityStates);
    fflush(stderr);
  }
  const auto reachableInvariant = integrateReachableStateInvariant(
      model0,
      model1,
      aligned.inputs,
      aligned.inductiveStateEqualities,
      symbolSpace.state0Symbols,
      symbolSpace.state1Symbols,
      symbolSpace.problem,
      solverType_,
      deriveResetBootstrapStrengthening,
      deriveResetBootstrapEqualities,
      secDiagEnabled);
  if (useLazyTransitionRemapping) {
    attachLazyTransitions(
        model0,
        model1,
        symbolSpace.state0Symbols,
        symbolSpace.state1Symbols,
        std::move(symbolSpace.localToCombined0),
        std::move(symbolSpace.localToCombined1),
        symbolSpace.problem);
  }
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
      solverType_,
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
