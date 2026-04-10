// Copyright 2024-2026 keplertech.io
// SPDX-License-Identifier: GPL-3.0-only

#include "strategy/SequentialEquivalenceStrategy.h"

#include <algorithm>
#include <cctype>
#include <iterator>
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
#include "kinduction/KInductionEngine.h"
#include "model/SequentialDesignModel.h"

namespace KEPLER_FORMAL::SEC {

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
    key.first.push_back(stableSignalKeyNameID(name.getString()));
  }
  key.first.push_back(
      stableSignalKeyNameID(terminal.getSnlBitTerm()->getName().getString()));
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
    oss << ", ... +" << (values.size() - printed) << " more";
  }
  return oss.str();
}

std::vector<std::string> setDifference(const std::set<std::string>& lhs,
                                       const std::set<std::string>& rhs) {
  std::vector<std::string> diff;
  std::set_difference(
      lhs.begin(), lhs.end(), rhs.begin(), rhs.end(), std::back_inserter(diff));
  return diff;
}

struct ScopedDnlContext {
  explicit ScopedDnlContext(naja::NL::SNLDesign* top)
      : universe_(naja::NL::NLUniverse::get()),
        previousTop_(universe_ ? universe_->getTopDesign() : nullptr) {
    if (universe_ == nullptr) {
      throw std::runtime_error("NLUniverse not created for SEC cone tracing");
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
      continue;
    }
    if (getTerminalDisplayName(term) == signalName) {
      return termID;
    }
  }
  return std::nullopt;
}

std::optional<naja::DNL::DNLID> findTermByKey(naja::DNL::DNLFull* dnl,
                                              const SignalKey& key) {
  for (naja::DNL::DNLID termID = 0; termID < dnl->getDNLTerms().size(); ++termID) {
    const auto& term = dnl->getDNLTerminalFromID(termID);
    if (term.isNull()) {
      continue;
    }
    if (getTerminalPathKey(term) == key) {
      return termID;
    }
  }
  return std::nullopt;
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
    return "<null>";
  }
  if (term.getIsoID() == naja::DNL::DNLID_MAX) {
    return getTerminalDisplayName(term);
  }

  const auto& iso = dnl->getDNLIsoDB().getIsoFromIsoIDconst(term.getIsoID());
  if (iso.isConstant0()) {
    return "Constant 0";
  }
  if (iso.isConstant1()) {
    return "Constant 1";
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
    return trace;
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
        levelTerms.insert("Constant 0");
        continue;
      }
      if (iso.isConstant1()) {
        levelTerms.insert("Constant 1");
        continue;
      }

      for (const auto driver : iso.getDrivers()) {
        if (driver == naja::DNL::DNLID_MAX) {
          continue;
        }

        const auto& driverTerm = dnl->getDNLTerminalFromID(driver);
        if (driverTerm.isNull()) {
          continue;
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
            continue;
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
    return "    <no traced cone terms>\n";
  }

  std::ostringstream oss;
  const size_t printedLevels = std::min(trace.levels.size(), kMaxLevels);
  for (size_t level = 0; level < printedLevels; ++level) {
    oss << "    step " << level << ": "
        << formatStringList(trace.levels[level], kMaxTermsPerLevel) << "\n";
  }
  if (trace.levels.size() > printedLevels) {
    oss << "    ... +" << (trace.levels.size() - printedLevels)
        << " more trace steps\n";
  }
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
    report.error =
        "could not resolve the differing SEC signal back into the DNL";
    return report;
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
    return "";
  }
  const auto& differencePoint = witness.outputMismatches.front();

  std::ostringstream oss;
  oss << "Traceback for first differing point `" << differencePoint.signal
      << "` at cycle " << witness.badFrame << ":\n";

  try {
    const auto report0 = buildConeDiffReport(
        top0, differencePoint.signal, model0.environmentInputs);
    const auto report1 = buildConeDiffReport(
        top1, differencePoint.signal, model1.environmentInputs);

    if (!report0.error.empty() || !report1.error.empty()) {
      oss << "  Cone traceback unavailable: ";
      if (!report0.error.empty()) {
        oss << "design0 " << report0.error;
      }
      if (!report0.error.empty() && !report1.error.empty()) {
        oss << "; ";
      }
      if (!report1.error.empty()) {
        oss << "design1 " << report1.error;
      }
      oss << "\n";
      return oss.str();
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
    oss << "  Cone traceback unavailable: " << e.what() << "\n";
  }

  return oss.str();
}

std::string formatCounterexampleWitness(const KInductionResult& result,
                                        const SequentialDesignModel& model0,
                                        const SequentialDesignModel& model1,
                                        naja::NL::SNLDesign* top0,
                                        naja::NL::SNLDesign* top1) {
  if (!result.witness.has_value()) {
    return "";
  }

  const auto& witness = *result.witness;
  std::ostringstream oss;
  oss << "Counterexample reaches the first bad frame at cycle "
      << witness.badFrame << ".\n";

  if (witness.inputTrace.empty()) {
    oss << "Input trace: <none>\n";
  } else {
    oss << "Input trace:\n";
    for (const auto& frame : witness.inputTrace) {
      oss << "  cycle " << frame.frame << ": ";
      if (frame.assignments.empty()) {
        oss << "<no environment inputs>";
      } else {
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

struct AlignedSignals {
  std::vector<std::string> names;
  std::vector<SignalKey> keys0;
  std::vector<SignalKey> keys1;
};

std::unordered_map<std::string, SignalKey> buildNameToKeyMap(
    const std::vector<SignalKey>& keys,
    const std::unordered_map<SignalKey, std::string, SignalKeyHash>& displayNames,
    const char* label) {
  std::unordered_map<std::string, SignalKey> byName;
  for (const auto& key : keys) {
    const auto nameIt = displayNames.find(key);
    if (nameIt == displayNames.end()) {
      throw std::runtime_error(
          std::string("Missing display name for SEC ") + label);
    }
    const auto [_, inserted] = byName.emplace(nameIt->second, key);
    if (!inserted) {
      throw std::runtime_error(
          std::string("Duplicate SEC ") + label + " name `" + nameIt->second + "`");
    }
  }
  return byName;
}

std::vector<std::string> sortedNames(
    const std::unordered_map<std::string, SignalKey>& byName) {
  std::vector<std::string> names;
  names.reserve(byName.size());
  for (const auto& [name, _] : byName) {
    names.push_back(name);
  }
  std::sort(names.begin(), names.end());
  return names;
}

AlignedSignals collectCommonSignalsByName(
    const std::vector<SignalKey>& keys0,
    const std::unordered_map<SignalKey, std::string, SignalKeyHash>& displayNames0,
    const std::vector<SignalKey>& keys1,
    const std::unordered_map<SignalKey, std::string, SignalKeyHash>& displayNames1,
    const char* label) {
  const auto byName0 = buildNameToKeyMap(keys0, displayNames0, label);
  const auto byName1 = buildNameToKeyMap(keys1, displayNames1, label);

  AlignedSignals aligned;
  const auto names0 = sortedNames(byName0);
  for (const auto& name : names0) {
    const auto it1 = byName1.find(name);
    if (it1 == byName1.end()) {
      continue;
    }
    aligned.names.push_back(name);
    aligned.keys0.push_back(byName0.at(name));
    aligned.keys1.push_back(it1->second);
  }
  return aligned;
}

AlignedSignals alignSignalsByName(
    const std::vector<SignalKey>& keys0,
    const std::unordered_map<SignalKey, std::string, SignalKeyHash>& displayNames0,
    const std::vector<SignalKey>& keys1,
    const std::unordered_map<SignalKey, std::string, SignalKeyHash>& displayNames1,
    const char* label) {
  const auto byName0 = buildNameToKeyMap(keys0, displayNames0, label);
  const auto byName1 = buildNameToKeyMap(keys1, displayNames1, label);
  const auto names0 = sortedNames(byName0);
  const auto names1 = sortedNames(byName1);
  if (names0 != names1) {
    throw std::runtime_error(describeMismatchedNames(names0, names1, label));
  }

  AlignedSignals aligned;
  aligned.names = names0;
  aligned.keys0.reserve(names0.size());
  aligned.keys1.reserve(names0.size());
  for (const auto& name : names0) {
    aligned.keys0.push_back(byName0.at(name));
    aligned.keys1.push_back(byName1.at(name));
  }
  return aligned;
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
    KEPLER_FORMAL::Config::SolverType solverType)
    : top0_(top0), top1_(top1), solverType_(solverType) {}

SequentialEquivalenceResult SequentialEquivalenceStrategy::run(size_t maxK) const {
  // Step 1: extract both tops into the same normalized SEC representation.
  SequentialDesignModel model0 = SequentialDesignModel::extract(top0_);
  SequentialDesignModel model1 = SequentialDesignModel::extract(top1_);

  if (model0.hasUnsupportedFeatures() || model1.hasUnsupportedFeatures()) {
    std::vector<std::string> reasons = model0.unsupportedReasons;
    reasons.insert(
        reasons.end(),
        model1.unsupportedReasons.begin(),
        model1.unsupportedReasons.end());
    return {
        SequentialEquivalenceStatus::Unsupported,
        0,
        joinReasons(reasons),
    };
  }

  // Step 2: SEC only makes sense when the observable interfaces align by the
  // user-visible term names, not by parser-local object IDs.
  AlignedSignals alignedInputs;
  AlignedSignals alignedOutputs;
  try {
    alignedInputs = alignSignalsByName(
        model0.environmentInputs,
        model0.displayNameByKey,
        model1.environmentInputs,
        model1.displayNameByKey,
        "environment input");
    alignedOutputs = alignSignalsByName(
        model0.observedOutputs,
        model0.displayNameByKey,
        model1.observedOutputs,
        model1.displayNameByKey,
        "observed output");
  } catch (const std::exception& e) {
    return {
        SequentialEquivalenceStatus::Unsupported,
        0,
        e.what(),
    };
  }

  KInductionProblem problem;
  problem.environmentInputNames = alignedInputs.names;
  problem.observedOutputNames = alignedOutputs.names;

  // Step 3: create the shared symbol space used by the combined SAT problem.
  // Inputs are shared, while each design keeps its own private state vector.
  std::unordered_map<SignalKey, size_t, SignalKeyHash> inputSymbols0;
  std::unordered_map<SignalKey, size_t, SignalKeyHash> inputSymbols1;
  std::unordered_map<SignalKey, size_t, SignalKeyHash> state0Symbols;
  std::unordered_map<SignalKey, size_t, SignalKeyHash> state1Symbols;
  size_t nextSymbol = 2;

  assignSymbols(model0.stateBits, state0Symbols, problem.allSymbols, nextSymbol);
  assignSymbols(model1.stateBits, state1Symbols, problem.allSymbols, nextSymbol);

  for (size_t i = 0; i < alignedInputs.names.size(); ++i) {
    const size_t symbol = nextSymbol++;
    inputSymbols0.emplace(alignedInputs.keys0[i], symbol);
    inputSymbols1.emplace(alignedInputs.keys1[i], symbol);
    problem.allSymbols.push_back(symbol);
    problem.inputSymbols.push_back(symbol);
    if (auto assertedValue = getResetAssertionValue(alignedInputs.names[i]);
        assertedValue.has_value()) {
      problem.resetBootstrapInputs.emplace_back(symbol, *assertedValue);
    }
  }
  for (const auto& key : model0.stateBits) {
    problem.state0Symbols.push_back(state0Symbols.at(key));
  }
  for (const auto& key : model1.stateBits) {
    problem.state1Symbols.push_back(state1Symbols.at(key));
  }
  const auto alignedStateBootstrap = collectCommonSignalsByName(
      model0.stateBits,
      model0.displayNameByKey,
      model1.stateBits,
      model1.displayNameByKey,
      "state bit");
  for (size_t i = 0; i < alignedStateBootstrap.names.size(); ++i) {
    problem.bootstrapStateEqualityPairs.emplace_back(
        state0Symbols.at(alignedStateBootstrap.keys0[i]),
        state1Symbols.at(alignedStateBootstrap.keys1[i]));
  }
  for (const auto& relation : model0.complementedStateRelations) {
    if (state0Symbols.find(relation.primaryKey) != state0Symbols.end() &&
        state0Symbols.find(relation.complementedKey) != state0Symbols.end()) {
      problem.complementedStatePairs0.emplace_back(
          state0Symbols.at(relation.primaryKey),
          state0Symbols.at(relation.complementedKey));
    }
  }
  for (const auto& relation : model1.complementedStateRelations) {
    if (state1Symbols.find(relation.primaryKey) != state1Symbols.end() &&
        state1Symbols.find(relation.complementedKey) != state1Symbols.end()) {
      problem.complementedStatePairs1.emplace_back(
          state1Symbols.at(relation.primaryKey),
          state1Symbols.at(relation.complementedKey));
    }
  }

  const auto localToCombined0 =
      buildLocalToCombinedMap(model0, inputSymbols0, state0Symbols);
  const auto localToCombined1 =
      buildLocalToCombinedMap(model1, inputSymbols1, state1Symbols);

  std::unordered_map<BoolExpr*, BoolExpr*> remapMemo0;
  std::unordered_map<BoolExpr*, BoolExpr*> remapMemo1;
  std::unordered_map<SignalKey, BoolExpr*, SignalKeyHash> remappedOutputs0;
  std::unordered_map<SignalKey, BoolExpr*, SignalKeyHash> remappedOutputs1;
  std::unordered_map<SignalKey, BoolExpr*, SignalKeyHash> remappedNext0;
  std::unordered_map<SignalKey, BoolExpr*, SignalKeyHash> remappedNext1;

  // Step 4: rewrite both designs' formulas into that shared symbol space.
  for (size_t i = 0; i < alignedOutputs.names.size(); ++i) {
    const auto& key0 = alignedOutputs.keys0[i];
    const auto& key1 = alignedOutputs.keys1[i];
    remappedOutputs0.emplace(
        key0,
        remapBoolExprVariables(
            model0.observedOutputExprByKey.at(key0), localToCombined0, remapMemo0));
    remappedOutputs1.emplace(
        key1,
        remapBoolExprVariables(
            model1.observedOutputExprByKey.at(key1), localToCombined1, remapMemo1));
    problem.observedOutputExprs0.push_back(remappedOutputs0.at(key0));
    problem.observedOutputExprs1.push_back(remappedOutputs1.at(key1));
  }

  for (const auto& key : model0.stateBits) {
    remappedNext0.emplace(
        key,
        remapBoolExprVariables(
            model0.nextStateExprByStateKey.at(key), localToCombined0, remapMemo0));
  }
  for (const auto& key : model1.stateBits) {
    remappedNext1.emplace(
        key,
        remapBoolExprVariables(
            model1.nextStateExprByStateKey.at(key), localToCombined1, remapMemo1));
  }

  // Step 5: if reset/init data is available, build the explicit frame-0 state
  // constraint before we hand the problem to k-induction.
  BoolExpr* initialCondition = BoolExpr::createTrue();
  auto addInitialStateAssignments =
      [&](const std::unordered_map<SignalKey, bool, SignalKeyHash>& initialValues,
          const std::unordered_map<SignalKey, size_t, SignalKeyHash>& stateSymbols) {
        for (const auto& [key, value] : initialValues) {
          const auto symbolIt = stateSymbols.find(key);
          if (symbolIt == stateSymbols.end()) {
            continue;
          }
          BoolExpr* literal = BoolExpr::Var(symbolIt->second);
          initialCondition = BoolExpr::And(
              initialCondition, value ? literal : BoolExpr::Not(literal));
          ++problem.initializedStateCount;
        }
      };
  addInitialStateAssignments(model0.initialStateValueByKey, state0Symbols);
  addInitialStateAssignments(model1.initialStateValueByKey, state1Symbols);
  problem.totalStateCount = problem.state0Symbols.size() + problem.state1Symbols.size();
  if (problem.hasExplicitInitialState()) {
    problem.initialCondition = BoolExpr::simplify(initialCondition);
  }

  // Step 6: build the SEC property. A frame is "good" when the observed
  // outputs match. Internal state vectors are private to each design and are
  // only used to unroll their transitions.
  BoolExpr* property = BoolExpr::createTrue();
  for (size_t i = 0; i < problem.observedOutputExprs0.size(); ++i) {
    property = BoolExpr::And(
        property,
        makeEqualityExpr(problem.observedOutputExprs0[i], problem.observedOutputExprs1[i]));
  }
  for (const auto& key : model0.stateBits) {
    problem.transitions0.emplace_back(state0Symbols.at(key), remappedNext0.at(key));
  }
  for (const auto& key : model1.stateBits) {
    problem.transitions1.emplace_back(state1Symbols.at(key), remappedNext1.at(key));
  }

  problem.property = BoolExpr::simplify(property);
  problem.bad = BoolExpr::simplify(BoolExpr::Not(problem.property));
  problem.description = "SEC property with aligned observed outputs";

  // Step 7: hand the combined transition system to the k-induction solver.
  KInductionEngine engine(problem, solverType_);
  const auto result = engine.run(maxK);
  switch (result.status) {
    case KInductionStatus::Equivalent:
      return {SequentialEquivalenceStatus::Equivalent, result.bound, ""};
    case KInductionStatus::Different:
      return {
          SequentialEquivalenceStatus::Different,
          result.bound,
          formatCounterexampleWitness(result, model0, model1, top0_, top1_),
      };
    case KInductionStatus::Inconclusive:
    default:
      return {
          SequentialEquivalenceStatus::Inconclusive,
          result.bound,
          "Reached max_k without a proof or counterexample",
      };
  }
}

}  // namespace KEPLER_FORMAL::SEC
