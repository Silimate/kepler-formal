// Copyright 2024-2026 keplertech.io
// SPDX-License-Identifier: GPL-3.0-only

#include "strategy/SequentialEquivalenceStrategy.h"

#include <algorithm>
#include <cctype>
#include <cstdio>
#include <cstdlib>
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

bool isConstBoolExpr(BoolExpr* expr, bool value) {
  return expr != nullptr && expr->getOp() == Op::VAR &&
         expr->getId() == static_cast<size_t>(value ? 1 : 0);
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

std::unordered_map<size_t, bool> collectResetAssignments(
    const SequentialDesignModel& model) {
  std::unordered_map<size_t, bool> assignments;
  for (const auto& key : model.environmentInputs) {
    const auto displayIt = model.displayNameByKey.find(key);
    const auto varIt = model.inputVarByKey.find(key);
    if (displayIt == model.displayNameByKey.end() ||
        varIt == model.inputVarByKey.end()) {
      continue;
    }
    const auto assertedValue = getResetAssertionValue(displayIt->second);
    if (!assertedValue.has_value()) {
      continue;
    }
    assignments.emplace(varIt->second, *assertedValue);
  }
  return assignments;
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

using LocalToAbstractVarMap = std::unordered_map<size_t, size_t>;

struct ExprPairHash {
  size_t operator()(const std::pair<BoolExpr*, BoolExpr*>& pair) const noexcept {
    size_t seed = std::hash<const void*>()(pair.first);
    seed ^= std::hash<const void*>()(pair.second) + 0x9e3779b9 + (seed << 6) +
            (seed >> 2);
    return seed;
  }
};

bool areEquivalentUnderAbstractMaps(
    BoolExpr* expr0,
    BoolExpr* expr1,
    const LocalToAbstractVarMap& abstractMap0,
    const LocalToAbstractVarMap& abstractMap1,
    std::unordered_map<std::pair<BoolExpr*, BoolExpr*>, bool, ExprPairHash>& memo) {
  if (expr0 == nullptr || expr1 == nullptr) {
    return expr0 == expr1;
  }

  const auto key = std::make_pair(expr0, expr1);
  if (const auto it = memo.find(key); it != memo.end()) {
    return it->second;
  }

  bool equivalent = false;
  if (expr0->getOp() == Op::VAR && expr1->getOp() == Op::VAR) {
    if (expr0->getId() < 2 || expr1->getId() < 2) {
      equivalent = expr0->getId() == expr1->getId();
    } else {
      const auto it0 = abstractMap0.find(expr0->getId());
      const auto it1 = abstractMap1.find(expr1->getId());
      equivalent = it0 != abstractMap0.end() && it1 != abstractMap1.end() &&
                   it0->second == it1->second;
    }
  } else if (expr0->getOp() == expr1->getOp()) {
    equivalent = areEquivalentUnderAbstractMaps(
                     expr0->getLeft(),
                     expr1->getLeft(),
                     abstractMap0,
                     abstractMap1,
                     memo) &&
                 areEquivalentUnderAbstractMaps(
                     expr0->getRight(),
                     expr1->getRight(),
                     abstractMap0,
                     abstractMap1,
                     memo);
  }

  memo.emplace(key, equivalent);
  return equivalent;
}

bool areEquivalentUnderAbstractMaps(
    BoolExpr* expr0,
    BoolExpr* expr1,
    const LocalToAbstractVarMap& abstractMap0,
    const LocalToAbstractVarMap& abstractMap1) {
  std::unordered_map<std::pair<BoolExpr*, BoolExpr*>, bool, ExprPairHash> memo;
  return areEquivalentUnderAbstractMaps(
      expr0, expr1, abstractMap0, abstractMap1, memo);
}

std::pair<LocalToAbstractVarMap, LocalToAbstractVarMap> buildAbstractTransitionMaps(
    const SequentialDesignModel& model0,
    const SequentialDesignModel& model1,
    const AlignedSignals& alignedInputs,
    const AlignedSignals& alignedStates) {
  LocalToAbstractVarMap abstractMap0;
  LocalToAbstractVarMap abstractMap1;
  size_t nextAbstractSymbol = 2;

  // Shared environment inputs keep the same abstract variable in both designs,
  // while private state only becomes shared when we currently believe that the
  // same-name state bit should stay equal across both transition systems.
  for (size_t i = 0; i < alignedInputs.names.size(); ++i) {
    const size_t symbol = nextAbstractSymbol++;
    abstractMap0.emplace(model0.inputVarByKey.at(alignedInputs.keys0[i]), symbol);
    abstractMap1.emplace(model1.inputVarByKey.at(alignedInputs.keys1[i]), symbol);
  }
  for (size_t i = 0; i < alignedStates.names.size(); ++i) {
    const size_t symbol = nextAbstractSymbol++;
    abstractMap0.emplace(model0.inputVarByKey.at(alignedStates.keys0[i]), symbol);
    abstractMap1.emplace(model1.inputVarByKey.at(alignedStates.keys1[i]), symbol);
  }

  auto assignPrivateStateSymbols = [&](const SequentialDesignModel& model,
                                       LocalToAbstractVarMap& abstractMap) {
    for (const auto& key : model.stateBits) {
      const size_t localVar = model.inputVarByKey.at(key);
      if (abstractMap.find(localVar) != abstractMap.end()) {
        continue;
      }
      abstractMap.emplace(localVar, nextAbstractSymbol++);
    }
  };
  assignPrivateStateSymbols(model0, abstractMap0);
  assignPrivateStateSymbols(model1, abstractMap1);

  return {std::move(abstractMap0), std::move(abstractMap1)};
}

AlignedSignals inferInductiveStateEqualities(
    const SequentialDesignModel& model0,
    const SequentialDesignModel& model1,
    const AlignedSignals& alignedInputs) {
  AlignedSignals candidateStates = collectCommonSignalsByName(
      model0.stateBits,
      model0.displayNameByKey,
      model1.stateBits,
      model1.displayNameByKey,
      "state bit");

  if (candidateStates.names.size() == model0.stateBits.size() &&
      candidateStates.names.size() == model1.stateBits.size()) {
    const auto [fullAbstractMap0, fullAbstractMap1] = buildAbstractTransitionMaps(
        model0, model1, alignedInputs, candidateStates);
    bool allEquivalent = true;
    for (size_t i = 0; i < candidateStates.names.size(); ++i) {
      const auto& key0 = candidateStates.keys0[i];
      const auto& key1 = candidateStates.keys1[i];
      if (!areEquivalentUnderAbstractMaps(
              model0.nextStateExprByStateKey.at(key0),
              model1.nextStateExprByStateKey.at(key1),
              fullAbstractMap0,
              fullAbstractMap1)) {
        allEquivalent = false;
        break;
      }
    }
    if (allEquivalent) {
      return candidateStates;
    }
  }

  bool changed = true;
  while (changed) {
    changed = false;

    const auto [abstractMap0, abstractMap1] = buildAbstractTransitionMaps(
        model0, model1, alignedInputs, candidateStates);
    AlignedSignals refinedStates;
    for (size_t i = 0; i < candidateStates.names.size(); ++i) {
      const auto& key0 = candidateStates.keys0[i];
      const auto& key1 = candidateStates.keys1[i];
      if (!areEquivalentUnderAbstractMaps(
              model0.nextStateExprByStateKey.at(key0),
              model1.nextStateExprByStateKey.at(key1),
              abstractMap0,
              abstractMap1)) {
        changed = true;
        continue;
      }

      refinedStates.names.push_back(candidateStates.names[i]);
      refinedStates.keys0.push_back(key0);
      refinedStates.keys1.push_back(key1);
    }
    candidateStates = std::move(refinedStates);
  }

  return candidateStates;
}

AlignedSignals filterStateEqualitiesByInitialValue(
    const SequentialDesignModel& model0,
    const SequentialDesignModel& model1,
    const AlignedSignals& candidateStates) {
  AlignedSignals anchoredStates;
  for (size_t i = 0; i < candidateStates.names.size(); ++i) {
    const auto initial0 = model0.initialStateValueByKey.find(candidateStates.keys0[i]);
    const auto initial1 = model1.initialStateValueByKey.find(candidateStates.keys1[i]);
    if (initial0 == model0.initialStateValueByKey.end() ||
        initial1 == model1.initialStateValueByKey.end() ||
        initial0->second != initial1->second) {
      continue;
    }

    anchoredStates.names.push_back(candidateStates.names[i]);
    anchoredStates.keys0.push_back(candidateStates.keys0[i]);
    anchoredStates.keys1.push_back(candidateStates.keys1[i]);
  }
  return anchoredStates;
}

AlignedSignals filterStateEqualitiesByInitialCompatibility(
    const SequentialDesignModel& model0,
    const SequentialDesignModel& model1,
    const AlignedSignals& candidateStates) {
  AlignedSignals compatibleStates;
  for (size_t i = 0; i < candidateStates.names.size(); ++i) {
    const auto initial0 = model0.initialStateValueByKey.find(candidateStates.keys0[i]);
    const auto initial1 = model1.initialStateValueByKey.find(candidateStates.keys1[i]);
    if (initial0 != model0.initialStateValueByKey.end() &&
        initial1 != model1.initialStateValueByKey.end() &&
        initial0->second != initial1->second) {
      continue;
    }

    compatibleStates.names.push_back(candidateStates.names[i]);
    compatibleStates.keys0.push_back(candidateStates.keys0[i]);
    compatibleStates.keys1.push_back(candidateStates.keys1[i]);
  }
  return compatibleStates;
}

AlignedSignals filterStateEqualitiesByKnownValue(
    const std::unordered_map<SignalKey, bool, SignalKeyHash>& knownValues0,
    const std::unordered_map<SignalKey, bool, SignalKeyHash>& knownValues1,
    const AlignedSignals& candidateStates) {
  AlignedSignals anchoredStates;
  for (size_t i = 0; i < candidateStates.names.size(); ++i) {
    const auto known0 = knownValues0.find(candidateStates.keys0[i]);
    const auto known1 = knownValues1.find(candidateStates.keys1[i]);
    if (known0 == knownValues0.end() || known1 == knownValues1.end() ||
        known0->second != known1->second) {
      continue;
    }

    anchoredStates.names.push_back(candidateStates.names[i]);
    anchoredStates.keys0.push_back(candidateStates.keys0[i]);
    anchoredStates.keys1.push_back(candidateStates.keys1[i]);
  }
  return anchoredStates;
}

size_t defaultResetBootstrapCycles(bool hasResetBootstrap, bool hasCompleteInitialState) {
  return (hasResetBootstrap && !hasCompleteInitialState) ? 3u : 0u;
}

std::optional<bool> evaluateConstantUnderAssignments(
    BoolExpr* expr,
    const std::unordered_map<size_t, bool>& assignments,
    std::unordered_map<BoolExpr*, std::optional<bool>>& memo) {
  if (expr == nullptr) {
    return std::nullopt;
  }
  if (const auto it = memo.find(expr); it != memo.end()) {
    return it->second;
  }

  std::optional<bool> value;
  switch (expr->getOp()) {
    case Op::VAR:
      if (expr->getId() < 2) {
        value = expr->getId() == 1;
      } else if (const auto it = assignments.find(expr->getId());
                 it != assignments.end()) {
        value = it->second;
      }
      break;
    case Op::NOT: {
      const auto operand =
          evaluateConstantUnderAssignments(expr->getLeft(), assignments, memo);
      if (operand.has_value()) {
        value = !*operand;
      }
      break;
    }
    case Op::AND: {
      const auto lhs =
          evaluateConstantUnderAssignments(expr->getLeft(), assignments, memo);
      if (lhs.has_value() && !*lhs) {
        value = false;
        break;
      }
      const auto rhs =
          evaluateConstantUnderAssignments(expr->getRight(), assignments, memo);
      if (rhs.has_value() && !*rhs) {
        value = false;
      } else if (lhs.has_value() && rhs.has_value()) {
        value = *lhs && *rhs;
      }
      break;
    }
    case Op::OR: {
      const auto lhs =
          evaluateConstantUnderAssignments(expr->getLeft(), assignments, memo);
      if (lhs.has_value() && *lhs) {
        value = true;
        break;
      }
      const auto rhs =
          evaluateConstantUnderAssignments(expr->getRight(), assignments, memo);
      if (rhs.has_value() && *rhs) {
        value = true;
      } else if (lhs.has_value() && rhs.has_value()) {
        value = *lhs || *rhs;
      }
      break;
    }
    case Op::XOR: {
      const auto lhs =
          evaluateConstantUnderAssignments(expr->getLeft(), assignments, memo);
      const auto rhs =
          evaluateConstantUnderAssignments(expr->getRight(), assignments, memo);
      if (lhs.has_value() && rhs.has_value()) {
        value = *lhs != *rhs;
      }
      break;
    }
    case Op::NONE:
    default:
      break;
  }

  memo.emplace(expr, value);
  return value;
}

std::unordered_map<SignalKey, bool, SignalKeyHash> deriveResetBootstrapStateValues(
    const SequentialDesignModel& model,
    size_t cycles) {
  const auto resetAssignments = collectResetAssignments(model);
  if (resetAssignments.empty() || cycles == 0) {
    return {};
  }

  std::unordered_map<SignalKey, bool, SignalKeyHash> knownStates =
      model.initialStateValueByKey;
  for (size_t step = 0; step < cycles; ++step) {
    std::unordered_map<size_t, bool> assignments = resetAssignments;
    for (const auto& [key, value] : knownStates) {
      const auto varIt = model.inputVarByKey.find(key);
      if (varIt != model.inputVarByKey.end()) {
        assignments.emplace(varIt->second, value);
      }
    }

    std::unordered_map<SignalKey, bool, SignalKeyHash> nextKnownStates;
    std::unordered_map<BoolExpr*, std::optional<bool>> memo;
    for (const auto& key : model.stateBits) {
      const auto value = evaluateConstantUnderAssignments(
          model.nextStateExprByStateKey.at(key), assignments, memo);
      if (value.has_value()) {
        nextKnownStates.emplace(key, *value);
      }
    }
    knownStates = std::move(nextKnownStates);
  }

  return knownStates;
}

AlignedSignals deriveResetBootstrapStateEqualities(
    const SequentialDesignModel& model0,
    const SequentialDesignModel& model1,
    const AlignedSignals& alignedInputs,
    const AlignedSignals& candidateStates,
    size_t cycles) {
  const bool secDiagEnabled = std::getenv("KEPLER_SEC_DIAG") != nullptr;
  if (cycles == 0 || candidateStates.names.empty()) {
    return filterStateEqualitiesByInitialValue(model0, model1, candidateStates);
  }

  const auto resetAssignments0 = collectResetAssignments(model0);
  const auto resetAssignments1 = collectResetAssignments(model1);
  if (resetAssignments0.empty() || resetAssignments1.empty()) {
    return filterStateEqualitiesByInitialValue(model0, model1, candidateStates);
  }

  auto specializeForReset = [](const SequentialDesignModel& model,
                               const std::unordered_map<size_t, bool>& resetAssignments) {
    std::unordered_map<SignalKey, BoolExpr*, SignalKeyHash> specialized;
    specialized.reserve(model.stateBits.size());
    std::unordered_map<BoolExpr*, BoolExpr*> memo;
    for (const auto& key : model.stateBits) {
      specialized.emplace(
          key,
          substituteBoolExprVariables(
              model.nextStateExprByStateKey.at(key), resetAssignments, memo));
    }
    return specialized;
  };

  const auto resetSpecializedNext0 = specializeForReset(model0, resetAssignments0);
  const auto resetSpecializedNext1 = specializeForReset(model1, resetAssignments1);

  AlignedSignals currentEqualities = filterStateEqualitiesByInitialValue(
      model0, model1, candidateStates);
  std::unordered_map<SignalKey, bool, SignalKeyHash> currentKnownValues0 =
      model0.initialStateValueByKey;
  std::unordered_map<SignalKey, bool, SignalKeyHash> currentKnownValues1 =
      model1.initialStateValueByKey;

  for (size_t step = 0; step < cycles; ++step) {
    std::unordered_map<size_t, bool> stateAssignments0;
    std::unordered_map<size_t, bool> stateAssignments1;
    stateAssignments0.reserve(currentKnownValues0.size());
    stateAssignments1.reserve(currentKnownValues1.size());
    for (const auto& [key, value] : currentKnownValues0) {
      if (const auto it = model0.inputVarByKey.find(key); it != model0.inputVarByKey.end()) {
        stateAssignments0.emplace(it->second, value);
      }
    }
    for (const auto& [key, value] : currentKnownValues1) {
      if (const auto it = model1.inputVarByKey.find(key); it != model1.inputVarByKey.end()) {
        stateAssignments1.emplace(it->second, value);
      }
    }

    std::unordered_map<SignalKey, BoolExpr*, SignalKeyHash> specializedNext0;
    std::unordered_map<SignalKey, BoolExpr*, SignalKeyHash> specializedNext1;
    specializedNext0.reserve(model0.stateBits.size());
    specializedNext1.reserve(model1.stateBits.size());
    std::unordered_map<BoolExpr*, BoolExpr*> stateSubMemo0;
    std::unordered_map<BoolExpr*, BoolExpr*> stateSubMemo1;
    for (const auto& key : model0.stateBits) {
      specializedNext0.emplace(
          key,
          substituteBoolExprVariables(
              resetSpecializedNext0.at(key), stateAssignments0, stateSubMemo0));
    }
    for (const auto& key : model1.stateBits) {
      specializedNext1.emplace(
          key,
          substituteBoolExprVariables(
              resetSpecializedNext1.at(key), stateAssignments1, stateSubMemo1));
    }

    std::unordered_map<SignalKey, bool, SignalKeyHash> nextKnownValues0;
    std::unordered_map<SignalKey, bool, SignalKeyHash> nextKnownValues1;
    nextKnownValues0.reserve(model0.stateBits.size());
    nextKnownValues1.reserve(model1.stateBits.size());
    for (const auto& key : model0.stateBits) {
      if (isConstBoolExpr(specializedNext0.at(key), false)) {
        nextKnownValues0.emplace(key, false);
      } else if (isConstBoolExpr(specializedNext0.at(key), true)) {
        nextKnownValues0.emplace(key, true);
      }
    }
    for (const auto& key : model1.stateBits) {
      if (isConstBoolExpr(specializedNext1.at(key), false)) {
        nextKnownValues1.emplace(key, false);
      } else if (isConstBoolExpr(specializedNext1.at(key), true)) {
        nextKnownValues1.emplace(key, true);
      }
    }

    const auto [abstractMap0, abstractMap1] = buildAbstractTransitionMaps(
        model0, model1, alignedInputs, currentEqualities);
    AlignedSignals nextEqualities;
    for (size_t i = 0; i < candidateStates.names.size(); ++i) {
      const auto& key0 = candidateStates.keys0[i];
      const auto& key1 = candidateStates.keys1[i];

      bool equalAfterStep = false;
      const auto known0 = nextKnownValues0.find(key0);
      const auto known1 = nextKnownValues1.find(key1);
      if (known0 != nextKnownValues0.end() && known1 != nextKnownValues1.end() &&
          known0->second == known1->second) {
        equalAfterStep = true;
      } else {
        equalAfterStep = areEquivalentUnderAbstractMaps(
            specializedNext0.at(key0),
            specializedNext1.at(key1),
            abstractMap0,
            abstractMap1);
      }

      if (!equalAfterStep) {
        continue;
      }

      nextEqualities.names.push_back(candidateStates.names[i]);
      nextEqualities.keys0.push_back(key0);
      nextEqualities.keys1.push_back(key1);
    }

    currentEqualities = std::move(nextEqualities);
    currentKnownValues0 = std::move(nextKnownValues0);
    currentKnownValues1 = std::move(nextKnownValues1);
    if (secDiagEnabled) {
      fprintf(
          stderr,
          "SEC diag: bootstrap step %zu equalities=%zu known0=%zu known1=%zu\n",
          step + 1,
          currentEqualities.names.size(),
          currentKnownValues0.size(),
          currentKnownValues1.size());
      fflush(stderr);
    }
  }

  return currentEqualities;
}

}  // namespace

SequentialEquivalenceStrategy::SequentialEquivalenceStrategy(
    naja::NL::SNLDesign* top0,
    naja::NL::SNLDesign* top1,
    KEPLER_FORMAL::Config::SolverType solverType)
    : top0_(top0), top1_(top1), solverType_(solverType) {}

SequentialEquivalenceResult SequentialEquivalenceStrategy::run(size_t maxK) const {
  const bool secDiagEnabled = std::getenv("KEPLER_SEC_DIAG") != nullptr;
  if (secDiagEnabled) {
    fprintf(stderr, "SEC diag: start run\n");
    fflush(stderr);
  }

  // Step 1: extract both tops into the same normalized SEC representation.
  SequentialDesignModel model0 = SequentialDesignModel::extract(top0_);
  if (secDiagEnabled) {
    fprintf(stderr, "SEC diag: extracted design0\n");
    fflush(stderr);
  }
  SequentialDesignModel model1 = SequentialDesignModel::extract(top1_);
  if (secDiagEnabled) {
    fprintf(stderr, "SEC diag: extracted design1\n");
    fflush(stderr);
  }

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
  AlignedSignals inductiveStateEqualities;
  try {
    if (secDiagEnabled) {
      fprintf(stderr, "SEC diag: aligning inputs/outputs\n");
      fflush(stderr);
    }
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
    if (secDiagEnabled) {
      fprintf(stderr, "SEC diag: inferring inductive state equalities\n");
      fflush(stderr);
    }
    inductiveStateEqualities = inferInductiveStateEqualities(
        model0, model1, alignedInputs);
    if (secDiagEnabled) {
      fprintf(stderr, "SEC diag: inferred inductive state equalities\n");
      fflush(stderr);
    }
  } catch (const std::exception& e) {
    return {
        SequentialEquivalenceStatus::Unsupported,
        0,
        e.what(),
    };
  }

  if (secDiagEnabled) {
    printf(
        "SEC diag: aligned_inputs=%zu aligned_outputs=%zu inductive_state_equalities=%zu "
        "state_bits0=%zu state_bits1=%zu\n",
        alignedInputs.names.size(),
        alignedOutputs.names.size(),
        inductiveStateEqualities.names.size(),
        model0.stateBits.size(),
        model1.stateBits.size());
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
  if (secDiagEnabled) {
    fprintf(stderr, "SEC diag: remapped observed outputs\n");
    fflush(stderr);
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
  if (secDiagEnabled) {
    fprintf(stderr, "SEC diag: remapped next-state formulas\n");
    fflush(stderr);
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
  const size_t bootstrapCycles =
      defaultResetBootstrapCycles(!problem.resetBootstrapInputs.empty(),
                                  problem.hasCompleteInitialState());

  const AlignedSignals initialStateCorrespondence =
      filterStateEqualitiesByInitialCompatibility(
          model0, model1, inductiveStateEqualities);
  for (size_t i = 0; i < initialStateCorrespondence.names.size(); ++i) {
    problem.initialStateEqualityPairs.emplace_back(
        state0Symbols.at(initialStateCorrespondence.keys0[i]),
        state1Symbols.at(initialStateCorrespondence.keys1[i]));
  }

  AlignedSignals anchoredStateEqualities;
  size_t chosenBootstrapCycles = bootstrapCycles;
  std::unordered_map<SignalKey, bool, SignalKeyHash> bootstrapValues0;
  std::unordered_map<SignalKey, bool, SignalKeyHash> bootstrapValues1;
  if (!problem.resetBootstrapInputs.empty()) {
    if (!initialStateCorrespondence.names.empty()) {
      anchoredStateEqualities = initialStateCorrespondence;
    } else {
      anchoredStateEqualities = deriveResetBootstrapStateEqualities(
          model0,
          model1,
          alignedInputs,
          inductiveStateEqualities,
          bootstrapCycles);
    }

    bootstrapValues0 =
        deriveResetBootstrapStateValues(model0, chosenBootstrapCycles);
    bootstrapValues1 =
        deriveResetBootstrapStateValues(model1, chosenBootstrapCycles);
    for (const auto& [key, value] : bootstrapValues0) {
      problem.bootstrapStateAssignments.emplace_back(state0Symbols.at(key), value);
    }
    for (const auto& [key, value] : bootstrapValues1) {
      problem.bootstrapStateAssignments.emplace_back(state1Symbols.at(key), value);
    }
  } else if (problem.hasExplicitInitialState()) {
    anchoredStateEqualities = filterStateEqualitiesByInitialValue(
        model0, model1, inductiveStateEqualities);
  }
  problem.resetBootstrapCycles = chosenBootstrapCycles;
  for (size_t i = 0; i < anchoredStateEqualities.names.size(); ++i) {
    problem.inductiveStateEqualityPairs.emplace_back(
        state0Symbols.at(anchoredStateEqualities.keys0[i]),
        state1Symbols.at(anchoredStateEqualities.keys1[i]));
    if (!problem.resetBootstrapInputs.empty()) {
      problem.bootstrapStateEqualityPairs.emplace_back(
          state0Symbols.at(anchoredStateEqualities.keys0[i]),
          state1Symbols.at(anchoredStateEqualities.keys1[i]));
    }
  }

  const auto [abstractOutputMap0, abstractOutputMap1] = buildAbstractTransitionMaps(
      model0, model1, alignedInputs, anchoredStateEqualities);
  if (secDiagEnabled) {
    fprintf(stderr, "SEC diag: built abstract transition maps\n");
    fflush(stderr);
  }

  // Step 6: build the SEC proof obligations. The checked SEC property remains
  // pure observed-output equality, while induction uses a stronger invariant
  // made of the anchored internal-state equalities plus any remaining output
  // obligations not already implied by that state correspondence.
  BoolExpr* property = BoolExpr::createTrue();
  for (const auto& key : model0.stateBits) {
    problem.transitions0.emplace_back(state0Symbols.at(key), remappedNext0.at(key));
  }
  for (const auto& key : model1.stateBits) {
    problem.transitions1.emplace_back(state1Symbols.at(key), remappedNext1.at(key));
  }

  // Keep the SEC property honest: the base case always checks every observed
  // output, while the induction step uses a stronger invariant whose state
  // equalities are explicit BoolExpr clauses instead of out-of-band SAT
  // assumptions.
  BoolExpr* inductionProperty = BoolExpr::createTrue();
  for (size_t i = 0; i < anchoredStateEqualities.names.size(); ++i) {
    inductionProperty = BoolExpr::And(
        inductionProperty,
        makeEqualityExpr(
            BoolExpr::Var(state0Symbols.at(anchoredStateEqualities.keys0[i])),
            BoolExpr::Var(state1Symbols.at(anchoredStateEqualities.keys1[i]))));
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
  if (secDiagEnabled) {
    fprintf(stderr, "SEC diag: built SEC and induction properties\n");
    fflush(stderr);
  }

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
        chosenBootstrapCycles,
        problem.bootstrapStateEqualityPairs.size(),
        problem.inductiveStateEqualityPairs.size());
    fflush(stdout);
  }

  // Step 7: hand the combined transition system to the k-induction solver.
  if (secDiagEnabled) {
    fprintf(stderr, "SEC diag: entering k-induction engine\n");
    fflush(stderr);
  }
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
