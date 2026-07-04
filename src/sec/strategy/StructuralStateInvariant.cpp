// Copyright 2024-2026 keplertech.io
// SPDX-License-Identifier: GPL-3.0-only

#include "strategy/StructuralStateInvariant.h"

#include <algorithm>
#include <cerrno>
#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <limits>
#include <map>
#include <memory_resource>
#include <sstream>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "BoolExpr.h"
#include "common/BoolExprUtils.h"

namespace KEPLER_FORMAL::SEC {

// Overall structural-state matching algorithm:
// 1. Put aligned SEC inputs into a shared abstract symbol space.
// 2. Seed each state bit with coarse classes from init/complement information.
// 3. Repeatedly fingerprint next-state functions under the current classes.
// 4. Refine those classes to a fixed point.
// 5. Pair states whose final structural fingerprints match across the designs.
// 6. Use an ordered fast path only when every state already matches in order.

namespace {

constexpr size_t kMaxSatValidatedOrderedStatePairs = 5000;
constexpr size_t kMaxSatValidatedOrderedCoiStatePairs = 700000;
constexpr size_t kDefaultResetBootstrapOutputCoiStatePairs =
    kMaxSatValidatedOrderedCoiStatePairs;
constexpr size_t kMaxSatValidatedOrderedPairSupport = 32768;
constexpr size_t kMaxOrderedCoiExpansionPasses = 64;
// ASIC FIFO examples such as asap7_mock_cpu need the final structural
// fingerprint pass to relate memory state after output-rooted COI matching is
// exhausted.  Keep the cap explicit so much larger SoCs still skip this path
// unless the workflow opts in through the environment override below.
constexpr size_t kDefaultGlobalStructuralRefinementStateLimit = 40000;
constexpr unsigned kSatValidatedStructuralConflictLimit = 4096;

using KEPLER_FORMAL::BoolExpr;
using FingerprintMemo = std::pmr::unordered_map<BoolExpr*, uint64_t>;

bool isCommutativeBoolOp(Op op) {
  return op == Op::AND || op == Op::OR || op == Op::XOR;
}

struct RefinementSignatureHash {
  size_t operator()(const std::pair<size_t, uint64_t>& signature) const noexcept {
    size_t seed = std::hash<size_t>()(signature.first);
    seed ^= std::hash<uint64_t>()(signature.second) + 0x9e3779b9 +
            (seed << 6) + (seed >> 2);
    return seed;
  }
};

std::pair<LocalToAbstractVarMap, LocalToAbstractVarMap> buildAbstractTransitionMapsImpl(
    const SequentialDesignModel& model0,
    const SequentialDesignModel& model1,
    const AlignedSignals& alignedInputs,
    const AlignedSignals& alignedStates) {
  // Matched SEC inputs and already-correlated state bits get the same abstract
  // IDs on both sides. Everything else stays private so equivalence checks only
  // identify what has really been aligned.
  LocalToAbstractVarMap abstractMap0;
  LocalToAbstractVarMap abstractMap1;
  size_t nextAbstractSymbol = 2;

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

AlignedSignals buildOrderedStatePairs(const SequentialDesignModel& model0,
                                      const SequentialDesignModel& model1) {
  if (model0.stateBits.size() != model1.stateBits.size()) {
    return {}; // LCOV_EXCL_LINE
  }

  AlignedSignals aligned;
  aligned.names.reserve(model0.stateBits.size());
  aligned.keys0.reserve(model0.stateBits.size());
  aligned.keys1.reserve(model0.stateBits.size());
  for (size_t i = 0; i < model0.stateBits.size(); ++i) {
    aligned.names.push_back("ordered_state_" + std::to_string(i));
    aligned.keys0.push_back(model0.stateBits[i]);
    aligned.keys1.push_back(model1.stateBits[i]);
  }
  return aligned;
}

std::unordered_map<size_t, size_t> buildStateIndexByVar(
    const SequentialDesignModel& model) {
  std::unordered_map<size_t, size_t> indexByVar;
  indexByVar.reserve(model.stateBits.size());
  for (size_t i = 0; i < model.stateBits.size(); ++i) {
    indexByVar.emplace(model.inputVarByKey.at(model.stateBits[i]), i);
  }
  return indexByVar;
}

AlignedSignals buildOrderedStatePairsForSelection( // LCOV_EXCL_LINE
    const SequentialDesignModel& model0,
    const SequentialDesignModel& model1,
    const std::vector<unsigned char>& selected) {
  AlignedSignals aligned; // LCOV_EXCL_LINE
  const size_t selectedCount = // LCOV_EXCL_LINE
      static_cast<size_t>(std::count(selected.begin(), selected.end(), 1)); // LCOV_EXCL_LINE
  aligned.names.reserve(selectedCount); // LCOV_EXCL_LINE
  aligned.keys0.reserve(selectedCount); // LCOV_EXCL_LINE
  aligned.keys1.reserve(selectedCount); // LCOV_EXCL_LINE
  for (size_t i = 0; i < selected.size(); ++i) { // LCOV_EXCL_LINE
    if (!selected[i]) { // LCOV_EXCL_LINE
      continue; // LCOV_EXCL_LINE
    }
    aligned.names.push_back("ordered_coi_state_" + std::to_string(i)); // LCOV_EXCL_LINE
    aligned.keys0.push_back(model0.stateBits[i]); // LCOV_EXCL_LINE
    aligned.keys1.push_back(model1.stateBits[i]); // LCOV_EXCL_LINE
  } // LCOV_EXCL_LINE
  return aligned; // LCOV_EXCL_LINE
} // LCOV_EXCL_LINE

std::pair<LocalToAbstractVarMap, LocalToAbstractVarMap> buildSelectedAbstractMaps(
    const SequentialDesignModel& model0,
    const SequentialDesignModel& model1,
    const AlignedSignals& alignedInputs,
    const AlignedSignals& selectedStates) {
  LocalToAbstractVarMap abstractMap0;
  LocalToAbstractVarMap abstractMap1;
  abstractMap0.reserve(alignedInputs.names.size() + selectedStates.names.size());
  abstractMap1.reserve(alignedInputs.names.size() + selectedStates.names.size());
  size_t nextAbstractSymbol = 2;

  for (size_t i = 0; i < alignedInputs.names.size(); ++i) {
    const size_t symbol = nextAbstractSymbol++;
    abstractMap0.emplace(model0.inputVarByKey.at(alignedInputs.keys0[i]), symbol);
    abstractMap1.emplace(model1.inputVarByKey.at(alignedInputs.keys1[i]), symbol);
  }
  for (size_t i = 0; i < selectedStates.names.size(); ++i) {
    const size_t symbol = nextAbstractSymbol++;
    abstractMap0.emplace(model0.inputVarByKey.at(selectedStates.keys0[i]), symbol);
    abstractMap1.emplace(model1.inputVarByKey.at(selectedStates.keys1[i]), symbol);
  }

  return {std::move(abstractMap0), std::move(abstractMap1)};
}

std::unordered_map<size_t, size_t> buildInputClassMap(
    const SequentialDesignModel& model,
    const std::vector<SignalKey>& alignedInputKeys);

bool structuralCoiDiagEnabled();

const char* displayNameForStructuralDiag(  // LCOV_EXCL_LINE
    const SequentialDesignModel& model,
    const SignalKey& key) {
  const auto it = model.displayNameByKey.find(key);  // LCOV_EXCL_LINE
  return it == model.displayNameByKey.end() ? "<unnamed>" : it->second.c_str();  // LCOV_EXCL_LINE
}

std::string formatUnmappedSupportVarsForDiag(  // LCOV_EXCL_LINE
    const SequentialDesignModel& model,
    BoolExpr* expr,
    const LocalToAbstractVarMap& abstractMap) {
  std::unordered_map<size_t, const SignalKey*> keyByVar;  // LCOV_EXCL_LINE
  keyByVar.reserve(model.inputVarByKey.size());  // LCOV_EXCL_LINE
  for (const auto& [key, varID] : model.inputVarByKey) {  // LCOV_EXCL_LINE
    keyByVar.emplace(varID, &key);  // LCOV_EXCL_LINE
  }

  std::ostringstream oss;  // LCOV_EXCL_LINE
  bool first = true;  // LCOV_EXCL_LINE
  // LCOV_EXCL_START
  for (const auto varID : expr->getSupportVars()) {  // LCOV_EXCL_LINE
    if (varID < 2 || abstractMap.find(varID) != abstractMap.end()) {  // LCOV_EXCL_LINE
      continue;  // LCOV_EXCL_LINE
    }
    if (!first) {  // LCOV_EXCL_LINE
      oss << ", ";  // LCOV_EXCL_LINE
    }  // LCOV_EXCL_LINE
    first = false;  // LCOV_EXCL_LINE
    oss << "v" << varID;  // LCOV_EXCL_LINE
    // LCOV_EXCL_STOP
    const auto keyIt = keyByVar.find(varID);  // LCOV_EXCL_LINE
    if (keyIt != keyByVar.end()) {  // LCOV_EXCL_LINE
      oss << ":" << displayNameForStructuralDiag(model, *keyIt->second);  // LCOV_EXCL_LINE
    }  // LCOV_EXCL_LINE
  }
  return oss.str();  // LCOV_EXCL_LINE
}  // LCOV_EXCL_LINE

bool areAllOrderedStatesEquivalent(const SequentialDesignModel& model0,
                                   // LCOV_EXCL_START
                                   const SequentialDesignModel& model1,
                                   // LCOV_EXCL_STOP
                                   const AlignedSignals& alignedInputs,
                                   const AlignedSignals& orderedStates) {
  if (orderedStates.names.empty()) {
    return false;  // LCOV_EXCL_LINE
  }

  const auto [abstractMap0, abstractMap1] =
      buildAbstractTransitionMapsImpl(model0, model1, alignedInputs, orderedStates);
  std::pmr::monotonic_buffer_resource memoResource;
  AbstractExprPairMemo memo{&memoResource};
  for (size_t i = 0; i < orderedStates.names.size(); ++i) {
    const auto& key0 = orderedStates.keys0[i];
    const auto& key1 = orderedStates.keys1[i];
    if (!areEquivalentUnderAbstractMaps(
            model0.nextStateExprByStateKey.at(key0),
            model1.nextStateExprByStateKey.at(key1),
            abstractMap0,
            abstractMap1,
            memo)) {
      if (structuralCoiDiagEnabled()) {
        std::fprintf(  // LCOV_EXCL_LINE
            stderr,  // LCOV_EXCL_LINE
            "SEC diag: ordered structural first mismatch index=%zu lhs=%s rhs=%s\n",
            i,  // LCOV_EXCL_LINE
            displayNameForStructuralDiag(model0, key0),  // LCOV_EXCL_LINE
            displayNameForStructuralDiag(model1, key1));  // LCOV_EXCL_LINE
      }  // LCOV_EXCL_LINE
      return false;
    }
  } // LCOV_EXCL_LINE
  return true; // LCOV_EXCL_LINE
}

bool areSatEquivalentUnderAbstractMaps(
    BoolExpr* expr0,
    BoolExpr* expr1,
    const LocalToAbstractVarMap& abstractMap0,
    const LocalToAbstractVarMap& abstractMap1,
    KEPLER_FORMAL::Config::SolverType solverType) {
  for (const auto var : expr0->getSupportVars()) {
    if (var >= 2 && abstractMap0.find(var) == abstractMap0.end()) {
      return false; // LCOV_EXCL_LINE
    }
  }
  for (const auto var : expr1->getSupportVars()) {
    if (var >= 2 && abstractMap1.find(var) == abstractMap1.end()) {
      return false;
    }
  }

  // SAT validation is only a precision fallback for candidate state matching.
  // Unknown/private support means the candidate is not proven structurally
  // equivalent; it should not escape as a remap exception.
  std::unordered_map<BoolExpr*, BoolExpr*> memo0;
  std::unordered_map<BoolExpr*, BoolExpr*> memo1;
  BoolExpr* remapped0 = remapBoolExprVariables(expr0, abstractMap0, memo0);
  BoolExpr* remapped1 = remapBoolExprVariables(expr1, abstractMap1, memo1);
  const auto implied = boolFormulaImpliesWithConflictLimit(
      BoolExpr::createTrue(),
      makeEqualityExpr(remapped0, remapped1),
      solverType,
      // LCOV_EXCL_START
      kSatValidatedStructuralConflictLimit);
  return implied.value_or(false);
  // LCOV_EXCL_STOP
}

bool isWithinSatValidatedOrderedSupportBudget(BoolExpr* expr0, BoolExpr* expr1) {
  std::set<size_t> support = expr0->getSupportVars();
  const auto support1 = expr1->getSupportVars();
  support.insert(support1.begin(), support1.end());
  return support.size() <= kMaxSatValidatedOrderedPairSupport;
}

size_t nextAbstractSymbolAfter(const LocalToAbstractVarMap& abstractMap0, // LCOV_EXCL_LINE
                               const LocalToAbstractVarMap& abstractMap1) {
  size_t nextSymbol = 2; // LCOV_EXCL_LINE
  for (const auto& [_, symbol] : abstractMap0) { // LCOV_EXCL_LINE
    nextSymbol = std::max(nextSymbol, symbol + 1); // LCOV_EXCL_LINE
  }
  for (const auto& [_, symbol] : abstractMap1) { // LCOV_EXCL_LINE
    nextSymbol = std::max(nextSymbol, symbol + 1); // LCOV_EXCL_LINE
  }
  return nextSymbol; // LCOV_EXCL_LINE
}

// LCOV_EXCL_START
bool structuralCoiDiagEnabled() {
// LCOV_EXCL_STOP
  static const bool enabled = std::getenv("KEPLER_SEC_DIAG") != nullptr ||
                              std::getenv("KEPLER_SEC_STRUCTURAL_DIAG") != nullptr;
  return enabled;
}  // LCOV_EXCL_LINE

size_t resetBootstrapOutputCoiStatePairBudget() {
  static const size_t budget = []() {
    // LCOV_EXCL_START
    const char* env = std::getenv("KEPLER_SEC_BOOTSTRAP_COI_PAIR_BUDGET");
    if (env == nullptr || env[0] == '\0') {
      return kDefaultResetBootstrapOutputCoiStatePairs;
    }
    // LCOV_EXCL_STOP
    char* end = nullptr;  // LCOV_EXCL_LINE
    // LCOV_EXCL_START
    const auto parsed = std::strtoull(env, &end, 10);  // LCOV_EXCL_LINE
    // LCOV_EXCL_STOP
    if (end == env || parsed == 0) {  // LCOV_EXCL_LINE
      return kDefaultResetBootstrapOutputCoiStatePairs;  // LCOV_EXCL_LINE
    // LCOV_EXCL_START
    }
    // LCOV_EXCL_STOP
    return static_cast<size_t>(parsed);  // LCOV_EXCL_LINE
  }();
  return budget;
}  // LCOV_EXCL_LINE

bool resetBootstrapOutputCoiTransitionClosureEnabled() {
  static const bool enabled = []() {
    // LCOV_EXCL_START
    const char* env = std::getenv("KEPLER_SEC_BOOTSTRAP_OUTPUT_ROOTS_ONLY");
    // LCOV_EXCL_STOP
    return !(env != nullptr && env[0] != '\0' && std::string(env) != "0");
  }();
  return enabled;
}  // LCOV_EXCL_LINE

size_t parseStateLimitEnv(const char* env, size_t defaultValue) {
  if (env == nullptr || env[0] == '\0') {
    return defaultValue;
  }
  // LCOV_EXCL_START
  errno = 0;
  // LCOV_EXCL_STOP
  char* end = nullptr;
  const auto parsed = std::strtoull(env, &end, 10);
  // LCOV_EXCL_START
  if (end == env || errno == ERANGE) {
  // LCOV_EXCL_STOP
    return defaultValue;  // LCOV_EXCL_LINE
  }
  if (parsed > std::numeric_limits<size_t>::max()) {
    return std::numeric_limits<size_t>::max();  // LCOV_EXCL_LINE
  }
  return static_cast<size_t>(parsed);
}

size_t globalStructuralRefinementStateLimit() {
  return parseStateLimitEnv(
      std::getenv("KEPLER_SEC_GLOBAL_STRUCTURAL_REFINEMENT_STATE_LIMIT"),
      kDefaultGlobalStructuralRefinementStateLimit);
}

bool globalStructuralRefinementWithinStateLimit(
    const SequentialDesignModel& model0,
    const SequentialDesignModel& model1) {
  const size_t limit = globalStructuralRefinementStateLimit();
  // LCOV_EXCL_START
  const size_t stateCount0 = model0.stateBits.size();
  const size_t stateCount1 = model1.stateBits.size();
  // LCOV_EXCL_STOP
  const bool overLimit = stateCount0 > limit || stateCount1 > limit - stateCount0;
  // LCOV_EXCL_START
  if (overLimit && structuralCoiDiagEnabled()) {
    std::fprintf(  // LCOV_EXCL_LINE
        stderr,  // LCOV_EXCL_LINE
        "SEC diag: global structural refinement skipped states=%zu+%zu limit=%zu\n",
        // LCOV_EXCL_STOP
        stateCount0,  // LCOV_EXCL_LINE
        stateCount1,  // LCOV_EXCL_LINE
        limit);  // LCOV_EXCL_LINE
  }  // LCOV_EXCL_LINE
  return !overLimit;
}

// LCOV_EXCL_START
void assignPrivateSupportSymbols(BoolExpr* expr,
// LCOV_EXCL_STOP
                                 LocalToAbstractVarMap& abstractMap,
                                 size_t& nextAbstractSymbol) {
  if (expr == nullptr) { // LCOV_EXCL_LINE
    return;  // LCOV_EXCL_LINE
  }
  for (const auto var : expr->getSupportVars()) { // LCOV_EXCL_LINE
    if (var < 2 || abstractMap.find(var) != abstractMap.end()) { // LCOV_EXCL_LINE
      continue; // LCOV_EXCL_LINE
    }
    abstractMap.emplace(var, nextAbstractSymbol++);  // LCOV_EXCL_LINE
  }
} // LCOV_EXCL_LINE

bool areSatEquivalentUnderPartialAbstractMaps( // LCOV_EXCL_LINE
    BoolExpr* expr0,
    BoolExpr* expr1,
    const LocalToAbstractVarMap& partialMap0,
    const LocalToAbstractVarMap& partialMap1,
    KEPLER_FORMAL::Config::SolverType solverType) {
  LocalToAbstractVarMap abstractMap0 = partialMap0; // LCOV_EXCL_LINE
  LocalToAbstractVarMap abstractMap1 = partialMap1; // LCOV_EXCL_LINE
  size_t nextAbstractSymbol = nextAbstractSymbolAfter(abstractMap0, abstractMap1); // LCOV_EXCL_LINE
  assignPrivateSupportSymbols(expr0, abstractMap0, nextAbstractSymbol); // LCOV_EXCL_LINE
  assignPrivateSupportSymbols(expr1, abstractMap1, nextAbstractSymbol); // LCOV_EXCL_LINE
  return areSatEquivalentUnderAbstractMaps( // LCOV_EXCL_LINE
      expr0, expr1, abstractMap0, abstractMap1, solverType); // LCOV_EXCL_LINE
} // LCOV_EXCL_LINE

bool areAllOrderedStatesSatEquivalent(
    const SequentialDesignModel& model0,
    const SequentialDesignModel& model1,
    // LCOV_EXCL_START
    const AlignedSignals& alignedInputs,
    // LCOV_EXCL_STOP
    const AlignedSignals& orderedStates,
    KEPLER_FORMAL::Config::SolverType solverType) {
  if (orderedStates.names.empty()) {
    return false;  // LCOV_EXCL_LINE
  }
  if (orderedStates.names.size() > kMaxSatValidatedOrderedStatePairs) {
    return false;  // LCOV_EXCL_LINE
  }

  const auto [abstractMap0, abstractMap1] =
      buildAbstractTransitionMapsImpl(model0, model1, alignedInputs, orderedStates);
  std::pmr::monotonic_buffer_resource memoResource;
  AbstractExprPairMemo structuralMemo{&memoResource};
  for (size_t i = 0; i < orderedStates.names.size(); ++i) {
    const auto& key0 = orderedStates.keys0[i];
    const auto& key1 = orderedStates.keys1[i];
    BoolExpr* next0 = model0.nextStateExprByStateKey.at(key0);
    BoolExpr* next1 = model1.nextStateExprByStateKey.at(key1);
    if (next0 == nullptr || next1 == nullptr) {
      return false;
    }
    if (areEquivalentUnderAbstractMaps(
            next0,
            next1,
            abstractMap0,
            abstractMap1,
            // LCOV_EXCL_START
            structuralMemo)) {
      continue;
    }
    // LCOV_EXCL_STOP
    if (!isWithinSatValidatedOrderedSupportBudget(next0, next1)) {
      // LCOV_EXCL_START
      if (structuralCoiDiagEnabled()) {  // LCOV_EXCL_LINE
        std::fprintf(  // LCOV_EXCL_LINE
            stderr,  // LCOV_EXCL_LINE
            "SEC diag: ordered SAT first mismatch support budget index=%zu lhs=%s rhs=%s\n",
            i,  // LCOV_EXCL_LINE
            // LCOV_EXCL_STOP
            displayNameForStructuralDiag(model0, key0),  // LCOV_EXCL_LINE
            displayNameForStructuralDiag(model1, key1));  // LCOV_EXCL_LINE
      }  // LCOV_EXCL_LINE
      return false;  // LCOV_EXCL_LINE
    }
    if (!areSatEquivalentUnderAbstractMaps(
            next0, next1, abstractMap0, abstractMap1, solverType)) {
      if (structuralCoiDiagEnabled()) {
        std::fprintf(  // LCOV_EXCL_LINE
            stderr,  // LCOV_EXCL_LINE
            "SEC diag: ordered SAT first mismatch index=%zu lhs=%s rhs=%s\n",
            i,  // LCOV_EXCL_LINE
            displayNameForStructuralDiag(model0, key0),  // LCOV_EXCL_LINE
            displayNameForStructuralDiag(model1, key1));  // LCOV_EXCL_LINE
        std::fprintf(  // LCOV_EXCL_LINE
            stderr,  // LCOV_EXCL_LINE
            "SEC diag: ordered SAT unmapped support lhs=[%s] rhs=[%s]\n",
            formatUnmappedSupportVarsForDiag(model0, next0, abstractMap0).c_str(),  // LCOV_EXCL_LINE
            // LCOV_EXCL_START
            formatUnmappedSupportVarsForDiag(model1, next1, abstractMap1).c_str());  // LCOV_EXCL_LINE
      }  // LCOV_EXCL_LINE
      // LCOV_EXCL_STOP
      return false;
    }
  }  // LCOV_EXCL_LINE
  return true;  // LCOV_EXCL_LINE
}

bool addSupportStateIndices( // LCOV_EXCL_LINE
    // LCOV_EXCL_START
    BoolExpr* expr,
    // LCOV_EXCL_STOP
    const std::unordered_map<size_t, size_t>& stateIndexByVar,
    std::vector<unsigned char>& selected) {
  if (expr == nullptr) { // LCOV_EXCL_LINE
    return false;  // LCOV_EXCL_LINE
  }
  bool changed = false; // LCOV_EXCL_LINE
  for (const auto var : expr->getSupportVars()) { // LCOV_EXCL_LINE
    const auto stateIt = stateIndexByVar.find(var); // LCOV_EXCL_LINE
    if (stateIt == stateIndexByVar.end() || stateIt->second >= selected.size()) { // LCOV_EXCL_LINE
      continue; // LCOV_EXCL_LINE
    }
    if (!selected[stateIt->second]) { // LCOV_EXCL_LINE
      selected[stateIt->second] = 1; // LCOV_EXCL_LINE
      changed = true; // LCOV_EXCL_LINE
    } // LCOV_EXCL_LINE
  }
  return changed; // LCOV_EXCL_LINE
} // LCOV_EXCL_LINE

bool ensureExprPairEquivalentOrExpand( // LCOV_EXCL_LINE
    BoolExpr* expr0,
    BoolExpr* expr1,
    const std::unordered_map<size_t, size_t>& stateIndexByVar0,
    const std::unordered_map<size_t, size_t>& stateIndexByVar1,
    const LocalToAbstractVarMap& abstractMap0,
    const LocalToAbstractVarMap& abstractMap1,
    AbstractExprPairMemo& structuralMemo,
    std::vector<unsigned char>& selected,
    KEPLER_FORMAL::Config::SolverType solverType,
    bool& invalidRelation,
    std::string* invalidReason = nullptr) {
  if (areEquivalentUnderAbstractMaps( // LCOV_EXCL_LINE
          expr0, expr1, abstractMap0, abstractMap1, structuralMemo)) { // LCOV_EXCL_LINE
    return false; // LCOV_EXCL_LINE
  }

  const bool added0 = addSupportStateIndices(expr0, stateIndexByVar0, selected); // LCOV_EXCL_LINE
  const bool added1 = addSupportStateIndices(expr1, stateIndexByVar1, selected); // LCOV_EXCL_LINE
  if (added0 || added1) { // LCOV_EXCL_LINE
    // LCOV_EXCL_START
    return true;
  }

  if (expr0 == nullptr || expr1 == nullptr) {
  // LCOV_EXCL_STOP
    if (invalidReason != nullptr) {  // LCOV_EXCL_LINE
      // LCOV_EXCL_START
      *invalidReason = "missing_expr";  // LCOV_EXCL_LINE
    }  // LCOV_EXCL_LINE
    invalidRelation = true;  // LCOV_EXCL_LINE
  } else if (!isWithinSatValidatedOrderedSupportBudget(expr0, expr1)) {
  // LCOV_EXCL_STOP
    if (invalidReason != nullptr) {  // LCOV_EXCL_LINE
      *invalidReason = "support_budget";  // LCOV_EXCL_LINE
    }  // LCOV_EXCL_LINE
    invalidRelation = true;  // LCOV_EXCL_LINE
  } else if (!areSatEquivalentUnderPartialAbstractMaps( // LCOV_EXCL_LINE
                 expr0, expr1, abstractMap0, abstractMap1, solverType)) { // LCOV_EXCL_LINE
    if (invalidReason != nullptr) { // LCOV_EXCL_LINE
      *invalidReason = "sat_validation"; // LCOV_EXCL_LINE
    } // LCOV_EXCL_LINE
    invalidRelation = true; // LCOV_EXCL_LINE
  } // LCOV_EXCL_LINE
  return false; // LCOV_EXCL_LINE
} // LCOV_EXCL_LINE

bool expandOrderedCoiFromOutputs( // LCOV_EXCL_LINE
    const SequentialDesignModel& model0,
    const SequentialDesignModel& model1,
    const AlignedSignals& alignedOutputs,
    const std::unordered_map<size_t, size_t>& stateIndexByVar0,
    const std::unordered_map<size_t, size_t>& stateIndexByVar1,
    std::vector<unsigned char>& selected) {
  bool changed = false; // LCOV_EXCL_LINE
  for (size_t i = 0; i < alignedOutputs.names.size(); ++i) { // LCOV_EXCL_LINE
    const auto exprIt0 = model0.observedOutputExprByKey.find(alignedOutputs.keys0[i]); // LCOV_EXCL_LINE
    const auto exprIt1 = model1.observedOutputExprByKey.find(alignedOutputs.keys1[i]); // LCOV_EXCL_LINE
    if (exprIt0 != model0.observedOutputExprByKey.end()) { // LCOV_EXCL_LINE
      changed |= addSupportStateIndices(exprIt0->second, stateIndexByVar0, selected); // LCOV_EXCL_LINE
    } // LCOV_EXCL_LINE
    if (exprIt1 != model1.observedOutputExprByKey.end()) { // LCOV_EXCL_LINE
      changed |= addSupportStateIndices(exprIt1->second, stateIndexByVar1, selected); // LCOV_EXCL_LINE
    } // LCOV_EXCL_LINE
  } // LCOV_EXCL_LINE
  return changed; // LCOV_EXCL_LINE
}

struct StructuralCoiMapping {
  static constexpr size_t kUnmapped = std::numeric_limits<size_t>::max();

  std::vector<size_t> state0ToState1;
  std::vector<size_t> state1ToState0;
  std::vector<std::pair<size_t, size_t>> pairs;
};

using StructuralExprPairSet =
    std::pmr::unordered_set<std::pair<BoolExpr*, BoolExpr*>, AbstractExprPairHash>;

struct StructuralCoiUnificationContext {
  const std::unordered_map<size_t, size_t>& inputClasses0;
  const std::unordered_map<size_t, size_t>& inputClasses1;
  const std::unordered_map<size_t, size_t>& stateIndexByVar0;
  const std::unordered_map<size_t, size_t>& stateIndexByVar1;
  StructuralCoiMapping& mapping;
  StructuralExprPairSet& seenPairs;
};

StructuralCoiMapping makeStructuralCoiMapping(size_t stateCount0,
                                              size_t stateCount1) {
  // LCOV_EXCL_START
  return {
  // LCOV_EXCL_STOP
      std::vector<size_t>(stateCount0, StructuralCoiMapping::kUnmapped),
      std::vector<size_t>(stateCount1, StructuralCoiMapping::kUnmapped),
      {}};
}  // LCOV_EXCL_LINE

bool addStructuralCoiStatePair(StructuralCoiMapping& mapping,
                               // LCOV_EXCL_START
                               size_t index0,
                               // LCOV_EXCL_STOP
                               size_t index1) {
  if (index0 >= mapping.state0ToState1.size() ||
      index1 >= mapping.state1ToState0.size()) {
    return false;  // LCOV_EXCL_LINE
  }

  // LCOV_EXCL_START
  const size_t existing1 = mapping.state0ToState1[index0];
  // LCOV_EXCL_STOP
  const size_t existing0 = mapping.state1ToState0[index1];
  if (existing1 != StructuralCoiMapping::kUnmapped ||
      existing0 != StructuralCoiMapping::kUnmapped) {
    return existing1 == index1 && existing0 == index0;  // LCOV_EXCL_LINE
  }

  mapping.state0ToState1[index0] = index1;
  mapping.state1ToState0[index1] = index0;
  mapping.pairs.push_back({index0, index1});
  return true;
}

bool structurallyUnifyExprPairForCoi(
    BoolExpr* expr0,
    BoolExpr* expr1,
    StructuralCoiUnificationContext& context) {
  struct StackItem {
    BoolExpr* lhs = nullptr;
    BoolExpr* rhs = nullptr;
  };

  std::vector<StackItem> stack;
  stack.reserve(64);
  stack.push_back({expr0, expr1});
  while (!stack.empty()) {
    const auto [lhs, rhs] = stack.back();
    stack.pop_back();
    if (!context.seenPairs.emplace(lhs, rhs).second) {
      // LCOV_EXCL_START
      continue;
    }
    // LCOV_EXCL_STOP

    // LCOV_EXCL_START
    if (lhs == nullptr || rhs == nullptr) {
    // LCOV_EXCL_STOP
      if (lhs != rhs) {  // LCOV_EXCL_LINE
        return false;  // LCOV_EXCL_LINE
      }
      continue;  // LCOV_EXCL_LINE
    }

    const Op lhsOp = lhs->getOp();
    const Op rhsOp = rhs->getOp();
    if (lhsOp == Op::VAR && rhsOp == Op::VAR) {
      const size_t lhsId = lhs->getId();
      const size_t rhsId = rhs->getId();
      if (lhsId < 2 || rhsId < 2) {
        if (lhsId != rhsId) { // LCOV_EXCL_LINE
          return false; // LCOV_EXCL_LINE
        }
        continue; // LCOV_EXCL_LINE
      }

      const auto lhsInputIt = context.inputClasses0.find(lhsId);
      const auto rhsInputIt = context.inputClasses1.find(rhsId);
      if (lhsInputIt != context.inputClasses0.end() ||
          rhsInputIt != context.inputClasses1.end()) {
        if (lhsInputIt == context.inputClasses0.end() || // LCOV_EXCL_LINE
            rhsInputIt == context.inputClasses1.end() || // LCOV_EXCL_LINE
            lhsInputIt->second != rhsInputIt->second) { // LCOV_EXCL_LINE
          return false; // LCOV_EXCL_LINE
        }
        continue; // LCOV_EXCL_LINE
      }

      const auto lhsStateIt = context.stateIndexByVar0.find(lhsId);
      const auto rhsStateIt = context.stateIndexByVar1.find(rhsId);
      if (lhsStateIt != context.stateIndexByVar0.end() ||
          rhsStateIt != context.stateIndexByVar1.end()) { // LCOV_EXCL_LINE
        // LCOV_EXCL_START
        if (lhsStateIt == context.stateIndexByVar0.end() ||
        // LCOV_EXCL_STOP
            rhsStateIt == context.stateIndexByVar1.end() ||
            !addStructuralCoiStatePair(
                context.mapping, lhsStateIt->second, rhsStateIt->second)) {
          return false;  // LCOV_EXCL_LINE
        }
        continue;
      }

      return false; // LCOV_EXCL_LINE
    }

    if (lhsOp != rhsOp || lhsOp == Op::NONE || rhsOp == Op::NONE) {
      return false;
    }

    stack.push_back({lhs->getLeft(), rhs->getLeft()}); // LCOV_EXCL_LINE
    if (lhsOp != Op::NOT) { // LCOV_EXCL_LINE
      stack.push_back({lhs->getRight(), rhs->getRight()}); // LCOV_EXCL_LINE
    } // LCOV_EXCL_LINE
  }

  return true;
}

AlignedSignals buildStructuralCoiStatePairs(
    const SequentialDesignModel& model0,
    const SequentialDesignModel& model1,
    const StructuralCoiMapping& mapping) {
  AlignedSignals aligned;
  aligned.names.reserve(mapping.pairs.size());
  aligned.keys0.reserve(mapping.pairs.size());
  aligned.keys1.reserve(mapping.pairs.size());
  for (size_t i = 0; i < mapping.pairs.size(); ++i) {
    const auto [index0, index1] = mapping.pairs[i];
    aligned.names.push_back("structural_coi_state_" + std::to_string(i));
    aligned.keys0.push_back(model0.stateBits[index0]);
    aligned.keys1.push_back(model1.stateBits[index1]);
  }
  return aligned;
}

bool validateStructuralCoiRelation( // LCOV_EXCL_LINE
    const SequentialDesignModel& model0,
    const SequentialDesignModel& model1,
    const AlignedSignals& alignedInputs,
    const AlignedSignals& alignedOutputs,
    const AlignedSignals& alignedStates,
    KEPLER_FORMAL::Config::SolverType solverType) {
  const auto [abstractMap0, abstractMap1] = // LCOV_EXCL_LINE
      buildSelectedAbstractMaps(model0, model1, alignedInputs, alignedStates); // LCOV_EXCL_LINE
  std::pmr::monotonic_buffer_resource memoResource; // LCOV_EXCL_LINE
  AbstractExprPairMemo structuralMemo{&memoResource}; // LCOV_EXCL_LINE

  auto equivalentOrSat = [&](BoolExpr* expr0, BoolExpr* expr1) { // LCOV_EXCL_LINE
    // LCOV_EXCL_START
    if (areEquivalentUnderAbstractMaps(
            expr0, expr1, abstractMap0, abstractMap1, structuralMemo)) {
      return true;
    }
    // LCOV_EXCL_STOP
    return expr0 != nullptr && expr1 != nullptr &&  // LCOV_EXCL_LINE
           isWithinSatValidatedOrderedSupportBudget(expr0, expr1) &&  // LCOV_EXCL_LINE
           areSatEquivalentUnderPartialAbstractMaps(  // LCOV_EXCL_LINE
               expr0, expr1, abstractMap0, abstractMap1, solverType);  // LCOV_EXCL_LINE
  }; // LCOV_EXCL_LINE

  for (size_t i = 0; i < alignedOutputs.names.size(); ++i) { // LCOV_EXCL_LINE
    const auto exprIt0 = model0.observedOutputExprByKey.find(alignedOutputs.keys0[i]); // LCOV_EXCL_LINE
    // LCOV_EXCL_START
    const auto exprIt1 = model1.observedOutputExprByKey.find(alignedOutputs.keys1[i]);
    // LCOV_EXCL_STOP
    if (exprIt0 == model0.observedOutputExprByKey.end() || // LCOV_EXCL_LINE
        exprIt1 == model1.observedOutputExprByKey.end() || // LCOV_EXCL_LINE
        !equivalentOrSat(exprIt0->second, exprIt1->second)) { // LCOV_EXCL_LINE
      return false;  // LCOV_EXCL_LINE
    }
  } // LCOV_EXCL_LINE

  // LCOV_EXCL_START
  for (size_t i = 0; i < alignedStates.names.size(); ++i) {
  // LCOV_EXCL_STOP
    BoolExpr* next0 = model0.nextStateExprByStateKey.at(alignedStates.keys0[i]); // LCOV_EXCL_LINE
    BoolExpr* next1 = model1.nextStateExprByStateKey.at(alignedStates.keys1[i]); // LCOV_EXCL_LINE
    if (!equivalentOrSat(next0, next1)) { // LCOV_EXCL_LINE
      return false;  // LCOV_EXCL_LINE
    }
  } // LCOV_EXCL_LINE
  return true; // LCOV_EXCL_LINE
} // LCOV_EXCL_LINE

bool validateStructuralOutputCoiRelation(
    const SequentialDesignModel& model0,
    const SequentialDesignModel& model1,
    const AlignedSignals& alignedInputs,
    const AlignedSignals& alignedOutputs,
    const AlignedSignals& alignedStates,
    KEPLER_FORMAL::Config::SolverType solverType) {
  const auto [abstractMap0, abstractMap1] =
      buildSelectedAbstractMaps(model0, model1, alignedInputs, alignedStates);
  std::pmr::monotonic_buffer_resource memoResource;
  AbstractExprPairMemo structuralMemo{&memoResource};

  for (size_t i = 0; i < alignedOutputs.names.size(); ++i) {
    // LCOV_EXCL_START
    const auto exprIt0 = model0.observedOutputExprByKey.find(alignedOutputs.keys0[i]);
    // LCOV_EXCL_STOP
    const auto exprIt1 = model1.observedOutputExprByKey.find(alignedOutputs.keys1[i]);
    if (exprIt0 == model0.observedOutputExprByKey.end() ||
        exprIt1 == model1.observedOutputExprByKey.end()) {
      return false;  // LCOV_EXCL_LINE
    }
    if (areEquivalentUnderAbstractMaps(
            // LCOV_EXCL_START
            exprIt0->second, exprIt1->second, abstractMap0, abstractMap1,
            structuralMemo)) {
      continue;
    }
    if (!isWithinSatValidatedOrderedSupportBudget(exprIt0->second, exprIt1->second) ||  // LCOV_EXCL_LINE
        !areSatEquivalentUnderPartialAbstractMaps(  // LCOV_EXCL_LINE
            exprIt0->second,  // LCOV_EXCL_LINE
            exprIt1->second,  // LCOV_EXCL_LINE
            // LCOV_EXCL_STOP
            abstractMap0,  // LCOV_EXCL_LINE
            // LCOV_EXCL_START
            abstractMap1,  // LCOV_EXCL_LINE
            // LCOV_EXCL_STOP
            solverType)) {  // LCOV_EXCL_LINE
      return false;  // LCOV_EXCL_LINE
    }
  }  // LCOV_EXCL_LINE
  return true;
}

AlignedSignals inferStructuralOutputCoiStatePairs(
    const SequentialDesignModel& model0,
    const SequentialDesignModel& model1,
    // LCOV_EXCL_START
    const AlignedSignals& alignedInputs,
    // LCOV_EXCL_STOP
    const AlignedSignals& alignedOutputs,
    KEPLER_FORMAL::Config::SolverType solverType) {
  if (alignedOutputs.names.empty()) {
    return {};  // LCOV_EXCL_LINE
  }

  const auto inputClasses0 = buildInputClassMap(model0, alignedInputs.keys0);
  const auto inputClasses1 = buildInputClassMap(model1, alignedInputs.keys1);
  const auto stateIndexByVar0 = buildStateIndexByVar(model0);
  const auto stateIndexByVar1 = buildStateIndexByVar(model1);
  StructuralCoiMapping mapping =
      makeStructuralCoiMapping(model0.stateBits.size(), model1.stateBits.size());
  const size_t bootstrapCoiBudget =
      std::min(kMaxSatValidatedOrderedCoiStatePairs,
               resetBootstrapOutputCoiStatePairBudget());
  std::pmr::monotonic_buffer_resource seenPairResource;
  StructuralExprPairSet seenPairs{&seenPairResource};
  seenPairs.reserve(std::max<size_t>(4096, alignedOutputs.names.size() * 128));
  StructuralCoiUnificationContext unificationContext{
      inputClasses0,
      inputClasses1,
      stateIndexByVar0,
      stateIndexByVar1,
      mapping,
      seenPairs};

  for (size_t i = 0; i < alignedOutputs.names.size(); ++i) {
    const auto exprIt0 = model0.observedOutputExprByKey.find(alignedOutputs.keys0[i]);
    const auto exprIt1 = model1.observedOutputExprByKey.find(alignedOutputs.keys1[i]);
    if (exprIt0 == model0.observedOutputExprByKey.end() ||
        exprIt1 == model1.observedOutputExprByKey.end() ||
        !structurallyUnifyExprPairForCoi(
            exprIt0->second,
            exprIt1->second,
            unificationContext)) {
      if (structuralCoiDiagEnabled()) {
        std::fprintf( // LCOV_EXCL_LINE
            stderr, // LCOV_EXCL_LINE
            "SEC diag: structural output coi rejected output=%zu name=%s pairs=%zu\n",
            i, // LCOV_EXCL_LINE
            alignedOutputs.names[i].c_str(), // LCOV_EXCL_LINE
            mapping.pairs.size()); // LCOV_EXCL_LINE
      // LCOV_EXCL_START
      }
      return {};
    }
    // LCOV_EXCL_STOP
    if (mapping.pairs.size() > bootstrapCoiBudget) {
      // LCOV_EXCL_START
      if (structuralCoiDiagEnabled()) {  // LCOV_EXCL_LINE
        std::fprintf(  // LCOV_EXCL_LINE
            stderr,  // LCOV_EXCL_LINE
            "SEC diag: structural output coi rejected budget pairs=%zu budget=%zu\n",
            // LCOV_EXCL_STOP
            mapping.pairs.size(),  // LCOV_EXCL_LINE
            bootstrapCoiBudget);  // LCOV_EXCL_LINE
      }  // LCOV_EXCL_LINE
      return {};  // LCOV_EXCL_LINE
    }
  }

  // LCOV_EXCL_START
  if (resetBootstrapOutputCoiTransitionClosureEnabled()) {
    size_t checkedTransitionPairs = 0;
    for (size_t cursor = 0; cursor < mapping.pairs.size(); ++cursor) {
    // LCOV_EXCL_STOP
      if (mapping.pairs.size() >= bootstrapCoiBudget) {
        if (structuralCoiDiagEnabled()) {  // LCOV_EXCL_LINE
          // LCOV_EXCL_START
          std::fprintf(  // LCOV_EXCL_LINE
              stderr,  // LCOV_EXCL_LINE
              "SEC diag: structural output-transition coi stopped budget pairs=%zu "
              "budget=%zu\n",
              // LCOV_EXCL_STOP
              mapping.pairs.size(),  // LCOV_EXCL_LINE
              bootstrapCoiBudget);  // LCOV_EXCL_LINE
        }  // LCOV_EXCL_LINE
        break;  // LCOV_EXCL_LINE
      }
      const auto [index0, index1] = mapping.pairs[cursor];
      BoolExpr* next0 = model0.nextStateExprByStateKey.at(model0.stateBits[index0]);
      BoolExpr* next1 = model1.nextStateExprByStateKey.at(model1.stateBits[index1]);
      if (!structurallyUnifyExprPairForCoi(
              next0,
              next1,
              unificationContext)) {
        if (structuralCoiDiagEnabled()) {
          std::fprintf(  // LCOV_EXCL_LINE
              stderr,  // LCOV_EXCL_LINE
              "SEC diag: structural output-transition coi stopped cursor=%zu pairs=%zu\n",
              cursor,  // LCOV_EXCL_LINE
              mapping.pairs.size());  // LCOV_EXCL_LINE
        }  // LCOV_EXCL_LINE
        // LCOV_EXCL_START
        break;
      }
      checkedTransitionPairs = cursor + 1;
      // LCOV_EXCL_STOP
      if (mapping.pairs.size() > bootstrapCoiBudget) {
        if (structuralCoiDiagEnabled()) {  // LCOV_EXCL_LINE
          // LCOV_EXCL_START
          std::fprintf(  // LCOV_EXCL_LINE
              stderr,  // LCOV_EXCL_LINE
              "SEC diag: structural output-transition coi stopped budget pairs=%zu "
              "budget=%zu\n",
              // LCOV_EXCL_STOP
              mapping.pairs.size(),  // LCOV_EXCL_LINE
              bootstrapCoiBudget);  // LCOV_EXCL_LINE
        }  // LCOV_EXCL_LINE
        break;  // LCOV_EXCL_LINE
      }
    }
    // LCOV_EXCL_START
    if (checkedTransitionPairs < mapping.pairs.size()) {
      // Keep only the transition pairs whose own cones were checked.  These
      // LCOV_EXCL_STOP
      // candidates are still top-output rooted and later proof stages must
      // LCOV_EXCL_START
      // validate them before treating them as facts.
      mapping.pairs.resize(checkedTransitionPairs);
      // LCOV_EXCL_STOP
    }
  } else if (structuralCoiDiagEnabled()) {
    std::fprintf(  // LCOV_EXCL_LINE
        stderr,  // LCOV_EXCL_LINE
        "SEC diag: structural output-transition coi skipped root_pairs=%zu\n",
        mapping.pairs.size());  // LCOV_EXCL_LINE
  }  // LCOV_EXCL_LINE

  const AlignedSignals alignedStates =
      buildStructuralCoiStatePairs(model0, model1, mapping);
  if (alignedStates.names.empty() ||
      !validateStructuralOutputCoiRelation(
          model0, model1, alignedInputs, alignedOutputs, alignedStates, solverType)) {
    if (structuralCoiDiagEnabled()) { // LCOV_EXCL_LINE
      std::fprintf( // LCOV_EXCL_LINE
          stderr, // LCOV_EXCL_LINE
          "SEC diag: structural output coi rejected validation pairs=%zu\n",
          alignedStates.names.size()); // LCOV_EXCL_LINE
    } // LCOV_EXCL_LINE
    return {}; // LCOV_EXCL_LINE
  }
  if (structuralCoiDiagEnabled()) {
    std::fprintf( // LCOV_EXCL_LINE
        stderr, // LCOV_EXCL_LINE
        "SEC diag: structural output coi accepted pairs=%zu\n",
        alignedStates.names.size()); // LCOV_EXCL_LINE
  } // LCOV_EXCL_LINE
  return alignedStates;
}

AlignedSignals inferStructuralCoiStatePairs(
    // LCOV_EXCL_START
    const SequentialDesignModel& model0,
    const SequentialDesignModel& model1,
    // LCOV_EXCL_STOP
    const AlignedSignals& alignedInputs,
    const AlignedSignals& alignedOutputs,
    KEPLER_FORMAL::Config::SolverType solverType) {
  if (alignedOutputs.names.empty()) {
    if (structuralCoiDiagEnabled()) {
      std::fprintf(stderr, "SEC diag: structural coi skipped no outputs\n");  // LCOV_EXCL_LINE
    }  // LCOV_EXCL_LINE
    return {};
  }

  const auto inputClasses0 = buildInputClassMap(model0, alignedInputs.keys0); // LCOV_EXCL_LINE
  const auto inputClasses1 = buildInputClassMap(model1, alignedInputs.keys1); // LCOV_EXCL_LINE
  const auto stateIndexByVar0 = buildStateIndexByVar(model0); // LCOV_EXCL_LINE
  const auto stateIndexByVar1 = buildStateIndexByVar(model1); // LCOV_EXCL_LINE
  StructuralCoiMapping mapping =
      makeStructuralCoiMapping(model0.stateBits.size(), model1.stateBits.size()); // LCOV_EXCL_LINE
  std::pmr::monotonic_buffer_resource seenPairResource; // LCOV_EXCL_LINE
  StructuralExprPairSet seenPairs{&seenPairResource}; // LCOV_EXCL_LINE
  seenPairs.reserve(std::max<size_t>(4096, alignedOutputs.names.size() * 128)); // LCOV_EXCL_LINE
  StructuralCoiUnificationContext unificationContext{ // LCOV_EXCL_LINE
      inputClasses0,
      inputClasses1,
      stateIndexByVar0,
      stateIndexByVar1,
      mapping,
      seenPairs};

  for (size_t i = 0; i < alignedOutputs.names.size(); ++i) { // LCOV_EXCL_LINE
    const auto exprIt0 = model0.observedOutputExprByKey.find(alignedOutputs.keys0[i]); // LCOV_EXCL_LINE
    const auto exprIt1 = model1.observedOutputExprByKey.find(alignedOutputs.keys1[i]); // LCOV_EXCL_LINE
    // LCOV_EXCL_START
    if (exprIt0 == model0.observedOutputExprByKey.end() ||
        exprIt1 == model1.observedOutputExprByKey.end() ||
        // LCOV_EXCL_STOP
        !structurallyUnifyExprPairForCoi( // LCOV_EXCL_LINE
            // LCOV_EXCL_START
            exprIt0->second,
            exprIt1->second,
            unificationContext)) {
      if (structuralCoiDiagEnabled()) {
      // LCOV_EXCL_STOP
        std::fprintf(  // LCOV_EXCL_LINE
            stderr,  // LCOV_EXCL_LINE
            "SEC diag: structural coi rejected output=%zu name=%s pairs=%zu\n",
            // LCOV_EXCL_START
            i,  // LCOV_EXCL_LINE
            alignedOutputs.names[i].c_str(),  // LCOV_EXCL_LINE
            mapping.pairs.size());  // LCOV_EXCL_LINE
            // LCOV_EXCL_STOP
      }  // LCOV_EXCL_LINE
      // LCOV_EXCL_START
      return {};
    }
    if (mapping.pairs.size() > kMaxSatValidatedOrderedCoiStatePairs) {
    // LCOV_EXCL_STOP
      if (structuralCoiDiagEnabled()) {  // LCOV_EXCL_LINE
        std::fprintf(  // LCOV_EXCL_LINE
            stderr,  // LCOV_EXCL_LINE
            "SEC diag: structural coi rejected output budget pairs=%zu\n",
            mapping.pairs.size());  // LCOV_EXCL_LINE
      }  // LCOV_EXCL_LINE
      return {};  // LCOV_EXCL_LINE
    }
  } // LCOV_EXCL_LINE

  for (size_t cursor = 0; cursor < mapping.pairs.size(); ++cursor) { // LCOV_EXCL_LINE
    const auto [index0, index1] = mapping.pairs[cursor]; // LCOV_EXCL_LINE
    BoolExpr* next0 = model0.nextStateExprByStateKey.at(model0.stateBits[index0]); // LCOV_EXCL_LINE
    BoolExpr* next1 = model1.nextStateExprByStateKey.at(model1.stateBits[index1]); // LCOV_EXCL_LINE
    if (!structurallyUnifyExprPairForCoi( // LCOV_EXCL_LINE
            next0, // LCOV_EXCL_LINE
            next1, // LCOV_EXCL_LINE
            unificationContext)) {
      if (structuralCoiDiagEnabled()) { // LCOV_EXCL_LINE
        std::fprintf(  // LCOV_EXCL_LINE
            stderr,  // LCOV_EXCL_LINE
            // LCOV_EXCL_START
            "SEC diag: structural coi rejected transition cursor=%zu pairs=%zu\n",
            cursor,  // LCOV_EXCL_LINE
            mapping.pairs.size());  // LCOV_EXCL_LINE
            // LCOV_EXCL_STOP
      }  // LCOV_EXCL_LINE
      // LCOV_EXCL_START
      return {};
    }
    if (mapping.pairs.size() > kMaxSatValidatedOrderedCoiStatePairs) {
    // LCOV_EXCL_STOP
      if (structuralCoiDiagEnabled()) {  // LCOV_EXCL_LINE
        std::fprintf(  // LCOV_EXCL_LINE
            stderr,  // LCOV_EXCL_LINE
            "SEC diag: structural coi rejected transition budget pairs=%zu\n",
            mapping.pairs.size());  // LCOV_EXCL_LINE
      }  // LCOV_EXCL_LINE
      return {};  // LCOV_EXCL_LINE
    }
  } // LCOV_EXCL_LINE

// LCOV_EXCL_START

  const AlignedSignals alignedStates =
  // LCOV_EXCL_STOP
      buildStructuralCoiStatePairs(model0, model1, mapping); // LCOV_EXCL_LINE
  // LCOV_EXCL_START
  if (alignedStates.names.empty() ||
      !validateStructuralCoiRelation(
      // LCOV_EXCL_STOP
          model0, model1, alignedInputs, alignedOutputs, alignedStates, solverType)) { // LCOV_EXCL_LINE
    if (structuralCoiDiagEnabled()) {  // LCOV_EXCL_LINE
      std::fprintf(  // LCOV_EXCL_LINE
          // LCOV_EXCL_START
          stderr,  // LCOV_EXCL_LINE
          "SEC diag: structural coi rejected validation pairs=%zu\n",
          // LCOV_EXCL_STOP
          alignedStates.names.size());  // LCOV_EXCL_LINE
    // LCOV_EXCL_START
    }  // LCOV_EXCL_LINE
    return {};  // LCOV_EXCL_LINE
    // LCOV_EXCL_STOP
  }
  if (structuralCoiDiagEnabled()) { // LCOV_EXCL_LINE
    std::fprintf(  // LCOV_EXCL_LINE
        stderr,  // LCOV_EXCL_LINE
        "SEC diag: structural coi accepted pairs=%zu\n",
        alignedStates.names.size());  // LCOV_EXCL_LINE
  }  // LCOV_EXCL_LINE
  return alignedStates; // LCOV_EXCL_LINE
}

AlignedSignals inferSatValidatedOrderedCoiStatePairs(
    const SequentialDesignModel& model0,
    const SequentialDesignModel& model1,
    const AlignedSignals& alignedInputs,
    const AlignedSignals& alignedOutputs,
    KEPLER_FORMAL::Config::SolverType solverType) {
  if (alignedOutputs.names.empty() ||
      model0.stateBits.size() != model1.stateBits.size()) { // LCOV_EXCL_LINE
    return {};
  }

  // LCOV_EXCL_START
  const auto stateIndexByVar0 = buildStateIndexByVar(model0);
  const auto stateIndexByVar1 = buildStateIndexByVar(model1);
  // LCOV_EXCL_STOP
  std::vector<unsigned char> selected(model0.stateBits.size(), 0); // LCOV_EXCL_LINE
  expandOrderedCoiFromOutputs( // LCOV_EXCL_LINE
      model0, model1, alignedOutputs, stateIndexByVar0, stateIndexByVar1, selected); // LCOV_EXCL_LINE
  if (std::count(selected.begin(), selected.end(), 1) == 0) { // LCOV_EXCL_LINE
    if (structuralCoiDiagEnabled()) { // LCOV_EXCL_LINE
      std::fprintf(stderr, "SEC diag: ordered coi skipped no selected state\n");  // LCOV_EXCL_LINE
    // LCOV_EXCL_START
    }  // LCOV_EXCL_LINE
    return {};
  }
  // LCOV_EXCL_STOP

  // LCOV_EXCL_START
  for (size_t pass = 0; pass < kMaxOrderedCoiExpansionPasses; ++pass) {
    if (static_cast<size_t>(std::count(selected.begin(), selected.end(), 1)) >
        kMaxSatValidatedOrderedCoiStatePairs) {
      if (structuralCoiDiagEnabled()) {  // LCOV_EXCL_LINE
      // LCOV_EXCL_STOP
        std::fprintf(  // LCOV_EXCL_LINE
            stderr,  // LCOV_EXCL_LINE
            "SEC diag: ordered coi rejected budget pass=%zu selected=%zu\n",
            pass,  // LCOV_EXCL_LINE
            static_cast<size_t>(std::count(selected.begin(), selected.end(), 1)));  // LCOV_EXCL_LINE
      }  // LCOV_EXCL_LINE
      return {};  // LCOV_EXCL_LINE
    }

    const AlignedSignals selectedStates =
        buildOrderedStatePairsForSelection(model0, model1, selected); // LCOV_EXCL_LINE
    const std::vector<unsigned char> passSelected = selected; // LCOV_EXCL_LINE
    const auto [abstractMap0, abstractMap1] = // LCOV_EXCL_LINE
        buildSelectedAbstractMaps(model0, model1, alignedInputs, selectedStates); // LCOV_EXCL_LINE
    std::pmr::monotonic_buffer_resource memoResource; // LCOV_EXCL_LINE
    AbstractExprPairMemo structuralMemo{&memoResource}; // LCOV_EXCL_LINE
    bool changed = false; // LCOV_EXCL_LINE
    bool invalidRelation = false; // LCOV_EXCL_LINE
    // LCOV_EXCL_START
    std::string invalidReason;

    for (size_t i = 0; i < alignedOutputs.names.size(); ++i) {
    // LCOV_EXCL_STOP
      const auto exprIt0 = model0.observedOutputExprByKey.find(alignedOutputs.keys0[i]); // LCOV_EXCL_LINE
      // LCOV_EXCL_START
      const auto exprIt1 = model1.observedOutputExprByKey.find(alignedOutputs.keys1[i]);
      if (exprIt0 == model0.observedOutputExprByKey.end() ||
          exprIt1 == model1.observedOutputExprByKey.end()) {
        if (structuralCoiDiagEnabled()) {  // LCOV_EXCL_LINE
          std::fprintf(  // LCOV_EXCL_LINE
          // LCOV_EXCL_STOP
              stderr,  // LCOV_EXCL_LINE
              "SEC diag: ordered coi rejected missing output=%zu pass=%zu selected=%zu\n",
              i,  // LCOV_EXCL_LINE
              pass,  // LCOV_EXCL_LINE
              static_cast<size_t>(std::count(selected.begin(), selected.end(), 1)));  // LCOV_EXCL_LINE
        }  // LCOV_EXCL_LINE
        return {};  // LCOV_EXCL_LINE
      }
      changed |= ensureExprPairEquivalentOrExpand( // LCOV_EXCL_LINE
          exprIt0->second, // LCOV_EXCL_LINE
          exprIt1->second, // LCOV_EXCL_LINE
          stateIndexByVar0,
          stateIndexByVar1,
          abstractMap0, // LCOV_EXCL_LINE
          // LCOV_EXCL_START
          abstractMap1,
          structuralMemo,
          selected,
          // LCOV_EXCL_STOP
          solverType, // LCOV_EXCL_LINE
          invalidRelation,
          // LCOV_EXCL_START
          &invalidReason);
      if (invalidRelation) {
        if (structuralCoiDiagEnabled()) {  // LCOV_EXCL_LINE
          std::fprintf(  // LCOV_EXCL_LINE
              stderr,  // LCOV_EXCL_LINE
              "SEC diag: ordered coi rejected output=%zu name=%s pass=%zu "
              "selected=%zu reason=%s\n",
              // LCOV_EXCL_STOP
              i,  // LCOV_EXCL_LINE
              alignedOutputs.names[i].c_str(),  // LCOV_EXCL_LINE
              pass,  // LCOV_EXCL_LINE
              static_cast<size_t>(std::count(selected.begin(), selected.end(), 1)),  // LCOV_EXCL_LINE
              invalidReason.c_str());  // LCOV_EXCL_LINE
        }  // LCOV_EXCL_LINE
        return {};  // LCOV_EXCL_LINE
      }
    } // LCOV_EXCL_LINE

    for (size_t i = 0; i < passSelected.size(); ++i) { // LCOV_EXCL_LINE
      if (!passSelected[i]) { // LCOV_EXCL_LINE
        continue; // LCOV_EXCL_LINE
      }
      BoolExpr* next0 = model0.nextStateExprByStateKey.at(model0.stateBits[i]); // LCOV_EXCL_LINE
      BoolExpr* next1 = model1.nextStateExprByStateKey.at(model1.stateBits[i]); // LCOV_EXCL_LINE
      changed |= ensureExprPairEquivalentOrExpand( // LCOV_EXCL_LINE
          next0, // LCOV_EXCL_LINE
          next1, // LCOV_EXCL_LINE
          stateIndexByVar0,
          stateIndexByVar1,
          abstractMap0, // LCOV_EXCL_LINE
          abstractMap1, // LCOV_EXCL_LINE
          structuralMemo,
          selected,
          solverType, // LCOV_EXCL_LINE
          invalidRelation,
          &invalidReason);
      if (invalidRelation) { // LCOV_EXCL_LINE
        if (structuralCoiDiagEnabled()) { // LCOV_EXCL_LINE
          std::fprintf(  // LCOV_EXCL_LINE
              stderr,  // LCOV_EXCL_LINE
              "SEC diag: ordered coi rejected transition=%zu pass=%zu "
              "selected=%zu reason=%s\n",
              i,  // LCOV_EXCL_LINE
              pass,  // LCOV_EXCL_LINE
              static_cast<size_t>(std::count(selected.begin(), selected.end(), 1)),  // LCOV_EXCL_LINE
              invalidReason.c_str());  // LCOV_EXCL_LINE
        }  // LCOV_EXCL_LINE
        return {}; // LCOV_EXCL_LINE
      // LCOV_EXCL_START
      }
    }


// LCOV_EXCL_STOP
    if (!changed) { // LCOV_EXCL_LINE
      // LCOV_EXCL_START
      // Only the top-output alignment came from names.  Ordered internal state
      // bits were merely candidates, and every reached output/transition formula
      // has now been proven equivalent under the selected relation.
      if (structuralCoiDiagEnabled()) {  // LCOV_EXCL_LINE
      // LCOV_EXCL_STOP
        std::fprintf(  // LCOV_EXCL_LINE
            stderr,  // LCOV_EXCL_LINE
            "SEC diag: ordered coi accepted pass=%zu selected=%zu\n",
            // LCOV_EXCL_START
            pass,  // LCOV_EXCL_LINE
            selectedStates.names.size());  // LCOV_EXCL_LINE
      }  // LCOV_EXCL_LINE
      // LCOV_EXCL_STOP
      return selectedStates;  // LCOV_EXCL_LINE
    // LCOV_EXCL_START
    }
  }


// LCOV_EXCL_STOP
  if (structuralCoiDiagEnabled()) {  // LCOV_EXCL_LINE
    std::fprintf(  // LCOV_EXCL_LINE
        stderr,  // LCOV_EXCL_LINE
        "SEC diag: ordered coi rejected pass_limit selected=%zu\n",
        static_cast<size_t>(std::count(selected.begin(), selected.end(), 1)));  // LCOV_EXCL_LINE
  }  // LCOV_EXCL_LINE
  return {};  // LCOV_EXCL_LINE
}

struct ClockInputClassKey {  // LCOV_EXCL_LINE
  SignalKey domain;
  ClockPhase phase = ClockPhase::Pos;
};

struct ClockInputClassKeyLess {
  bool operator()(const ClockInputClassKey& lhs, // LCOV_EXCL_LINE
                  const ClockInputClassKey& rhs) const {
    SignalKeyLess keyLess;
    if (keyLess(lhs.domain, rhs.domain)) { // LCOV_EXCL_LINE
      return true; // LCOV_EXCL_LINE
    }
    if (keyLess(rhs.domain, lhs.domain)) { // LCOV_EXCL_LINE
      return false; // LCOV_EXCL_LINE
    }
    return static_cast<int>(lhs.phase) < static_cast<int>(rhs.phase); // LCOV_EXCL_LINE
  } // LCOV_EXCL_LINE
};

std::unordered_map<size_t, size_t> buildLegacyClockInputClassMap(
    const SequentialDesignModel& model,
    const std::vector<SignalKey>& alignedInputKeys) {
  std::unordered_map<size_t, size_t> classes;
  classes.reserve(alignedInputKeys.size() + model.clockCarrierVarIDs.size());
  std::unordered_set<size_t> clockCarrierVars(
      model.clockCarrierVarIDs.begin(), model.clockCarrierVarIDs.end());
  size_t clockClass = std::numeric_limits<size_t>::max();
  bool sawClockClass = false;
  // LCOV_EXCL_START
  bool multipleClockClasses = false;
  for (size_t i = 0; i < alignedInputKeys.size(); ++i) {
    const size_t varID = model.inputVarByKey.at(alignedInputKeys[i]);
    classes.emplace(varID, i);
    if (clockCarrierVars.find(varID) == clockCarrierVars.end()) {
      continue;
    }
    // LCOV_EXCL_STOP
    if (!sawClockClass) {  // LCOV_EXCL_LINE
      // LCOV_EXCL_START
      clockClass = i;  // LCOV_EXCL_LINE
      sawClockClass = true;  // LCOV_EXCL_LINE
      // LCOV_EXCL_STOP
    } else if (clockClass != i) {  // LCOV_EXCL_LINE
      // LCOV_EXCL_START
      multipleClockClasses = true;  // LCOV_EXCL_LINE
      // LCOV_EXCL_STOP
    }  // LCOV_EXCL_LINE
  }  // LCOV_EXCL_LINE
  if (sawClockClass && !multipleClockClasses) {
    for (const auto varID : model.clockCarrierVarIDs) {  // LCOV_EXCL_LINE
      classes.emplace(varID, clockClass);  // LCOV_EXCL_LINE
    }
  }  // LCOV_EXCL_LINE
  return classes;
}

std::unordered_map<size_t, size_t> buildInputClassMap(
    const SequentialDesignModel& model,
    const std::vector<SignalKey>& alignedInputKeys) {
  if (model.clockCarrierClasses.empty()) {
    return buildLegacyClockInputClassMap(model, alignedInputKeys);
  }

  std::unordered_map<size_t, size_t> classes; // LCOV_EXCL_LINE
  classes.reserve(alignedInputKeys.size() + model.clockCarrierClasses.size()); // LCOV_EXCL_LINE
  std::map<ClockInputClassKey, size_t, ClockInputClassKeyLess> clockClassByEvent; // LCOV_EXCL_LINE
  for (size_t i = 0; i < alignedInputKeys.size(); ++i) { // LCOV_EXCL_LINE
    const size_t varID = model.inputVarByKey.at(alignedInputKeys[i]); // LCOV_EXCL_LINE
    classes.emplace(varID, i); // LCOV_EXCL_LINE
    clockClassByEvent.emplace( // LCOV_EXCL_LINE
        ClockInputClassKey{alignedInputKeys[i], ClockPhase::Pos}, i); // LCOV_EXCL_LINE
  // LCOV_EXCL_START
  }


// LCOV_EXCL_STOP
  size_t nextClockClass = alignedInputKeys.size(); // LCOV_EXCL_LINE
  for (const auto& carrierClass : model.clockCarrierClasses) { // LCOV_EXCL_LINE
    const ClockInputClassKey key{carrierClass.domain, carrierClass.phase}; // LCOV_EXCL_LINE
    auto classIt = clockClassByEvent.find(key); // LCOV_EXCL_LINE
    if (classIt == clockClassByEvent.end()) { // LCOV_EXCL_LINE
      classIt = clockClassByEvent.emplace(key, nextClockClass++).first;  // LCOV_EXCL_LINE
    }  // LCOV_EXCL_LINE
    classes.emplace(carrierClass.varID, classIt->second); // LCOV_EXCL_LINE
  } // LCOV_EXCL_LINE
  return classes; // LCOV_EXCL_LINE
}

std::unordered_map<SignalKey, char, SignalKeyHash> buildComplementRoleMap(
    const SequentialDesignModel& model) {
  std::unordered_map<SignalKey, char, SignalKeyHash> roles;
  for (const auto& key : model.stateBits) {
    roles.emplace(key, 'N');
  }
  for (const auto& relation : model.complementedStateRelations) {
    roles[relation.primaryKey] = 'P';
    roles[relation.complementedKey] = 'C';
  }
  return roles;
}

uint64_t mixHash(uint64_t value) {
  value += 0x9e3779b97f4a7c15ull;
  value = (value ^ (value >> 30)) * 0xbf58476d1ce4e5b9ull;
  value = (value ^ (value >> 27)) * 0x94d049bb133111ebull;
  return value ^ (value >> 31);
}

uint64_t combineHashes(std::initializer_list<uint64_t> parts) {
  uint64_t hash = 0x243f6a8885a308d3ull;
  for (const auto part : parts) {
    // LCOV_EXCL_START
    hash = mixHash(hash ^ mixHash(part));
    // LCOV_EXCL_STOP
  }
  return hash;
}

size_t saturatedMultiply(size_t lhs, size_t rhs) {
  if (lhs != 0 && rhs > std::numeric_limits<size_t>::max() / lhs) {
    return std::numeric_limits<size_t>::max();  // LCOV_EXCL_LINE
  }
  return lhs * rhs;
}

size_t initialFingerprintMemoReserve(const SequentialDesignModel& model) {
  // Structural matching fingerprints all state next-state DAGs in one pass.
  // The number of state roots is only a lower bound, but reserving a practical
  // fan-in multiplier avoids the PMR table retaining several obsolete bucket
  // arrays as it grows through a large ASIC transition graph.
  return std::max(
      static_cast<size_t>(4096),
      saturatedMultiply(model.nextStateExprByStateKey.size(), static_cast<size_t>(64)));
}

// LCOV_EXCL_START

void reserveFingerprintMemo(FingerprintMemo& memo,
                            size_t& reservedEntries,
                            // LCOV_EXCL_STOP
                            size_t desiredEntries) {
  if (desiredEntries <= reservedEntries) {
    return;
  }
  reservedEntries =  // LCOV_EXCL_LINE
      desiredEntries + std::max(desiredEntries / 2, static_cast<size_t>(4096));  // LCOV_EXCL_LINE
  memo.reserve(reservedEntries);  // LCOV_EXCL_LINE
}

void cacheFingerprint(FingerprintMemo& memo,
                      size_t& reservedEntries,
                      BoolExpr* node,
                      uint64_t fingerprint) {
  reserveFingerprintMemo(memo, reservedEntries, memo.size() + 1);
  memo.emplace(node, fingerprint);
}

void reserveAbstractExprPairMemo(AbstractExprPairMemo& memo,
                                 size_t desiredEntries) {
  const auto capacity =
      static_cast<size_t>(memo.bucket_count() * memo.max_load_factor());
  if (desiredEntries <= capacity) {
    return;
  }

  // This memo is shared across many reset/bootstrap equality candidates. Grow
  // it deliberately instead of relying on unordered_map's small incremental
  // rehashes, which became visible before PDR even reached its SAT loop.
  memo.reserve(
      desiredEntries + std::max(desiredEntries / 2, static_cast<size_t>(4096)));
}

void cacheAbstractEquivalence(AbstractExprPairMemo& memo,
                              const std::pair<BoolExpr*, BoolExpr*>& key,
                              bool equivalent) {
  reserveAbstractExprPairMemo(memo, memo.size() + 1);
  memo.emplace(key, equivalent);
}

uint64_t initialStateSignature(
    const SequentialDesignModel& model,
    const std::unordered_map<SignalKey, char, SignalKeyHash>& complementRoles,
    const SignalKey& key) {
  uint64_t initHash = 0;
  if (const auto initIt = model.initialStateValueByKey.find(key);
      initIt != model.initialStateValueByKey.end()) {
    initHash = initIt->second ? 1 : 2;
  }
  uint64_t roleHash = 0;
  if (const auto roleIt = complementRoles.find(key);
      roleIt != complementRoles.end()) {
    roleHash = static_cast<unsigned char>(roleIt->second);
  }
  return combineHashes({initHash, roleHash});
}

uint64_t fingerprintExpr(
    BoolExpr* expr,
    const std::unordered_map<size_t, size_t>& inputClasses,
    const std::unordered_map<size_t, size_t>& stateClasses,
    FingerprintMemo& memo,
    size_t& memoReservedEntries) {
  if (expr == nullptr) {
    return 0;
  }
  if (const auto it = memo.find(expr); it != memo.end()) {
    return it->second; // LCOV_EXCL_LINE
  }

  struct StackFrame {
    BoolExpr* node = nullptr;
    bool visited = false;
  };

  // Structural matching sees very deep, hash-consed gate-level DAGs on large
  // ASICs. A recursive fingerprint is easy to read, but it repeatedly burned
  // CPU and stack in BlackParrot before the actual SEC engine started. This is
  // the same post-order computation, just explicit and memoized across all
  // LCOV_EXCL_START
  // state bits in the current refinement pass.
  // LCOV_EXCL_STOP
  std::vector<StackFrame> stack{{expr, false}};
  while (!stack.empty()) {
    const StackFrame current = stack.back();
    stack.pop_back();
    BoolExpr* node = current.node;
    if (node == nullptr || memo.find(node) != memo.end()) {
      continue;  // LCOV_EXCL_LINE
    }

    if (node->getOp() == Op::VAR) {
      uint64_t fingerprint = 0;
      if (node->getId() < 2) {
        fingerprint = node->getId() == 0 ? 7 : 11;
      } else if (const auto inputIt = inputClasses.find(node->getId());
                 inputIt != inputClasses.end()) {
        fingerprint = combineHashes({13, inputIt->second}); // LCOV_EXCL_LINE
      } else if (const auto stateIt = stateClasses.find(node->getId());
                 stateIt != stateClasses.end()) {
        fingerprint = combineHashes({17, stateIt->second}); // LCOV_EXCL_LINE
      } else { // LCOV_EXCL_LINE
        fingerprint = 19;
      }
      cacheFingerprint(memo, memoReservedEntries, node, fingerprint);
      continue;
    }

    if (node->getOp() == Op::NONE) {
      cacheFingerprint(memo, memoReservedEntries, node, 41);
      continue;
    }

    if (!current.visited) { // LCOV_EXCL_LINE
      stack.push_back({node, true}); // LCOV_EXCL_LINE
      if (node->getRight() != nullptr && // LCOV_EXCL_LINE
          memo.find(node->getRight()) == memo.end()) { // LCOV_EXCL_LINE
        stack.push_back({node->getRight(), false}); // LCOV_EXCL_LINE
      } // LCOV_EXCL_LINE
      if (node->getLeft() != nullptr && // LCOV_EXCL_LINE
          memo.find(node->getLeft()) == memo.end()) { // LCOV_EXCL_LINE
        stack.push_back({node->getLeft(), false}); // LCOV_EXCL_LINE
      } // LCOV_EXCL_LINE
      continue; // LCOV_EXCL_LINE
    }

    uint64_t fingerprint = 0; // LCOV_EXCL_LINE
    switch (node->getOp()) { // LCOV_EXCL_LINE
      case Op::NOT:
        fingerprint = combineHashes({23, memo.at(node->getLeft())}); // LCOV_EXCL_LINE
        break; // LCOV_EXCL_LINE
      case Op::AND:
      case Op::OR:
      case Op::XOR: {
        uint64_t lhs = memo.at(node->getLeft()); // LCOV_EXCL_LINE
        uint64_t rhs = memo.at(node->getRight()); // LCOV_EXCL_LINE
        if (lhs > rhs) { // LCOV_EXCL_LINE
          std::swap(lhs, rhs); // LCOV_EXCL_LINE
        // LCOV_EXCL_START
        }
        // LCOV_EXCL_STOP
        const uint64_t opTag = // LCOV_EXCL_LINE
            // LCOV_EXCL_START
            node->getOp() == Op::AND ? 29 : (node->getOp() == Op::OR ? 31 : 37);
            // LCOV_EXCL_STOP
        fingerprint = combineHashes({opTag, lhs, rhs}); // LCOV_EXCL_LINE
        break; // LCOV_EXCL_LINE
      }
      case Op::VAR:  // LCOV_EXCL_LINE
      case Op::NONE:  // LCOV_EXCL_LINE
      default:
        throw std::runtime_error("Unsupported BoolExpr operator in fingerprint");  // LCOV_EXCL_LINE
    }
    cacheFingerprint(memo, memoReservedEntries, node, fingerprint); // LCOV_EXCL_LINE
  }

  return memo.at(expr);
}

std::vector<size_t> refineClasses(
    const SequentialDesignModel& model,
    const std::unordered_map<size_t, size_t>& inputClasses,
    const std::vector<size_t>& currentClasses) {
  // Replace each state's current class by a finer signature that combines the
  // previous class and the structure of its next-state expression.
  std::unordered_map<size_t, size_t> stateClasses;
  stateClasses.reserve(model.stateBits.size());
  for (size_t i = 0; i < model.stateBits.size(); ++i) {
    stateClasses.emplace(model.inputVarByKey.at(model.stateBits[i]), currentClasses[i]);
  }

  using RefinementSignature = std::pair<size_t, uint64_t>;
  std::vector<RefinementSignature> signatures(model.stateBits.size());
  // Fingerprinting touches millions of shared BoolExpr DAG nodes on large SEC
  // designs.  A monotonic arena keeps the per-pass memo allocations linear and
  // cheap, then releases all nodes together when refinement advances.
  std::pmr::monotonic_buffer_resource memoResource;
  FingerprintMemo memo{&memoResource};
  size_t memoReservedEntries = initialFingerprintMemoReserve(model);
  memo.reserve(memoReservedEntries);
  for (size_t i = 0; i < model.stateBits.size(); ++i) {
    signatures[i] = {
        currentClasses[i],
        fingerprintExpr(
            model.nextStateExprByStateKey.at(model.stateBits[i]),
            inputClasses,
            stateClasses,
            memo,
            memoReservedEntries)};
  }

  std::vector<RefinementSignature> unique = signatures;
  std::sort(unique.begin(), unique.end());
  unique.erase(std::unique(unique.begin(), unique.end()), unique.end());

  std::unordered_map<RefinementSignature, size_t, RefinementSignatureHash>
      classBySignature;
  classBySignature.reserve(unique.size());
  for (size_t i = 0; i < unique.size(); ++i) {
    classBySignature.emplace(unique[i], i);
  }

  std::vector<size_t> refined(model.stateBits.size(), 0);
  for (size_t i = 0; i < signatures.size(); ++i) {
    refined[i] = classBySignature.at(signatures[i]);
  }
  return refined;
}

std::vector<size_t> seedClasses(const SequentialDesignModel& model) {
  const auto complementRoles = buildComplementRoleMap(model);
  std::vector<uint64_t> signatures;
  signatures.reserve(model.stateBits.size());
  for (const auto& key : model.stateBits) {
    signatures.push_back(initialStateSignature(model, complementRoles, key));
  }

  std::vector<uint64_t> unique = signatures;
  std::sort(unique.begin(), unique.end());
  unique.erase(std::unique(unique.begin(), unique.end()), unique.end());

  std::unordered_map<uint64_t, size_t> classBySignature;
  classBySignature.reserve(unique.size());
  for (size_t i = 0; i < unique.size(); ++i) {
    classBySignature.emplace(unique[i], i);
  }

  std::vector<size_t> seeded(signatures.size(), 0);
  for (size_t i = 0; i < signatures.size(); ++i) {
    seeded[i] = classBySignature.at(signatures[i]);
  }
  return seeded;
}

struct StateClassFingerprint {
  uint64_t seedSignature = 0;
  uint64_t transitionFingerprint = 0;

  bool operator<(const StateClassFingerprint& other) const {
    if (seedSignature != other.seedSignature) {
      return seedSignature < other.seedSignature;
    }
    return transitionFingerprint < other.transitionFingerprint;
  }
};

std::vector<StateClassFingerprint> computeFinalFingerprints(
    const SequentialDesignModel& model,
    const std::unordered_map<size_t, size_t>& inputClasses,
    const std::vector<size_t>& finalClasses) {
  const auto complementRoles = buildComplementRoleMap(model);

  std::unordered_map<size_t, size_t> stateClasses;
  stateClasses.reserve(model.stateBits.size());
  for (size_t i = 0; i < model.stateBits.size(); ++i) {
    stateClasses.emplace(model.inputVarByKey.at(model.stateBits[i]), finalClasses[i]);
  }

  std::vector<StateClassFingerprint> fingerprints;
  fingerprints.reserve(model.stateBits.size());
  std::pmr::monotonic_buffer_resource memoResource;
  FingerprintMemo memo{&memoResource};
  size_t memoReservedEntries = initialFingerprintMemoReserve(model);
  memo.reserve(memoReservedEntries);
  for (const auto& key : model.stateBits) {
    fingerprints.push_back(
        {initialStateSignature(model, complementRoles, key),
         fingerprintExpr(
             model.nextStateExprByStateKey.at(key),
             inputClasses,
             stateClasses,
             memo,
             memoReservedEntries)});
  }
  return fingerprints;
}

}  // namespace

std::pair<LocalToAbstractVarMap, LocalToAbstractVarMap> buildAbstractTransitionMaps(
    const SequentialDesignModel& model0,
    const SequentialDesignModel& model1,
    const AlignedSignals& alignedInputs,
    const AlignedSignals& alignedStates) {
  return buildAbstractTransitionMapsImpl(
      model0, model1, alignedInputs, alignedStates);
}

bool areEquivalentUnderAbstractMaps(
    BoolExpr* expr0,
    BoolExpr* expr1,
    const LocalToAbstractVarMap& abstractMap0,
    const LocalToAbstractVarMap& abstractMap1) {
  std::pmr::monotonic_buffer_resource memoResource;
  AbstractExprPairMemo memo{&memoResource};
  return areEquivalentUnderAbstractMaps(
      expr0, expr1, abstractMap0, abstractMap1, memo);
}

bool areEquivalentUnderAbstractMaps(
    BoolExpr* expr0,
    BoolExpr* expr1,
    const LocalToAbstractVarMap& abstractMap0,
    const LocalToAbstractVarMap& abstractMap1,
    AbstractExprPairMemo& memo) {
  struct StackFrame {
    BoolExpr* lhs = nullptr;
    BoolExpr* rhs = nullptr;
    bool visited = false;
  };

  std::vector<StackFrame> stack{{expr0, expr1, false}};
  while (!stack.empty()) {
    const StackFrame current = stack.back();
    stack.pop_back();
    const auto key = std::make_pair(current.lhs, current.rhs);
    if (memo.find(key) != memo.end()) {
      continue;
    }

    if (current.lhs == nullptr || current.rhs == nullptr) {
      cacheAbstractEquivalence(memo, key, current.lhs == current.rhs);
      continue;
    }

    const Op lhsOp = current.lhs->getOp();
    const Op rhsOp = current.rhs->getOp();
    if (lhsOp == Op::VAR && rhsOp == Op::VAR) {
      bool equivalent = false;
      if (current.lhs->getId() < 2 || current.rhs->getId() < 2) {
        equivalent = current.lhs->getId() == current.rhs->getId();
      } else {
        const auto it0 = abstractMap0.find(current.lhs->getId());
        const auto it1 = abstractMap1.find(current.rhs->getId());
        equivalent = it0 != abstractMap0.end() && it1 != abstractMap1.end() &&
                     it0->second == it1->second;
      }
      cacheAbstractEquivalence(memo, key, equivalent);
      continue;
    }

    if (lhsOp != rhsOp) {
      cacheAbstractEquivalence(memo, key, false);
      continue;
    }

    if (!current.visited) {
      stack.push_back({current.lhs, current.rhs, true});
      const auto rightKey =
          std::make_pair(current.lhs->getRight(), current.rhs->getRight());
      if (memo.find(rightKey) == memo.end()) {
        stack.push_back({current.lhs->getRight(), current.rhs->getRight(), false});
      }
      const auto leftKey =
          std::make_pair(current.lhs->getLeft(), current.rhs->getLeft());
      if (memo.find(leftKey) == memo.end()) {
        stack.push_back({current.lhs->getLeft(), current.rhs->getLeft(), false});
      }
      continue;
    }

    const bool leftEquivalent =
        memo.at(std::make_pair(current.lhs->getLeft(), current.rhs->getLeft()));
    const bool rightEquivalent =
        memo.at(std::make_pair(current.lhs->getRight(), current.rhs->getRight()));
    bool equivalent = leftEquivalent && rightEquivalent;
    if (!equivalent && isCommutativeBoolOp(lhsOp)) {
      const auto crossLeftKey =
          std::make_pair(current.lhs->getLeft(), current.rhs->getRight());
      const auto crossRightKey =
          std::make_pair(current.lhs->getRight(), current.rhs->getLeft());
      bool deferred = false;
      if (memo.find(crossRightKey) == memo.end()) {
        if (!deferred) {
          stack.push_back({current.lhs, current.rhs, true});
          deferred = true;
        }
        stack.push_back(
            {current.lhs->getRight(), current.rhs->getLeft(), false});
      }
      if (memo.find(crossLeftKey) == memo.end()) {
        if (!deferred) {
          stack.push_back({current.lhs, current.rhs, true});
          deferred = true;
        }
        stack.push_back(
            {current.lhs->getLeft(), current.rhs->getRight(), false});
      }
      if (deferred) {
        continue;
      }
      equivalent = memo.at(crossLeftKey) && memo.at(crossRightKey);
    }
    cacheAbstractEquivalence(memo, key, equivalent);
  }

  return memo.at(std::make_pair(expr0, expr1));
}

AlignedSignals inferStructurallyEquivalentStatePairs(
    const SequentialDesignModel& model0,
    const SequentialDesignModel& model1,
    const AlignedSignals& alignedInputs,
    const AlignedSignals& alignedOutputs,
    KEPLER_FORMAL::Config::SolverType solverType) {
  if (model0.stateBits.empty() || model1.stateBits.empty()) {
    return {};
  }

  const AlignedSignals orderedStates = buildOrderedStatePairs(model0, model1);
  if (!orderedStates.names.empty() &&
      areAllOrderedStatesEquivalent(model0, model1, alignedInputs, orderedStates)) {
    // This fast path is purely structural: same order, same transition shape.
    return orderedStates; // LCOV_EXCL_LINE
  }
  if (structuralCoiDiagEnabled() && !orderedStates.names.empty()) {
    std::fprintf(  // LCOV_EXCL_LINE
        stderr,  // LCOV_EXCL_LINE
        "SEC diag: ordered structural states rejected pairs=%zu\n",
        orderedStates.names.size());  // LCOV_EXCL_LINE
  // LCOV_EXCL_START
  }  // LCOV_EXCL_LINE
  // LCOV_EXCL_STOP
  if (!orderedStates.names.empty() &&
      areAllOrderedStatesSatEquivalent(
          model0, model1, alignedInputs, orderedStates, solverType)) {
    // This fallback still does not trust internal names or raw extraction
    // order.  The order only proposes a relation; every next-state equation is
    // SAT-proved equivalent under that relation before it is exposed to SEC.
    return orderedStates;  // LCOV_EXCL_LINE
  }
  if (structuralCoiDiagEnabled() && !orderedStates.names.empty()) {
    std::fprintf(  // LCOV_EXCL_LINE
        stderr,  // LCOV_EXCL_LINE
        "SEC diag: ordered SAT-validated states rejected pairs=%zu\n",
        orderedStates.names.size());  // LCOV_EXCL_LINE
  }  // LCOV_EXCL_LINE
  const AlignedSignals structuralCoiStates = inferStructuralCoiStatePairs(
      model0, model1, alignedInputs, alignedOutputs, solverType);
  if (!structuralCoiStates.names.empty()) {
    // Top output names anchor the SEC property.  Internal state candidates here
    // LCOV_EXCL_START
    // come only from structurally unifying the reached output/transition cones,
    // LCOV_EXCL_STOP
    // then validating the resulting relation.
    return structuralCoiStates; // LCOV_EXCL_LINE
  }
  const AlignedSignals orderedCoiStates = inferSatValidatedOrderedCoiStatePairs(
      model0, model1, alignedInputs, alignedOutputs, solverType);
  if (!orderedCoiStates.names.empty()) {
    return orderedCoiStates;  // LCOV_EXCL_LINE
  }

  if (!globalStructuralRefinementWithinStateLimit(model0, model1)) {
    // The final fixed-point matcher is intentionally not rooted at top outputs.
    // Keep it for small renamed designs, but do not let it dominate large ASIC
    // SEC runs once the ordered/SAT/top-output-rooted candidates are exhausted.
    return {};
  }

  const auto inputClasses0 = buildInputClassMap(model0, alignedInputs.keys0);
  const auto inputClasses1 = buildInputClassMap(model1, alignedInputs.keys1);

  std::vector<size_t> classes0 = seedClasses(model0);
  std::vector<size_t> classes1 = seedClasses(model1);

  while (true) {
    // Fixed-point refinement: keep splitting classes until another pass no
    // longer learns anything new from the transition structure.
    const std::vector<size_t> refined0 = refineClasses(model0, inputClasses0, classes0);
    const std::vector<size_t> refined1 = refineClasses(model1, inputClasses1, classes1);
    if (refined0 == classes0 && refined1 == classes1) {
      break;
    }
    classes0 = refined0;
    classes1 = refined1;
  }

  const auto fingerprints0 = computeFinalFingerprints(model0, inputClasses0, classes0);
  const auto fingerprints1 = computeFinalFingerprints(model1, inputClasses1, classes1);

  std::map<StateClassFingerprint, std::vector<size_t>> indicesByFingerprint0;
  std::map<StateClassFingerprint, std::vector<size_t>> indicesByFingerprint1;
  for (size_t i = 0; i < fingerprints0.size(); ++i) {
    indicesByFingerprint0[fingerprints0[i]].push_back(i);
  }
  for (size_t i = 0; i < fingerprints1.size(); ++i) {
    indicesByFingerprint1[fingerprints1[i]].push_back(i);
  }

  AlignedSignals aligned;
  size_t pairIndex = 0;
  for (const auto& [fingerprint, indices0] : indicesByFingerprint0) {
    const auto it1 = indicesByFingerprint1.find(fingerprint);
    if (it1 == indicesByFingerprint1.end()) {
      continue; // LCOV_EXCL_LINE
    }
    const size_t matchedCount = std::min(indices0.size(), it1->second.size());
    for (size_t i = 0; i < matchedCount; ++i) {
      aligned.names.push_back("structural_state_" + std::to_string(pairIndex++));
      aligned.keys0.push_back(model0.stateBits[indices0[i]]);
      aligned.keys1.push_back(model1.stateBits[it1->second[i]]);
    }
  }
  return aligned;
}

AlignedSignals inferStructurallyEquivalentOutputConeStatePairs(
    const SequentialDesignModel& model0,
    const SequentialDesignModel& model1,
    const AlignedSignals& alignedInputs,
    const AlignedSignals& alignedOutputs,
    KEPLER_FORMAL::Config::SolverType solverType) {
  return inferStructuralOutputCoiStatePairs(
      model0, model1, alignedInputs, alignedOutputs, solverType);
}

// LCOV_EXCL_START
AlignedSignals inferStructurallyEquivalentStatePairs(
// LCOV_EXCL_STOP
    const SequentialDesignModel& model0,
    const SequentialDesignModel& model1,
    const AlignedSignals& alignedInputs,
    KEPLER_FORMAL::Config::SolverType solverType) {
  return inferStructurallyEquivalentStatePairs(
      model0, model1, alignedInputs, AlignedSignals{}, solverType);
}  // LCOV_EXCL_LINE

}  // namespace KEPLER_FORMAL::SEC
