// Copyright 2024-2026 keplertech.io
// SPDX-License-Identifier: GPL-3.0-only

#include "strategy/ReachableStateInvariant.h"

#include <algorithm>
#include <cctype>
#include <cstdio>
#include <optional>
#include <stdexcept>
#include <unordered_map>
#include <unordered_set>
#include <utility>

#include "common/BoolExprUtils.h"
#include "strategy/StructuralStateInvariant.h"

namespace KEPLER_FORMAL::SEC {

// Overall reachable-state strengthening algorithm:
// 1. Discover any reset inputs and explicit initial-state information.
// 2. Filter structural state pairs down to ones compatible with startup.
// 3. If reset/bootstrap is available, specialize next-state logic under reset.
// 4. Symbolically push known reset-state values forward for a few cycles.
// 5. Keep only the state equalities that survive each bootstrap step.
// 6. Return both the startup correspondence and the anchored equalities/value
//    facts that later proof engines can rely on.

namespace {

bool isConstBoolExpr(BoolExpr* expr, bool value) {
  return expr != nullptr && expr->getOp() == Op::VAR &&
         expr->getId() == static_cast<size_t>(value ? 1 : 0);
}

bool areSatEquivalentUnderAbstractMaps(
    BoolExpr* expr0,
    BoolExpr* expr1,
    const LocalToAbstractVarMap& abstractMap0,
    const LocalToAbstractVarMap& abstractMap1,
    KEPLER_FORMAL::Config::SolverType solverType) {
  try {
    std::unordered_map<BoolExpr*, BoolExpr*> memo0;
    std::unordered_map<BoolExpr*, BoolExpr*> memo1;
    BoolExpr* remapped0 = remapBoolExprVariables(expr0, abstractMap0, memo0);
    BoolExpr* remapped1 = remapBoolExprVariables(expr1, abstractMap1, memo1);
    return boolFormulaImplies(
        BoolExpr::createTrue(),
        makeEqualityExpr(remapped0, remapped1),
        solverType);
  } catch (const std::runtime_error&) {
    return false;
  }
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
  // Reset controls are identified from the aligned user-visible signal names
  // and then converted into the local BoolExpr variable IDs used by the model.
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

bool haveConflictingInitialValues(
    const SequentialDesignModel& model0,
    const SignalKey& key0,
    const SequentialDesignModel& model1,
    const SignalKey& key1) {
  const auto initial0 = model0.initialStateValueByKey.find(key0);
  const auto initial1 = model1.initialStateValueByKey.find(key1);
  return initial0 != model0.initialStateValueByKey.end() &&
         initial1 != model1.initialStateValueByKey.end() &&
         initial0->second != initial1->second;
}

std::unordered_map<std::string, std::vector<SignalKey>> groupStatesByDisplayName(
    const SequentialDesignModel& model) {
  std::unordered_map<std::string, std::vector<SignalKey>> statesByName;
  for (const auto& key : model.stateBits) {
    const auto displayIt = model.displayNameByKey.find(key);
    if (displayIt == model.displayNameByKey.end()) {
      continue;
    }
    statesByName[displayIt->second].push_back(key);
  }
  return statesByName;
}

void appendStatePairIfUnused(
    AlignedSignals& states,
    const std::string& name,
    const SignalKey& key0,
    const SignalKey& key1,
    std::unordered_set<SignalKey, SignalKeyHash>& usedKeys0,
    std::unordered_set<SignalKey, SignalKeyHash>& usedKeys1) {
  if (usedKeys0.find(key0) != usedKeys0.end() ||
      usedKeys1.find(key1) != usedKeys1.end()) {
    return;
  }

  states.names.push_back(name);
  states.keys0.push_back(key0);
  states.keys1.push_back(key1);
  usedKeys0.insert(key0);
  usedKeys1.insert(key1);
}

AlignedSignals alignSameNamedStatesByDisplayName(
    const SequentialDesignModel& model0,
    const SequentialDesignModel& model1,
    bool requireInitialCompatibility) {
  // Exact state display-name matches are useful SEC candidates after
  // optimization keeps register names but changes surrounding logic. Startup
  // assumptions must respect explicit init values; bootstrap candidates may be
  // reset-derived later even if explicit init values differ.
  const auto statesByName0 = groupStatesByDisplayName(model0);
  const auto statesByName1 = groupStatesByDisplayName(model1);

  AlignedSignals sameNamedStates;
  for (const auto& key0 : model0.stateBits) {
    const auto displayIt = model0.displayNameByKey.find(key0);
    if (displayIt == model0.displayNameByKey.end()) {
      continue;
    }

    const auto countIt0 = statesByName0.find(displayIt->second);
    const auto countIt1 = statesByName1.find(displayIt->second);
    if (countIt0 == statesByName0.end() || countIt0->second.size() != 1 ||
        countIt1 == statesByName1.end() || countIt1->second.size() != 1) {
      continue;
    }

    const auto& key1 = countIt1->second.front();
    if (requireInitialCompatibility &&
        haveConflictingInitialValues(model0, key0, model1, key1)) {
      continue;
    }

    sameNamedStates.names.push_back(displayIt->second);
    sameNamedStates.keys0.push_back(key0);
    sameNamedStates.keys1.push_back(key1);
  }
  return sameNamedStates;
}

AlignedSignals alignSameNamedStatesForStartup(
    const SequentialDesignModel& model0,
    const SequentialDesignModel& model1) {
  // Startup equalities are frame-0 assumptions, so they are allowed only when
  // explicit init information does not contradict the name-based pairing.
  return alignSameNamedStatesByDisplayName(
      model0, model1, /*requireInitialCompatibility=*/true);
}

AlignedSignals alignSameNamedStatesForBootstrapCandidates(
    const SequentialDesignModel& model0,
    const SequentialDesignModel& model1) {
  // Reset/bootstrap can later prove a pair equal even if frame-0 explicit init
  // values disagree, so candidate collection itself does not reject those pairs.
  return alignSameNamedStatesByDisplayName(
      model0, model1, /*requireInitialCompatibility=*/false);
}

AlignedSignals mergeStartupCorrespondence(
    const AlignedSignals& structuralStates,
    const AlignedSignals& sameNamedStates) {
  AlignedSignals mergedStates;
  std::unordered_set<SignalKey, SignalKeyHash> usedKeys0;
  std::unordered_set<SignalKey, SignalKeyHash> usedKeys1;
  for (size_t i = 0; i < structuralStates.names.size(); ++i) {
    appendStatePairIfUnused(
        mergedStates,
        structuralStates.names[i],
        structuralStates.keys0[i],
        structuralStates.keys1[i],
        usedKeys0,
        usedKeys1);
  }
  for (size_t i = 0; i < sameNamedStates.names.size(); ++i) {
    appendStatePairIfUnused(
        mergedStates,
        sameNamedStates.names[i],
        sameNamedStates.keys0[i],
        sameNamedStates.keys1[i],
        usedKeys0,
        usedKeys1);
  }
  return mergedStates;
}

AlignedSignals keepEqualitiesWithStateVariables(
    const SequentialDesignModel& model0,
    const SequentialDesignModel& model1,
    const AlignedSignals& states) {
  AlignedSignals filteredStates;
  for (size_t i = 0; i < states.names.size(); ++i) {
    if (model0.inputVarByKey.find(states.keys0[i]) == model0.inputVarByKey.end() ||
        model1.inputVarByKey.find(states.keys1[i]) == model1.inputVarByKey.end()) {
      continue;
    }
    filteredStates.names.push_back(states.names[i]);
    filteredStates.keys0.push_back(states.keys0[i]);
    filteredStates.keys1.push_back(states.keys1[i]);
  }
  return filteredStates;
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
    if (haveConflictingInitialValues(
            model0, candidateStates.keys0[i], model1, candidateStates.keys1[i])) {
      continue;
    }

    compatibleStates.names.push_back(candidateStates.names[i]);
    compatibleStates.keys0.push_back(candidateStates.keys0[i]);
    compatibleStates.keys1.push_back(candidateStates.keys1[i]);
  }
  return compatibleStates;
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
          evaluateConstantUnderAssignments(expr->getLeft(), assignments, memo);  // LCOV_EXCL_LINE
      const auto rhs =
          evaluateConstantUnderAssignments(expr->getRight(), assignments, memo);  // LCOV_EXCL_LINE
      if (lhs.has_value() && rhs.has_value()) {  // LCOV_EXCL_LINE
        value = *lhs != *rhs;  // LCOV_EXCL_LINE
      }  // LCOV_EXCL_LINE
      break;  // LCOV_EXCL_LINE
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
  // This is a small symbolic reset simulation. We keep only states whose value
  // becomes constant under the asserted-reset environment.
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
    const AlignedSignals& startupEqualities,
    size_t cycles,
    KEPLER_FORMAL::Config::SolverType solverType,
    bool secDiagEnabled) {
  // Push candidate state equalities through the reset-specialized next-state
  // logic. A pair survives only if both sides either collapse to the same
  // constant or stay structurally equivalent after each bootstrap step.
  if (cycles == 0 || candidateStates.names.empty()) {
    return filterStateEqualitiesByInitialValue(model0, model1, candidateStates);
  }

  const auto resetAssignments0 = collectResetAssignments(model0);
  const auto resetAssignments1 = collectResetAssignments(model1);
  if (resetAssignments0.empty() || resetAssignments1.empty()) {
    return filterStateEqualitiesByInitialValue(model0, model1, candidateStates);  // LCOV_EXCL_LINE
  }

  auto specializeForReset = [](const SequentialDesignModel& model,
                               const std::unordered_map<size_t, bool>& resetAssignments) {
    std::unordered_map<SignalKey, BoolExpr*, SignalKeyHash> specialized;
    specialized.reserve(model.stateBits.size());
    std::unordered_map<BoolExpr*, BoolExpr*> memo;
    for (const auto& key : model.stateBits) {
      const auto nextIt = model.nextStateExprByStateKey.find(key);
      if (nextIt == model.nextStateExprByStateKey.end()) {
        specialized.emplace(key, nullptr);
        continue;
      }
      try {
        specialized.emplace(
            key,
            substituteBoolExprVariables(nextIt->second, resetAssignments, memo));
      } catch (const std::runtime_error&) {
        specialized.emplace(key, nullptr);
      }
    }
    return specialized;
  };

  const auto resetSpecializedNext0 = specializeForReset(model0, resetAssignments0);
  const auto resetSpecializedNext1 = specializeForReset(model1, resetAssignments1);

  AlignedSignals currentEqualities = mergeStartupCorrespondence(
      filterStateEqualitiesByInitialValue(model0, model1, candidateStates),
      startupEqualities);
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
      try {
        specializedNext0.emplace(
            key,
            substituteBoolExprVariables(
                resetSpecializedNext0.at(key), stateAssignments0, stateSubMemo0));
      } catch (const std::runtime_error&) {  // LCOV_EXCL_LINE
        specializedNext0.emplace(key, nullptr);  // LCOV_EXCL_LINE
      }  // LCOV_EXCL_LINE
    }
    for (const auto& key : model1.stateBits) {
      try {
        specializedNext1.emplace(
            key,
            substituteBoolExprVariables(
                resetSpecializedNext1.at(key), stateAssignments1, stateSubMemo1));
      } catch (const std::runtime_error&) {  // LCOV_EXCL_LINE
        specializedNext1.emplace(key, nullptr);  // LCOV_EXCL_LINE
      }  // LCOV_EXCL_LINE
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

    bool abstractMapsBuilt = false;
    bool abstractMapsAvailable = true;
    LocalToAbstractVarMap abstractMap0;
    LocalToAbstractVarMap abstractMap1;
    size_t satRecoveredEqualities = 0;
    auto ensureAbstractMaps = [&]() {
      if (abstractMapsBuilt) {
        return abstractMapsAvailable;
      }
      abstractMapsBuilt = true;
      const auto mappedCurrentEqualities =
          keepEqualitiesWithStateVariables(model0, model1, currentEqualities);
      try {
        auto maps = buildAbstractTransitionMaps(
            model0, model1, alignedInputs, mappedCurrentEqualities);
        abstractMap0 = std::move(maps.first);
        abstractMap1 = std::move(maps.second);
      } catch (const std::out_of_range&) {
        abstractMapsAvailable = false;
      }
      return abstractMapsAvailable;
    };

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
      } else if (specializedNext0.at(key0) == nullptr ||
                 specializedNext1.at(key1) == nullptr) {
        equalAfterStep = false;
      } else if (!ensureAbstractMaps()) {
        equalAfterStep = false;
      } else {
        equalAfterStep = areEquivalentUnderAbstractMaps(
            specializedNext0.at(key0),
            specializedNext1.at(key1),
            abstractMap0,
            abstractMap1);
        if (!equalAfterStep) {
          equalAfterStep = areSatEquivalentUnderAbstractMaps(
              specializedNext0.at(key0),
              specializedNext1.at(key1),
              abstractMap0,
              abstractMap1,
              solverType);
          if (equalAfterStep) {
            ++satRecoveredEqualities;
          }
        }
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
      if (satRecoveredEqualities != 0) {
        fprintf(
            stderr,
            "SEC diag: bootstrap step %zu sat_recovered_equalities=%zu\n",
            step + 1,
            satRecoveredEqualities);
      }
      fflush(stderr);
    }
  }

  return currentEqualities;
}

bool hasCompleteInitialState(const SequentialDesignModel& model0,
                             const SequentialDesignModel& model1) {
  return model0.initialStateValueByKey.size() == model0.stateBits.size() &&
         model1.initialStateValueByKey.size() == model1.stateBits.size();
}

bool hasExplicitInitialState(const SequentialDesignModel& model0,
                             const SequentialDesignModel& model1) {
  return !model0.initialStateValueByKey.empty() ||
         !model1.initialStateValueByKey.empty();
}

}  // namespace

ReachableStateInvariant buildReachableStateInvariant(
    const SequentialDesignModel& model0,
    const SequentialDesignModel& model1,
    const AlignedSignals& alignedInputs,
    const AlignedSignals& inductiveStateEqualities,
    bool secDiagEnabled,
    KEPLER_FORMAL::Config::SolverType solverType) {
  ReachableStateInvariant invariant;
  // First decide which startup model we have: explicit init, reset bootstrap,
  // both, or neither. That determines how strong the frame-0 correspondence
  // may safely be.
  const bool hasResetBootstrap = !collectResetAssignments(model0).empty() &&
      !collectResetAssignments(model1).empty();

  invariant.bootstrapCycles = defaultResetBootstrapCycles(
      hasResetBootstrap, hasCompleteInitialState(model0, model1));
  const auto structuralStartupCorrespondence = filterStateEqualitiesByInitialCompatibility(
      model0, model1, inductiveStateEqualities);
  invariant.initialStateCorrespondence = mergeStartupCorrespondence(
      structuralStartupCorrespondence,
      alignSameNamedStatesForStartup(model0, model1));

  if (hasResetBootstrap) {
    // Walk the reset window to find which candidate equalities are true at the
    // first checked frame. The seed includes startup equalities, but a pair is
    // promoted only if reset-specialized transition logic proves it survives.
    if (invariant.bootstrapCycles == 0) {
      invariant.anchoredStateEqualities = structuralStartupCorrespondence;
    } else {
      const auto bootstrapCandidateStates = mergeStartupCorrespondence(
          inductiveStateEqualities,
          alignSameNamedStatesForBootstrapCandidates(model0, model1));
      invariant.anchoredStateEqualities = deriveResetBootstrapStateEqualities(
          model0,
          model1,
          alignedInputs,
          bootstrapCandidateStates,
          invariant.initialStateCorrespondence,
          invariant.bootstrapCycles,
          solverType,
          secDiagEnabled);
    }

    invariant.bootstrapValues0 =
        deriveResetBootstrapStateValues(model0, invariant.bootstrapCycles);
    invariant.bootstrapValues1 =
        deriveResetBootstrapStateValues(model1, invariant.bootstrapCycles);
  } else if (hasExplicitInitialState(model0, model1)) {
    // Without reset, we can only anchor the state pairs whose explicit init
    // values agree on both sides.
    invariant.anchoredStateEqualities = filterStateEqualitiesByInitialValue(
        model0, model1, inductiveStateEqualities);
  }

  return invariant;
}

}  // namespace KEPLER_FORMAL::SEC
