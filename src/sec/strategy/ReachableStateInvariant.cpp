// Copyright 2024-2026 keplertech.io
// SPDX-License-Identifier: GPL-3.0-only

#include "strategy/ReachableStateInvariant.h"

#include <algorithm>
#include <cctype>
#include <cstdint>
#include <memory_resource>
#include <optional>
#include <unordered_map>
#include <vector>

namespace KEPLER_FORMAL::SEC {

namespace {

using ConstantEvalMemo =
    std::pmr::unordered_map<BoolExpr*, std::optional<bool>>;

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

bool isResetNameToken(const std::string& candidate, const std::string& token) {
  // Domain-prefixed top resets, for example `wb_rst_i`, normalize to `WB_RST`
  // after input-suffix stripping.  Match only a final underscore-separated
  // reset token so prefixes do not block reachable-state reset bootstrap.
  return candidate == token || hasSuffix(candidate, "_" + token);
}

bool isActiveLowResetToken(const std::string& candidate) {
  return candidate == "RESET_N" || candidate == "RESETN" ||
         candidate == "RESET_L" || candidate == "RST_N" ||
         candidate == "RSTN" || candidate == "RST_L";
}

void appendDomainPrefixedActiveLowResetCandidates(
    std::vector<std::string>& candidates) {
  const size_t originalSize = candidates.size();
  for (size_t index = 0; index < originalSize; ++index) {
    const std::string& candidate = candidates[index];
    if (candidate.size() <= 1) {
      continue;
    }
    const std::string strippedDomain = candidate.substr(1);
    if (isActiveLowResetToken(strippedDomain)) {
      // Async FIFOs often spell read/write resets as rrst_n/wrst_n.  Keep the
      // rule active-low and one-letter-prefixed to avoid broad reset matching.
      candidates.push_back(strippedDomain);
    }
  }
}

std::vector<std::string> resetNameCandidates(const std::string& displayName) {
  // Reset ports frequently carry RTL direction suffixes (`reset_i`, `rst_ni`).
  // Strip only those common input suffixes before classification so a real
  // reset is bootstrapped, without broadening the matcher to arbitrary names.
  const std::string normalized = normalizeSignalBaseName(displayName);
  std::vector<std::string> candidates = {normalized};
  if (hasSuffix(normalized, "_IN")) {
    candidates.push_back(normalized.substr(0, normalized.size() - 3));
  }
  if (hasSuffix(normalized, "_I")) {
    candidates.push_back(normalized.substr(0, normalized.size() - 2));
  }
  if (hasSuffix(normalized, "_NI")) {
    candidates.push_back(normalized.substr(0, normalized.size() - 1));
  }
  appendDomainPrefixedActiveLowResetCandidates(candidates);
  return candidates;
}

std::optional<bool> getResetAssertionValue(const std::string& displayName) {
  for (const auto& candidate : resetNameCandidates(displayName)) {
    if (isResetNameToken(candidate, "RESET") ||
        isResetNameToken(candidate, "RST")) {
      return true;
    }
    if (isResetNameToken(candidate, "RESET_N") ||
        isResetNameToken(candidate, "RESETN") ||
        isResetNameToken(candidate, "RESET_L") ||
        isResetNameToken(candidate, "RST_N") ||
        isResetNameToken(candidate, "RSTN") ||
        isResetNameToken(candidate, "RST_L")) {
      return false;
    }
  }
  return std::nullopt;
}

std::unordered_map<size_t, bool> collectResetAssignments(
    const SequentialDesignModel& model) {
  // Reset controls are identified from the design's own user-visible input
  // names and converted into that design's local BoolExpr variable IDs.
  std::unordered_map<size_t, bool> assignments;
  for (const auto& key : model.environmentInputs) {
    const auto displayIt = model.displayNameByKey.find(key);
    const auto varIt = model.inputVarByKey.find(key);
    if (displayIt == model.displayNameByKey.end() ||
        varIt == model.inputVarByKey.end()) {
      continue;
    }
    const auto assertedValue = getResetAssertionValue(displayIt->second);
    if (assertedValue.has_value()) {
      assignments.emplace(varIt->second, *assertedValue);
    }
  }
  return assignments;
}

size_t defaultResetBootstrapCycles(bool hasResetBootstrap,
                                   bool hasCompleteInitialState) {
  return (hasResetBootstrap && !hasCompleteInitialState) ? 3u : 0u;
}

std::optional<bool> evaluateConstantUnderAssignments(
    BoolExpr* expr,
    const std::unordered_map<size_t, bool>& assignments,
    ConstantEvalMemo& memo) {
  if (expr == nullptr) {
    return std::nullopt;
  }
  if (const auto it = memo.find(expr); it != memo.end()) {
    return it->second;
  }

  struct EvalFrame {
    BoolExpr* node = nullptr;
    uint8_t stage = 0;
  };

  auto childValue = [&](BoolExpr* child) -> std::optional<bool> {
    if (child == nullptr) {
      return std::nullopt;
    }
    if (const auto it = memo.find(child); it != memo.end()) {
      return it->second;
    }
    return std::nullopt;
  };

  // Reset bootstrap evaluates large shared next-state DAGs.  Use an explicit
  // stack so one local constant sweep does not risk recursive stack growth
  // before the real proof engine starts.
  std::vector<EvalFrame> stack{{expr, 0}};
  while (!stack.empty()) {
    EvalFrame& frame = stack.back();
    BoolExpr* node = frame.node;
    if (node == nullptr || memo.find(node) != memo.end()) {
      stack.pop_back();
      continue;
    }

    switch (node->getOp()) {
      case Op::VAR: {
        std::optional<bool> value;
        if (node->getId() < 2) {
          value = node->getId() == 1;
        } else if (const auto it = assignments.find(node->getId());
                   it != assignments.end()) {
          value = it->second;
        }
        memo.emplace(node, value);
        stack.pop_back();
        break;
      }
      case Op::NOT:
        if (frame.stage == 0) {
          frame.stage = 1;
          if (node->getLeft() != nullptr &&
              memo.find(node->getLeft()) == memo.end()) {
            stack.push_back({node->getLeft(), 0});
          }
          break;
        }
        if (const auto operand = childValue(node->getLeft());
            operand.has_value()) {
          memo.emplace(node, !*operand);
        } else {
          memo.emplace(node, std::nullopt);
        }
        stack.pop_back();
        break;
      case Op::AND:
        if (frame.stage == 0) {
          frame.stage = 1;
          if (node->getLeft() != nullptr &&
              memo.find(node->getLeft()) == memo.end()) {
            stack.push_back({node->getLeft(), 0});
          }
          break;
        }
        if (frame.stage == 1) {
          const auto lhs = childValue(node->getLeft());
          if (lhs.has_value() && !*lhs) {
            memo.emplace(node, false);
            stack.pop_back();
            break;
          }
          frame.stage = 2;
          if (node->getRight() != nullptr &&
              memo.find(node->getRight()) == memo.end()) {
            stack.push_back({node->getRight(), 0});
          }
          break;
        }
        {
          const auto lhs = childValue(node->getLeft());
          const auto rhs = childValue(node->getRight());
          if (rhs.has_value() && !*rhs) {
            memo.emplace(node, false);
          } else if (lhs.has_value() && rhs.has_value()) {
            memo.emplace(node, *lhs && *rhs);
          } else {
            memo.emplace(node, std::nullopt);
          }
          stack.pop_back();
        }
        break;
      case Op::OR:
        if (frame.stage == 0) {
          frame.stage = 1;
          if (node->getLeft() != nullptr &&
              memo.find(node->getLeft()) == memo.end()) {
            stack.push_back({node->getLeft(), 0});
          }
          break;
        }
        if (frame.stage == 1) {
          const auto lhs = childValue(node->getLeft());
          if (lhs.has_value() && *lhs) {
            memo.emplace(node, true);
            stack.pop_back();
            break;
          }
          frame.stage = 2;
          if (node->getRight() != nullptr &&
              memo.find(node->getRight()) == memo.end()) {
            stack.push_back({node->getRight(), 0});
          }
          break;
        }
        {
          const auto lhs = childValue(node->getLeft());
          const auto rhs = childValue(node->getRight());
          if (rhs.has_value() && *rhs) {
            memo.emplace(node, true);
          } else if (lhs.has_value() && rhs.has_value()) {
            memo.emplace(node, *lhs || *rhs);
          } else {
            memo.emplace(node, std::nullopt);
          }
          stack.pop_back();
        }
        break;
      case Op::XOR:
        if (frame.stage == 0) {
          frame.stage = 1;
          if (node->getLeft() != nullptr &&
              memo.find(node->getLeft()) == memo.end()) {
            stack.push_back({node->getLeft(), 0});
          }
          break;
        }
        if (frame.stage == 1) {
          frame.stage = 2;
          if (node->getRight() != nullptr &&
              memo.find(node->getRight()) == memo.end()) {
            stack.push_back({node->getRight(), 0});
          }
          break;
        }
        {
          const auto lhs = childValue(node->getLeft());
          const auto rhs = childValue(node->getRight());
          if (lhs.has_value() && rhs.has_value()) {
            memo.emplace(node, *lhs != *rhs);
          } else {
            memo.emplace(node, std::nullopt);
          }
          stack.pop_back();
        }
        break;
      case Op::NONE:
      default:
        memo.emplace(node, std::nullopt);
        stack.pop_back();
        break;
    }
  }

  return memo.at(expr);
}

std::unordered_map<SignalKey, bool, SignalKeyHash> deriveResetBootstrapStateValues(
    const SequentialDesignModel& model,
    size_t cycles) {
  // This is a design-local symbolic reset simulation.  It derives only
  // concrete values inside one design, never equality to the other design.
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
    std::pmr::monotonic_buffer_resource memoResource;
    ConstantEvalMemo memo{&memoResource};
    memo.reserve(std::min<size_t>(model.stateBits.size() * 4, 1'000'000));
    for (const auto& key : model.stateBits) {
      const auto nextIt = model.nextStateExprByStateKey.find(key);
      if (nextIt == model.nextStateExprByStateKey.end()) {
        continue;
      }
      const auto value =
          evaluateConstantUnderAssignments(nextIt->second, assignments, memo);
      if (value.has_value()) {
        nextKnownStates.emplace(key, *value);
      }
    }
    knownStates = std::move(nextKnownStates);
  }

  return knownStates;
}

bool hasCompleteInitialState(const SequentialDesignModel& model0,
                             const SequentialDesignModel& model1) {
  return model0.initialStateValueByKey.size() == model0.stateBits.size() &&
         model1.initialStateValueByKey.size() == model1.stateBits.size();
}

}  // namespace

ReachableStateInvariant buildReachableStateInvariant(
    const SequentialDesignModel& model0,
    const SequentialDesignModel& model1,
    bool deriveResetBootstrapStrengthening) {
  ReachableStateInvariant invariant;
  const bool hasResetBootstrap = !collectResetAssignments(model0).empty() &&
                                 !collectResetAssignments(model1).empty();

  invariant.bootstrapCycles = defaultResetBootstrapCycles(
      hasResetBootstrap, hasCompleteInitialState(model0, model1));

  if (hasResetBootstrap && deriveResetBootstrapStrengthening) {
    invariant.bootstrapValues0 =
        deriveResetBootstrapStateValues(model0, invariant.bootstrapCycles);
    invariant.bootstrapValues1 =
        deriveResetBootstrapStateValues(model1, invariant.bootstrapCycles);
  }

  return invariant;
}

}  // namespace KEPLER_FORMAL::SEC
