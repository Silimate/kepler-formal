// Copyright 2024-2026 keplertech.io
// SPDX-License-Identifier: GPL-3.0-only

#include "strategy/StructuralStateInvariant.h"

#include <algorithm>
#include <cstdint>
#include <limits>
#include <map>
#include <memory_resource>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

#include "BoolExpr.h"

namespace KEPLER_FORMAL::SEC {

// Overall structural-state matching algorithm:
// 1. Put aligned SEC inputs into a shared abstract symbol space.
// 2. Seed each state bit with coarse classes from init/complement information.
// 3. Repeatedly fingerprint next-state functions under the current classes.
// 4. Refine those classes to a fixed point.
// 5. Pair states whose final structural fingerprints match across the designs.
// 6. Use an ordered fast path only when every state already matches in order.

namespace {

using KEPLER_FORMAL::BoolExpr;
using FingerprintMemo = std::pmr::unordered_map<BoolExpr*, uint64_t>;

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
    return {};
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

bool areAllOrderedStatesEquivalent(const SequentialDesignModel& model0,
                                   const SequentialDesignModel& model1,
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
      return false;
    }
  }
  return true;
}

std::unordered_map<SignalKey, size_t, SignalKeyHash> buildStateIndexMap(
    const std::vector<SignalKey>& stateBits) {
  std::unordered_map<SignalKey, size_t, SignalKeyHash> indices;
  indices.reserve(stateBits.size());
  for (size_t i = 0; i < stateBits.size(); ++i) {
    indices.emplace(stateBits[i], i);
  }
  return indices;
}

std::unordered_map<size_t, size_t> buildInputClassMap(
    const SequentialDesignModel& model,
    const std::vector<SignalKey>& alignedInputKeys) {
  std::unordered_map<size_t, size_t> classes;
  classes.reserve(alignedInputKeys.size());
  for (size_t i = 0; i < alignedInputKeys.size(); ++i) {
    classes.emplace(model.inputVarByKey.at(alignedInputKeys[i]), i);
  }
  return classes;
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
    hash = mixHash(hash ^ mixHash(part));
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

void reserveFingerprintMemo(FingerprintMemo& memo,
                            size_t& reservedEntries,
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
    return it->second;
  }

  struct StackFrame {
    BoolExpr* node = nullptr;
    bool visited = false;
  };

  // Structural matching sees very deep, hash-consed gate-level DAGs on large
  // ASICs. A recursive fingerprint is easy to read, but it repeatedly burned
  // CPU and stack in BlackParrot before the actual SEC engine started. This is
  // the same post-order computation, just explicit and memoized across all
  // state bits in the current refinement pass.
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
        fingerprint = combineHashes({13, inputIt->second});
      } else if (const auto stateIt = stateClasses.find(node->getId());
                 stateIt != stateClasses.end()) {
        fingerprint = combineHashes({17, stateIt->second});
      } else {
        fingerprint = 19;
      }
      cacheFingerprint(memo, memoReservedEntries, node, fingerprint);
      continue;
    }

    if (node->getOp() == Op::NONE) {
      cacheFingerprint(memo, memoReservedEntries, node, 41);
      continue;
    }

    if (!current.visited) {
      stack.push_back({node, true});
      if (node->getRight() != nullptr &&
          memo.find(node->getRight()) == memo.end()) {
        stack.push_back({node->getRight(), false});
      }
      if (node->getLeft() != nullptr &&
          memo.find(node->getLeft()) == memo.end()) {
        stack.push_back({node->getLeft(), false});
      }
      continue;
    }

    uint64_t fingerprint = 0;
    switch (node->getOp()) {
      case Op::NOT:
        fingerprint = combineHashes({23, memo.at(node->getLeft())});
        break;
      case Op::AND:
      case Op::OR:
      case Op::XOR: {
        uint64_t lhs = memo.at(node->getLeft());
        uint64_t rhs = memo.at(node->getRight());
        if (lhs > rhs) {
          std::swap(lhs, rhs);
        }
        const uint64_t opTag =
            node->getOp() == Op::AND ? 29 : (node->getOp() == Op::OR ? 31 : 37);
        fingerprint = combineHashes({opTag, lhs, rhs});
        break;
      }
      case Op::VAR:
      case Op::NONE:  // LCOV_EXCL_LINE
      default:
        throw std::runtime_error("Unsupported BoolExpr operator in fingerprint");  // LCOV_EXCL_LINE
    }
    cacheFingerprint(memo, memoReservedEntries, node, fingerprint);
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

std::string stateFingerprintKey(const StateClassFingerprint& fingerprint) {
  return std::to_string(fingerprint.seedSignature) + ":" +
      std::to_string(fingerprint.transitionFingerprint);
}  // LCOV_EXCL_LINE

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
    cacheAbstractEquivalence(memo, key, leftEquivalent && rightEquivalent);
  }

  return memo.at(std::make_pair(expr0, expr1));
}

AlignedSignals inferStructurallyEquivalentStatePairs(
    const SequentialDesignModel& model0,
    const SequentialDesignModel& model1,
    const AlignedSignals& alignedInputs) {
  if (model0.stateBits.empty() || model1.stateBits.empty()) {
    return {};
  }

  const AlignedSignals orderedStates = buildOrderedStatePairs(model0, model1);
  if (!orderedStates.names.empty() &&
      areAllOrderedStatesEquivalent(model0, model1, alignedInputs, orderedStates)) {
    // This fast path is purely structural: same order, same transition shape.
    return orderedStates;
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

  std::map<std::string, std::vector<size_t>> indicesByFingerprint0;
  std::map<std::string, std::vector<size_t>> indicesByFingerprint1;
  for (size_t i = 0; i < fingerprints0.size(); ++i) {
    indicesByFingerprint0[stateFingerprintKey(fingerprints0[i])].push_back(i);
  }
  for (size_t i = 0; i < fingerprints1.size(); ++i) {
    indicesByFingerprint1[stateFingerprintKey(fingerprints1[i])].push_back(i);
  }

  AlignedSignals aligned;
  size_t pairIndex = 0;
  for (const auto& [fingerprint, indices0] : indicesByFingerprint0) {
    const auto it1 = indicesByFingerprint1.find(fingerprint);
    if (it1 == indicesByFingerprint1.end()) {
      continue;
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

}  // namespace KEPLER_FORMAL::SEC
