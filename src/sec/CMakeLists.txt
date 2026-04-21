# Copyright 2024-2026 keplertech.io
# SPDX-License-Identifier: GPL-3.0-only

add_library(kepler_sec STATIC
    engine/ClassicKInductionEngine.cpp
    engine/ExactInterpolationEngine.cpp
    engine/IMCEngine.cpp
    engine/KInductionEngine.cpp
    engine/PDREngine.cpp
    common/BoolExprUtils.cpp
    model/SequentialDesignModel.cpp
    proof/ProofEngineShared.cpp
    kinduction/BaseCaseSolver.cpp
    kinduction/InductionStepSolver.cpp
    kinduction/SatEncoding.cpp
    strategy/ReachableStateInvariant.cpp
    strategy/StructuralStateInvariant.cpp
    strategy/SequentialEquivalenceStrategy.cpp
)

target_include_directories(kepler_sec PUBLIC ${CMAKE_CURRENT_SOURCE_DIR})
target_link_libraries(kepler_sec
    PUBLIC
      formal_strategies
      kepler_config
      formal_structures
      naja_dnl
      naja_nl
      kissat
)
