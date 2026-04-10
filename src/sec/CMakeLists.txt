# Copyright 2024-2026 keplertech.io
# SPDX-License-Identifier: GPL-3.0-only

add_library(kepler_sec STATIC
    common/BoolExprUtils.cpp
    model/SequentialDesignModel.cpp
    kinduction/SatEncoding.cpp
    kinduction/KInductionEngine.cpp
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
