# Copyright 2024-2026 keplertech.io
# SPDX-License-Identifier: GPL-3.0-only

add_executable(secStrategyTests SequentialEquivalenceStrategyTests.cpp)
set_target_properties(secStrategyTests PROPERTIES INTERPROCEDURAL_OPTIMIZATION FALSE)
target_compile_options(secStrategyTests PRIVATE -fno-lto)
target_link_options(secStrategyTests PRIVATE -fno-lto)

target_link_libraries(secStrategyTests
    kepler_config
    kepler_sec
    formal_strategies
    naja_nl
    naja_snl_liberty
    naja_snl_systemverilog
    ${GTEST_LIBRARIES}
    gmock
    gtest_main
)

GTEST_DISCOVER_TESTS(secStrategyTests)
