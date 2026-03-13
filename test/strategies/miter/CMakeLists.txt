# Copyright 2024-2025 keplertech.io
# SPDX-License-Identifier: GPL-3.0-only

include(GoogleTest)

cmake_minimum_required(VERSION 3.10)
project(MiterTests)

# Enable testing
enable_testing()

# Google Test setup
find_package(GTest REQUIRED)
include_directories(${GTEST_INCLUDE_DIRS})

# Add main and test files
add_executable(miterTests MiterTests.cpp)

target_link_libraries(miterTests
    kepler_config
    naja_nl
    ${GTEST_LIBRARIES}
    naja_opt
    naja_snl_visual
    kepler_clauses          # 👈 place first
    formal_strategies       # 👈 after its dependencies
    formal_structures
    naja_dnl
    pthread
    naja_snl_pyloader
)

GTEST_DISCOVER_TESTS(miterTests)

add_executable(keplerFormalCliTests
    KeplerFormalCliTests.cpp
    ${CMAKE_SOURCE_DIR}/src/bin/KeplerFormal.cpp
)

target_compile_definitions(keplerFormalCliTests PRIVATE KEPLER_FORMAL_NO_MAIN KEPLER_FORMAL_TESTING)
target_include_directories(keplerFormalCliTests PRIVATE ${CMAKE_SOURCE_DIR}/src/bin)

target_link_libraries(keplerFormalCliTests
    kepler_config
    naja_snl_pyloader
    naja_dnl
    naja_opt
    kissat
    formal_strategies
    scope_extraction
    yaml-cpp
    ${SPDLOG_TARGET}
    pthread
)

if (TARGET GTest::gtest_main)
    target_link_libraries(keplerFormalCliTests GTest::gtest_main)
elseif (DEFINED GTEST_MAIN_LIBRARIES)
    target_link_libraries(keplerFormalCliTests ${GTEST_MAIN_LIBRARIES})
else()
    target_link_libraries(keplerFormalCliTests ${GTEST_LIBRARIES})
endif()

GTEST_DISCOVER_TESTS(keplerFormalCliTests)
