# Copyright 2024-2026 keplertech.io
# SPDX-License-Identifier: GPL-3.0-only

add_library(kepler_clocks STATIC
    SecClockModel.cpp
)

target_include_directories(kepler_clocks
    PUBLIC
      ${CMAKE_CURRENT_SOURCE_DIR}/..
      ${CMAKE_CURRENT_SOURCE_DIR}/../formal
      ${CMAKE_CURRENT_SOURCE_DIR}/../sec
      /opt/homebrew/include
)

target_link_libraries(kepler_clocks
    PUBLIC
      formal_strategies
      formal_structures
)
