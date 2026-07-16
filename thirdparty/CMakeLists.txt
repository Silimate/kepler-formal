# Copyright 2024-2025 keplertech.io
# SPDX-License-Identifier: GPL-3.0-only

# Match the producer identity embedded by the pinned Naja PyPI wheels. Naja's
# default Git %h is repository-size dependent and changes between shallow and
# full-history checkouts, which makes otherwise identical snapshots unreadable.
set(NAJA_GIT_HASH "e1a649e")
set(_KEPLER_GIT_CONFIG_PARAMETERS_WAS_DEFINED FALSE)
if(DEFINED ENV{GIT_CONFIG_PARAMETERS})
  set(_KEPLER_GIT_CONFIG_PARAMETERS_WAS_DEFINED TRUE)
  set(_KEPLER_GIT_CONFIG_PARAMETERS "$ENV{GIT_CONFIG_PARAMETERS}")
  set(ENV{GIT_CONFIG_PARAMETERS}
      "$ENV{GIT_CONFIG_PARAMETERS} 'core.abbrev=7'")
else()
  set(ENV{GIT_CONFIG_PARAMETERS} "'core.abbrev=7'")
endif()
add_subdirectory(naja)
if(_KEPLER_GIT_CONFIG_PARAMETERS_WAS_DEFINED)
  set(ENV{GIT_CONFIG_PARAMETERS} "${_KEPLER_GIT_CONFIG_PARAMETERS}")
else()
  unset(ENV{GIT_CONFIG_PARAMETERS})
endif()
unset(_KEPLER_GIT_CONFIG_PARAMETERS)
unset(_KEPLER_GIT_CONFIG_PARAMETERS_WAS_DEFINED)
add_subdirectory(glucose)
add_subdirectory(yaml-cpp)
#add_subdirectory(kissat)
# cadical is built through the root ExternalProject because upstream does not
# provide a CMake subdirectory target.
#add_subdirectory(cpptrace EXCLUDE_FROM_ALL)
