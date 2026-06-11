// Copyright 2024-2026 keplertech.io
// SPDX-License-Identifier: GPL-3.0-only

#pragma once

#include <cstdlib>
#include <sstream>
#include <string>
#include <utility>
#include <unistd.h>

namespace KEPLER_FORMAL::SEC {

inline bool isSecDiagEnabled() {
  return std::getenv("KEPLER_SEC_DIAG") != nullptr;
}

inline bool isSecDiagOutputEnabled() {
  // Keep normal SEC runs stderr-clean: wrappers such as Tcl exec can treat any
  // raw stderr as failure even when Kepler exits successfully.
  return isSecDiagEnabled() ||
         std::getenv("KEPLER_SEC_KI_DIAG") != nullptr ||
         std::getenv("KEPLER_SEC_KI_COI_DIAG") != nullptr ||
         std::getenv("KEPLER_SEC_PDR_RESET_SHORTCUT_DIAG") != nullptr ||
         std::getenv("KEPLER_SEC_PDR_STATS") != nullptr ||
         std::getenv("KEPLER_SEC_PDR_TRACE") != nullptr ||
         std::getenv("KEPLER_SEC_SUMMARY_STATS") != nullptr;
}

inline void appendSecDiagPart(std::ostringstream& stream, const char* value) {
  stream << (value != nullptr ? value : "<null>");
}

inline void appendSecDiagPart(std::ostringstream& stream, char* value) {
  stream << (value != nullptr ? value : "<null>");
}

// Diagnostic formatting templates instantiate many one-off call shapes from
// optional debug paths; line coverage is tracked at the call sites instead.
// LCOV_EXCL_START
template <typename T>
inline void appendSecDiagPart(std::ostringstream& stream, T&& value) {
  stream << std::forward<T>(value);
}

template <typename... Args>
inline void emitSecDiag(Args&&... args) {
  if (!isSecDiagOutputEnabled()) {
    return;
  }
  std::ostringstream stream;
  (appendSecDiagPart(stream, std::forward<Args>(args)), ...);
  stream << '\n';
  const std::string message = stream.str();
  const char* data = message.data();
  size_t remaining = message.size();
  while (remaining > 0) {
    const ssize_t written = ::write(STDERR_FILENO, data, remaining);
    if (written <= 0) {
      break;  // LCOV_EXCL_LINE
    }
    data += written;
    remaining -= static_cast<size_t>(written);
  }
}
// LCOV_EXCL_STOP

}  // namespace KEPLER_FORMAL::SEC
