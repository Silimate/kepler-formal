// Copyright 2024-2026 keplertech.io
// SPDX-License-Identifier: GPL-3.0-only

#pragma once

#include <filesystem>
#include <string>
#include <vector>

#include "strategy/SequentialEquivalenceStrategy.h"

// Shared helper for consistent filename handling.
std::string sanitizeFileToken(const std::string& input);

void writeBoundaryTermsReport(
    const std::filesystem::path& reportPath,
    const std::vector<KEPLER_FORMAL::SEC::ExtractedBoundaryReportEntry>& reports);
