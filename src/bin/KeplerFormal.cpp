// Copyright 2024-2026 keplertech.io
// SPDX-License-Identifier: GPL-3.0-only

#include <chrono>
#include <cstdlib>
#include <string>
#include <vector>
#include <iostream>
#include <optional>
#include <cctype>
#include <unordered_set>

#include <spdlog/spdlog.h>
#include <spdlog/sinks/stdout_color_sinks.h>

#include <yaml-cpp/yaml.h>

#include "NajaPerf.h"

// Naja interfaces
#include "DNL.h"
#include "MiterStrategy.h"
#include "SNLCapnP.h"
#include "SNLLibertyConstructor.h"
#include "SNLVRLConstructor.h"
#include "SNLVRLDumper.h"
#include "SNLUtils.h"
#include "ScopeExtraction.h"
#include "Config.h"

static void print_usage(const char* prog) {
  SPDLOG_INFO(
      "Usage: {} [--config <file>] | <-naja_if/-verilog> <netlist1> <netlist2> "
      "[<liberty-file>...]",
      prog);
}

static std::vector<std::string> yamlToVector(const YAML::Node& node) {
  std::vector<std::string> out;
  if (!node) return out;
  if (!node.IsSequence()) return out;
  for (const auto& n : node) {
    if (n.IsScalar()) out.emplace_back(n.as<std::string>());
  }
  return out;
}

static bool validateConfigKeys(const YAML::Node& cfg) {
  if (!cfg || !cfg.IsMap()) {
    return true;
  }
  static const std::unordered_set<std::string> kAllowedKeys = {
      "format",
      "input_paths",
      "liberty_files",
      "log_level",
      "log_file",
      "use_scopes",
      "clean_scopes",
      "cnf_export",
      "cnf_export_path",
      "dump_cnf",
      "dump_cnf_path",
      "solver",
  };

  for (auto it = cfg.begin(); it != cfg.end(); ++it) {
    if (!it->first.IsScalar()) {
      SPDLOG_CRITICAL("Config key is not a scalar; invalid YAML key");
      return false;
    }
    const std::string key = it->first.as<std::string>();
    if (kAllowedKeys.find(key) == kAllowedKeys.end()) {
      SPDLOG_CRITICAL("Unknown config option: {}", key);
      return false;
    }
  }
  return true;
}

static std::string sanitizeFileToken(const std::string& input) {
  std::string out;
  out.reserve(input.size());
  for (unsigned char ch : input) {
    if (std::isalnum(ch) || ch == '_' || ch == '-' || ch == '.') {
      out.push_back(static_cast<char>(ch));
    } else {
      out.push_back('_');
    }
  }
  if (out.empty()) {
    out = "scope";
  }
  return out;
}

int main(int argc, char** argv) {
  using namespace std::chrono;
  enum class FormatType { VERILOG, NAJA_IF };

  // Default values
  FormatType inputFormatType = FormatType::VERILOG;
  std::vector<std::string> inputPaths;
  std::vector<std::string> libertyFiles;
  std::string logLevel = "info";

  // Basic argument sanity
  if (argc < 2) {
    print_usage(argv[0]);
    return EXIT_SUCCESS;
  }

  // Check for config mode (--config or -c). If present, YAML takes precedence.
  bool usedConfig = false;

  std::string logFileName;

  bool useScopes = false;
  bool cleanScopes = false;
  bool dumpCnf = false;
  std::string dumpCnfPath;

  for (int i = 1; i < argc; ++i) {
    std::string a = argv[i];
    if (a == "--config" || a == "-c") {
      if (i + 1 >= argc) {
        SPDLOG_CRITICAL("Missing config file after {}", a);
        return EXIT_FAILURE;
      }
      const std::string cfgPath = argv[i + 1];
      try {
        YAML::Node cfg = YAML::LoadFile(cfgPath);
        if (!validateConfigKeys(cfg)) {
          return EXIT_FAILURE;
        }

        // format
        if (cfg["format"] && cfg["format"].IsScalar()) {
          std::string fmt = cfg["format"].as<std::string>();
          if (fmt == "naja_if" || fmt == "naja-if" || fmt == "snl")
            inputFormatType = FormatType::NAJA_IF;
          else if (fmt == "verilog" || fmt == "v")
            inputFormatType = FormatType::VERILOG;
          else {
            SPDLOG_CRITICAL("Unrecognized format in config: {}", fmt);
            return EXIT_FAILURE;
          }
        }

        // input_paths
        inputPaths = yamlToVector(cfg["input_paths"]);

        // liberty_files
        libertyFiles = yamlToVector(cfg["liberty_files"]);

        // log level
        if (cfg["log_level"] && cfg["log_level"].IsScalar()) {
          logLevel = cfg["log_level"].as<std::string>();
        }

        // Add log file name
        if (cfg["log_file"] && cfg["log_file"].IsScalar()) {
          logFileName = cfg["log_file"].as<std::string>();
        }
        
        // use_scopes
        if (cfg["use_scopes"] && cfg["use_scopes"].IsScalar()) {
          useScopes = cfg["use_scopes"].as<bool>();
        }

        // clean_scopes
        if (cfg["clean_scopes"] && cfg["clean_scopes"].IsScalar()) {
          cleanScopes = cfg["clean_scopes"].as<bool>();
        }

        // cnf_export
        if (cfg["cnf_export"] && cfg["cnf_export"].IsScalar()) {
          dumpCnf = cfg["cnf_export"].as<bool>();
        }

        // cnf_export_path (optional)
        if (cfg["cnf_export_path"] && cfg["cnf_export_path"].IsScalar()) {
          dumpCnfPath = cfg["cnf_export_path"].as<std::string>();
        }

        // solver (glucose | kissat)
        if (cfg["solver"] && cfg["solver"].IsScalar()) {
          std::string solver = cfg["solver"].as<std::string>();
          if (solver == "glucose") {
            KEPLER_FORMAL::Config::setSolverType(KEPLER_FORMAL::Config::GLUCOSE);
          } else if (solver == "kissat") {
            KEPLER_FORMAL::Config::setSolverType(KEPLER_FORMAL::Config::KISSAT);
          } else {
            SPDLOG_CRITICAL("Unrecognized solver in config: {}", solver);
            return EXIT_FAILURE;
          }
        }

        usedConfig = true;
      } catch (const std::exception& e) {
        SPDLOG_CRITICAL("Failed to parse config {}: {}", cfgPath, e.what());
        return EXIT_FAILURE;
      }
      break;
    }
  }

  // If not using config, fall back to original CLI parsing
  if (!usedConfig) {
    if (argc < 4 || (std::string(argv[1]) == "--help") ||
        (std::string(argv[1]) == "-h")) {
      print_usage(argv[0]);
      return EXIT_SUCCESS;
    }

    std::string formatType = argv[1];
    if (formatType == "-naja_if" || formatType == "-naja-if") {
      inputFormatType = FormatType::NAJA_IF;
    } else if (formatType == "-verilog") {
      inputFormatType = FormatType::VERILOG;
    } else {
      SPDLOG_CRITICAL("Unrecognized input format type: {}", formatType);
      return EXIT_FAILURE;
    }

    // collect paths and liberty files from argv
    for (int i = 2; i < argc; ++i) inputPaths.emplace_back(argv[i]);

    // If user provided more than two paths, treat the rest as liberty files
    if (inputPaths.size() > 2) {
      for (size_t i = 2; i < inputPaths.size(); ++i)
        libertyFiles.push_back(inputPaths[i]);
    }
  }

  // Basic validation
  if (inputPaths.size() < 2) {
    SPDLOG_CRITICAL("Need two input netlist paths; got {}", inputPaths.size());
    print_usage(argv[0]);
    return EXIT_FAILURE;
  }

  // Configure logging level
  auto console = spdlog::stdout_color_mt("console");
  if (logLevel == "debug")
    spdlog::set_level(spdlog::level::debug);
  else if (logLevel == "info")
    spdlog::set_level(spdlog::level::info);
  // else if (logLevel == "warn")
  //   spdlog::set_level(spdlog::level::warn);
  // else if (logLevel == "error")
  //   spdlog::set_level(spdlog::level::err);
  // else if (logLevel == "critical")
  //   spdlog::set_level(spdlog::level::critical);
  else
    spdlog::set_level(spdlog::level::info);

  SPDLOG_INFO("KEPLER FORMAL: Run.");
  SPDLOG_INFO("Input format: {}", (inputFormatType == FormatType::NAJA_IF) ? "SNL" : "VERILOG");
  SPDLOG_INFO("Netlist 1: {}", inputPaths[0]);
  SPDLOG_INFO("Netlist 2: {}", inputPaths[1]);
  auto solverType = KEPLER_FORMAL::Config::getSolverType();
  SPDLOG_INFO("Solver: {}",
              solverType == KEPLER_FORMAL::Config::SolverType::KISSAT ? "KISSAT" : "GLUCOSE");
  if (!libertyFiles.empty()) {
    for (const auto& lf : libertyFiles) SPDLOG_INFO("Liberty: {}", lf);
  }

  // --------------------------------------------------------------------------
  // 2. Load two netlists via Cap’n Proto (or via VRL constructor)
  // --------------------------------------------------------------------------
  naja::NL::SNLDesign* top0 = nullptr;
  naja::NL::SNLDesign* top1 = nullptr;
  try {
    NLUniverse::create();
    NLDB* db0 = nullptr;
    bool primitivesAreLoaded = false;

    if (!libertyFiles.empty()) {
      db0 = NLDB::create(NLUniverse::get());
      auto primitivesLibrary =
          NLLibrary::create(db0, NLLibrary::Type::Primitives, NLName("PRIMS"));
      SNLLibertyConstructor constructor(primitivesLibrary);
      for (const auto& lf : libertyFiles) {
        SPDLOG_INFO("Loading liberty file: {}", lf);
        constructor.construct(lf.c_str());
      }
      primitivesAreLoaded = true;
    }

    if (inputFormatType == FormatType::VERILOG) {
      SPDLOG_INFO("Parsing verilog file: {}", inputPaths[0]);
      auto designLibrary = NLLibrary::create(db0, NLName("DESIGN"));
      SNLVRLConstructor constructor(designLibrary);
      constructor.construct(inputPaths[0].c_str());
      auto top = SNLUtils::findTop(designLibrary);
      if (top) {
        db0->setTopDesign(top);
        SPDLOG_INFO("Found top design: {}", top->getString());
      } else {
        // LCOV_EXCL_START
        SPDLOG_CRITICAL("No top design was found after parsing verilog");
        return EXIT_FAILURE;
        // LCOV_EXCL_STOP
      }
    } else {  // SNL
      SPDLOG_INFO("Loading Naja IF: {}", inputPaths[0]);
      naja::NL::SNLCapnP::LoadingConfiguration config;
      config.primitiveConflictPolicy_ = primitivesAreLoaded ? naja::NL::SNLCapnP::LoadingConfiguration::PrimitiveConflictPolicy::PreferExisting :
                                                              naja::NL::SNLCapnP::LoadingConfiguration::PrimitiveConflictPolicy::ForbidConflicts;
      db0 = SNLCapnP::load(inputPaths[0].c_str(), config);
      if (!db0) {
        // LCOV_EXCL_START
        SPDLOG_CRITICAL("Failed to load Naja IF: {}", inputPaths[0]);
        return EXIT_FAILURE;
        // LCOV_EXCL_STOP
      }
    }

    // get db0 top
    top0 = db0->getTopDesign();
    if (!top0) {
      // LCOV_EXCL_START
      SPDLOG_CRITICAL("Top design not set for first netlist");
      return EXIT_FAILURE;
      // LCOV_EXCL_STOP
    }
    db0->setID(2);  // Increment ID to avoid conflicts

    NLDB* db1 = nullptr;

    // Prepare second DB and primitives if needed
    if (!libertyFiles.empty()) {
      db1 = NLDB::create(NLUniverse::get());
      db1->setID(1);
      auto primitivesLibrary =
          NLLibrary::create(db1, NLLibrary::Type::Primitives, NLName("PRIMS"));
      SNLLibertyConstructor constructor(primitivesLibrary);
      for (const auto& lf : libertyFiles) {
        constructor.construct(lf.c_str());
      }
    }

    if (inputFormatType == FormatType::VERILOG) {
      SPDLOG_INFO("Parsing verilog file: {}", inputPaths[1]);
      auto designLibrary = NLLibrary::create(db1, NLName("DESIGN"));
      SNLVRLConstructor constructor(designLibrary);
      constructor.construct(inputPaths[1].c_str());
      auto top = SNLUtils::findTop(designLibrary);
      if (top) {
        db1->setTopDesign(top);
        SPDLOG_INFO("Found top design: {}", top->getString());
      } else {
        // LCOV_EXCL_START
        SPDLOG_CRITICAL("No top design was found after parsing verilog");
        return EXIT_FAILURE;
        // LCOV_EXCL_STOP
      }
    } else {  // SNL
      SPDLOG_INFO("Loading Naja IF: {}", inputPaths[1]);
      naja::NL::SNLCapnP::LoadingConfiguration config;
      config.primitiveConflictPolicy_ = primitivesAreLoaded ? naja::NL::SNLCapnP::LoadingConfiguration::PrimitiveConflictPolicy::PreferExisting :
                                                              naja::NL::SNLCapnP::LoadingConfiguration::PrimitiveConflictPolicy::ForbidConflicts;
      db1 = SNLCapnP::load(inputPaths[1].c_str(), config);
      if (!db1) {
        // LCOV_EXCL_START
        SPDLOG_CRITICAL("Failed to load Naja IF: {}", inputPaths[1]);
        return EXIT_FAILURE;
        // LCOV_EXCL_STOP
      }
    }

    // get db1 top
    top1 = db1->getTopDesign();
    if (!top1) {
      // LCOV_EXCL_START
      SPDLOG_CRITICAL("Top design not set for second netlist");
      return EXIT_FAILURE;
      // LCOV_EXCL_STOP
    }
  } catch (const std::exception& e) {
    SPDLOG_CRITICAL("Netlist loading failed: {}", e.what());
    return EXIT_FAILURE;
  }

  // --------------------------------------------------------------------------
  // 4. Hand off to the rest of the editing/analysis workflow
  // --------------------------------------------------------------------------
  if (inputFormatType == FormatType::NAJA_IF && useScopes) {
    KEPLER_FORMAL::MiterStrategy MiterS(top0, top1);
    MiterS.init();
    ScopeExtraction extractor(top0, top1);
    extractor.collectVerificationScopes();
    if (cleanScopes) {
      extractor.cleanVerificationScopes(MiterS.getPIs0(), MiterS.getPIs1());
    }
    for (auto scopes : extractor.getScopesToVerify()) {
      SPDLOG_INFO("Looking at scope: {} ",
                  scopes.first->getName().getString());
      // std::string scopeLogFile = (logFileName.empty() ? "kf_" : logFileName) + "_" +
      //                           scopes.first->getName().getString() + ".txt";
      try {
        KEPLER_FORMAL::MiterStrategy MiterScope(scopes.first, scopes.second, logFileName);
        if (dumpCnf) {
          std::string scopeName = sanitizeFileToken(scopes.first->getName().getString());
          std::string outPath = dumpCnfPath.empty()
                                    ? ("miter_" + scopeName + ".cnf")
                                    : dumpCnfPath;
          MiterScope.setCnfDump(true, outPath);
        }
        MiterScope.init();
        if (MiterScope.run()) {
          SPDLOG_INFO("No difference was found for scope: {} , {}",
                      scopes.first->getName().getString(),
                      scopes.second->getName().getString());
        } else {
          SPDLOG_INFO("Difference was found for scope: {} , {}. Please refer to the log(miter_log_x.txt) for details.",
                      scopes.first->getName().getString(),
                      scopes.second->getName().getString());
        }
      } catch (const std::exception& e) {
        // LCOV_EXCL_START
        SPDLOG_ERROR("Workflow failed for scope: {} , {}: {}", 
                      scopes.first->getName().getString(),
                      scopes.second->getName().getString(),
                      e.what());
        return EXIT_FAILURE;
        // LCOV_EXCL_STOP
      }
    }
  } else {
    try {
      KEPLER_FORMAL::MiterStrategy MiterS(top0, top1, logFileName);
      if (dumpCnf) {
        const std::string outPath = dumpCnfPath.empty() ? "miter.cnf" : dumpCnfPath;
        MiterS.setCnfDump(true, outPath);
      }
      MiterS.init();
      if (MiterS.run()) {
        SPDLOG_INFO("No difference was found.");
      } else {
        SPDLOG_INFO("Difference was found. Please refer to the log(miter_log_x.txt) for details.");
      }
    } catch (const std::exception& e) {
      // LCOV_EXCL_START
      SPDLOG_ERROR("Workflow failed: {}", e.what());
      return EXIT_FAILURE;
      // LCOV_EXCL_STOP
    }
  }

  return EXIT_SUCCESS;
}
