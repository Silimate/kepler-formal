// Copyright 2024-2026 keplertech.io
// SPDX-License-Identifier: GPL-3.0-only

#include <gtest/gtest.h>

#include <cstdlib>
#include <filesystem>
#include <fstream>
#include <string>
#include <vector>

#include "KeplerFormalUtils.h"

extern int KeplerFormalMain(int argc, char** argv);

namespace {

std::filesystem::path repoRoot() {
  return std::filesystem::path(__FILE__).parent_path().parent_path().parent_path().parent_path();
}

}  // namespace

TEST(KeplerFormalCliTests, SanitizeFileToken) {
  EXPECT_EQ(sanitizeFileToken("scope"), "scope");
  EXPECT_EQ(sanitizeFileToken("my scope"), "my_scope");
  EXPECT_EQ(sanitizeFileToken("a/b\\c"), "a_b_c");
  EXPECT_EQ(sanitizeFileToken(""), "scope");
}

TEST(KeplerFormalCliTests, DumpCnfFromConfig) {
  const auto root = repoRoot();
  const auto exampleDir = root / "example";
  const auto design0 = exampleDir / "tinyrocket.v";
  const auto design1 = exampleDir / "tinyrocket_edited.v";
  const auto lib0 = exampleDir / "NangateOpenCellLibrary_typical.lib";
  const auto lib1 = exampleDir / "fakeram45_1024x32.lib";
  const auto lib2 = exampleDir / "fakeram45_64x32.lib";
  const auto lib3 = exampleDir / "fakeram45_64x15.lib";

  ASSERT_TRUE(std::filesystem::exists(design0));
  ASSERT_TRUE(std::filesystem::exists(design1));
  ASSERT_TRUE(std::filesystem::exists(lib0));
  ASSERT_TRUE(std::filesystem::exists(lib1));
  ASSERT_TRUE(std::filesystem::exists(lib2));
  ASSERT_TRUE(std::filesystem::exists(lib3));

  const auto tmpDir = std::filesystem::temp_directory_path() / "kepler_formal_cli_test";
  std::filesystem::create_directories(tmpDir);
  const auto cnfPath = tmpDir / "miter_test.cnf";
  const auto cfgPath = tmpDir / "config.yaml";

  if (std::filesystem::exists(cnfPath)) {
    std::filesystem::remove(cnfPath);
  }

  std::ofstream cfg(cfgPath);
  cfg << "format: verilog\n";
  cfg << "input_paths:\n";
  cfg << "  - " << design0.string() << "\n";
  cfg << "  - " << design1.string() << "\n";
  cfg << "liberty_files:\n";
  cfg << "  - " << lib0.string() << "\n";
  cfg << "  - " << lib1.string() << "\n";
  cfg << "  - " << lib2.string() << "\n";
  cfg << "  - " << lib3.string() << "\n";
  cfg << "log_level: info\n";
  cfg << "cnf_export: true\n";
  cfg << "cnf_export_path: " << cnfPath.string() << "\n";
  cfg.close();

  std::string argv0 = "kepler-formal";
  std::string argv1 = "--config";
  std::string argv2 = cfgPath.string();
  char* argv[] = {argv0.data(), argv1.data(), argv2.data()};
  int argc = 3;

  int rc = KeplerFormalMain(argc, argv);
  EXPECT_EQ(rc, EXIT_SUCCESS);
  EXPECT_TRUE(std::filesystem::exists(cnfPath));

  std::filesystem::remove(cnfPath);
  std::filesystem::remove(cfgPath);
  std::filesystem::remove_all(tmpDir);
}

TEST(KeplerFormalCliTests, MultiFileVerilogConfig) {
  const auto tmpDir =
      std::filesystem::temp_directory_path() / "kepler_formal_cli_multi_v";
  std::filesystem::create_directories(tmpDir);

  const auto design0Leaf = tmpDir / "design0_leaf.v";
  const auto design0Top = tmpDir / "design0_top.v";
  const auto design1Leaf = tmpDir / "design1_leaf.v";
  const auto design1Top = tmpDir / "design1_top.v";
  const auto cfgPath = tmpDir / "config.yaml";
  const auto root = repoRoot();
  const auto exampleDir = root / "example";
  const auto lib0 = exampleDir / "NangateOpenCellLibrary_typical.lib";
  const auto lib1 = exampleDir / "fakeram45_1024x32.lib";
  const auto lib2 = exampleDir / "fakeram45_64x32.lib";
  const auto lib3 = exampleDir / "fakeram45_64x15.lib";

  ASSERT_TRUE(std::filesystem::exists(lib0));
  ASSERT_TRUE(std::filesystem::exists(lib1));
  ASSERT_TRUE(std::filesystem::exists(lib2));
  ASSERT_TRUE(std::filesystem::exists(lib3));

  {
    std::ofstream leaf(design0Leaf);
    leaf << "module leaf(input a, input b, output y);\n";
    leaf << "  wire n;\n";
    leaf << "  NAND2_X1 u1(.A1(a), .A2(b), .ZN(n));\n";
    leaf << "  INV_X1 u2(.A(n), .ZN(y));\n";
    leaf << "endmodule\n";
  }
  {
    std::ofstream top(design0Top);
    top << "module top(input a, input b, output y);\n";
    top << "  wire w;\n";
    top << "  leaf u1(.a(a), .b(b), .y(w));\n";
    top << "  INV_X1 u2(.A(w), .ZN(y));\n";
    top << "endmodule\n";
  }
  {
    std::ofstream leaf(design1Leaf);
    leaf << "module leaf(input a, input b, output y);\n";
    leaf << "  wire n;\n";
    leaf << "  NAND2_X1 u1(.A1(a), .A2(b), .ZN(n));\n";
    leaf << "  INV_X1 u2(.A(n), .ZN(y));\n";
    leaf << "endmodule\n";
  }
  {
    std::ofstream top(design1Top);
    top << "module top(input a, input b, output y);\n";
    top << "  wire w;\n";
    top << "  leaf u1(.a(a), .b(b), .y(w));\n";
    top << "  INV_X1 u2(.A(w), .ZN(y));\n";
    top << "endmodule\n";
  }

  std::ofstream cfg(cfgPath);
  cfg << "format: verilog\n";
  cfg << "input_paths:\n";
  cfg << "  -\n";
  cfg << "    - " << design0Leaf.string() << "\n";
  cfg << "    - " << design0Top.string() << "\n";
  cfg << "  -\n";
  cfg << "    - " << design1Leaf.string() << "\n";
  cfg << "    - " << design1Top.string() << "\n";
  cfg << "liberty_files:\n";
  cfg << "  - " << lib0.string() << "\n";
  cfg << "  - " << lib1.string() << "\n";
  cfg << "  - " << lib2.string() << "\n";
  cfg << "  - " << lib3.string() << "\n";
  cfg << "log_level: info\n";
  cfg.close();

  std::string argv0 = "kepler-formal";
  std::string argv1 = "--config";
  std::string argv2 = cfgPath.string();
  char* argv[] = {argv0.data(), argv1.data(), argv2.data()};
  int argc = 3;

  int rc = KeplerFormalMain(argc, argv);
  EXPECT_EQ(rc, EXIT_SUCCESS);

  std::filesystem::remove_all(tmpDir);
}
