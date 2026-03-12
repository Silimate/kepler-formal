// Copyright 2024-2026 keplertech.io
// SPDX-License-Identifier: GPL-3.0-only

#include <gtest/gtest.h>

#include <filesystem>
#include <fstream>
#include <sstream>
#include <string>

#include "BoolExpr.h"
#include "BoolExprCache.h"
#include "BoolExprCnfWriter.h"

using namespace KEPLER_FORMAL;

namespace {

class BoolExprCnfWriterTests : public ::testing::Test {
 protected:
  void TearDown() override {
    KEPLER_FORMAL::BoolExprCache::destroy();
  }
};

}  // namespace

TEST_F(BoolExprCnfWriterTests, EncodeAndWriteAndExpression) {
  BoolExpr* a = BoolExpr::Var(2);
  BoolExpr* b = BoolExpr::Var(3);
  BoolExpr* expr = BoolExpr::And(a, b);

  CnfFormula cnf = encodeBoolExprToCnf(expr);

  EXPECT_EQ(cnf.numVars, 3);
  EXPECT_EQ(cnf.clauses.size(), 3u);
  EXPECT_TRUE(cnf.varNameToDimacs.count("x2") > 0);
  EXPECT_TRUE(cnf.varNameToDimacs.count("x3") > 0);
  EXPECT_GT(cnf.rootLit, 0);

  std::stringstream out;
  EXPECT_TRUE(writeDimacsCnf(cnf, out, true));

  const std::string text = out.str();
  EXPECT_NE(text.find("p cnf 3 4\n"), std::string::npos);
  EXPECT_NE(text.find("\n3 0\n"), std::string::npos);
}

TEST_F(BoolExprCnfWriterTests, WriteWithoutRootClause) {
  BoolExpr* a = BoolExpr::Var(2);
  BoolExpr* b = BoolExpr::Var(3);
  BoolExpr* expr = BoolExpr::And(a, b);

  CnfFormula cnf = encodeBoolExprToCnf(expr);

  std::stringstream out;
  EXPECT_TRUE(writeDimacsCnf(cnf, out, false));

  const std::string text = out.str();
  EXPECT_NE(text.find("p cnf 3 3\n"), std::string::npos);
  EXPECT_EQ(text.find("\n3 0\n"), std::string::npos);
}

TEST_F(BoolExprCnfWriterTests, EncodeConstantTrue) {
  BoolExpr* expr = BoolExpr::Var(1);
  CnfFormula cnf = encodeBoolExprToCnf(expr);

  EXPECT_EQ(cnf.numVars, 1);
  EXPECT_EQ(cnf.clauses.size(), 1u);
  EXPECT_EQ(cnf.rootLit, 1);
}

TEST_F(BoolExprCnfWriterTests, DumpToFileAndInvalidPath) {
  BoolExpr* expr = BoolExpr::And(BoolExpr::Var(2), BoolExpr::Var(3));

  std::filesystem::path tmpDir = std::filesystem::temp_directory_path();
  std::filesystem::path filePath = tmpDir / "bool_expr_cnf_test.cnf";
  std::filesystem::path dirPath = tmpDir / "bool_expr_cnf_dir";

  if (std::filesystem::exists(filePath)) {
    std::filesystem::remove(filePath);
  }
  if (std::filesystem::exists(dirPath)) {
    std::filesystem::remove_all(dirPath);
  }
  std::filesystem::create_directory(dirPath);

  EXPECT_TRUE(dumpBoolExprToDimacs(expr, filePath.string()));
  EXPECT_TRUE(std::filesystem::exists(filePath));

  std::ifstream in(filePath);
  std::string header;
  std::getline(in, header);
  EXPECT_TRUE(header.rfind("p cnf", 0) == 0);

  CnfFormula cnf = encodeBoolExprToCnf(expr);
  EXPECT_FALSE(dumpDimacsCnf(cnf, dirPath.string()));

  std::filesystem::remove(filePath);
  std::filesystem::remove_all(dirPath);
}
