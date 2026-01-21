// Copyright 2024-2025 keplertech.io
// SPDX-License-Identifier: GPL-3.0-only

#include "gtest/gtest.h"

#include <filesystem>
#include <fstream>

#include "NLUniverse.h"

#include "SNLDesign.h"
#include "SNLScalarTerm.h"
#include "SNLDesignModeling.h"
#include "SNLInstance.h"
#include "SNLTruthTable.h"
#include "SNLUtils.h"
#include "SNLVRLConstructor.h"
#include "MiterStrategy.h"

using namespace naja::NL;

#ifndef BENCHMARKS_PATH
#define BENCHMARKS_PATH "Undefined"
#endif

class UnitDesignCompare: public ::testing::Test {
  protected:
    void SetUp() override {
      NLUniverse* universe = NLUniverse::create();
      auto db = NLDB::create(universe);
      library0_ = NLLibrary::create(db, NLName("LIB0"));
      library1_ = NLLibrary::create(db, NLName("LIB1"));
    }
    void TearDown() override {
      NLUniverse::get()->destroy();
    }
  protected:
    NLLibrary*  library0_;
    NLLibrary*  library1_;
};

TEST_F(UnitDesignCompare, testSameDesigns) {
  SNLVRLConstructor constructor0(library0_);
  std::filesystem::path benchmarksPath(BENCHMARKS_PATH);
  constructor0.construct(benchmarksPath/"simple0.v");
  auto top = SNLUtils::findTop(library0_);

  auto sum = top->getScalarTerm(NLName("sum"));
  ASSERT_NE(nullptr, sum);
  EXPECT_EQ(SNLTerm::Direction::Output, sum->getDirection());
  auto sumNet = sum->getNet();
  ASSERT_NE(nullptr, sumNet);
  EXPECT_EQ(2, sumNet->getComponents().size());

  auto cout = top->getScalarTerm(NLName("cout"));
  ASSERT_NE(nullptr, cout);
  EXPECT_EQ(SNLTerm::Direction::Output, cout->getDirection());
  auto coutNet = cout->getNet();
  ASSERT_NE(nullptr, coutNet);
  EXPECT_EQ(2, coutNet->getComponents().size());

  KEPLER_FORMAL::MiterStrategy miterS(top, top);
  EXPECT_TRUE(miterS.run());
}

TEST_F(UnitDesignCompare, testDifferentDesigns) {
  std::filesystem::path benchmarksPath(BENCHMARKS_PATH);
  SNLVRLConstructor constructor0(library0_);
  constructor0.construct(benchmarksPath/"simple0.v");
  auto top0 = SNLUtils::findTop(library0_);

  SNLVRLConstructor constructor1(library1_);
  constructor1.construct(benchmarksPath/"simple1.v");
  auto top1 = SNLUtils::findTop(library1_);

  auto halfadder0 = library0_->getSNLDesign(NLName("halfadder"));
  ASSERT_NE(nullptr, halfadder0);
  auto sumXor0 = halfadder0->getInstance(NLName("sum_xor"));
  ASSERT_NE(nullptr, sumXor0);
  auto ttSum0 = SNLDesignModeling::getTruthTable(sumXor0->getModel());

  auto halfadder1 = library1_->getSNLDesign(NLName("halfadder"));
  ASSERT_NE(nullptr, halfadder1);
  auto sumXor1 = halfadder1->getInstance(NLName("sum_xor"));
  ASSERT_NE(nullptr, sumXor1);
  auto ttSum1 = SNLDesignModeling::getTruthTable(sumXor1->getModel());

  EXPECT_EQ(ttSum0, SNLTruthTable(2, 6));   // xor
  EXPECT_EQ(ttSum1, SNLTruthTable(2, 14));  // or (bug)

  KEPLER_FORMAL::MiterStrategy miterS(top0, top1);
  EXPECT_FALSE(miterS.run());
  //should be different
  //here the issue comes from missing truth table but nothing is reported
}

TEST_F(UnitDesignCompare, testDiffWithConstants) {
  std::filesystem::path benchmarksPath(BENCHMARKS_PATH);
  SNLVRLConstructor constructor0(library0_);
  constructor0.construct(benchmarksPath/"simple1.v");
  auto top0 = SNLUtils::findTop(library0_);

  SNLVRLConstructor constructor1(library1_);
  constructor1.construct(benchmarksPath/"simple2.v");
  auto top1 = SNLUtils::findTop(library1_);

  KEPLER_FORMAL::MiterStrategy miterS(top0, top1);
  EXPECT_FALSE(miterS.run());
  //should be different
  //here the issue comes from missing truth table but nothing is reported
}
