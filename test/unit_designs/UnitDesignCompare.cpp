// Copyright 2024-2025 keplertech.io
// SPDX-License-Identifier: GPL-3.0-only

#include "gtest/gtest.h"

#include <filesystem>
#include <fstream>

#include "NLUniverse.h"

#include "SNLDesign.h"
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
  auto topClone = top->clone(NLName("topClone"));
  KEPLER_FORMAL::MiterStrategy miterS(top, topClone);
  miterS.init();
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
  printf("TT sum0: %s\n", ttSum0.getString().c_str());
  for (auto term : sumXor0->getModel()->getBitTerms()) {
    printf("Term in sum0: %s\n", term->getDescription().c_str());
    // print direction 
    printf(" Direction: %d\n", static_cast<int>(term->getDirection()));
    if (term->getDirection() == SNLBitTerm::Direction::Input) {
      continue;
    }
    auto ttSum0 = SNLDesignModeling::getTruthTable(sumXor0->getModel(), term->getOrderID());
  }

  auto halfadder1 = library1_->getSNLDesign(NLName("halfadder"));
  ASSERT_NE(nullptr, halfadder1);
  auto sumXor1 = halfadder1->getInstance(NLName("sum_xor"));
  ASSERT_NE(nullptr, sumXor1);
  auto ttSum1 = SNLDesignModeling::getTruthTable(sumXor1->getModel());
  printf("TT sum1: %s\n", ttSum1.getString().c_str());

  EXPECT_EQ(ttSum0, SNLTruthTable(2, 6));   // xor
  EXPECT_EQ(ttSum1, SNLTruthTable(2, 14));  // or (bug)

  KEPLER_FORMAL::MiterStrategy miterS(top0, top1, "./logB");
  miterS.init();
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
  miterS.init();
  EXPECT_FALSE(miterS.run());
  //should be different
  //here the issue comes from missing truth table but nothing is reported
}
