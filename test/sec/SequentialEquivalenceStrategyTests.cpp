// Copyright 2024-2026 keplertech.io
// SPDX-License-Identifier: GPL-3.0-only

#include <gtest/gtest.h>

#include "BoolExprCache.h"
#include "DNL.h"
#include "NLDB0.h"
#include "NLUniverse.h"
#include "SNLDesign.h"
#include "SNLDesignModeling.h"
#include "SNLScalarNet.h"
#include "SNLScalarTerm.h"
#include "strategy/SequentialEquivalenceStrategy.h"

using namespace naja::NL;
using namespace KEPLER_FORMAL::SEC;

namespace {

class SequentialEquivalenceStrategyTests : public ::testing::Test {
 protected:
  void TearDown() override {
    naja::DNL::destroy();
    if (auto* universe = NLUniverse::get()) {
      universe->destroy();
    }
    KEPLER_FORMAL::BoolExprCache::destroy();
  }
};

SNLDesign* createInvModel(NLLibrary* library) {
  auto* model =
      SNLDesign::create(library, SNLDesign::Type::Primitive, NLName("INV"));
  auto* input =
      SNLScalarTerm::create(model, SNLTerm::Direction::Input, NLName("A"));
  auto* output =
      SNLScalarTerm::create(model, SNLTerm::Direction::Output, NLName("Y"));
  SNLDesignModeling::addCombinatorialArcs({input}, {output});
  SNLDesignModeling::setTruthTable(model, SNLTruthTable::Inv());
  return model;
}

SNLDesign* createDffTop(
    NLLibrary* library,
    const std::string& name,
    SNLDesign* invModel,
    bool invertData,
    bool invertOutput,
    const std::string& ffName = "ff0") {
  auto* top =
      SNLDesign::create(library, SNLDesign::Type::Standard, NLName(name));
  auto* topIn =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("in"));
  auto* topClock =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("clk"));
  auto* topOut =
      SNLScalarTerm::create(top, SNLTerm::Direction::Output, NLName("out"));

  auto* ff = SNLInstance::create(top, NLDB0::getDFF(), NLName(ffName));
  SNLInstance* dataInv = nullptr;
  SNLInstance* outputInv = nullptr;
  if (invertData) {
    dataInv = SNLInstance::create(top, invModel, NLName("inv_data"));
  }
  if (invertOutput) {
    outputInv = SNLInstance::create(top, invModel, NLName("inv_out"));
  }

  auto* netIn = SNLScalarNet::create(top, NLName("net_in"));
  auto* netClock = SNLScalarNet::create(top, NLName("net_clk"));
  auto* netData = SNLScalarNet::create(top, NLName("net_data"));
  auto* netQ = SNLScalarNet::create(top, NLName("net_q"));
  auto* netOut = SNLScalarNet::create(top, NLName("net_out"));

  topIn->setNet(netIn);
  topClock->setNet(netClock);

  if (invertData) {
    dataInv->getInstTerm(invModel->getScalarTerm(NLName("A")))->setNet(netIn);
    dataInv->getInstTerm(invModel->getScalarTerm(NLName("Y")))->setNet(netData);
  }

  ff->getInstTerm(NLDB0::getDFFClock())->setNet(netClock);
  ff->getInstTerm(NLDB0::getDFFData())->setNet(invertData ? netData : netIn);
  ff->getInstTerm(NLDB0::getDFFOutput())->setNet(netQ);

  if (invertOutput) {
    topOut->setNet(netOut);
    outputInv->getInstTerm(invModel->getScalarTerm(NLName("A")))->setNet(netQ);
    outputInv->getInstTerm(invModel->getScalarTerm(NLName("Y")))->setNet(netOut);
  } else {
    topOut->setNet(netQ);
  }

  return top;
}

SNLDesign* createDffeTop(
    NLLibrary* library,
    const std::string& name) {
  auto* top =
      SNLDesign::create(library, SNLDesign::Type::Standard, NLName(name));
  auto* topIn =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("in"));
  auto* topEnable =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("en"));
  auto* topClock =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("clk"));
  auto* topOut =
      SNLScalarTerm::create(top, SNLTerm::Direction::Output, NLName("out"));

  auto* ff = SNLInstance::create(top, NLDB0::getDFFE(), NLName("ff0"));
  auto* netIn = SNLScalarNet::create(top, NLName("net_in"));
  auto* netEnable = SNLScalarNet::create(top, NLName("net_en"));
  auto* netClock = SNLScalarNet::create(top, NLName("net_clk"));
  auto* netQ = SNLScalarNet::create(top, NLName("net_q"));

  topIn->setNet(netIn);
  topEnable->setNet(netEnable);
  topClock->setNet(netClock);
  topOut->setNet(netQ);

  ff->getInstTerm(NLDB0::getDFFEClock())->setNet(netClock);
  ff->getInstTerm(NLDB0::getDFFEData())->setNet(netIn);
  ff->getInstTerm(NLDB0::getDFFEEnable())->setNet(netEnable);
  ff->getInstTerm(NLDB0::getDFFEOutput())->setNet(netQ);

  return top;
}

SNLDesign* createResetInitializedPipelineTop(
    NLLibrary* library,
    const std::string& name,
    bool driveLastStageFromReset) {
  auto* top =
      SNLDesign::create(library, SNLDesign::Type::Standard, NLName(name));
  auto* topIn =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("in"));
  auto* topResetN =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("rst_n"));
  auto* topClock =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("clk"));
  auto* topOut =
      SNLScalarTerm::create(top, SNLTerm::Direction::Output, NLName("out"));

  auto* ff0 = SNLInstance::create(top, NLDB0::getDFFRN(), NLName("ff0"));
  auto* ff1 = SNLInstance::create(top, NLDB0::getDFFRN(), NLName("ff1"));
  auto* ff2 = SNLInstance::create(top, NLDB0::getDFFRN(), NLName("ff2"));

  auto* netIn = SNLScalarNet::create(top, NLName("net_in"));
  auto* netResetN = SNLScalarNet::create(top, NLName("net_rst_n"));
  auto* netClock = SNLScalarNet::create(top, NLName("net_clk"));
  auto* netQ0 = SNLScalarNet::create(top, NLName("net_q0"));
  auto* netQ1 = SNLScalarNet::create(top, NLName("net_q1"));
  auto* netQ2 = SNLScalarNet::create(top, NLName("net_q2"));

  topIn->setNet(netIn);
  topResetN->setNet(netResetN);
  topClock->setNet(netClock);
  topOut->setNet(netQ0);

  for (auto* ff : {ff0, ff1, ff2}) {
    ff->getInstTerm(NLDB0::getDFFRNClock())->setNet(netClock);
    ff->getInstTerm(NLDB0::getDFFRNResetN())->setNet(netResetN);
  }

  ff0->getInstTerm(NLDB0::getDFFRNData())->setNet(netQ1);
  ff0->getInstTerm(NLDB0::getDFFRNOutput())->setNet(netQ0);
  ff1->getInstTerm(NLDB0::getDFFRNData())->setNet(netQ2);
  ff1->getInstTerm(NLDB0::getDFFRNOutput())->setNet(netQ1);
  ff2->getInstTerm(NLDB0::getDFFRNData())->setNet(
      driveLastStageFromReset ? netResetN : netIn);
  ff2->getInstTerm(NLDB0::getDFFRNOutput())->setNet(netQ2);

  return top;
}

SNLDesign* createDffQnModel(NLLibrary* library) {
  auto* model =
      SNLDesign::create(library, SNLDesign::Type::Primitive, NLName("DFF_Q_QN"));
  auto* data =
      SNLScalarTerm::create(model, SNLTerm::Direction::Input, NLName("D"));
  auto* clock =
      SNLScalarTerm::create(model, SNLTerm::Direction::Input, NLName("CK"));
  auto* q =
      SNLScalarTerm::create(model, SNLTerm::Direction::Output, NLName("Q"));
  auto* qn =
      SNLScalarTerm::create(model, SNLTerm::Direction::Output, NLName("QN"));
  SNLDesignModeling::addInputsToClockArcs({data}, clock);
  SNLDesignModeling::addClockToOutputsArcs(clock, {q, qn});
  return model;
}

SNLDesign* createComplementedOutputTop(
    NLLibrary* library,
    const std::string& name,
    SNLDesign* ffModel,
    SNLDesign* invModel,
    bool rebuildOutputsFromComplements) {
  auto* top =
      SNLDesign::create(library, SNLDesign::Type::Standard, NLName(name));
  auto* topIn =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("in"));
  auto* topClock =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("clk"));
  auto* topOutQ =
      SNLScalarTerm::create(top, SNLTerm::Direction::Output, NLName("out_q"));
  auto* topOutQn =
      SNLScalarTerm::create(top, SNLTerm::Direction::Output, NLName("out_qn"));

  auto* ff = SNLInstance::create(top, ffModel, NLName("ff0"));
  SNLInstance* qnToQInv = nullptr;
  SNLInstance* qToQnInv = nullptr;
  if (rebuildOutputsFromComplements) {
    qnToQInv = SNLInstance::create(top, invModel, NLName("inv_qn_to_q"));
    qToQnInv = SNLInstance::create(top, invModel, NLName("inv_q_to_qn"));
  }

  auto* netIn = SNLScalarNet::create(top, NLName("net_in"));
  auto* netClock = SNLScalarNet::create(top, NLName("net_clk"));
  auto* netQ = SNLScalarNet::create(top, NLName("net_q"));
  auto* netQn = SNLScalarNet::create(top, NLName("net_qn"));
  auto* netOutQ = SNLScalarNet::create(top, NLName("net_out_q"));
  auto* netOutQn = SNLScalarNet::create(top, NLName("net_out_qn"));

  topIn->setNet(netIn);
  topClock->setNet(netClock);

  ff->getInstTerm(ffModel->getScalarTerm(NLName("CK")))->setNet(netClock);
  ff->getInstTerm(ffModel->getScalarTerm(NLName("D")))->setNet(netIn);
  ff->getInstTerm(ffModel->getScalarTerm(NLName("Q")))->setNet(netQ);
  ff->getInstTerm(ffModel->getScalarTerm(NLName("QN")))->setNet(netQn);

  if (rebuildOutputsFromComplements) {
    topOutQ->setNet(netOutQ);
    topOutQn->setNet(netOutQn);
    qnToQInv->getInstTerm(invModel->getScalarTerm(NLName("A")))->setNet(netQn);
    qnToQInv->getInstTerm(invModel->getScalarTerm(NLName("Y")))->setNet(netOutQ);
    qToQnInv->getInstTerm(invModel->getScalarTerm(NLName("A")))->setNet(netQ);
    qToQnInv->getInstTerm(invModel->getScalarTerm(NLName("Y")))->setNet(netOutQn);
  } else {
    topOutQ->setNet(netQ);
    topOutQn->setNet(netQn);
  }

  return top;
}

}  // namespace

TEST_F(SequentialEquivalenceStrategyTests, IdenticalDffDesignsAreEquivalent) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* primitives =
      NLLibrary::create(db, NLLibrary::Type::Primitives, NLName("prims"));
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* invModel = createInvModel(primitives);
  auto* top0 = createDffTop(library, "top0", invModel, false, false);
  auto* top1 = createDffTop(library, "top1", invModel, false, false);

  SequentialEquivalenceStrategy strategy(top0, top1);
  const auto result = strategy.run(3);

  EXPECT_EQ(result.status, SequentialEquivalenceStatus::Equivalent);
  EXPECT_EQ(result.bound, 1u);
}

TEST_F(SequentialEquivalenceStrategyTests, OutputMismatchFailsAfterInitialObservation) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* primitives =
      NLLibrary::create(db, NLLibrary::Type::Primitives, NLName("prims"));
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* invModel = createInvModel(primitives);
  auto* top0 = createDffTop(library, "top0", invModel, false, false);
  auto* top1 = createDffTop(library, "top1", invModel, false, true);

  SequentialEquivalenceStrategy strategy(top0, top1);
  const auto result = strategy.run(3);

  EXPECT_EQ(result.status, SequentialEquivalenceStatus::Different);
  EXPECT_EQ(result.bound, 1u);
}

TEST_F(SequentialEquivalenceStrategyTests, NextStateMismatchFailsAtOneStep) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* primitives =
      NLLibrary::create(db, NLLibrary::Type::Primitives, NLName("prims"));
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* invModel = createInvModel(primitives);
  auto* top0 = createDffTop(library, "top0", invModel, false, false);
  auto* top1 = createDffTop(library, "top1", invModel, true, false);

  SequentialEquivalenceStrategy strategy(top0, top1);
  const auto result = strategy.run(3);

  EXPECT_EQ(result.status, SequentialEquivalenceStatus::Different);
  EXPECT_EQ(result.bound, 1u);
}

TEST_F(SequentialEquivalenceStrategyTests, DffeHoldSemanticsAreProved) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* top0 = createDffeTop(library, "top0");
  auto* top1 = createDffeTop(library, "top1");

  SequentialEquivalenceStrategy strategy(top0, top1);
  const auto result = strategy.run(3);

  EXPECT_EQ(result.status, SequentialEquivalenceStatus::Equivalent);
  EXPECT_EQ(result.bound, 1u);
}

TEST_F(SequentialEquivalenceStrategyTests, ComplementedStateOutputsRemainConsistent) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* primitives =
      NLLibrary::create(db, NLLibrary::Type::Primitives, NLName("prims"));
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* invModel = createInvModel(primitives);
  auto* dffQnModel = createDffQnModel(primitives);
  auto* top0 =
      createComplementedOutputTop(library, "top0", dffQnModel, invModel, false);
  auto* top1 =
      createComplementedOutputTop(library, "top1", dffQnModel, invModel, true);

  SequentialEquivalenceStrategy strategy(top0, top1);
  const auto result = strategy.run(3);

  EXPECT_EQ(result.status, SequentialEquivalenceStatus::Equivalent);
  EXPECT_EQ(result.bound, 1u);
}

TEST_F(SequentialEquivalenceStrategyTests, EquivalentDesignsWithRenamedStateAreAccepted) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* primitives =
      NLLibrary::create(db, NLLibrary::Type::Primitives, NLName("prims"));
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* invModel = createInvModel(primitives);
  auto* top0 = createDffTop(library, "top0", invModel, false, false, "state_a");
  auto* top1 = createDffTop(library, "top1", invModel, false, false, "state_b");

  SequentialEquivalenceStrategy strategy(top0, top1);
  const auto result = strategy.run(3);

  EXPECT_EQ(result.status, SequentialEquivalenceStatus::Equivalent);
  EXPECT_EQ(result.bound, 1u);
}

TEST_F(SequentialEquivalenceStrategyTests,
       ResetInitializedThreeStagePipelineFailsAtThreeSteps) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* top0 = createResetInitializedPipelineTop(library, "top0", false);
  auto* top1 = createResetInitializedPipelineTop(library, "top1", true);

  SequentialEquivalenceStrategy strategy(top0, top1);
  const auto result = strategy.run(4);

  EXPECT_EQ(result.status, SequentialEquivalenceStatus::Different);
  EXPECT_EQ(result.bound, 3u);
}
