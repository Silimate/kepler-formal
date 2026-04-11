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
#include "kinduction/KInductionEngine.h"
#include "model/SequentialDesignModel.h"
#include "strategy/SequentialEquivalenceStrategy.h"

using namespace naja::NL;
using namespace KEPLER_FORMAL::SEC;
using KEPLER_FORMAL::BoolExpr;

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

SNLDesign* createAnd2Model(NLLibrary* library) {
  auto* model =
      SNLDesign::create(library, SNLDesign::Type::Primitive, NLName("AND2"));
  auto* input0 =
      SNLScalarTerm::create(model, SNLTerm::Direction::Input, NLName("A"));
  auto* input1 =
      SNLScalarTerm::create(model, SNLTerm::Direction::Input, NLName("B"));
  auto* output =
      SNLScalarTerm::create(model, SNLTerm::Direction::Output, NLName("Y"));
  SNLDesignModeling::addCombinatorialArcs({input0, input1}, {output});
  SNLDesignModeling::setTruthTable(
      model,
      SNLTruthTable(
          2,
          SNLTruthTable::GenericType::AND,
          SNLTruthTable::fullDependencies(2)));
  return model;
}

SNLDesign* createOr2Model(NLLibrary* library) {
  auto* model =
      SNLDesign::create(library, SNLDesign::Type::Primitive, NLName("OR2"));
  auto* input0 =
      SNLScalarTerm::create(model, SNLTerm::Direction::Input, NLName("A"));
  auto* input1 =
      SNLScalarTerm::create(model, SNLTerm::Direction::Input, NLName("B"));
  auto* output =
      SNLScalarTerm::create(model, SNLTerm::Direction::Output, NLName("Y"));
  SNLDesignModeling::addCombinatorialArcs({input0, input1}, {output});
  SNLDesignModeling::setTruthTable(
      model,
      SNLTruthTable(
          2,
          SNLTruthTable::GenericType::OR,
          SNLTruthTable::fullDependencies(2)));
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
    bool driveLastStageFromReset,
    const std::vector<std::string>& ffNames);

SNLDesign* createResetInitializedPipelineTop(
    NLLibrary* library,
    const std::string& name,
    bool driveLastStageFromReset) {
  return createResetInitializedPipelineTop(
      library,
      name,
      driveLastStageFromReset,
      {"ff0", "ff1", "ff2"});
}

SNLDesign* createResetInitializedPipelineTop(
    NLLibrary* library,
    const std::string& name,
    bool driveLastStageFromReset,
    const std::vector<std::string>& ffNames) {
  if (ffNames.size() != 3) {
    throw std::invalid_argument(
        "createResetInitializedPipelineTop expects exactly three flop names");
  }

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

  auto* ff0 = SNLInstance::create(top, NLDB0::getDFFRN(), NLName(ffNames[0]));
  auto* ff1 = SNLInstance::create(top, NLDB0::getDFFRN(), NLName(ffNames[1]));
  auto* ff2 = SNLInstance::create(top, NLDB0::getDFFRN(), NLName(ffNames[2]));

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

SNLDesign* createBootstrapPipelineTopWithStages(
    NLLibrary* library,
    const std::string& name,
    SNLDesign* invModel,
    SNLDesign* andModel,
    size_t stages) {
  auto* top =
      SNLDesign::create(library, SNLDesign::Type::Standard, NLName(name));
  auto* topIn =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("in"));
  auto* topReset =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("rst"));
  auto* topClock =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("clk"));
  auto* topOut =
      SNLScalarTerm::create(top, SNLTerm::Direction::Output, NLName("out"));

  auto* resetInv = SNLInstance::create(top, invModel, NLName("reset_inv"));
  std::vector<SNLInstance*> gates;
  std::vector<SNLInstance*> flops;
  gates.reserve(stages);
  flops.reserve(stages);
  for (size_t i = 0; i < stages; ++i) {
    gates.push_back(
        SNLInstance::create(top, andModel, NLName("gate" + std::to_string(i))));
    flops.push_back(
        SNLInstance::create(top, NLDB0::getDFF(), NLName("ff" + std::to_string(i))));
  }

  auto* netIn = SNLScalarNet::create(top, NLName("net_in"));
  auto* netReset = SNLScalarNet::create(top, NLName("net_rst"));
  auto* netResetN = SNLScalarNet::create(top, NLName("net_rst_n"));
  auto* netClock = SNLScalarNet::create(top, NLName("net_clk"));
  std::vector<SNLScalarNet*> dataNets;
  std::vector<SNLScalarNet*> stateNets;
  dataNets.reserve(stages);
  stateNets.reserve(stages);
  for (size_t i = 0; i < stages; ++i) {
    dataNets.push_back(
        SNLScalarNet::create(top, NLName("net_d" + std::to_string(i))));
    stateNets.push_back(
        SNLScalarNet::create(top, NLName("net_q" + std::to_string(i))));
  }

  topIn->setNet(netIn);
  topReset->setNet(netReset);
  topClock->setNet(netClock);
  topOut->setNet(stateNets.front());

  resetInv->getInstTerm(invModel->getScalarTerm(NLName("A")))->setNet(netReset);
  resetInv->getInstTerm(invModel->getScalarTerm(NLName("Y")))->setNet(netResetN);

  for (size_t i = 0; i < stages; ++i) {
    gates[i]->getInstTerm(andModel->getScalarTerm(NLName("A")))->setNet(
        i + 1 == stages ? netIn : stateNets[i + 1]);
    gates[i]->getInstTerm(andModel->getScalarTerm(NLName("B")))->setNet(netResetN);
    gates[i]->getInstTerm(andModel->getScalarTerm(NLName("Y")))->setNet(dataNets[i]);
  }

  for (auto* ff : flops) {
    ff->getInstTerm(NLDB0::getDFFClock())->setNet(netClock);
  }
  for (size_t i = 0; i < stages; ++i) {
    flops[i]->getInstTerm(NLDB0::getDFFData())->setNet(dataNets[i]);
    flops[i]->getInstTerm(NLDB0::getDFFOutput())->setNet(stateNets[i]);
  }

  return top;
}

SNLDesign* createBootstrapPipelineTop(
    NLLibrary* library,
    const std::string& name,
    SNLDesign* invModel,
    SNLDesign* andModel) {
  return createBootstrapPipelineTopWithStages(library, name, invModel, andModel, 3);
}

SNLDesign* createResetLoadsInputTop(
    NLLibrary* library,
    const std::string& name,
    SNLDesign* invModel,
    SNLDesign* andModel,
    SNLDesign* orModel) {
  auto* top =
      SNLDesign::create(library, SNLDesign::Type::Standard, NLName(name));
  auto* topIn =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("in"));
  auto* topReset =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("rst"));
  auto* topClock =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("clk"));
  auto* topOut =
      SNLScalarTerm::create(top, SNLTerm::Direction::Output, NLName("out"));

  auto* resetInv = SNLInstance::create(top, invModel, NLName("reset_inv"));
  auto* loadData = SNLInstance::create(top, andModel, NLName("load_data"));
  auto* holdData = SNLInstance::create(top, andModel, NLName("hold_data"));
  auto* muxOut = SNLInstance::create(top, orModel, NLName("mux_out"));
  auto* ff = SNLInstance::create(top, NLDB0::getDFF(), NLName("ff0"));

  auto* netIn = SNLScalarNet::create(top, NLName("net_in"));
  auto* netReset = SNLScalarNet::create(top, NLName("net_rst"));
  auto* netResetN = SNLScalarNet::create(top, NLName("net_rst_n"));
  auto* netClock = SNLScalarNet::create(top, NLName("net_clk"));
  auto* netLoad = SNLScalarNet::create(top, NLName("net_load"));
  auto* netHold = SNLScalarNet::create(top, NLName("net_hold"));
  auto* netD = SNLScalarNet::create(top, NLName("net_d"));
  auto* netQ = SNLScalarNet::create(top, NLName("net_q"));

  topIn->setNet(netIn);
  topReset->setNet(netReset);
  topClock->setNet(netClock);
  topOut->setNet(netQ);

  resetInv->getInstTerm(invModel->getScalarTerm(NLName("A")))->setNet(netReset);
  resetInv->getInstTerm(invModel->getScalarTerm(NLName("Y")))->setNet(netResetN);

  loadData->getInstTerm(andModel->getScalarTerm(NLName("A")))->setNet(netReset);
  loadData->getInstTerm(andModel->getScalarTerm(NLName("B")))->setNet(netIn);
  loadData->getInstTerm(andModel->getScalarTerm(NLName("Y")))->setNet(netLoad);

  holdData->getInstTerm(andModel->getScalarTerm(NLName("A")))->setNet(netResetN);
  holdData->getInstTerm(andModel->getScalarTerm(NLName("B")))->setNet(netQ);
  holdData->getInstTerm(andModel->getScalarTerm(NLName("Y")))->setNet(netHold);

  muxOut->getInstTerm(orModel->getScalarTerm(NLName("A")))->setNet(netLoad);
  muxOut->getInstTerm(orModel->getScalarTerm(NLName("B")))->setNet(netHold);
  muxOut->getInstTerm(orModel->getScalarTerm(NLName("Y")))->setNet(netD);

  ff->getInstTerm(NLDB0::getDFFClock())->setNet(netClock);
  ff->getInstTerm(NLDB0::getDFFData())->setNet(netD);
  ff->getInstTerm(NLDB0::getDFFOutput())->setNet(netQ);

  return top;
}

SNLDesign* createResetLoadsInputTwoStageTop(
    NLLibrary* library,
    const std::string& name,
    SNLDesign* invModel,
    SNLDesign* andModel,
    SNLDesign* orModel) {
  auto* top =
      SNLDesign::create(library, SNLDesign::Type::Standard, NLName(name));
  auto* topIn =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("in"));
  auto* topReset =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("rst"));
  auto* topClock =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("clk"));
  auto* topOut =
      SNLScalarTerm::create(top, SNLTerm::Direction::Output, NLName("out"));

  auto* resetInv = SNLInstance::create(top, invModel, NLName("reset_inv"));
  auto* loadData = SNLInstance::create(top, andModel, NLName("load_data"));
  auto* holdData = SNLInstance::create(top, andModel, NLName("hold_data"));
  auto* muxOut = SNLInstance::create(top, orModel, NLName("mux_out"));
  auto* ffHidden = SNLInstance::create(top, NLDB0::getDFF(), NLName("ff_hidden"));
  auto* ffOut = SNLInstance::create(top, NLDB0::getDFF(), NLName("ff_out"));

  auto* netIn = SNLScalarNet::create(top, NLName("net_in"));
  auto* netReset = SNLScalarNet::create(top, NLName("net_rst"));
  auto* netResetN = SNLScalarNet::create(top, NLName("net_rst_n"));
  auto* netClock = SNLScalarNet::create(top, NLName("net_clk"));
  auto* netLoad = SNLScalarNet::create(top, NLName("net_load"));
  auto* netHold = SNLScalarNet::create(top, NLName("net_hold"));
  auto* netHiddenD = SNLScalarNet::create(top, NLName("net_hidden_d"));
  auto* netHiddenQ = SNLScalarNet::create(top, NLName("net_hidden_q"));
  auto* netOutQ = SNLScalarNet::create(top, NLName("net_out_q"));

  topIn->setNet(netIn);
  topReset->setNet(netReset);
  topClock->setNet(netClock);
  topOut->setNet(netOutQ);

  resetInv->getInstTerm(invModel->getScalarTerm(NLName("A")))->setNet(netReset);
  resetInv->getInstTerm(invModel->getScalarTerm(NLName("Y")))->setNet(netResetN);

  loadData->getInstTerm(andModel->getScalarTerm(NLName("A")))->setNet(netReset);
  loadData->getInstTerm(andModel->getScalarTerm(NLName("B")))->setNet(netIn);
  loadData->getInstTerm(andModel->getScalarTerm(NLName("Y")))->setNet(netLoad);

  holdData->getInstTerm(andModel->getScalarTerm(NLName("A")))->setNet(netResetN);
  holdData->getInstTerm(andModel->getScalarTerm(NLName("B")))->setNet(netHiddenQ);
  holdData->getInstTerm(andModel->getScalarTerm(NLName("Y")))->setNet(netHold);

  muxOut->getInstTerm(orModel->getScalarTerm(NLName("A")))->setNet(netLoad);
  muxOut->getInstTerm(orModel->getScalarTerm(NLName("B")))->setNet(netHold);
  muxOut->getInstTerm(orModel->getScalarTerm(NLName("Y")))->setNet(netHiddenD);

  for (auto* ff : {ffHidden, ffOut}) {
    ff->getInstTerm(NLDB0::getDFFClock())->setNet(netClock);
  }
  ffHidden->getInstTerm(NLDB0::getDFFData())->setNet(netHiddenD);
  ffHidden->getInstTerm(NLDB0::getDFFOutput())->setNet(netHiddenQ);
  ffOut->getInstTerm(NLDB0::getDFFData())->setNet(netHiddenQ);
  ffOut->getInstTerm(NLDB0::getDFFOutput())->setNet(netOutQ);

  return top;
}

SNLDesign* createResetLoadsInputShiftPipelineTopWithStages(
    NLLibrary* library,
    const std::string& name,
    SNLDesign* invModel,
    SNLDesign* andModel,
    SNLDesign* orModel,
    size_t stages) {
  auto* top =
      SNLDesign::create(library, SNLDesign::Type::Standard, NLName(name));
  auto* topIn =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("in"));
  auto* topReset =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("rst"));
  auto* topClock =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("clk"));
  auto* topOut =
      SNLScalarTerm::create(top, SNLTerm::Direction::Output, NLName("out"));

  auto* resetInv = SNLInstance::create(top, invModel, NLName("reset_inv"));
  auto* loadData = SNLInstance::create(top, andModel, NLName("load_data"));
  auto* holdData = SNLInstance::create(top, andModel, NLName("hold_data"));
  auto* muxOut = SNLInstance::create(top, orModel, NLName("mux_out"));

  std::vector<SNLInstance*> flops;
  flops.reserve(stages);
  for (size_t i = 0; i < stages; ++i) {
    flops.push_back(
        SNLInstance::create(top, NLDB0::getDFF(), NLName("ff" + std::to_string(i))));
  }

  auto* netIn = SNLScalarNet::create(top, NLName("net_in"));
  auto* netReset = SNLScalarNet::create(top, NLName("net_rst"));
  auto* netResetN = SNLScalarNet::create(top, NLName("net_rst_n"));
  auto* netClock = SNLScalarNet::create(top, NLName("net_clk"));
  auto* netLoad = SNLScalarNet::create(top, NLName("net_load"));
  auto* netHold = SNLScalarNet::create(top, NLName("net_hold"));
  auto* netLastD = SNLScalarNet::create(top, NLName("net_last_d"));
  std::vector<SNLScalarNet*> stateNets;
  stateNets.reserve(stages);
  for (size_t i = 0; i < stages; ++i) {
    stateNets.push_back(
        SNLScalarNet::create(top, NLName("net_q" + std::to_string(i))));
  }

  topIn->setNet(netIn);
  topReset->setNet(netReset);
  topClock->setNet(netClock);
  topOut->setNet(stateNets.front());

  resetInv->getInstTerm(invModel->getScalarTerm(NLName("A")))->setNet(netReset);
  resetInv->getInstTerm(invModel->getScalarTerm(NLName("Y")))->setNet(netResetN);

  loadData->getInstTerm(andModel->getScalarTerm(NLName("A")))->setNet(netReset);
  loadData->getInstTerm(andModel->getScalarTerm(NLName("B")))->setNet(netIn);
  loadData->getInstTerm(andModel->getScalarTerm(NLName("Y")))->setNet(netLoad);

  holdData->getInstTerm(andModel->getScalarTerm(NLName("A")))->setNet(netResetN);
  holdData->getInstTerm(andModel->getScalarTerm(NLName("B")))->setNet(stateNets.back());
  holdData->getInstTerm(andModel->getScalarTerm(NLName("Y")))->setNet(netHold);

  muxOut->getInstTerm(orModel->getScalarTerm(NLName("A")))->setNet(netLoad);
  muxOut->getInstTerm(orModel->getScalarTerm(NLName("B")))->setNet(netHold);
  muxOut->getInstTerm(orModel->getScalarTerm(NLName("Y")))->setNet(netLastD);

  for (auto* ff : flops) {
    ff->getInstTerm(NLDB0::getDFFClock())->setNet(netClock);
  }
  for (size_t i = 0; i + 1 < stages; ++i) {
    flops[i]->getInstTerm(NLDB0::getDFFData())->setNet(stateNets[i + 1]);
    flops[i]->getInstTerm(NLDB0::getDFFOutput())->setNet(stateNets[i]);
  }
  flops.back()->getInstTerm(NLDB0::getDFFData())->setNet(netLastD);
  flops.back()->getInstTerm(NLDB0::getDFFOutput())->setNet(stateNets.back());

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
  EXPECT_EQ(result.bound, 0u);
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

TEST_F(SequentialEquivalenceStrategyTests,
       ResetInitializedEquivalentPipelineIsProved) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* top0 = createResetInitializedPipelineTop(library, "top0", false);
  auto* top1 = createResetInitializedPipelineTop(library, "top1", false);

  SequentialEquivalenceStrategy strategy(top0, top1);
  const auto result = strategy.run(3);

  EXPECT_EQ(result.status, SequentialEquivalenceStatus::Equivalent);
  EXPECT_EQ(result.bound, 1u);
}

TEST_F(SequentialEquivalenceStrategyTests,
       ResetInitializedRenamedPipelineNeedsThreeStepSecProof) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* top0 = createResetInitializedPipelineTop(
      library, "top0", false, {"ff0", "ff1", "ff2"});
  auto* top1 = createResetInitializedPipelineTop(
      library, "top1", false, {"state_a", "state_b", "state_c"});

  SequentialEquivalenceStrategy strategy(top0, top1);
  const auto result = strategy.run(4);

  EXPECT_EQ(result.status, SequentialEquivalenceStatus::Equivalent);
  EXPECT_EQ(result.bound, 3u);
}

TEST_F(SequentialEquivalenceStrategyTests,
       ResetBootstrapEquivalentPipelineIsProved) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* primitives =
      NLLibrary::create(db, NLLibrary::Type::Primitives, NLName("prims"));
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* invModel = createInvModel(primitives);
  auto* andModel = createAnd2Model(primitives);
  auto* top0 =
      createBootstrapPipelineTop(library, "top0", invModel, andModel);
  auto* top1 =
      createBootstrapPipelineTop(library, "top1", invModel, andModel);

  SequentialEquivalenceStrategy strategy(top0, top1);
  const auto result = strategy.run(3);

  EXPECT_EQ(result.status, SequentialEquivalenceStatus::Equivalent);
  EXPECT_LE(result.bound, 3u);
}

TEST_F(SequentialEquivalenceStrategyTests,
       ResetBootstrapCanAnchorEqualStatesWithoutConstantValues) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* primitives =
      NLLibrary::create(db, NLLibrary::Type::Primitives, NLName("prims"));
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* invModel = createInvModel(primitives);
  auto* andModel = createAnd2Model(primitives);
  auto* orModel = createOr2Model(primitives);
  auto* top0 =
      createResetLoadsInputTop(library, "top0", invModel, andModel, orModel);
  auto* top1 =
      createResetLoadsInputTop(library, "top1", invModel, andModel, orModel);

  SequentialEquivalenceStrategy strategy(top0, top1);
  const auto result = strategy.run(3);

  EXPECT_EQ(result.status, SequentialEquivalenceStatus::Equivalent);
  EXPECT_LE(result.bound, 3u);
}

TEST_F(SequentialEquivalenceStrategyTests,
       ResetBootstrapCanAnchorHiddenEqualStatesWithoutConstantValues) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* primitives =
      NLLibrary::create(db, NLLibrary::Type::Primitives, NLName("prims"));
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* invModel = createInvModel(primitives);
  auto* andModel = createAnd2Model(primitives);
  auto* orModel = createOr2Model(primitives);
  auto* top0 = createResetLoadsInputTwoStageTop(
      library, "top0", invModel, andModel, orModel);
  auto* top1 = createResetLoadsInputTwoStageTop(
      library, "top1", invModel, andModel, orModel);

  SequentialEquivalenceStrategy strategy(top0, top1);
  const auto result = strategy.run(3);

  EXPECT_EQ(result.status, SequentialEquivalenceStatus::Equivalent);
  EXPECT_LE(result.bound, 3u);
}

TEST_F(SequentialEquivalenceStrategyTests,
       ResetBootstrapAutomaticallyExtendsForHiddenShiftPipelines) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* primitives =
      NLLibrary::create(db, NLLibrary::Type::Primitives, NLName("prims"));
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* invModel = createInvModel(primitives);
  auto* andModel = createAnd2Model(primitives);
  auto* orModel = createOr2Model(primitives);
  auto* top0 = createResetLoadsInputShiftPipelineTopWithStages(
      library, "top0", invModel, andModel, orModel, 20);
  auto* top1 = createResetLoadsInputShiftPipelineTopWithStages(
      library, "top1", invModel, andModel, orModel, 20);

  SequentialEquivalenceStrategy strategy(top0, top1);
  const auto result = strategy.run(1);

  EXPECT_EQ(result.status, SequentialEquivalenceStatus::Equivalent);
  EXPECT_EQ(result.bound, 1u);
}

TEST_F(SequentialEquivalenceStrategyTests,
       ResetBootstrapLongEquivalentPipelineStillClosesAtSmallK) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* primitives =
      NLLibrary::create(db, NLLibrary::Type::Primitives, NLName("prims"));
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* invModel = createInvModel(primitives);
  auto* andModel = createAnd2Model(primitives);
  auto* top0 =
      createBootstrapPipelineTopWithStages(library, "top0", invModel, andModel, 12);
  auto* top1 =
      createBootstrapPipelineTopWithStages(library, "top1", invModel, andModel, 12);

  SequentialEquivalenceStrategy strategy(top0, top1);
  const auto result = strategy.run(3);

  EXPECT_EQ(result.status, SequentialEquivalenceStatus::Equivalent);
  EXPECT_LE(result.bound, 3u);
}

TEST_F(SequentialEquivalenceStrategyTests,
       SynthesizedResetInferencePropagatesThroughLongBootstrapPipeline) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* primitives =
      NLLibrary::create(db, NLLibrary::Type::Primitives, NLName("prims"));
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* invModel = createInvModel(primitives);
  auto* andModel = createAnd2Model(primitives);
  auto* top = createBootstrapPipelineTopWithStages(
      library, "top", invModel, andModel, 12);

  const auto model = SequentialDesignModel::extract(top);

  EXPECT_FALSE(model.hasUnsupportedFeatures());
  EXPECT_EQ(model.initialStateValueByKey.size(), model.stateBits.size());
}

TEST_F(SequentialEquivalenceStrategyTests,
       SynthesizedResetInferenceScalesPastLargeStateCutoff) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* primitives =
      NLLibrary::create(db, NLLibrary::Type::Primitives, NLName("prims"));
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* invModel = createInvModel(primitives);
  auto* andModel = createAnd2Model(primitives);
  auto* top = createBootstrapPipelineTopWithStages(
      library, "top", invModel, andModel, 2200);

  const auto model = SequentialDesignModel::extract(top);

  EXPECT_FALSE(model.hasUnsupportedFeatures());
  EXPECT_EQ(model.initialStateValueByKey.size(), model.stateBits.size());
}

TEST_F(SequentialEquivalenceStrategyTests,
       ResetBootstrapInductionProvesPostResetInvariant) {
  KInductionProblem problem;
  problem.environmentInputNames = {"rst"};
  problem.observedOutputNames = {"out"};
  problem.inputSymbols = {2};
  problem.resetBootstrapInputs = {{2, true}};
  problem.bootstrapStateEqualityPairs = {{3, 4}};
  problem.inductiveStateEqualityPairs = {{3, 4}};
  problem.state0Symbols = {3};
  problem.state1Symbols = {4};
  problem.allSymbols = {2, 3, 4};
  problem.observedOutputExprs0 = {BoolExpr::Var(3)};
  problem.observedOutputExprs1 = {BoolExpr::Var(4)};
  problem.transitions0 = {{3, BoolExpr::Var(3)}};
  problem.transitions1 = {{4, BoolExpr::Var(4)}};
  problem.property =
      BoolExpr::Not(BoolExpr::Xor(BoolExpr::Var(3), BoolExpr::Var(4)));
  problem.bad = BoolExpr::Xor(BoolExpr::Var(3), BoolExpr::Var(4));
  problem.description = "bootstrap induction regression";

  KInductionEngine engine(problem, KEPLER_FORMAL::Config::SolverType::KISSAT);
  const auto result = engine.run(3);

  EXPECT_EQ(result.status, KInductionStatus::Equivalent);
  EXPECT_LE(result.bound, 3u);
}

TEST_F(SequentialEquivalenceStrategyTests,
       StrongerInductionInvariantClosesOutputOnlySecAtOneStep) {
  KInductionProblem problem;
  problem.observedOutputNames = {"out"};
  problem.state0Symbols = {2, 3};
  problem.state1Symbols = {4, 5};
  problem.allSymbols = {2, 3, 4, 5};
  problem.observedOutputExprs0 = {BoolExpr::Var(2)};
  problem.observedOutputExprs1 = {BoolExpr::Var(4)};
  problem.transitions0 = {{2, BoolExpr::Var(3)}, {3, BoolExpr::Var(3)}};
  problem.transitions1 = {{4, BoolExpr::Var(5)}, {5, BoolExpr::Var(5)}};
  problem.initialCondition = BoolExpr::And(
      BoolExpr::And(BoolExpr::Not(BoolExpr::Var(2)), BoolExpr::Not(BoolExpr::Var(3))),
      BoolExpr::And(BoolExpr::Not(BoolExpr::Var(4)), BoolExpr::Not(BoolExpr::Var(5))));
  problem.initializedStateCount = 4;
  problem.totalStateCount = 4;
  problem.property =
      BoolExpr::Not(BoolExpr::Xor(BoolExpr::Var(2), BoolExpr::Var(4)));
  problem.bad = BoolExpr::Xor(BoolExpr::Var(2), BoolExpr::Var(4));
  problem.description = "output-only SEC needs a stronger invariant";

  KInductionEngine withoutInvariant(
      problem, KEPLER_FORMAL::Config::SolverType::KISSAT);
  const auto withoutInvariantResult = withoutInvariant.run(1);
  EXPECT_EQ(withoutInvariantResult.status, KInductionStatus::Inconclusive);

  problem.inductionProperty = BoolExpr::And(
      BoolExpr::Not(BoolExpr::Xor(BoolExpr::Var(2), BoolExpr::Var(4))),
      BoolExpr::Not(BoolExpr::Xor(BoolExpr::Var(3), BoolExpr::Var(5))));
  problem.inductionBad = BoolExpr::Not(problem.inductionProperty);

  KInductionEngine withInvariant(
      problem, KEPLER_FORMAL::Config::SolverType::KISSAT);
  const auto withInvariantResult = withInvariant.run(1);
  EXPECT_EQ(withInvariantResult.status, KInductionStatus::Equivalent);
  EXPECT_EQ(withInvariantResult.bound, 1u);
}
