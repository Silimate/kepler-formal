// Copyright 2024-2026 keplertech.io
// SPDX-License-Identifier: GPL-3.0-only

#include <gtest/gtest.h>

#include <cstdlib>
#include <optional>

#include "BoolExprCache.h"
#include "DNL.h"
#include "NLDB0.h"
#include "NLUniverse.h"
#include "SNLDesign.h"
#include "SNLDesignModeling.h"
#include "SNLInstance.h"
#include "SNLScalarNet.h"
#include "SNLScalarTerm.h"
#include "common/BoolExprUtils.h"
#include "kinduction/BaseCaseSolver.h"
#include "kinduction/KInductionEngine.h"
#include "kinduction/InductionStepSolver.h"
#include "model/SequentialDesignModel.h"
#include "proof/ExactInterpolationEngine.h"
#include "proof/IC3Engine.h"
#include "strategy/ReachableStateInvariant.h"
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

class ScopedEnvVar {
 public:
  ScopedEnvVar(const char* name, const char* value)
      : name_(name) {
    if (const char* current = std::getenv(name_); current != nullptr) {
      previousValue_ = current;
    }
    setenv(name_, value, 1);
  }

  ~ScopedEnvVar() {
    if (previousValue_.has_value()) {
      setenv(name_, previousValue_->c_str(), 1);
    } else {
      unsetenv(name_);
    }
  }

 private:
  const char* name_;
  std::optional<std::string> previousValue_;
};

SignalKey makeSignalKey(const std::string& name) {
  SignalKey key;
  key.first.push_back(stableSignalKeyNameID(name));
  key.second.push_back(stableSignalKeyNameID(name));
  return key;
}

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
    const std::string& inputName,
    const std::string& outputName,
    const std::string& ffName) {
  auto* top =
      SNLDesign::create(library, SNLDesign::Type::Standard, NLName(name));
  auto* topIn =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName(inputName));
  auto* topClock =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("clk"));
  auto* topOut =
      SNLScalarTerm::create(top, SNLTerm::Direction::Output, NLName(outputName));

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

SNLDesign* createDffTop(
    NLLibrary* library,
    const std::string& name,
    SNLDesign* invModel,
    bool invertData,
    bool invertOutput,
    const std::string& ffName = "ff0") {
  return createDffTop(
      library, name, invModel, invertData, invertOutput, "in", "out", ffName);
}

SNLDesign* createNamedOutputDffTop(
    NLLibrary* library,
    const std::string& name,
    SNLDesign* invModel,
    const std::string& outputName) {
  return createDffTop(
      library, name, invModel, false, false, "in", outputName, "ff0");
}

SNLDesign* createNamedInputDffTop(
    NLLibrary* library,
    const std::string& name,
    SNLDesign* invModel,
    const std::string& inputName) {
  return createDffTop(
      library, name, invModel, false, false, inputName, "out", "ff0");
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

SNLDesign* createResetInitializedShiftPipelineTopWithStages(
    NLLibrary* library,
    const std::string& name,
    size_t stages);

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

SNLDesign* createResetInitializedShiftPipelineTopWithStages(
    NLLibrary* library,
    const std::string& name,
    size_t stages) {
  if (stages == 0) {
    throw std::invalid_argument(
        "createResetInitializedShiftPipelineTopWithStages expects at least one stage");
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

  auto* netIn = SNLScalarNet::create(top, NLName("net_in"));
  auto* netResetN = SNLScalarNet::create(top, NLName("net_rst_n"));
  auto* netClock = SNLScalarNet::create(top, NLName("net_clk"));
  std::vector<SNLScalarNet*> stageNets;
  stageNets.reserve(stages);
  for (size_t i = 0; i < stages; ++i) {
    stageNets.push_back(
        SNLScalarNet::create(top, NLName("net_q" + std::to_string(i))));
  }

  topIn->setNet(netIn);
  topResetN->setNet(netResetN);
  topClock->setNet(netClock);
  topOut->setNet(stageNets.front());

  for (size_t i = 0; i < stages; ++i) {
    auto* ff = SNLInstance::create(
        top, NLDB0::getDFFRN(), NLName("ff" + std::to_string(i)));
    ff->getInstTerm(NLDB0::getDFFRNClock())->setNet(netClock);
    ff->getInstTerm(NLDB0::getDFFRNResetN())->setNet(netResetN);
    ff->getInstTerm(NLDB0::getDFFRNData())->setNet(
        i + 1 == stages ? netIn : stageNets[i + 1]);
    ff->getInstTerm(NLDB0::getDFFRNOutput())->setNet(stageNets[i]);
  }

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

SNLDesign* createNamedComplementSequentialModel(
    NLLibrary* library,
    const std::string& name,
    const std::string& primaryPinName,
    const std::string& complementPinName) {
  auto* model =
      SNLDesign::create(library, SNLDesign::Type::Primitive, NLName(name));
  auto* data =
      SNLScalarTerm::create(model, SNLTerm::Direction::Input, NLName("D"));
  auto* clock =
      SNLScalarTerm::create(model, SNLTerm::Direction::Input, NLName("CK"));
  auto* primary = SNLScalarTerm::create(
      model, SNLTerm::Direction::Output, NLName(primaryPinName));
  auto* complement = SNLScalarTerm::create(
      model, SNLTerm::Direction::Output, NLName(complementPinName));
  SNLDesignModeling::addInputsToClockArcs({data}, clock);
  SNLDesignModeling::addClockToOutputsArcs(clock, {primary, complement});
  return model;
}

SNLDesign* createSetOnlySequentialModel(NLLibrary* library,
                                        const std::string& name) {
  auto* model =
      SNLDesign::create(library, SNLDesign::Type::Primitive, NLName(name));
  auto* data =
      SNLScalarTerm::create(model, SNLTerm::Direction::Input, NLName("D"));
  auto* set =
      SNLScalarTerm::create(model, SNLTerm::Direction::Input, NLName("S"));
  auto* clock =
      SNLScalarTerm::create(model, SNLTerm::Direction::Input, NLName("CK"));
  auto* output =
      SNLScalarTerm::create(model, SNLTerm::Direction::Output, NLName("Q"));
  SNLDesignModeling::addInputsToClockArcs({data, set}, clock);
  SNLDesignModeling::addClockToOutputsArcs(clock, {output});
  return model;
}

SNLDesign* createNoDataSequentialModel(NLLibrary* library,
                                       const std::string& name) {
  auto* model =
      SNLDesign::create(library, SNLDesign::Type::Primitive, NLName(name));
  auto* clock =
      SNLScalarTerm::create(model, SNLTerm::Direction::Input, NLName("CK"));
  auto* output =
      SNLScalarTerm::create(model, SNLTerm::Direction::Output, NLName("Q"));
  SNLDesignModeling::addClockToOutputsArcs(clock, {output});
  return model;
}

SNLDesign* createNamedComplementSetSequentialModel(
    NLLibrary* library,
    const std::string& name,
    const std::string& primaryPinName,
    const std::string& complementPinName) {
  auto* model =
      SNLDesign::create(library, SNLDesign::Type::Primitive, NLName(name));
  auto* data =
      SNLScalarTerm::create(model, SNLTerm::Direction::Input, NLName("D"));
  auto* set =
      SNLScalarTerm::create(model, SNLTerm::Direction::Input, NLName("S"));
  auto* clock =
      SNLScalarTerm::create(model, SNLTerm::Direction::Input, NLName("CK"));
  auto* primary = SNLScalarTerm::create(
      model, SNLTerm::Direction::Output, NLName(primaryPinName));
  auto* complement = SNLScalarTerm::create(
      model, SNLTerm::Direction::Output, NLName(complementPinName));
  SNLDesignModeling::addInputsToClockArcs({data, set}, clock);
  SNLDesignModeling::addClockToOutputsArcs(clock, {primary, complement});
  return model;
}

SNLDesign* createSequentialOutputPairTop(
    NLLibrary* library,
    const std::string& name,
    SNLDesign* sequentialModel,
    const std::string& primaryPinName,
    const std::string& secondaryPinName) {
  auto* top =
      SNLDesign::create(library, SNLDesign::Type::Standard, NLName(name));
  auto* topIn =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("in"));
  auto* topClock =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("clk"));
  auto* topPrimary =
      SNLScalarTerm::create(top, SNLTerm::Direction::Output, NLName("out_primary"));
  auto* topSecondary = SNLScalarTerm::create(
      top, SNLTerm::Direction::Output, NLName("out_secondary"));

  auto* seq = SNLInstance::create(top, sequentialModel, NLName("ff0"));
  auto* netIn = SNLScalarNet::create(top, NLName("net_in"));
  auto* netClock = SNLScalarNet::create(top, NLName("net_clk"));
  auto* netPrimary = SNLScalarNet::create(top, NLName("net_primary"));
  auto* netSecondary = SNLScalarNet::create(top, NLName("net_secondary"));

  topIn->setNet(netIn);
  topClock->setNet(netClock);
  topPrimary->setNet(netPrimary);
  topSecondary->setNet(netSecondary);

  seq->getInstTerm(sequentialModel->getScalarTerm(NLName("D")))->setNet(netIn);
  seq->getInstTerm(sequentialModel->getScalarTerm(NLName("CK")))->setNet(netClock);
  seq->getInstTerm(sequentialModel->getScalarTerm(NLName(primaryPinName)))->setNet(
      netPrimary);
  seq->getInstTerm(sequentialModel->getScalarTerm(NLName(secondaryPinName)))->setNet(
      netSecondary);

  return top;
}

SNLDesign* createSetOnlySequentialTop(
    NLLibrary* library,
    const std::string& name,
    SNLDesign* sequentialModel) {
  auto* top =
      SNLDesign::create(library, SNLDesign::Type::Standard, NLName(name));
  auto* topIn =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("in"));
  auto* topSet =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("set"));
  auto* topClock =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("clk"));
  auto* topOut =
      SNLScalarTerm::create(top, SNLTerm::Direction::Output, NLName("out"));

  auto* seq = SNLInstance::create(top, sequentialModel, NLName("ff0"));
  auto* netIn = SNLScalarNet::create(top, NLName("net_in"));
  auto* netSet = SNLScalarNet::create(top, NLName("net_set"));
  auto* netClock = SNLScalarNet::create(top, NLName("net_clk"));
  auto* netOut = SNLScalarNet::create(top, NLName("net_out"));

  topIn->setNet(netIn);
  topSet->setNet(netSet);
  topClock->setNet(netClock);
  topOut->setNet(netOut);

  seq->getInstTerm(sequentialModel->getScalarTerm(NLName("D")))->setNet(netIn);
  seq->getInstTerm(sequentialModel->getScalarTerm(NLName("S")))->setNet(netSet);
  seq->getInstTerm(sequentialModel->getScalarTerm(NLName("CK")))->setNet(netClock);
  seq->getInstTerm(sequentialModel->getScalarTerm(NLName("Q")))->setNet(netOut);

  return top;
}

SNLDesign* createNoDataSequentialTop(
    NLLibrary* library,
    const std::string& name,
    SNLDesign* sequentialModel) {
  auto* top =
      SNLDesign::create(library, SNLDesign::Type::Standard, NLName(name));
  auto* topClock =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("clk"));
  auto* topOut =
      SNLScalarTerm::create(top, SNLTerm::Direction::Output, NLName("out"));

  auto* seq = SNLInstance::create(top, sequentialModel, NLName("ff0"));
  auto* netClock = SNLScalarNet::create(top, NLName("net_clk"));
  auto* netOut = SNLScalarNet::create(top, NLName("net_out"));

  topClock->setNet(netClock);
  topOut->setNet(netOut);

  seq->getInstTerm(sequentialModel->getScalarTerm(NLName("CK")))->setNet(netClock);
  seq->getInstTerm(sequentialModel->getScalarTerm(NLName("Q")))->setNet(netOut);

  return top;
}

SNLDesign* createDffreTop(
    NLLibrary* library,
    const std::string& name) {
  auto* top =
      SNLDesign::create(library, SNLDesign::Type::Standard, NLName(name));
  auto* topIn =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("in"));
  auto* topEnable =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("en"));
  auto* topReset =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("rst"));
  auto* topClock =
      SNLScalarTerm::create(top, SNLTerm::Direction::Input, NLName("clk"));
  auto* topOut =
      SNLScalarTerm::create(top, SNLTerm::Direction::Output, NLName("out"));

  auto* ff = SNLInstance::create(top, NLDB0::getDFFRE(), NLName("ff0"));
  auto* netIn = SNLScalarNet::create(top, NLName("net_in"));
  auto* netEnable = SNLScalarNet::create(top, NLName("net_en"));
  auto* netReset = SNLScalarNet::create(top, NLName("net_rst"));
  auto* netClock = SNLScalarNet::create(top, NLName("net_clk"));
  auto* netOut = SNLScalarNet::create(top, NLName("net_out"));

  topIn->setNet(netIn);
  topEnable->setNet(netEnable);
  topReset->setNet(netReset);
  topClock->setNet(netClock);
  topOut->setNet(netOut);

  ff->getInstTerm(NLDB0::getDFFREData())->setNet(netIn);
  ff->getInstTerm(NLDB0::getDFFREEnable())->setNet(netEnable);
  ff->getInstTerm(NLDB0::getDFFREReset())->setNet(netReset);
  ff->getInstTerm(NLDB0::getDFFREClock())->setNet(netClock);
  ff->getInstTerm(NLDB0::getDFFREOutput())->setNet(netOut);

  return top;
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
       RenamedStatePipelineIsProvedWithoutNameBasedStateMatching) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* top0 = createResetInitializedPipelineTop(
      library, "top0", false, {"left0", "left1", "left2"});
  auto* top1 = createResetInitializedPipelineTop(
      library, "top1", false, {"right0", "right1", "right2"});

  SequentialEquivalenceStrategy strategy(top0, top1);
  const auto result = strategy.run(3);

  EXPECT_EQ(result.status, SequentialEquivalenceStatus::Equivalent);
  EXPECT_LE(result.bound, 3u);
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
       ResetInitializedRenamedPipelineClosesWithinThreeStepSecProof) {
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
  EXPECT_LE(result.bound, 3u);
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
       StructuralInvariantHandlesMismatchedStateCountsWithoutOscillation) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* top0 = createResetInitializedShiftPipelineTopWithStages(
      library, "top0", 5);
  auto* top1 = createResetInitializedShiftPipelineTopWithStages(
      library, "top1", 1);

  SequentialEquivalenceStrategy strategy(top0, top1);
  const auto result = strategy.run(6);

  EXPECT_EQ(result.status, SequentialEquivalenceStatus::Different);
  EXPECT_EQ(result.bound, 1u);
  EXPECT_LE(result.bound, 6u);
}

TEST_F(SequentialEquivalenceStrategyTests,
       ReachableStateInvariantUsesExplicitInitialCompatibilityWithoutReset) {
  const SignalKey state0A = makeSignalKey("state0A");
  const SignalKey state0B = makeSignalKey("state0B");
  const SignalKey state1A = makeSignalKey("state1A");
  const SignalKey state1B = makeSignalKey("state1B");

  SequentialDesignModel model0;
  model0.stateBits = {state0A, state0B};
  model0.initialStateValueByKey.emplace(state0A, false);
  model0.initialStateValueByKey.emplace(state0B, true);

  SequentialDesignModel model1;
  model1.stateBits = {state1A, state1B};
  model1.initialStateValueByKey.emplace(state1A, false);
  model1.initialStateValueByKey.emplace(state1B, false);

  AlignedSignals candidateStates;
  candidateStates.names = {"state_a", "state_b"};
  candidateStates.keys0 = {state0A, state0B};
  candidateStates.keys1 = {state1A, state1B};

  const auto invariant =
      buildReachableStateInvariant(model0, model1, AlignedSignals{}, candidateStates);

  EXPECT_EQ(invariant.bootstrapCycles, 0u);
  ASSERT_EQ(invariant.initialStateCorrespondence.names.size(), 1u);
  EXPECT_EQ(invariant.initialStateCorrespondence.names[0], "state_a");
  ASSERT_EQ(invariant.anchoredStateEqualities.names.size(), 1u);
  EXPECT_EQ(invariant.anchoredStateEqualities.names[0], "state_a");
  EXPECT_TRUE(invariant.bootstrapValues0.empty());
  EXPECT_TRUE(invariant.bootstrapValues1.empty());
}

TEST_F(SequentialEquivalenceStrategyTests,
       ReachableStateInvariantSkipsBootstrapWhenResetAndInitialStateAreComplete) {
  const SignalKey rst0 = makeSignalKey("rst0");
  const SignalKey rst1 = makeSignalKey("rst1");
  const SignalKey state0 = makeSignalKey("state0");
  const SignalKey state1 = makeSignalKey("state1");

  SequentialDesignModel model0;
  model0.environmentInputs = {rst0};
  model0.stateBits = {state0};
  model0.inputVarByKey.emplace(rst0, 2);
  model0.displayNameByKey.emplace(rst0, "rst");
  model0.initialStateValueByKey.emplace(state0, false);

  SequentialDesignModel model1;
  model1.environmentInputs = {rst1};
  model1.stateBits = {state1};
  model1.inputVarByKey.emplace(rst1, 3);
  model1.displayNameByKey.emplace(rst1, "rst");
  model1.initialStateValueByKey.emplace(state1, false);

  AlignedSignals alignedInputs;
  alignedInputs.names = {"rst"};
  alignedInputs.keys0 = {rst0};
  alignedInputs.keys1 = {rst1};

  AlignedSignals candidateStates;
  candidateStates.names = {"state"};
  candidateStates.keys0 = {state0};
  candidateStates.keys1 = {state1};

  const auto invariant =
      buildReachableStateInvariant(model0, model1, alignedInputs, candidateStates);

  EXPECT_EQ(invariant.bootstrapCycles, 0u);
  ASSERT_EQ(invariant.initialStateCorrespondence.names.size(), 1u);
  EXPECT_EQ(invariant.initialStateCorrespondence.names[0], "state");
  ASSERT_EQ(invariant.anchoredStateEqualities.names.size(), 1u);
  EXPECT_EQ(invariant.anchoredStateEqualities.names[0], "state");
  EXPECT_TRUE(invariant.bootstrapValues0.empty());
  EXPECT_TRUE(invariant.bootstrapValues1.empty());
}

TEST_F(SequentialEquivalenceStrategyTests,
       ReachableStateInvariantDerivesBootstrapValuesAndAnchorsFromReset) {
  const SignalKey rst0 = makeSignalKey("rst0");
  const SignalKey rst1 = makeSignalKey("rst1");
  const SignalKey state0 = makeSignalKey("state0");
  const SignalKey state1 = makeSignalKey("state1");

  SequentialDesignModel model0;
  model0.environmentInputs = {rst0};
  model0.stateBits = {state0};
  model0.inputVarByKey.emplace(rst0, 2);
  model0.displayNameByKey.emplace(rst0, "rst");
  model0.nextStateExprByStateKey.emplace(state0, BoolExpr::Not(BoolExpr::Var(2)));

  SequentialDesignModel model1;
  model1.environmentInputs = {rst1};
  model1.stateBits = {state1};
  model1.inputVarByKey.emplace(rst1, 3);
  model1.displayNameByKey.emplace(rst1, "rst");
  model1.nextStateExprByStateKey.emplace(state1, BoolExpr::Not(BoolExpr::Var(3)));

  AlignedSignals alignedInputs;
  alignedInputs.names = {"rst"};
  alignedInputs.keys0 = {rst0};
  alignedInputs.keys1 = {rst1};

  AlignedSignals candidateStates;
  candidateStates.names = {"state"};
  candidateStates.keys0 = {state0};
  candidateStates.keys1 = {state1};

  const auto invariant =
      buildReachableStateInvariant(model0, model1, alignedInputs, candidateStates);

  EXPECT_EQ(invariant.bootstrapCycles, 3u);
  ASSERT_EQ(invariant.initialStateCorrespondence.names.size(), 1u);
  EXPECT_EQ(invariant.initialStateCorrespondence.names[0], "state");
  ASSERT_EQ(invariant.anchoredStateEqualities.names.size(), 1u);
  EXPECT_EQ(invariant.anchoredStateEqualities.names[0], "state");
  ASSERT_EQ(invariant.bootstrapValues0.size(), 1u);
  EXPECT_FALSE(invariant.bootstrapValues0.at(state0));
  ASSERT_EQ(invariant.bootstrapValues1.size(), 1u);
  EXPECT_FALSE(invariant.bootstrapValues1.at(state1));
}

TEST_F(SequentialEquivalenceStrategyTests,
       ReachableStateInvariantBootstrapRecoversEqualitiesAfterMismatchedInitialValues) {
  const SignalKey rst0 = makeSignalKey("rst0");
  const SignalKey rst1 = makeSignalKey("rst1");
  const SignalKey state0 = makeSignalKey("state0");
  const SignalKey state1 = makeSignalKey("state1");
  const SignalKey shadow0 = makeSignalKey("shadow0");
  const SignalKey shadow1 = makeSignalKey("shadow1");

  SequentialDesignModel model0;
  model0.environmentInputs = {rst0};
  model0.stateBits = {state0, shadow0};
  model0.inputVarByKey.emplace(rst0, 2);
  model0.inputVarByKey.emplace(state0, 3);
  model0.inputVarByKey.emplace(shadow0, 6);
  model0.displayNameByKey.emplace(rst0, "rst");
  model0.initialStateValueByKey.emplace(state0, false);
  model0.nextStateExprByStateKey.emplace(state0, BoolExpr::Not(BoolExpr::Var(2)));
  model0.nextStateExprByStateKey.emplace(shadow0, BoolExpr::Var(6));

  SequentialDesignModel model1;
  model1.environmentInputs = {rst1};
  model1.stateBits = {state1, shadow1};
  model1.inputVarByKey.emplace(rst1, 4);
  model1.inputVarByKey.emplace(state1, 5);
  model1.inputVarByKey.emplace(shadow1, 7);
  model1.displayNameByKey.emplace(rst1, "rst");
  model1.initialStateValueByKey.emplace(state1, true);
  model1.nextStateExprByStateKey.emplace(state1, BoolExpr::Not(BoolExpr::Var(4)));
  model1.nextStateExprByStateKey.emplace(shadow1, BoolExpr::Var(7));

  AlignedSignals alignedInputs;
  alignedInputs.names = {"rst"};
  alignedInputs.keys0 = {rst0};
  alignedInputs.keys1 = {rst1};

  AlignedSignals candidateStates;
  candidateStates.names = {"state"};
  candidateStates.keys0 = {state0};
  candidateStates.keys1 = {state1};

  ScopedEnvVar secDiag("KEPLER_SEC_DIAG", "1");
  testing::internal::CaptureStderr();
  const auto invariant = buildReachableStateInvariant(
      model0, model1, alignedInputs, candidateStates, true);
  const std::string stderrOutput = testing::internal::GetCapturedStderr();

  EXPECT_EQ(invariant.bootstrapCycles, 3u);
  EXPECT_TRUE(invariant.initialStateCorrespondence.names.empty());
  ASSERT_EQ(invariant.anchoredStateEqualities.names.size(), 1u);
  EXPECT_EQ(invariant.anchoredStateEqualities.names[0], "state");
  ASSERT_EQ(invariant.bootstrapValues0.size(), 1u);
  EXPECT_FALSE(invariant.bootstrapValues0.at(state0));
  ASSERT_EQ(invariant.bootstrapValues1.size(), 1u);
  EXPECT_FALSE(invariant.bootstrapValues1.at(state1));
  EXPECT_NE(stderrOutput.find("SEC diag: bootstrap step 1"), std::string::npos);
}

TEST_F(SequentialEquivalenceStrategyTests,
       BoolExprRemapThrowsOnMissingVariableMapping) {
  auto* expr = BoolExpr::And(BoolExpr::Var(2), BoolExpr::Var(3));

  EXPECT_THROW(
      static_cast<void>(remapBoolExprVariables(expr, {{2, 10}})),
      std::runtime_error);
}

TEST_F(SequentialEquivalenceStrategyTests,
       BoolExprSubstitutionRewritesAssignedVariablesAndKeepsOthers) {
  auto* expr = BoolExpr::And(BoolExpr::Var(2), BoolExpr::Not(BoolExpr::Var(3)));
  auto* substituted = substituteBoolExprVariables(expr, {{2, true}, {3, false}});

  EXPECT_TRUE(substituted->evaluate({}));
  EXPECT_EQ(substituted->getOp(), KEPLER_FORMAL::Op::VAR);
  EXPECT_EQ(substituted->getId(), 1u);
}

TEST_F(SequentialEquivalenceStrategyTests,
       BaseCaseSolverFindsCombinationalCounterexampleAtFrameZero) {
  KInductionProblem problem;
  problem.environmentInputNames = {"in"};
  problem.observedOutputNames = {"out"};
  problem.inputSymbols = {2};
  problem.allSymbols = {2};
  problem.observedOutputExprs0 = {BoolExpr::Var(2)};
  problem.observedOutputExprs1 = {BoolExpr::Not(BoolExpr::Var(2))};
  problem.property = makeEqualityExpr(
      problem.observedOutputExprs0[0], problem.observedOutputExprs1[0]);
  problem.bad = BoolExpr::Not(problem.property);

  const auto witness = findBaseCounterexample(
      problem, KEPLER_FORMAL::Config::SolverType::KISSAT, 0);

  ASSERT_TRUE(witness.has_value());
  EXPECT_EQ(witness->badFrame, 0u);
  ASSERT_EQ(witness->inputTrace.size(), 1u);
  EXPECT_EQ(witness->inputTrace[0].frame, 0u);
  ASSERT_EQ(witness->outputMismatches.size(), 1u);
  EXPECT_EQ(witness->outputMismatches[0].signal, "out");
}

TEST_F(SequentialEquivalenceStrategyTests,
       BaseCaseSolverObservationOnlyStartsSearchingAtFrameOne) {
  KInductionProblem problem;
  problem.environmentInputNames = {"in"};
  problem.observedOutputNames = {"out"};
  problem.inputSymbols = {2};
  problem.state0Symbols = {3};
  problem.state1Symbols = {4};
  problem.allSymbols = {2, 3, 4};
  problem.observedOutputExprs0 = {BoolExpr::Var(3)};
  problem.observedOutputExprs1 = {BoolExpr::Var(4)};
  problem.transitions0 = {{3, BoolExpr::Var(2)}};
  problem.transitions1 = {{4, BoolExpr::createFalse()}};
  problem.property = makeEqualityExpr(
      problem.observedOutputExprs0[0], problem.observedOutputExprs1[0]);
  problem.bad = BoolExpr::Not(problem.property);

  const auto witness = findBaseCounterexample(
      problem, KEPLER_FORMAL::Config::SolverType::KISSAT, 1);

  ASSERT_TRUE(witness.has_value());
  EXPECT_EQ(witness->badFrame, 1u);
  ASSERT_EQ(witness->inputTrace.size(), 2u);
  EXPECT_EQ(witness->inputTrace.front().frame, 0u);
  EXPECT_EQ(witness->inputTrace.back().frame, 1u);
}

TEST_F(SequentialEquivalenceStrategyTests,
       BaseCaseSolverOffsetsWitnessAfterResetBootstrap) {
  KInductionProblem problem;
  problem.environmentInputNames = {"rst", "in"};
  problem.observedOutputNames = {"out"};
  problem.inputSymbols = {2, 5};
  problem.resetBootstrapCycles = 2;
  problem.resetBootstrapInputs = {{2, true}};
  problem.bootstrapStateAssignments = {{3, false}, {4, false}};
  problem.bootstrapStateEqualityPairs = {{3, 4}};
  problem.state0Symbols = {3};
  problem.state1Symbols = {4};
  problem.allSymbols = {2, 3, 4, 5};
  problem.observedOutputExprs0 = {BoolExpr::Var(3)};
  problem.observedOutputExprs1 = {BoolExpr::Var(4)};
  problem.transitions0 = {{3, BoolExpr::Var(5)}};
  problem.transitions1 = {{4, BoolExpr::createFalse()}};
  problem.property = makeEqualityExpr(
      problem.observedOutputExprs0[0], problem.observedOutputExprs1[0]);
  problem.bad = BoolExpr::Not(problem.property);

  const auto witness = findBaseCounterexample(
      problem, KEPLER_FORMAL::Config::SolverType::KISSAT, 1);

  ASSERT_TRUE(witness.has_value());
  EXPECT_EQ(witness->badFrame, 1u);
  ASSERT_EQ(witness->inputTrace.size(), 2u);
  EXPECT_EQ(witness->inputTrace[0].frame, 0u);
  ASSERT_EQ(witness->inputTrace[0].assignments.size(), 2u);
  EXPECT_EQ(witness->inputTrace[0].assignments[0].signal, "rst");
  EXPECT_FALSE(witness->inputTrace[0].assignments[0].value);
}

TEST_F(SequentialEquivalenceStrategyTests,
       ExactInterpolationEngineDerivesOneStepReachableStateInvariant) {
  KInductionProblem problem;
  problem.state0Symbols = {2};
  problem.allSymbols = {2, 3};
  problem.inputSymbols = {3};
  problem.transitions0.emplace_back(2, BoolExpr::createFalse());
  problem.initialCondition = BoolExpr::Not(BoolExpr::Var(2));
  problem.initializedStateCount = 1;
  problem.totalStateCount = 1;
  problem.bad = BoolExpr::Var(2);
  problem.property = BoolExpr::Not(problem.bad);
  problem.inductionProperty = problem.property;
  problem.inductionBad = problem.bad;

  ExactInterpolationEngine engine(
      problem, KEPLER_FORMAL::Config::SolverType::KISSAT);
  const auto interpolant = engine.deriveOneStepReachableStateInvariant(4);

  ASSERT_TRUE(interpolant.has_value());
  EXPECT_TRUE((*interpolant)->evaluate({{2, false}}));
  EXPECT_FALSE((*interpolant)->evaluate({{2, true}}));
}

TEST_F(SequentialEquivalenceStrategyTests,
       ExactInterpolationEngineReturnsNulloptWhenStateBudgetIsExceeded) {
  KInductionProblem problem;
  problem.state0Symbols = {2, 3};
  problem.allSymbols = {2, 3};
  problem.transitions0.emplace_back(2, BoolExpr::Var(2));
  problem.transitions0.emplace_back(3, BoolExpr::Var(3));
  problem.initialCondition =
      BoolExpr::And(BoolExpr::Not(BoolExpr::Var(2)), BoolExpr::Not(BoolExpr::Var(3)));
  problem.initializedStateCount = 2;
  problem.totalStateCount = 2;
  problem.bad = BoolExpr::Var(2);
  problem.property = BoolExpr::Not(problem.bad);
  problem.inductionProperty = problem.property;
  problem.inductionBad = problem.bad;

  ExactInterpolationEngine engine(
      problem, KEPLER_FORMAL::Config::SolverType::KISSAT);
  const auto interpolant = engine.deriveOneStepReachableStateInvariant(1);

  EXPECT_FALSE(interpolant.has_value());
}

TEST_F(SequentialEquivalenceStrategyTests,
       ExactInterpolationEngineReturnsNulloptWhenBadIsReachableInOneStep) {
  KInductionProblem problem;
  problem.state0Symbols = {2};
  problem.allSymbols = {2};
  problem.transitions0.emplace_back(2, BoolExpr::createTrue());
  problem.initialCondition = BoolExpr::Not(BoolExpr::Var(2));
  problem.initializedStateCount = 1;
  problem.totalStateCount = 1;
  problem.bad = BoolExpr::Var(2);
  problem.property = BoolExpr::Not(problem.bad);
  problem.inductionProperty = problem.property;
  problem.inductionBad = problem.bad;

  ExactInterpolationEngine engine(
      problem, KEPLER_FORMAL::Config::SolverType::KISSAT);
  const auto interpolant = engine.deriveOneStepReachableStateInvariant(4);

  EXPECT_FALSE(interpolant.has_value());
}

TEST_F(SequentialEquivalenceStrategyTests,
       ExactInterpolationEngineRejectsNonInductiveInterpolant) {
  KInductionProblem problem;
  problem.state0Symbols = {2, 3};
  problem.allSymbols = {2, 3};
  problem.transitions0.emplace_back(2, BoolExpr::Var(3));
  problem.transitions0.emplace_back(3, BoolExpr::createTrue());
  problem.initialCondition =
      BoolExpr::And(BoolExpr::Not(BoolExpr::Var(2)), BoolExpr::Not(BoolExpr::Var(3)));
  problem.initializedStateCount = 2;
  problem.totalStateCount = 2;
  problem.bad = BoolExpr::Var(2);
  problem.property = BoolExpr::Not(problem.bad);
  problem.inductionProperty = problem.property;
  problem.inductionBad = problem.bad;

  ExactInterpolationEngine engine(
      problem, KEPLER_FORMAL::Config::SolverType::KISSAT);
  const auto interpolant = engine.deriveOneStepReachableStateInvariant(4);

  EXPECT_FALSE(interpolant.has_value());
}

TEST_F(SequentialEquivalenceStrategyTests,
       IC3EngineProvesEquivalentSmallTransitionSystem) {
  KInductionProblem problem;
  problem.state0Symbols = {2};
  problem.allSymbols = {2};
  problem.transitions0.emplace_back(2, BoolExpr::createFalse());
  problem.initialCondition = BoolExpr::Not(BoolExpr::Var(2));
  problem.initializedStateCount = 1;
  problem.totalStateCount = 1;
  problem.bad = BoolExpr::Var(2);
  problem.property = BoolExpr::Not(problem.bad);
  problem.inductionProperty = problem.property;
  problem.inductionBad = problem.bad;

  IC3Engine engine(problem, KEPLER_FORMAL::Config::SolverType::KISSAT);
  const auto result = engine.run(3, 4);

  EXPECT_EQ(result.status, IC3Status::Equivalent);
  EXPECT_LE(result.bound, 1u);
}

TEST_F(SequentialEquivalenceStrategyTests,
       IC3EngineFindsReachableBadState) {
  KInductionProblem problem;
  problem.state0Symbols = {2};
  problem.allSymbols = {2};
  problem.transitions0.emplace_back(2, BoolExpr::createTrue());
  problem.initialCondition = BoolExpr::Not(BoolExpr::Var(2));
  problem.initializedStateCount = 1;
  problem.totalStateCount = 1;
  problem.bad = BoolExpr::Var(2);
  problem.property = BoolExpr::Not(problem.bad);
  problem.inductionProperty = problem.property;
  problem.inductionBad = problem.bad;

  IC3Engine engine(problem, KEPLER_FORMAL::Config::SolverType::KISSAT);
  const auto result = engine.run(3, 4);

  EXPECT_EQ(result.status, IC3Status::Different);
  EXPECT_EQ(result.bound, 1u);
}

TEST_F(SequentialEquivalenceStrategyTests,
       IC3EngineReturnsInconclusiveWithoutInitialConstraint) {
  KInductionProblem problem;
  problem.state0Symbols = {2};
  problem.allSymbols = {2};
  problem.transitions0.emplace_back(2, BoolExpr::createFalse());
  problem.totalStateCount = 1;
  problem.bad = BoolExpr::Var(2);
  problem.property = BoolExpr::Not(problem.bad);
  problem.inductionProperty = problem.property;
  problem.inductionBad = problem.bad;

  IC3Engine engine(problem, KEPLER_FORMAL::Config::SolverType::KISSAT);
  const auto result = engine.run(3, 4);

  EXPECT_EQ(result.status, IC3Status::Inconclusive);
  EXPECT_EQ(result.bound, 0u);
}

TEST_F(SequentialEquivalenceStrategyTests,
       IC3EngineReturnsInconclusiveWhenStateBudgetIsExceeded) {
  KInductionProblem problem;
  problem.state0Symbols = {2, 3};
  problem.allSymbols = {2, 3};
  problem.transitions0.emplace_back(2, BoolExpr::createFalse());
  problem.transitions0.emplace_back(3, BoolExpr::createFalse());
  problem.initialCondition =
      BoolExpr::And(BoolExpr::Not(BoolExpr::Var(2)), BoolExpr::Not(BoolExpr::Var(3)));
  problem.initializedStateCount = 2;
  problem.totalStateCount = 2;
  problem.bad = BoolExpr::Var(2);
  problem.property = BoolExpr::Not(problem.bad);
  problem.inductionProperty = problem.property;
  problem.inductionBad = problem.bad;

  IC3Engine engine(problem, KEPLER_FORMAL::Config::SolverType::KISSAT);
  const auto result = engine.run(3, 1);

  EXPECT_EQ(result.status, IC3Status::Inconclusive);
  EXPECT_EQ(result.bound, 0u);
}

TEST_F(SequentialEquivalenceStrategyTests,
       IC3EngineReturnsInconclusiveWhenFrameBudgetIsZero) {
  KInductionProblem problem;
  problem.state0Symbols = {2};
  problem.allSymbols = {2};
  problem.transitions0.emplace_back(2, BoolExpr::createFalse());
  problem.initialCondition = BoolExpr::Not(BoolExpr::Var(2));
  problem.initializedStateCount = 1;
  problem.totalStateCount = 1;
  problem.bad = BoolExpr::Var(2);
  problem.property = BoolExpr::Not(problem.bad);
  problem.inductionProperty = problem.property;
  problem.inductionBad = problem.bad;

  IC3Engine engine(problem, KEPLER_FORMAL::Config::SolverType::KISSAT);
  const auto result = engine.run(0, 4);

  EXPECT_EQ(result.status, IC3Status::Inconclusive);
  EXPECT_EQ(result.bound, 0u);
}

TEST_F(SequentialEquivalenceStrategyTests,
       InductionStepSolverUsesExplicitInvariantWhenProvided) {
  KInductionProblem problem;
  problem.state0Symbols = {2};
  problem.state1Symbols = {3};
  problem.allSymbols = {2, 3};
  problem.transitions0 = {{2, BoolExpr::Var(2)}};
  problem.transitions1 = {{3, BoolExpr::Var(3)}};
  problem.property = BoolExpr::createTrue();
  problem.bad = BoolExpr::createFalse();
  problem.inductionProperty =
      makeEqualityExpr(BoolExpr::Var(2), BoolExpr::Var(3));
  problem.inductionBad = BoolExpr::Not(problem.inductionProperty);

  EXPECT_TRUE(
      provesByInduction(problem, KEPLER_FORMAL::Config::SolverType::KISSAT, 1));
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
       SequentialDesignModelExtractSupportsGenericComplementedStateNames) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* primitives =
      NLLibrary::create(db, NLLibrary::Type::Primitives, NLName("prims"));
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* model = createNamedComplementSequentialModel(
      primitives, "DFF_STATE_STATEN", "STATE", "STATEN");
  auto* top = createSequentialOutputPairTop(
      library, "top", model, "STATE", "STATEN");

  const auto extracted = SequentialDesignModel::extract(top);

  EXPECT_FALSE(extracted.hasUnsupportedFeatures());
  ASSERT_EQ(extracted.complementedStateRelations.size(), 1u);
  EXPECT_EQ(
      extracted.complementedStateRelations.front().primaryKey,
      extracted.stateBits.front());
}

TEST_F(SequentialEquivalenceStrategyTests,
       SequentialDesignModelExtractSupportsSetHighInitialState) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* primitives =
      NLLibrary::create(db, NLLibrary::Type::Primitives, NLName("prims"));
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* model = createSetOnlySequentialModel(primitives, "DFF_SET");
  auto* top = createSetOnlySequentialTop(library, "top", model);

  const auto extracted = SequentialDesignModel::extract(top);

  EXPECT_FALSE(extracted.hasUnsupportedFeatures());
  ASSERT_EQ(extracted.stateBits.size(), 1u);
  EXPECT_TRUE(extracted.initialStateValueByKey.at(extracted.stateBits.front()));
}

TEST_F(SequentialEquivalenceStrategyTests,
       SequentialDesignModelExtractSupportsResetHighInitialState) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* top = createDffreTop(library, "top");

  const auto extracted = SequentialDesignModel::extract(top);

  EXPECT_FALSE(extracted.hasUnsupportedFeatures());
  ASSERT_EQ(extracted.stateBits.size(), 1u);
  EXPECT_FALSE(extracted.initialStateValueByKey.at(extracted.stateBits.front()));
}

TEST_F(SequentialEquivalenceStrategyTests,
       SequentialDesignModelExtractRejectsNullTop) {
  EXPECT_THROW(
      static_cast<void>(SequentialDesignModel::extract(nullptr)),
      std::invalid_argument);
}

TEST_F(SequentialEquivalenceStrategyTests,
       SequentialDesignModelExtractRejectsMissingUniverse) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* primitives =
      NLLibrary::create(db, NLLibrary::Type::Primitives, NLName("prims"));
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* invModel = createInvModel(primitives);
  auto* top = createDffTop(library, "top", invModel, false, false);
  NLUniverse::get()->destroy();

  EXPECT_THROW(
      static_cast<void>(SequentialDesignModel::extract(top)),
      std::runtime_error);
}

TEST_F(SequentialEquivalenceStrategyTests,
       SequentialDesignModelExtractReportsUnsupportedSequentialWithoutDInput) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* primitives =
      NLLibrary::create(db, NLLibrary::Type::Primitives, NLName("prims"));
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* model = createNoDataSequentialModel(primitives, "SEQ_NO_D");
  auto* top = createNoDataSequentialTop(library, "top", model);

  const auto extracted = SequentialDesignModel::extract(top);

  EXPECT_TRUE(extracted.hasUnsupportedFeatures());
  EXPECT_FALSE(extracted.unsupportedReasons.empty());
}

TEST_F(SequentialEquivalenceStrategyTests,
       SequentialDesignModelExtractMirrorsComplementedInitialStateValue) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* primitives =
      NLLibrary::create(db, NLLibrary::Type::Primitives, NLName("prims"));
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* model = createNamedComplementSetSequentialModel(
      primitives, "DFF_STATE_SET", "STATE", "STATEN");
  auto* top = createSequentialOutputPairTop(
      library, "top", model, "STATE", "STATEN");

  const auto extracted = SequentialDesignModel::extract(top);

  ASSERT_EQ(extracted.stateBits.size(), 2u);
  ASSERT_EQ(extracted.initialStateValueByKey.size(), 2u);
  const auto& relation = extracted.complementedStateRelations.front();
  EXPECT_TRUE(extracted.initialStateValueByKey.at(relation.primaryKey));
  EXPECT_FALSE(extracted.initialStateValueByKey.at(relation.complementedKey));
}

TEST_F(SequentialEquivalenceStrategyTests,
       SequentialDesignModelExtractReportsUnsupportedNonComplementedStateOutput) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* primitives =
      NLLibrary::create(db, NLLibrary::Type::Primitives, NLName("prims"));
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* model = createNamedComplementSequentialModel(
      primitives, "DFF_STATE_ALT", "STATE", "ALT");
  auto* top = createSequentialOutputPairTop(
      library, "top", model, "STATE", "ALT");

  const auto extracted = SequentialDesignModel::extract(top);

  EXPECT_TRUE(extracted.hasUnsupportedFeatures());
  ASSERT_FALSE(extracted.unsupportedReasons.empty());
  EXPECT_NE(
      extracted.unsupportedReasons.front().find("multiple state outputs"),
      std::string::npos);
}

TEST_F(SequentialEquivalenceStrategyTests,
       MismatchedObservedOutputNamesAreReportedAsUnsupported) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* primitives =
      NLLibrary::create(db, NLLibrary::Type::Primitives, NLName("prims"));
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* invModel = createInvModel(primitives);
  auto* top0 = createNamedOutputDffTop(library, "top0", invModel, "out0");
  auto* top1 = createNamedOutputDffTop(library, "top1", invModel, "out1");

  SequentialEquivalenceStrategy strategy(top0, top1);
  const auto result = strategy.run(1);

  EXPECT_EQ(result.status, SequentialEquivalenceStatus::Unsupported);
  EXPECT_NE(result.reason.find("Mismatched observed output sets"), std::string::npos);
}

TEST_F(SequentialEquivalenceStrategyTests,
       MismatchedInputNamesAreReportedAsUnsupported) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* primitives =
      NLLibrary::create(db, NLLibrary::Type::Primitives, NLName("prims"));
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* invModel = createInvModel(primitives);
  auto* top0 = createNamedInputDffTop(library, "top0", invModel, "in0");
  auto* top1 = createNamedInputDffTop(library, "top1", invModel, "in1");

  SequentialEquivalenceStrategy strategy(top0, top1);
  const auto result = strategy.run(1);

  EXPECT_EQ(result.status, SequentialEquivalenceStatus::Unsupported);
  EXPECT_NE(
      result.reason.find("Mismatched environment input sets"),
      std::string::npos);
}

TEST_F(SequentialEquivalenceStrategyTests,
       TooSmallBoundRemainsInconclusiveBeforeCounterexampleDepth) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* top0 = createResetInitializedPipelineTop(library, "top0", false);
  auto* top1 = createResetInitializedPipelineTop(library, "top1", true);

  SequentialEquivalenceStrategy strategy(top0, top1);
  const auto result = strategy.run(2);

  EXPECT_EQ(result.status, SequentialEquivalenceStatus::Inconclusive);
  EXPECT_EQ(result.bound, 2u);
}

TEST_F(SequentialEquivalenceStrategyTests,
       DifferentResultIncludesCounterexampleTracebackDetails) {
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
  EXPECT_NE(result.reason.find("Input trace:"), std::string::npos);
  EXPECT_NE(
      result.reason.find("Observed output mismatches at cycle"),
      std::string::npos);
  EXPECT_NE(
      result.reason.find("Traceback for first differing point"),
      std::string::npos);
  EXPECT_NE(
      result.reason.find("design0 cone to environment inputs"),
      std::string::npos);
  EXPECT_NE(result.reason.find("cone terms only in design1"), std::string::npos);
}

TEST_F(SequentialEquivalenceStrategyTests,
       UnsupportedReasonsFromBothDesignsAreJoined) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* primitives =
      NLLibrary::create(db, NLLibrary::Type::Primitives, NLName("prims"));
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* unsupportedModel = createNamedComplementSequentialModel(
      primitives, "DFF_STATE_ALT", "STATE", "ALT");
  auto* top0 = createSequentialOutputPairTop(
      library, "top0", unsupportedModel, "STATE", "ALT");
  auto* top1 = createSequentialOutputPairTop(
      library, "top1", unsupportedModel, "STATE", "ALT");

  SequentialEquivalenceStrategy strategy(top0, top1);
  const auto result = strategy.run(1);

  EXPECT_EQ(result.status, SequentialEquivalenceStatus::Unsupported);
  EXPECT_NE(result.reason.find(" | "), std::string::npos);
}

TEST_F(SequentialEquivalenceStrategyTests,
       DiagnosticModePrintsStrategyAndExtractionProgress) {
  NLUniverse::create();
  auto* db = NLDB::create(NLUniverse::get());
  auto* primitives =
      NLLibrary::create(db, NLLibrary::Type::Primitives, NLName("prims"));
  auto* library =
      NLLibrary::create(db, NLLibrary::Type::Standard, NLName("designs"));
  auto* invModel = createInvModel(primitives);
  auto* top0 = createDffTop(library, "top0", invModel, false, false);
  auto* top1 = createDffTop(library, "top1", invModel, false, false);

  ScopedEnvVar secDiag("KEPLER_SEC_DIAG", "1");
  testing::internal::CaptureStdout();
  testing::internal::CaptureStderr();
  SequentialEquivalenceStrategy strategy(top0, top1);
  const auto result = strategy.run(3);
  const std::string stdoutOutput = testing::internal::GetCapturedStdout();
  const std::string stderrOutput = testing::internal::GetCapturedStderr();

  EXPECT_EQ(result.status, SequentialEquivalenceStatus::Equivalent);
  EXPECT_NE(stderrOutput.find("SEC diag: start run"), std::string::npos);
  EXPECT_NE(
      stderrOutput.find("SEC diag: extract(top0) collect begin"),
      std::string::npos);
  EXPECT_NE(
      stderrOutput.find("SEC diag: remapped next-state formulas"),
      std::string::npos);
  EXPECT_NE(
      stderrOutput.find("SEC diag: entering k-induction engine"),
      std::string::npos);
  EXPECT_NE(stdoutOutput.find("SEC diag: aligned_inputs="), std::string::npos);
  EXPECT_NE(stdoutOutput.find("SEC diag: property_is_true="), std::string::npos);
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
