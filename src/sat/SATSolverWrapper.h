#pragma once

#include <algorithm>
#include <cstdint>
#include <vector>
#include <string>
#include <cstdlib>
#include <initializer_list>
#include <limits>
#include <stdexcept>
#include <memory>

#include "simp/SimpSolver.h"
#include "cadical.hpp"
extern "C" {
  #include "kissat.h"
}

#include "../config/Config.h"

//#define USE_KISSAT

class SATSolverWrapper {
public:
  enum class SolveStatus {
    Sat,
    Unsat,
    Unknown,
  };

  static KEPLER_FORMAL::Config::SolverType assumptionSolverTypeFor(
      KEPLER_FORMAL::Config::SolverType chosenSolverType) {
    return chosenSolverType == KEPLER_FORMAL::Config::SolverType::GLUCOSE
               ? KEPLER_FORMAL::Config::SolverType::GLUCOSE
               : KEPLER_FORMAL::Config::SolverType::CADICAL;
  }

  explicit SATSolverWrapper(KEPLER_FORMAL::Config::SolverType type = KEPLER_FORMAL::Config::SolverType::CADICAL)
    : solverType_(type) {
    if (solverType_ == KEPLER_FORMAL::Config::SolverType::GLUCOSE) {
      glucoseSolver_ = std::make_unique<Glucose::SimpSolver>();
      // Keep embedded solver calls quiet. The command-line Glucose default is
      // already low, but SimpSolver still prints eliminated-clause summaries at
      // verbosity 0.
      glucoseSolver_->verbosity = -1;
    } else if (solverType_ == KEPLER_FORMAL::Config::SolverType::KISSAT) {
      kissatSolver_ = kissat_init();
      // Embedded SEC runs can create thousands of short-lived Kissat queries.
      // Keep those solver instances quiet so regressions are not dominated by
      // progress-report I/O.  Some embedded Kissat builds do not expose
      // application-only options such as "quiet", so this must remain
      // best-effort instead of aborting the proof setup.
      setKissatOptionIfSupported(static_cast<kissat*>(kissatSolver_), "quiet", 1);
      kissatNumVars_ = 0;
      kissatReservedVars_ = 0;
    } else if (solverType_ == KEPLER_FORMAL::Config::SolverType::CADICAL) {
      cadicalSolver_ = std::make_unique<CaDiCaL::Solver>();
      cadicalNumVars_ = 0;
      cadicalReservedVars_ = 0;
      if (CaDiCaL::Solver::is_valid_option("quiet")) {
        cadicalSolver_->set("quiet", 1);  // LCOV_EXCL_LINE
      }  // LCOV_EXCL_LINE
    } else {
      // LCOV_EXCL_START
      throw std::invalid_argument("Unknown solver type");
      // LCOV_EXCL_STOP
    }
  }

  ~SATSolverWrapper() {
    if (solverType_ == KEPLER_FORMAL::Config::SolverType::KISSAT && kissatSolver_) {
      kissat_release(static_cast<kissat*>(kissatSolver_));
    }
  }

  // Create a new variable (returns 0-based index)
  int newVar() {
    if (solverType_ == KEPLER_FORMAL::Config::SolverType::GLUCOSE) {
      return glucoseSolver_->newVar();
    } else if (solverType_ == KEPLER_FORMAL::Config::SolverType::KISSAT) {
      // Kissat does not require explicit variable creation, but SEC encoders
      // create variables before streaming clauses. Reserving at creation time
      // keeps Kissat from growing its internal variable arrays inside
      // kissat_add(), which is the hottest path for large PDR queries.
      reserveVars(static_cast<size_t>(kissatNumVars_) + 1);
      return kissatNumVars_++;
    } else if (solverType_ == KEPLER_FORMAL::Config::SolverType::CADICAL) {
      reserveVars(static_cast<size_t>(cadicalNumVars_) + 1);
      return cadicalNumVars_++;
    }
    // LCOV_EXCL_START
    throw std::runtime_error("Unknown solver type");
    // LCOV_EXCL_STOP
  }

  void reserveVars(size_t numVars) {
    if (solverType_ == KEPLER_FORMAL::Config::SolverType::KISSAT) {
      if (numVars <= static_cast<size_t>(kissatReservedVars_)) {
        return;
      }
      const size_t currentReserved = static_cast<size_t>(kissatReservedVars_);
      const size_t growthSlack =
          std::max(currentReserved / 2, static_cast<size_t>(4096));
      const size_t targetVars =
          currentReserved == 0
              ? numVars
              : std::max(numVars, currentReserved + growthSlack);
      // Kissat allocates variable storage lazily while clauses are added. PDR
      // creates many short-lived solvers with thousands of frame variables, so
      // reserving the known frame-variable prefix avoids repeated internal
      // growth during Tseitin clause emission.
      kissat_reserve(static_cast<kissat*>(kissatSolver_),
                     static_cast<int>(targetVars));
      kissatReservedVars_ = static_cast<int>(targetVars);
    } else if (solverType_ == KEPLER_FORMAL::Config::SolverType::CADICAL) {
      if (numVars <= static_cast<size_t>(cadicalReservedVars_)) {
        return;
      }
      const size_t currentReserved = static_cast<size_t>(cadicalReservedVars_);
      const size_t growthSlack =
          std::max(currentReserved / 2, static_cast<size_t>(4096));
      const size_t targetVars =
          currentReserved == 0
              ? numVars
              : std::max(numVars, currentReserved + growthSlack);
      if (targetVars > static_cast<size_t>(std::numeric_limits<int>::max())) {
        throw std::runtime_error("CaDiCaL variable reservation exceeds int range");  // LCOV_EXCL_LINE
      }
      cadicalSolver_->resize(static_cast<int>(targetVars));
      cadicalReservedVars_ = static_cast<int>(targetVars);
    }
  }

  void reserveAdditionalVars(size_t additionalVars) {
    if (solverType_ == KEPLER_FORMAL::Config::SolverType::KISSAT) {
      // Formula encoders create Tseitin variables after the frame variables
      // have already been allocated. Reserving from the wrapper's current
      // variable count targets Kissat's variable-vector growth directly without
      // changing the external literal numbering convention.
      reserveVars(static_cast<size_t>(kissatNumVars_) + additionalVars);
    } else if (solverType_ == KEPLER_FORMAL::Config::SolverType::CADICAL) {
      reserveVars(static_cast<size_t>(cadicalNumVars_) + additionalVars);
    }
  }

  // Add a clause, literals are signed ints:
  // external convention: 0=false, 1=true, vars are ±(var_id + 2)
  void addClause(const std::vector<int>& lits) {
    addClauseRange(lits);
  }

  void addClause(std::initializer_list<int> lits) {
    addClauseRange(lits);
  }

 private:
  template <typename ClauseRange>
  void addClauseRange(const ClauseRange& lits) {
    if (solverType_ == KEPLER_FORMAL::Config::SolverType::GLUCOSE) {
      Glucose::vec<Glucose::Lit> clause;
      for (int lit : lits) {
        if (lit == 0 || lit == 1) {
          // We should never see raw consts here: they are encoded via forced vars.
          // LCOV_EXCL_START
          throw std::runtime_error("Constant literal (0/1) passed to Glucose clause");
          // LCOV_EXCL_STOP
        }
        int v = std::abs(lit);
        int var = v - 2;  // external ±(var+2) -> internal var index
        if (var < 0) {
          // LCOV_EXCL_START
          throw std::runtime_error("Invalid literal (<2) passed to Glucose clause");
          // LCOV_EXCL_STOP
        }
        while (var >= glucoseSolver_->nVars())
          glucoseSolver_->newVar();  // LCOV_EXCL_LINE
        clause.push((lit > 0) ? Glucose::mkLit(var) : ~Glucose::mkLit(var));
      }
      glucoseSolver_->addClause(clause);
    } else if (solverType_ == KEPLER_FORMAL::Config::SolverType::KISSAT) {
      // Kissat expects ±(var+1), 0 terminates a clause.
      for (int lit : lits) {
        if (lit == 0 || lit == 1) {
          // LCOV_EXCL_START
          throw std::runtime_error("Constant literal (0/1) passed to Kissat clause");
          // LCOV_EXCL_STOP
        }
        int v = std::abs(lit);
        int var = v - 2;  // external ±(var+2) -> internal var index
        if (var < 0) {
          // LCOV_EXCL_START
          throw std::runtime_error("Invalid literal (<2) passed to Kissat clause");
          // LCOV_EXCL_STOP
        }
        if (var >= kissatNumVars_) {
          kissatNumVars_ = var + 1;
        }
        int kissatLit = (lit > 0 ? var + 1 : -(var + 1)); // ±(var+1)
        kissat_add(static_cast<kissat*>(kissatSolver_), kissatLit);
      }
      kissat_add(static_cast<kissat*>(kissatSolver_), 0); // end of clause
    } else if (solverType_ == KEPLER_FORMAL::Config::SolverType::CADICAL) {
      for (int lit : lits) {
        if (lit == 0 || lit == 1) {
          // LCOV_EXCL_START
          throw std::runtime_error("Constant literal (0/1) passed to CaDiCaL clause");
          // LCOV_EXCL_STOP
        }
        int v = std::abs(lit);
        int var = v - 2;  // external ±(var+2) -> internal var index
        if (var < 0) {
          // LCOV_EXCL_START
          throw std::runtime_error("Invalid literal (<2) passed to CaDiCaL clause");
          // LCOV_EXCL_STOP
        }
        if (var >= cadicalNumVars_) {
          cadicalNumVars_ = var + 1;  // LCOV_EXCL_LINE
          reserveVars(static_cast<size_t>(cadicalNumVars_));  // LCOV_EXCL_LINE
        }  // LCOV_EXCL_LINE
        int cadicalLit = (lit > 0 ? var + 1 : -(var + 1)); // ±(var+1)
        cadicalSolver_->add(cadicalLit);
      }
      cadicalSolver_->add(0); // end of clause
    } else {
      // LCOV_EXCL_START
      throw std::runtime_error("Unknown solver type");
      // LCOV_EXCL_STOP
    }
  }

 public:
  bool solve() {
    return solveStatus() == SolveStatus::Sat;
  }

  SolveStatus solveStatus() {
    if (solverType_ == KEPLER_FORMAL::Config::SolverType::GLUCOSE) {
      return glucoseSolver_->solve() ? SolveStatus::Sat : SolveStatus::Unsat;
    } else if (solverType_ == KEPLER_FORMAL::Config::SolverType::KISSAT) {
      int res = kissat_solve(static_cast<kissat*>(kissatSolver_));
      if (res == 10) { // 10 = SAT
        return SolveStatus::Sat;
      }
      if (res == 20) { // 20 = UNSAT
        return SolveStatus::Unsat;
      }
      return SolveStatus::Unknown;
    } else if (solverType_ == KEPLER_FORMAL::Config::SolverType::CADICAL) {  // LCOV_EXCL_LINE
      lastAssumptionSolveStatus_ = SolveStatus::Unknown;  // LCOV_EXCL_LINE
      lastAssumptions_.clear();  // LCOV_EXCL_LINE
      const int res = cadicalSolver_->solve();  // LCOV_EXCL_LINE
      if (res == 10) { // 10 = SAT LCOV_EXCL_LINE
        return SolveStatus::Sat;  // LCOV_EXCL_LINE
      }
      if (res == 20) { // 20 = UNSAT LCOV_EXCL_LINE
        return SolveStatus::Unsat;  // LCOV_EXCL_LINE
      }
      return SolveStatus::Unknown;  // LCOV_EXCL_LINE
    }
    // LCOV_EXCL_START
    throw std::runtime_error("Unknown solver type");
    // LCOV_EXCL_STOP
  }

  SolveStatus solveWithKissatResourceLimits(
      unsigned conflictLimit,
      unsigned decisionLimit =
          std::numeric_limits<unsigned>::max()) {
    if (solverType_ != KEPLER_FORMAL::Config::SolverType::KISSAT) {
      throw std::runtime_error(  // LCOV_EXCL_LINE
          "Kissat resource limits requested for non-Kissat solver");
    }
    auto* solver = static_cast<kissat*>(kissatSolver_);
    if (conflictLimit != std::numeric_limits<unsigned>::max()) {
      kissat_set_conflict_limit(solver, conflictLimit);
    }
    if (decisionLimit != std::numeric_limits<unsigned>::max()) {
      kissat_set_decision_limit(solver, decisionLimit);
    }
    return solveStatus();
  }  // LCOV_EXCL_LINE

  SolveStatus solveWithAssumptionsStatus(
      const std::vector<int>& assumptions,
      int64_t conflictLimit = -1,
      int64_t propagationLimit = -1) {
    if (solverType_ == KEPLER_FORMAL::Config::SolverType::GLUCOSE) {
      Glucose::vec<Glucose::Lit> glucoseAssumptions;  // LCOV_EXCL_LINE
      for (int lit : assumptions) {  // LCOV_EXCL_LINE
        if (lit == 0 || lit == 1) {  // LCOV_EXCL_LINE
          // LCOV_EXCL_START
          throw std::runtime_error("Constant literal (0/1) passed as Glucose assumption");
          // LCOV_EXCL_STOP
        }
        const int var = std::abs(lit) - 2;  // LCOV_EXCL_LINE
        if (var < 0) {  // LCOV_EXCL_LINE
          // LCOV_EXCL_START
          throw std::runtime_error("Invalid literal (<2) passed as Glucose assumption");
          // LCOV_EXCL_STOP
        }
        while (var >= glucoseSolver_->nVars()) {  // LCOV_EXCL_LINE
          glucoseSolver_->newVar();  // LCOV_EXCL_LINE
        }
        glucoseAssumptions.push((lit > 0) ? Glucose::mkLit(var)  // LCOV_EXCL_LINE
                                          : ~Glucose::mkLit(var));  // LCOV_EXCL_LINE
      }
      if (conflictLimit >= 0 || propagationLimit >= 0) {  // LCOV_EXCL_LINE
        if (conflictLimit >= 0) {  // LCOV_EXCL_LINE
          glucoseSolver_->setConfBudget(conflictLimit);  // LCOV_EXCL_LINE
        }  // LCOV_EXCL_LINE
        if (propagationLimit >= 0) {  // LCOV_EXCL_LINE
          glucoseSolver_->setPropBudget(propagationLimit);  // LCOV_EXCL_LINE
        }  // LCOV_EXCL_LINE
        const auto result = glucoseSolver_->solveLimited(  // LCOV_EXCL_LINE
            glucoseAssumptions,
            /*do_simp=*/false,
            /*turn_off_simp=*/true);
        glucoseSolver_->budgetOff();  // LCOV_EXCL_LINE
        if (Glucose::toInt(result) == 0) {  // LCOV_EXCL_LINE
          return SolveStatus::Sat;  // LCOV_EXCL_LINE
        }
        if (Glucose::toInt(result) == 1) {  // LCOV_EXCL_LINE
          return SolveStatus::Unsat;  // LCOV_EXCL_LINE
        }
        return SolveStatus::Unknown;  // LCOV_EXCL_LINE
      }
      // Repeated CEGAR reachability checks reuse the same solver and vary only
      // assumptions. Running variable elimination on each assumption solve
      // dominates those small queries, so keep this path in plain CDCL mode.
      return glucoseSolver_->solve(  // LCOV_EXCL_LINE
                 glucoseAssumptions,
                 /*do_simp=*/false,
                 /*turn_off_simp=*/true)
                 ? SolveStatus::Sat
                 : SolveStatus::Unsat;
    } else if (solverType_ == KEPLER_FORMAL::Config::SolverType::KISSAT) {
      // This vendored Kissat exposes only the partial IPASIR API and has no
      // assumption call. Callers that need repeated assumption solves should use
      // CaDiCaL for that local incremental query.
      if (assumptions.empty()) {  // LCOV_EXCL_LINE
        return solveStatus();  // LCOV_EXCL_LINE
      }
      throw std::runtime_error("Kissat assumptions are not available in this build");  // LCOV_EXCL_LINE
    } else if (solverType_ == KEPLER_FORMAL::Config::SolverType::CADICAL) {
      lastAssumptions_ = assumptions;
      lastAssumptionSolveStatus_ = SolveStatus::Unknown;
      for (int lit : assumptions) {
        if (lit == 0 || lit == 1) {
          // LCOV_EXCL_START
          throw std::runtime_error("Constant literal (0/1) passed as CaDiCaL assumption");
          // LCOV_EXCL_STOP
        }
        const int var = std::abs(lit) - 2;
        if (var < 0) {
          // LCOV_EXCL_START
          throw std::runtime_error("Invalid literal (<2) passed as CaDiCaL assumption");
          // LCOV_EXCL_STOP
        }
        if (var >= cadicalNumVars_) {
          cadicalNumVars_ = var + 1;  // LCOV_EXCL_LINE
          reserveVars(static_cast<size_t>(cadicalNumVars_));  // LCOV_EXCL_LINE
        }  // LCOV_EXCL_LINE
        cadicalSolver_->assume(lit > 0 ? var + 1 : -(var + 1));
      }
      if (conflictLimit >= 0) {
        cadicalSolver_->limit(
            "conflicts",
            static_cast<int>(
                std::min<int64_t>(conflictLimit, std::numeric_limits<int>::max())));
      }
      if (propagationLimit >= 0) {
        // CaDiCaL does not expose a propagation budget. Use a decision budget
        // as the closest available solve limiter for callers that pass both.
        cadicalSolver_->limit(
            "decisions",
            static_cast<int>(
                std::min<int64_t>(propagationLimit, std::numeric_limits<int>::max())));
      }
      const int res = cadicalSolver_->solve();
      if (res == 10) {
        lastAssumptionSolveStatus_ = SolveStatus::Sat;
      } else if (res == 20) {
        lastAssumptionSolveStatus_ = SolveStatus::Unsat;
      } else {
        lastAssumptionSolveStatus_ = SolveStatus::Unknown;  // LCOV_EXCL_LINE
      }
      if (lastAssumptionSolveStatus_ != SolveStatus::Unsat) {
        lastAssumptions_.clear();
      }
      return lastAssumptionSolveStatus_;
    }
    // LCOV_EXCL_START
    throw std::runtime_error("Unknown solver type");
    // LCOV_EXCL_STOP
  }

  bool solveWithAssumptions(const std::vector<int>& assumptions) {
    return solveWithAssumptionsStatus(assumptions) == SolveStatus::Sat;
  }

  std::vector<int> failedAssumptions() const {
    std::vector<int> failed;
    if (solverType_ == KEPLER_FORMAL::Config::SolverType::GLUCOSE) {
      failed.reserve(glucoseSolver_->conflict.size());  // LCOV_EXCL_LINE
      for (int i = 0; i < glucoseSolver_->conflict.size(); ++i) {  // LCOV_EXCL_LINE
        const auto lit = glucoseSolver_->conflict[i];  // LCOV_EXCL_LINE
        const int externalVar = Glucose::var(lit) + 2;  // LCOV_EXCL_LINE
        const int conflictLiteral =  // LCOV_EXCL_LINE
            Glucose::sign(lit) ? -externalVar : externalVar;  // LCOV_EXCL_LINE
        // Glucose exposes the final conflict clause over the negated failed
        // assumptions. Return the caller's original assumption literals so SEC
        // can map them directly back to PDR cube literals.
        failed.push_back(-conflictLiteral);  // LCOV_EXCL_LINE
      }  // LCOV_EXCL_LINE
    } else if (solverType_ == KEPLER_FORMAL::Config::SolverType::CADICAL &&
               lastAssumptionSolveStatus_ == SolveStatus::Unsat) {
      failed.reserve(lastAssumptions_.size());
      for (int lit : lastAssumptions_) {
        const int var = std::abs(lit) - 2;
        const int cadicalLit = lit > 0 ? var + 1 : -(var + 1);
        if (cadicalSolver_->failed(cadicalLit)) {
          failed.push_back(lit);
        }
      }
    }
    return failed;
  }

  bool getLiteralValue(int lit) const {
    if (lit == 0) {
      return false;
    }
    if (lit == 1) {
      return true;
    }

    const int external = std::abs(lit);
    const int var = external - 2;
    if (var < 0) {
      throw std::runtime_error("Invalid literal passed to getLiteralValue");
    }

    bool positiveValue = false;
    if (solverType_ == KEPLER_FORMAL::Config::SolverType::GLUCOSE) {
      const auto value = glucoseSolver_->modelValue(Glucose::mkLit(var));
      if (Glucose::toInt(value) == 2) {
        positiveValue = false;  // LCOV_EXCL_LINE
      } else {  // LCOV_EXCL_LINE
        positiveValue = Glucose::toInt(value) == 0;
      }
    } else if (solverType_ == KEPLER_FORMAL::Config::SolverType::KISSAT) {
      const int value = kissat_value(static_cast<kissat*>(kissatSolver_), var + 1);
      if (value == 0) {
        positiveValue = false;
      } else {
        positiveValue = value > 0;
      }
    } else if (solverType_ == KEPLER_FORMAL::Config::SolverType::CADICAL) {
      const int value = cadicalSolver_->val(var + 1);  // LCOV_EXCL_LINE
      positiveValue = value > 0;  // LCOV_EXCL_LINE
    } else {  // LCOV_EXCL_LINE
      throw std::runtime_error("Unknown solver type");  // LCOV_EXCL_LINE
    }

    return lit > 0 ? positiveValue : !positiveValue;
  }

  void configureForSecConeProof(size_t coneSymbols = 0) {
    if (solverType_ != KEPLER_FORMAL::Config::SolverType::KISSAT) {
      return;  // LCOV_EXCL_LINE
    }

    auto* solver = static_cast<kissat*>(kissatSolver_);
    // SEC proof obligations are normally expected to be UNSAT when the designs
    // are equivalent, so bias Kissat toward its UNSAT/stable search profile.
    // Keep the rest of the default solver machinery for small and medium COIs:
    // on those instances preprocessing and clause minimization can be the real
    // speedup, and disabling them globally makes BlackParrot-style proofs worse.
    setKissatOptionOrThrow(solver, "stable", 2);

    // The threshold is intentionally based on the engine's COI size, not on a
    // design name. Small and medium SEC cones still benefit from Kissat's normal
    // congruence/probing passes because those passes recognize duplicated
    // gate-level structure. Reserve the stripped-down profile for truly huge
    // cones where the prepasses themselves dominate memory and runtime.
    constexpr size_t kLargeSecConeSymbolThreshold = 100000;
    if (coneSymbols < kLargeSecConeSymbolThreshold) {
      return;
    }

    // Large SEC cones are already sliced and Tseitin-encoded by the engine.
    // Profiles on very large ASIC obligations showed Kissat spending most of
    // its time in speculative preprocessing before reaching CDCL. For only
    // those large cones, skip the speculative passes and keep the query focused
    // on SAT search.
    setKissatOptionOrThrow(solver, "preprocess", 0);  // LCOV_EXCL_LINE
    setKissatOptionOrThrow(solver, "simplify", 0);  // LCOV_EXCL_LINE
    setKissatOptionOrThrow(solver, "preprocesscongruence", 0);  // LCOV_EXCL_LINE
    setKissatOptionOrThrow(solver, "preprocessprobe", 0);  // LCOV_EXCL_LINE
    setKissatOptionOrThrow(solver, "congruence", 0);  // LCOV_EXCL_LINE
    setKissatOptionOrThrow(solver, "probe", 0);  // LCOV_EXCL_LINE
    setKissatOptionOrThrow(solver, "probeinit", 0);  // LCOV_EXCL_LINE
    setKissatOptionOrThrow(solver, "eliminate", 0);  // LCOV_EXCL_LINE
    setKissatOptionOrThrow(solver, "eliminateinit", 0);  // LCOV_EXCL_LINE
    setKissatOptionOrThrow(solver, "lucky", 0);  // LCOV_EXCL_LINE
    setKissatOptionOrThrow(solver, "luckyearly", 0);  // LCOV_EXCL_LINE
    setKissatOptionOrThrow(solver, "luckylate", 0);  // LCOV_EXCL_LINE
    // Recursive learned-clause shrinking can dominate these very large shallow
    // equivalence cones, so disable it only for this large-cone profile.
    setKissatOptionOrThrow(solver, "minimize", 0);  // LCOV_EXCL_LINE
    setKissatOptionOrThrow(solver, "shrink", 0);  // LCOV_EXCL_LINE
  }

  void configureForSecPdrQuery(size_t coneSymbols = 0) {
    if (solverType_ == KEPLER_FORMAL::Config::SolverType::CADICAL) {
      auto* solver = cadicalSolver_.get();
      // CaDiCaL is the default local solver for assumption-capable validation
      // queries.  These SEC/PDR validators are rebuilt from scratch and only
      // need a quick SAT/UNSAT answer, so avoid expensive inprocessing and
      // recursive clause polishing that samples showed dominating deeper
      // sky130hs_ibex frontier checks.
      setCadicalOptionIfSupported(solver, "inprocessing", 0);
      setCadicalOptionIfSupported(solver, "compact", 0);
      setCadicalOptionIfSupported(solver, "arenacompact", 0);
      setCadicalOptionIfSupported(solver, "elim", 0);
      setCadicalOptionIfSupported(solver, "fastelim", 0);
      setCadicalOptionIfSupported(solver, "preprocesslight", 0);
      setCadicalOptionIfSupported(solver, "probe", 0);
      setCadicalOptionIfSupported(solver, "inprobing", 0);
      setCadicalOptionIfSupported(solver, "congruence", 0);
      setCadicalOptionIfSupported(solver, "decompose", 0);
      setCadicalOptionIfSupported(solver, "deduplicate", 0);
      setCadicalOptionIfSupported(solver, "factor", 0);
      setCadicalOptionIfSupported(solver, "subsume", 0);
      setCadicalOptionIfSupported(solver, "sweep", 0);
      setCadicalOptionIfSupported(solver, "lucky", 0);
      setCadicalOptionIfSupported(solver, "luckyearly", 0);
      setCadicalOptionIfSupported(solver, "luckylate", 0);
      setCadicalOptionIfSupported(solver, "minimize", 0);
      setCadicalOptionIfSupported(solver, "shrink", 0);
      setCadicalOptionIfSupported(solver, "rephase", 0);
      setCadicalOptionIfSupported(solver, "walk", 0);
      (void)coneSymbols;
      return;
    }

    if (solverType_ != KEPLER_FORMAL::Config::SolverType::KISSAT) {
      return;
    }

    auto* solver = static_cast<kissat*>(kissatSolver_);
    // PDR issues many short-lived predecessor queries while blocking one cube
    // at a time.  These obligations are frequently SAT because PDR walks
    // backward through reachable predecessors before eventually learning an
    // UNSAT blocking clause.  Use focused/SAT-oriented CDCL here; the stable
    // UNSAT-oriented Kissat mode periodically rephases via local search, which
    // dominated ASIC PDR predecessor samples without helping those SAT walks.
    // The generic SEC cone profile below remains available for k-induction and
    // IMC, whose large monolithic queries can benefit from preprocessing.
    setKissatOptionOrThrow(solver, "stable", 0);
    setKissatOptionOrThrow(solver, "target", 2);
    setKissatOptionOrThrow(solver, "restartint", 10);
    setKissatOptionOrThrow(solver, "restartreusetrail", 0);

    setKissatOptionOrThrow(solver, "rephase", 0);
    setKissatOptionOrThrow(solver, "walkeffort", 0);
    setKissatOptionOrThrow(solver, "lucky", 0);
    setKissatOptionOrThrow(solver, "luckyearly", 0);
    setKissatOptionOrThrow(solver, "luckylate", 0);
    setKissatOptionOrThrow(solver, "minimize", 0);
    setKissatOptionOrThrow(solver, "shrink", 0);
    // PDR predecessor queries are rebuilt from engine-level learned frame
    // clauses, so Kissat's own on-the-fly clause strengthening adds heavy
    // per-conflict bookkeeping without preserving state across queries. Keep
    // this disabled only for PDR; k-induction/IMC still use the generic SEC
    // profile where in-solver strengthening can help monolithic UNSAT proofs.
    setKissatOptionOrThrow(solver, "otfs", 0);

    (void)coneSymbols;
    setKissatOptionOrThrow(solver, "preprocess", 0);
    setKissatOptionOrThrow(solver, "simplify", 0);
    setKissatOptionOrThrow(solver, "preprocesscongruence", 0);
    setKissatOptionOrThrow(solver, "preprocessprobe", 0);
    setKissatOptionOrThrow(solver, "congruence", 0);
    setKissatOptionOrThrow(solver, "probe", 0);
    setKissatOptionOrThrow(solver, "probeinit", 0);
    setKissatOptionOrThrow(solver, "eliminate", 0);
    setKissatOptionOrThrow(solver, "eliminateinit", 0);
  }

  void configureForSecLocalBooleanCheck(size_t coneSymbols = 0) {
    if (solverType_ == KEPLER_FORMAL::Config::SolverType::CADICAL) {
      auto* solver = cadicalSolver_.get();
      // Structural SEC validators rebuild many small one-shot Boolean queries.
      // Use CaDiCaL as the assumption-capable default, but keep it on a direct
      // CDCL path so startup inference does not spend minutes in gate
      // extraction and inprocessing before the real proof engine starts.
      setCadicalOptionIfSupported(solver, "inprocessing", 0);
      setCadicalOptionIfSupported(solver, "compact", 0);
      setCadicalOptionIfSupported(solver, "arenacompact", 0);
      setCadicalOptionIfSupported(solver, "elim", 0);
      setCadicalOptionIfSupported(solver, "fastelim", 0);
      setCadicalOptionIfSupported(solver, "preprocesslight", 0);
      setCadicalOptionIfSupported(solver, "probe", 0);
      setCadicalOptionIfSupported(solver, "inprobing", 0);
      setCadicalOptionIfSupported(solver, "congruence", 0);
      setCadicalOptionIfSupported(solver, "decompose", 0);
      setCadicalOptionIfSupported(solver, "deduplicate", 0);
      setCadicalOptionIfSupported(solver, "factor", 0);
      setCadicalOptionIfSupported(solver, "subsume", 0);
      setCadicalOptionIfSupported(solver, "sweep", 0);
      setCadicalOptionIfSupported(solver, "lucky", 0);
      setCadicalOptionIfSupported(solver, "luckyearly", 0);
      setCadicalOptionIfSupported(solver, "luckylate", 0);
      setCadicalOptionIfSupported(solver, "minimize", 0);
      setCadicalOptionIfSupported(solver, "shrink", 0);
      setCadicalOptionIfSupported(solver, "rephase", 0);
      setCadicalOptionIfSupported(solver, "walk", 0);
      (void)coneSymbols;
      return;
    }

    if (solverType_ != KEPLER_FORMAL::Config::SolverType::KISSAT) {
      return;
    }

    auto* solver = static_cast<kissat*>(kissatSolver_);
    // Local Boolean checks are short-lived validators used while building SEC
    // invariants and output slices. They are not the main proof engine, and
    // sampled sky130hs_ibex runs spent minutes in Kissat's speculative
    // preprocessing before PDR even started. Keep these checks on a direct CDCL
    // path; if the validator cannot decide quickly, the caller falls back to a
    // weaker but still sound SEC obligation.
    setKissatOptionOrThrow(solver, "stable", 0);
    setKissatOptionOrThrow(solver, "target", 2);
    setKissatOptionOrThrow(solver, "restartint", 10);
    setKissatOptionOrThrow(solver, "restartreusetrail", 0);
    setKissatOptionOrThrow(solver, "rephase", 0);
    setKissatOptionOrThrow(solver, "walkeffort", 0);
    setKissatOptionOrThrow(solver, "lucky", 0);
    setKissatOptionOrThrow(solver, "luckyearly", 0);
    setKissatOptionOrThrow(solver, "luckylate", 0);
    setKissatOptionOrThrow(solver, "minimize", 0);
    setKissatOptionOrThrow(solver, "shrink", 0);
    setKissatOptionOrThrow(solver, "otfs", 0);
    setKissatOptionOrThrow(solver, "preprocess", 0);
    setKissatOptionOrThrow(solver, "simplify", 0);
    setKissatOptionOrThrow(solver, "preprocesscongruence", 0);
    setKissatOptionOrThrow(solver, "preprocessprobe", 0);
    setKissatOptionOrThrow(solver, "congruence", 0);
    setKissatOptionOrThrow(solver, "probe", 0);
    setKissatOptionOrThrow(solver, "probeinit", 0);
    setKissatOptionOrThrow(solver, "eliminate", 0);
    setKissatOptionOrThrow(solver, "eliminateinit", 0);
    (void)coneSymbols;
  }

  void configureForSecResetExpressionProof(size_t coneSymbols = 0) {
    if (solverType_ != KEPLER_FORMAL::Config::SolverType::KISSAT) {
      return;  // LCOV_EXCL_LINE
    }

    auto* solver = static_cast<kissat*>(kissatSolver_);
    // Reset-expression checks are optional local UNSAT proofs over the
    // symbolic reset image.  They are reached only after PDR has produced a
    // candidate startup conflict, so use Kissat's proof-oriented stable mode
    // instead of the SAT-oriented predecessor-walk profile.  AES sampling
    // showed otherwise useful 500-symbol reset-image proofs spending their
    // runtime in focused CDCL propagation.
    setKissatOptionOrThrow(solver, "stable", 2);
    setKissatOptionOrThrow(solver, "target", 1);
    setKissatOptionOrThrow(solver, "rephase", 0);
    setKissatOptionOrThrow(solver, "walkeffort", 0);
    setKissatOptionOrThrow(solver, "lucky", 0);
    setKissatOptionOrThrow(solver, "luckyearly", 0);
    setKissatOptionOrThrow(solver, "luckylate", 0);
    // These local proofs are already bounded by an engine-level conflict
    // limit. Sampling the AES reset-image proof with a larger cap showed the
    // extra time going into recursive learned-clause shrinking/minimization
    // rather than useful propagation, so keep this shortcut on a cheap CDCL
    // path and let UNKNOWN fall through to exact validation.
    setKissatOptionOrThrow(solver, "minimize", 0);
    setKissatOptionOrThrow(solver, "shrink", 0);

    (void)coneSymbols;
    // Reset-expression solvers are short-lived and rebuilt for each PDR
    // candidate.  Sampling showed even moderate AES reset-image proofs spending
    // most wall time in speculative probe/sweep/kitten preprocessing, so keep
    // these local proof solvers on a direct CDCL path for every cone size.
    setKissatOptionOrThrow(solver, "preprocess", 0);
    setKissatOptionOrThrow(solver, "simplify", 0);
    setKissatOptionOrThrow(solver, "preprocesscongruence", 0);
    setKissatOptionOrThrow(solver, "preprocessprobe", 0);
    setKissatOptionOrThrow(solver, "congruence", 0);
    setKissatOptionOrThrow(solver, "probe", 0);
    setKissatOptionOrThrow(solver, "probeinit", 0);
    setKissatOptionOrThrow(solver, "eliminate", 0);
    setKissatOptionOrThrow(solver, "eliminateinit", 0);
  }

private:
  static bool setKissatOptionIfSupported(kissat* solver, const char* name, int value) {
    kissat_set_option(solver, name, value);
    return kissat_get_option(solver, name) == value;
  }

  static void setKissatOptionOrThrow(kissat* solver, const char* name, int value) {
    // Kissat option availability varies across the embedded builds used by
    // CMake, Bazel, and CI. These profiles are performance hints only; falling
    // back to the solver default is better than aborting an otherwise valid SEC
    // proof when an option such as `quiet` is not present in that build.
    (void)setKissatOptionIfSupported(solver, name, value);
  }

  static bool setCadicalOptionIfSupported(
      CaDiCaL::Solver* solver, const char* name, int value) {
    return CaDiCaL::Solver::is_valid_option(name) && solver->set(name, value);
  }

  KEPLER_FORMAL::Config::SolverType solverType_;
  std::unique_ptr<Glucose::SimpSolver> glucoseSolver_;
  std::unique_ptr<CaDiCaL::Solver> cadicalSolver_;
  void* kissatSolver_ = nullptr;
  int kissatNumVars_ = 0;
  int kissatReservedVars_ = 0;
  int cadicalNumVars_ = 0;
  int cadicalReservedVars_ = 0;
  std::vector<int> lastAssumptions_;
  SolveStatus lastAssumptionSolveStatus_ = SolveStatus::Unknown;
};
