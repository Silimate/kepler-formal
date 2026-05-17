#pragma once

#include <algorithm>
#include <vector>
#include <string>
#include <cstdlib>
#include <initializer_list>
#include <stdexcept>
#include <memory>

#include "simp/SimpSolver.h"
extern "C" {
  #include "kissat.h"
}

#include "../config/Config.h"

//#define USE_KISSAT

class SATSolverWrapper {
public:

  explicit SATSolverWrapper(KEPLER_FORMAL::Config::SolverType type = KEPLER_FORMAL::Config::SolverType::GLUCOSE)
    : solverType_(type) {
    if (solverType_ == KEPLER_FORMAL::Config::SolverType::GLUCOSE) {
      glucoseSolver_ = std::make_unique<Glucose::SimpSolver>();
      // Keep embedded solver calls quiet. The command-line Glucose default is
      // already low, but SimpSolver still prints eliminated-clause summaries at
      // verbosity 0.
      glucoseSolver_->verbosity = -1;
    } else if (solverType_ == KEPLER_FORMAL::Config::SolverType::KISSAT) {
      kissatSolver_ = kissat_init();
      kissatNumVars_ = 0;
      kissatReservedVars_ = 0;
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
    }
  }

  void reserveAdditionalVars(size_t additionalVars) {
    if (solverType_ == KEPLER_FORMAL::Config::SolverType::KISSAT) {
      // Formula encoders create Tseitin variables after the frame variables
      // have already been allocated. Reserving from the wrapper's current
      // variable count targets Kissat's variable-vector growth directly without
      // changing the external literal numbering convention.
      reserveVars(static_cast<size_t>(kissatNumVars_) + additionalVars);
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
          glucoseSolver_->newVar();
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
    } else {
      // LCOV_EXCL_START
      throw std::runtime_error("Unknown solver type");
      // LCOV_EXCL_STOP
    }
  }

 public:
  bool solve() {
    if (solverType_ == KEPLER_FORMAL::Config::SolverType::GLUCOSE) {
      return glucoseSolver_->solve();
    } else if (solverType_ == KEPLER_FORMAL::Config::SolverType::KISSAT) {
      int res = kissat_solve(static_cast<kissat*>(kissatSolver_));
      return res == 10; // 10 = SAT, 20 = UNSAT
    }
    // LCOV_EXCL_START
    throw std::runtime_error("Unknown solver type");
    // LCOV_EXCL_STOP
  }

  bool solveWithAssumptions(const std::vector<int>& assumptions) {
    if (solverType_ == KEPLER_FORMAL::Config::SolverType::GLUCOSE) {
      Glucose::vec<Glucose::Lit> glucoseAssumptions;
      for (int lit : assumptions) {
        if (lit == 0 || lit == 1) {
          // LCOV_EXCL_START
          throw std::runtime_error("Constant literal (0/1) passed as Glucose assumption");
          // LCOV_EXCL_STOP
        }
        const int var = std::abs(lit) - 2;
        if (var < 0) {
          // LCOV_EXCL_START
          throw std::runtime_error("Invalid literal (<2) passed as Glucose assumption");
          // LCOV_EXCL_STOP
        }
        while (var >= glucoseSolver_->nVars()) {
          glucoseSolver_->newVar();
        }
        glucoseAssumptions.push((lit > 0) ? Glucose::mkLit(var)
                                          : ~Glucose::mkLit(var));
      }
      // Repeated CEGAR reachability checks reuse the same solver and vary only
      // assumptions. Running variable elimination on each assumption solve
      // dominates those small queries, so keep this path in plain CDCL mode.
      return glucoseSolver_->solve(
          glucoseAssumptions,
          /*do_simp=*/false,
          /*turn_off_simp=*/true);
    } else if (solverType_ == KEPLER_FORMAL::Config::SolverType::KISSAT) {
      // This vendored Kissat exposes only the partial IPASIR API and has no
      // assumption call. Callers that need repeated assumption solves should use
      // Glucose for that local incremental query.
      if (assumptions.empty()) {
        return solve();
      }
      throw std::runtime_error("Kissat assumptions are not available in this build");
    }
    // LCOV_EXCL_START
    throw std::runtime_error("Unknown solver type");
    // LCOV_EXCL_STOP
  }

  std::vector<int> failedAssumptions() const {
    if (solverType_ != KEPLER_FORMAL::Config::SolverType::GLUCOSE) {
      return {};
    }

    std::vector<int> failed;
    failed.reserve(glucoseSolver_->conflict.size());
    for (int i = 0; i < glucoseSolver_->conflict.size(); ++i) {
      const auto lit = glucoseSolver_->conflict[i];
      const int externalVar = Glucose::var(lit) + 2;
      const int conflictLiteral =
          Glucose::sign(lit) ? -externalVar : externalVar;
      // Glucose exposes the final conflict clause over the negated failed
      // assumptions. Return the caller's original assumption literals so SEC
      // can map them directly back to PDR cube literals.
      failed.push_back(-conflictLiteral);
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
    } else {
      throw std::runtime_error("Unknown solver type");  // LCOV_EXCL_LINE
    }

    return lit > 0 ? positiveValue : !positiveValue;
  }

  void* getSolver() {
    if (solverType_ == KEPLER_FORMAL::Config::SolverType::GLUCOSE) {
      return glucoseSolver_.get();
    } else if (solverType_ == KEPLER_FORMAL::Config::SolverType::KISSAT) {
      return kissatSolver_;
    }
    return nullptr;
  }

  KEPLER_FORMAL::Config::SolverType getSolverType() const { return solverType_; }

  void configureForSecConeProof(size_t coneSymbols = 0) {
    if (solverType_ != KEPLER_FORMAL::Config::SolverType::KISSAT) {
      return;
    }

    auto* solver = static_cast<kissat*>(kissatSolver_);
    // SEC proof obligations are normally expected to be UNSAT when the designs
    // are equivalent, so bias Kissat toward its UNSAT/stable search profile.
    // Keep the rest of the default solver machinery for small and medium COIs:
    // on those instances preprocessing and clause minimization can be the real
    // speedup, and disabling them globally makes BlackParrot-style proofs worse.
    setKissatOptionOrThrow(solver, "stable", 2);

    // The threshold is intentionally based on the engine's COI size, not on a
    // design name. Medium SEC cones still benefit from Kissat's normal
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
    setKissatOptionOrThrow(solver, "preprocess", 0);
    setKissatOptionOrThrow(solver, "simplify", 0);
    setKissatOptionOrThrow(solver, "preprocesscongruence", 0);
    setKissatOptionOrThrow(solver, "preprocessprobe", 0);
    setKissatOptionOrThrow(solver, "congruence", 0);
    setKissatOptionOrThrow(solver, "probe", 0);
    setKissatOptionOrThrow(solver, "probeinit", 0);
    setKissatOptionOrThrow(solver, "eliminateinit", 0);
    setKissatOptionOrThrow(solver, "lucky", 0);
    setKissatOptionOrThrow(solver, "luckyearly", 0);
    setKissatOptionOrThrow(solver, "luckylate", 0);
    // Recursive learned-clause shrinking can dominate these very large shallow
    // equivalence cones, so disable it only for this large-cone profile.
    setKissatOptionOrThrow(solver, "minimize", 0);
    setKissatOptionOrThrow(solver, "shrink", 0);
  }

  void configureForSecPdrQuery(size_t coneSymbols = 0) {
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
    setKissatOptionOrThrow(solver, "eliminateinit", 0);
  }

private:
  static void setKissatOptionOrThrow(kissat* solver, const char* name, int value) {
    kissat_set_option(solver, name, value);
    if (kissat_get_option(solver, name) != value) {
      throw std::runtime_error(
          std::string("Failed to configure Kissat option `") + name + "`");
    }
  }

  KEPLER_FORMAL::Config::SolverType solverType_;
  std::unique_ptr<Glucose::SimpSolver> glucoseSolver_;
  void* kissatSolver_ = nullptr;
  int kissatNumVars_ = 0;
  int kissatReservedVars_ = 0;
};
