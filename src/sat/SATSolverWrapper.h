#pragma once

#include <vector>
#include <string>
#include <stdexcept>
#include <memory>

#include "simp/SimpSolver.h"

extern "C" {
#include "kissat.h"
}

#define USE_KISSAT

class SATSolverWrapper {
public:
    enum SolverType { GLUCOSE, KISSAT };

    static SolverType selectBackend() {
    #ifdef USE_KISSAT
        return KISSAT;
    #else
        return GLUCOSE;
    #endif
    }

    explicit SATSolverWrapper(SolverType type = GLUCOSE)
        : solverType_(type)
    {
        if (solverType_ == GLUCOSE) {
            glucoseSolver_ = std::make_unique<Glucose::SimpSolver>();
        } else if (solverType_ == KISSAT) {
            kissatSolver_ = kissat_init();
            kissatNumVars_ = 0;
        } else {
            throw std::invalid_argument("Unknown solver type");
        }
    }

    ~SATSolverWrapper() {
        if (solverType_ == KISSAT && kissatSolver_) {
            kissat_release(static_cast<kissat*>(kissatSolver_));
        }
    }

    // Create a new variable (returns 0-based index)
    int newVar() {
        if (solverType_ == GLUCOSE) {
            return glucoseSolver_->newVar();
        } else if (solverType_ == KISSAT) {
            // Kissat does not require explicit variable creation, but we track max var.
            return kissatNumVars_++;
        }
        throw std::runtime_error("Unknown solver type");
    }

    // Add a clause, literals are signed ints (positive=normal, negative=inverted)
    void addClause(const std::vector<int>& lits) {
        if (solverType_ == GLUCOSE) {
            Glucose::vec<Glucose::Lit> clause;
            for (int lit : lits) {
                int var = std::abs(lit);
                while (var >= glucoseSolver_->nVars())
                    glucoseSolver_->newVar();
                clause.push((lit > 0) ? Glucose::mkLit(var) : ~Glucose::mkLit(var));
            }
            glucoseSolver_->addClause(clause);
        } else if (solverType_ == KISSAT) {
            // Kissat expects 1-based literals, positive for normal, negative for inverted.
            // API: void kissat_add(kissat *, int lit); (0 to terminate)
            // Our convention: input lits are signed ints, 0-based variable index.
            for (int lit : lits) {
                int var = std::abs(lit);
                if (var >= kissatNumVars_)
                    kissatNumVars_ = var + 1;
                int kissatLit = (lit > 0 ? var + 1 : -(var + 1));
                kissat_add(static_cast<kissat*>(kissatSolver_), kissatLit);
            }
            kissat_add(static_cast<kissat*>(kissatSolver_), 0); // end of clause
        } else {
            throw std::runtime_error("Unknown solver type");
        }
    }

    // Solve the SAT instance
    bool solve() {
        if (solverType_ == GLUCOSE) {
            return glucoseSolver_->solve();
        } else if (solverType_ == KISSAT) {
            int res = kissat_solve(static_cast<kissat*>(kissatSolver_));
            return res == 10; // 10 = SAT, 20 = UNSAT
        }
        throw std::runtime_error("Unknown solver type");
    }

    // Access underlying solver for functions like tseitinEncode
    // For Glucose: returns Glucose::SimpSolver&
    // For Kissat: returns kissat*
    void* getSolver() {
        if (solverType_ == GLUCOSE) {
            return glucoseSolver_.get();
        } else if (solverType_ == KISSAT) {
            return kissatSolver_;
        }
        return nullptr;
    }

    SolverType getSolverType() const { return solverType_; }

private:
    SolverType solverType_;
    std::unique_ptr<Glucose::SimpSolver> glucoseSolver_;
    void* kissatSolver_ = nullptr;
    int kissatNumVars_ = 0;
};
