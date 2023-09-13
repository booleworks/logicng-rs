#include <cmath>
#include "include/library.h"

#include "algorithms/Alg_LinearSU.h"
#include "algorithms/Alg_WBO.h"
#include "algorithms/Alg_OLL.h"
#include "algorithms/Alg_MSU3.h"
#include "algorithms/Alg_PartMSU3.h"

namespace wrapper {

    OpenWboError last_error = OpenWboError::NoError;
    OpenWboError get_error() {
        auto e = last_error;
        last_error = OpenWboError::NoError;
        return e;
    }

    MaxSAT *linear_su(Verbosity verbosity, bool bmo, CardEncoding enc, PB pb) {
        return new openwbo::LinearSU(verbosity, bmo, enc, pb);
    }

    MaxSAT *wbo(Verbosity verbosity, Weight weight, bool symmetry, int32_t limit) {
        return new openwbo::WBO(verbosity, weight, symmetry, limit);
    }

    MaxSAT *oll(Verbosity verbosity, CardEncoding enc) {
        return new openwbo::OLL(verbosity, enc);
    }

    MaxSAT *part_msu_3(Verbosity verbosity, Merge merge, GraphType graph, CardEncoding enc) {
        return new openwbo::PartMSU3(verbosity, merge, graph, enc);
    }

    MaxSAT *msu_3(Verbosity verbosity) {
        return new openwbo::MSU3(verbosity);
    }

    void drop_algorithm(MaxSAT *algorithm) {
        //This also deletes the formula.
        delete algorithm;
    }

    void drop_model(bool *model) {
        free(model);
    }

    //Don't call this if the formula is/was part of a MaxSAT-Algorithm
    void drop_formula(MaxSATFormula *formula) {
        delete formula;
    }

    //Don't call this if the clause is/was part of a MaxSATFormula
    void drop_clause(Clause *clause) {
        delete clause;
    }

    MaxSATFormula *new_formula() {
        auto *F = new openwbo::MaxSATFormula();
        F->setMaximumWeight(1);
        return F;
    }

    Clause *new_clause() {
        auto *C = new Glucose::vec<Lit>();
        return C;
    }

    void load_formula(MaxSAT *algorithm, MaxSATFormula *formula) {
        algorithm->loadFormula(formula);
    }

    StatusCode search(MaxSAT *algorithm) {
        auto formula = algorithm->getMaxSATFormula();
        if (formula->getMaximumWeight() == 1) {
            formula->setProblemType(openwbo::_UNWEIGHTED_);
        } else {
            formula->setProblemType(openwbo::_WEIGHTED_);
        }

        try {
            auto status = algorithm->search();
            return (StatusCode) status;
        } catch (const openwbo::MaxSATException& e) {
            last_error = OpenWboError::MaxSATError;
        } catch (const Glucose::OutOfMemoryException& e) {
            last_error = OpenWboError::OutOfMemoryError;
        }
        return StatusCode::Error;
    }

    void add_literal(MaxSATFormula *formula, Clause *clause, int32_t var) {
        if (var == 0) {
            last_error = OpenWboError::InvalidRequest;
        } else {
            int32_t v = std::abs(var) - 1;

            while (v >= formula->nVars()) {
                formula->newVar();
            }

            Lit lit = Glucose::mkLit(v, var < 0);
            clause->push(lit);
        }
    }

    void add_hard_clause(MaxSATFormula *formula, Clause *clause) {
        formula->addHardClause(*clause);
    }

    void add_soft_clause(MaxSATFormula *formula, uint64_t weight, Clause *clause) {
        if (weight >= 1) {
            formula->setMaximumWeight(weight);
            formula->updateSumWeights(weight);
            formula->addSoftClause(weight, *clause);
        } else {
            last_error = OpenWboError::InvalidRequest;
        }
    }

    bool *get_model(MaxSAT *algorithm) {
        if(algorithm->getStatus() == openwbo::StatusCode::_OPTIMUM_
        || algorithm->getStatus() == openwbo::StatusCode::_SATISFIABLE_) {
            return ((ExposeProtectedFields*) algorithm)->get_model();
        } else {
            last_error = OpenWboError::InvalidRequest;
            return nullptr;
        }
    }

    uint32_t get_model_size(MaxSAT *algorithm) {
        return (uint32_t) ((ExposeProtectedFields*) algorithm)->get_model_size();
    }

    //In order to get a protected fields of the MaxSAT classes, we let inherit a class from MaxSAT, which then exposes
    //those fields. In the following functions we will then cast to that class and access those fields.
    //This is a terrible approach! But as long as we cannot edit the library, we have to do some kind of workaround.
    int nb_cores(MaxSAT *algorithm) {
        return ((ExposeProtectedFields *) algorithm)->get_nb_cores();
    }

    int nb_symmetry_clauses(MaxSAT *algorithm) {
        return ((ExposeProtectedFields *) algorithm)->get_nb_symmetry_clauses();
    }

    int nb_satisfiable(MaxSAT *algorithm) {
        return ((ExposeProtectedFields *) algorithm)->get_nb_satisfiable();
    }

    uint64_t sum_size_cores(MaxSAT *algorithm) {
        return ((ExposeProtectedFields *) algorithm)->get_sum_size_cores();
    }

    uint64_t ub_cost(MaxSAT *algorithm) {
        return ((ExposeProtectedFields *) algorithm)->get_ub_cost();
    }
}


