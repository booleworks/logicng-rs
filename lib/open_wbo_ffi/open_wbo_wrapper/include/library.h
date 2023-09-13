#ifndef WRAPPER_API_LIBRARY_H
#define WRAPPER_API_LIBRARY_H

#include "MaxSAT.h"
#include "MaxSATFormula.h"
#include "core/SolverTypes.h"
#include "MaxSAT_Partition.h"
//#include "MaxTypes.h"

#include <string>

namespace wrapper {
    using MaxSAT = openwbo::MaxSAT;
    using MaxSATFormula = openwbo::MaxSATFormula;
    using Clause = Glucose::vec<Lit>;

    //Enum types
    enum Verbosity {
        Minimal = openwbo::_VERBOSITY_MINIMAL_,
        Some = openwbo::_VERBOSITY_SOME_,
    };

    enum Weight {
        None = openwbo::_WEIGHT_NONE_,
        Normal = openwbo::_WEIGHT_NORMAL_,
        Diversify = openwbo::_WEIGHT_DIVERSIFY_,
    };

    enum StatusCode {
        Satisfiable = openwbo::_SATISFIABLE_,
        Unsatisfiable = openwbo::_UNSATISFIABLE_,
        Optimum = openwbo::_OPTIMUM_,
        Unknown = openwbo::_UNKNOWN_,
        Error = openwbo::_ERROR_,
    };

    enum CardEncoding {
        CNetworks = openwbo::_CARD_CNETWORKS_,
        Totalizer = openwbo::_CARD_TOTALIZER_,
        MTotalizer = openwbo::_CARD_MTOTALIZER_,
    };

    enum PB {
        Swc = openwbo::_PB_SWC_,
        Gte = openwbo::_PB_GTE_,
        Adder = openwbo::_PB_ADDER_,
    };

    enum Merge {
        Sequential = openwbo::_PART_SEQUENTIAL_,
        SequentialSorted = openwbo::_PART_SEQUENTIAL_SORTED_,
        Binary = openwbo::_PART_BINARY_,
    };

    enum GraphType {
        Vig = openwbo::graphType_::VIG_GRAPH,
        CVig = openwbo::graphType_::CVIG_GRAPH,
        Res = openwbo::graphType_::RES_GRAPH,
    };

    enum OpenWboError {
        NoError,
        MaxSATError,
        OutOfMemoryError,
        InvalidRequest,
    };

    OpenWboError get_error();

    MaxSAT *linear_su(Verbosity verbosity, bool bmo, CardEncoding enc, PB pb);

    MaxSAT *wbo(Verbosity verbosity, Weight weight, bool symmetry, int32_t limit);

    MaxSAT *oll(Verbosity verbosity, CardEncoding enc);

    MaxSAT *part_msu_3(Verbosity verbosity, Merge merge, GraphType graph, CardEncoding enc);

    MaxSAT *msu_3(Verbosity verbosity);

    MaxSATFormula *new_formula();

    void drop_algorithm(MaxSAT *algorithm);

    void drop_model(bool *model);

    void drop_formula(MaxSATFormula *formula);

    void drop_clause(Clause *clause);

    Clause *new_clause();

    void load_formula(MaxSAT *algorithm, MaxSATFormula *formula);

    StatusCode search(MaxSAT *algorithm);

    bool *get_model(MaxSAT *algorithm);

    uint32_t get_model_size(MaxSAT *algorithm);

    void add_literal(MaxSATFormula *formula, Clause *clause, int32_t var);

    void add_hard_clause(MaxSATFormula* formula, Clause* clause);

    void add_soft_clause(MaxSATFormula* formula, uint64_t weight, Clause* clause);

    int nb_cores(MaxSAT *algorithm);

    int nb_symmetry_clauses(MaxSAT *algorithm);

    int nb_satisfiable(MaxSAT *algorithm);

    uint64_t sum_size_cores(MaxSAT *algorithm);

    uint64_t ub_cost(MaxSAT *algorithm);
    
    namespace {
        class ExposeProtectedFields : MaxSAT {
        public:

            int get_nb_cores() {
                return nbCores;
            }

            int get_nb_symmetry_clauses() {
                return nbSymmetryClauses;
            }

            int get_nb_satisfiable() {
                return nbSatisfiable;
            }

            uint64_t get_sum_size_cores(){
                return sumSizeCores;
            }

            uint64_t get_ub_cost() {
                return ubCost;
            }

            int get_model_size() {
                return model.size();
            }

            bool *get_model() {
                if (model.size() == 0) {
                    return nullptr;
                }

                auto *model_array = (bool*) malloc(sizeof(bool) * ((size_t) model.size()));

                if(model_array == nullptr) {
                    return nullptr;
                }

                for (int i = 0; i < model.size(); ++i) {
                    auto res = model[i];
                    model_array[i] = (res == l_True);
                }
                return model_array;
            }
        };
    }
}



#endif //WRAPPER_API_LIBRARY_H
