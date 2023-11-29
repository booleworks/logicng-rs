#include "include/library.h"

namespace wrapper {

    Solver *new_solver() {
        return new InteractiveSolver{};
    }

    void drop_solver(Solver* solver) {
        delete solver;
    }

    void add_clause(Solver* solver, int32_t const* clauses, uint32_t size) {
        solver->add_clause(clauses, size);
    }

    const std::string& solve(Solver* solver) {
        solver->solve();
        return solver->last_result;
    }
}