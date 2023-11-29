#include "interactive_solver.h"

namespace wrapper {

    using Solver = InteractiveSolver;
    using Clause = vector<int32_t>;

    Solver *new_solver();

    void drop_solver(Solver* solver);

    void add_clause(Solver* solver, int32_t const *clauses, uint32_t size);

    const std::string& solve(Solver* solver);
}