/// Represents a state of a SAT-Solver.
///
/// You can obtain the current state of a [`MiniSat`](`crate::solver::minisat::MiniSat`)-Solver by calling
/// [`MiniSat::save_state()`](`crate::solver::minisat::MiniSat::save_state`).
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct SolverState {
    pub(crate) id: usize,
    pub(crate) state: [usize; 7],
}

impl SolverState {
    /// Manual construction of a new state.
    pub const fn new(id: usize, state: [usize; 7]) -> Self {
        Self { id, state }
    }
}
