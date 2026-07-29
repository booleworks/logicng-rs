#![allow(dead_code)]

mod linear_su;
mod msu3;
mod oll;
mod solver;
mod wbo;

use crate::errors::LngResult;
use crate::solver::maxsat::openwbo_rs::config::Algorithm;
use crate::solver::maxsat::openwbo_rs::config::OpenWboConfig;

use crate::backends::MaxSatResult;
use crate::handlers::{CancelableResult, ComputationHandler};
use solver::ProblemType;
pub(crate) use solver::{MaxSatState, Solver};

pub(crate) enum OpenWboAlgorithm {
    Wbo(wbo::Wbo),
    Oll(oll::Oll),
    LinearSu(linear_su::LinearSu),
    Msu3(msu3::Msu3),
}

impl OpenWboAlgorithm {
    pub(crate) fn from_config(config: &OpenWboConfig) -> Self {
        match config.algorithm {
            Algorithm::Wbo => Self::Wbo(wbo::Wbo::new(config)),
            Algorithm::Oll => Self::Oll(oll::Oll::new()),
            Algorithm::LinearSu => Self::LinearSu(linear_su::LinearSu::new(config)),
            Algorithm::Msu3 => Self::Msu3(msu3::Msu3::new(config)),
        }
    }

    pub(crate) fn search(
        &mut self,
        solver: &mut Solver,
        handler: &mut dyn ComputationHandler,
    ) -> LngResult<CancelableResult<MaxSatResult>> {
        solver.problem_type = if solver.current_weight == 1 {
            ProblemType::Unweighted
        } else {
            ProblemType::Weighted
        };
        let state_before_solving = solver.save_state();
        // TODO Result necessary?
        let result = match self {
            Self::Wbo(algorithm) => algorithm.search(solver, handler),
            Self::Oll(algorithm) => algorithm.search(solver, handler),
            Self::LinearSu(algorithm) => Ok(algorithm.search(solver, handler)),
            Self::Msu3(algorithm) => algorithm.search(solver, handler),
        };
        solver.load_state(&state_before_solving)?;
        result
    }
}
