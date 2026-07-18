use crate::datastructures::{Assignment, Model};
use crate::errors::LngResult;
use crate::formulas::{EncodedFormula, FormulaFactory, Literal, Variable};
use crate::handlers::{CancelableResult, ComputationHandler, LngEvent};
use crate::solver::SolverError;
use crate::solver::maxsat::MaxSatResult::{Optimum, Undef, Unsatisfiable};
use crate::solver::maxsat::{
    Algorithm, CardinalEncoding, GraphType, MaxSatConfig, MaxSatResult, MaxSatStats, MergeStrategy,
    PbEncoding, Symmetry, Verbosity, WeightStrategy,
};
use logicng_open_wbo_sys::ffi;
use std::collections::{BTreeSet, HashMap};

pub(super) struct OpenWboSolver {
    solver: *mut ffi::MaxSAT,
    formula: *mut ffi::MaxSATFormula,
    var_map_down: HashMap<Variable, i32>,
    var_map_up: Vec<Variable>,
    status: ffi::StatusCode,
    model: Option<Model>,
    algorithm: Algorithm,
    config: MaxSatConfig,
}

impl OpenWboSolver {
    pub(super) fn new(algorithm: &Algorithm, config: &MaxSatConfig) -> LngResult<Self> {
        let solver = match algorithm {
            Algorithm::Wbo => wbo_solver(config),
            Algorithm::Oll => oll_solver(config),
            Algorithm::LinearSu => linear_su_solver(config),
            Algorithm::PartMsu3 => part_msu_3_solver(config),
            Algorithm::Msu3 => msu_3_solver(config),
        }?;

        let formula = unsafe { ffi::new_formula() };
        check_error()?;
        if formula.is_null() {
            return Err(SolverError::InvalidExternalResponse.into());
        }

        Ok(Self {
            solver,
            formula,
            status: ffi::StatusCode::Unknown,
            var_map_down: HashMap::default(),
            var_map_up: Vec::default(),
            model: None,
            algorithm: algorithm.clone(),
            config: config.clone(),
        })
    }

    pub(super) fn add_soft_clause(
        &mut self,
        weight: u64,
        formula: &EncodedFormula,
        f: &FormulaFactory,
    ) -> LngResult<()> {
        if weight < 1 {
            return Err(SolverError::IllegalWeightedClause.into());
        }
        if weight > 1 && !self.algorithm.weighted(&self.config) {
            return Err(SolverError::IllegalWeightedClause.into());
        }

        let clause = self.convert_clause(formula, f)?;
        unsafe {
            ffi::add_soft_clause(self.formula, weight, clause);
        };
        check_error()
    }

    pub(super) fn add_hard_clause(
        &mut self,
        formula: &EncodedFormula,
        f: &FormulaFactory,
    ) -> LngResult<()> {
        let clause = self.convert_clause(formula, f)?;
        unsafe { ffi::add_hard_clause(self.formula, clause) };
        check_error()
    }

    fn convert_clause(
        &mut self,
        formula: &EncodedFormula,
        f: &FormulaFactory,
    ) -> LngResult<*mut ffi::Clause> {
        let clause = unsafe { ffi::new_clause() };
        check_error()?;
        if clause.is_null() {
            return Err(SolverError::InvalidExternalResponse.into());
        }

        for lit in &*formula.literals(f) {
            let mut wbo_var = self.add_var(lit.variable());
            wbo_var += 1; //Name representation for OpenWBO is "Index representation" + 1
            if let Literal::Neg(_) = lit {
                wbo_var *= -1;
            }
            unsafe {
                ffi::add_literal(self.formula, clause, wbo_var);

                let err = ffi::get_error();
                if err != ffi::OpenWboError::NoError {
                    ffi::drop_clause(clause);
                    return Err(SolverError::ExternalError { error: err }.into());
                }
            };
        }
        Ok(clause)
    }

    fn add_var(&mut self, var: Variable) -> i32 {
        if let Some(i) = self.var_map_down.get(&var) {
            return *i;
        }

        #[allow(
            clippy::cast_precision_loss,
            clippy::cast_possible_truncation,
            clippy::cast_possible_wrap
        )]
        let index = self.var_map_down.len() as i32;
        self.var_map_down.insert(var, index);
        self.var_map_up.push(var);
        index
    }

    pub(super) fn search(
        &mut self,
        handler: &mut dyn ComputationHandler,
    ) -> LngResult<CancelableResult<MaxSatResult>> {
        let mut formula = unsafe {
            let l = ffi::new_formula();
            check_error()?;
            if l.is_null() {
                return Err(SolverError::InvalidExternalResponse.into());
            }
            l
        };
        // we must have a valid formula in the `self.formula` field
        // s.t. we don't have a dangling pointer when we drop the struct.
        std::mem::swap(&mut self.formula, &mut formula);
        unsafe {
            ffi::load_formula(self.solver, formula);
            check_error()?;
        };

        struct CallbackContext<'a> {
            handler: &'a mut dyn ComputationHandler,
            cause: Option<LngEvent>,
        }

        unsafe fn callback(context: usize, event: u32, _: u64) -> bool {
            let context = unsafe { &mut *(context as *mut CallbackContext<'_>) };
            let event = if event == 1 {
                LngEvent::SatConflictDetected
            } else {
                LngEvent::MaxSatSolverCall
            };
            let resume = context.handler.should_resume(event.clone());
            if !resume {
                context.cause = Some(event);
            }
            resume
        }

        let mut context = CallbackContext {
            handler,
            cause: None,
        };
        let mut native_handler = logicng_open_wbo_sys::MaxSatHandler::new(
            (&mut context as *mut CallbackContext<'_>) as usize,
            callback,
        );
        let code = unsafe { ffi::search(self.solver, &mut native_handler) };
        check_error()?;
        self.status = code;
        let result = self.status()?;
        if let Some(cause) = context.cause {
            if unsafe { ffi::get_model_size(self.solver) } > 0 {
                Ok(CancelableResult::Partial(
                    Optimum(unsafe { ffi::ub_cost(self.solver) }),
                    cause,
                ))
            } else {
                Ok(CancelableResult::Canceled(cause))
            }
        } else {
            Ok(CancelableResult::Ok(result))
        }
    }

    pub(super) fn status(&self) -> LngResult<MaxSatResult> {
        match self.status {
            ffi::StatusCode::Satisfiable | ffi::StatusCode::Optimum => {
                let c = unsafe { ffi::ub_cost(self.solver) };
                check_error()?;
                Ok(Optimum(c))
            }
            ffi::StatusCode::Unsatisfiable => Ok(Unsatisfiable),
            ffi::StatusCode::Unknown | ffi::StatusCode::Canceled => Ok(Undef),
            _ => Err(SolverError::InvalidExternalResponse.into()),
        }
    }

    pub(super) fn model(&mut self, selection_variables: &BTreeSet<Variable>) -> LngResult<Model> {
        match (&self.model, &self.status) {
            (Some(model), _) => Ok(model.clone()),
            (
                None,
                &ffi::StatusCode::Optimum
                | &ffi::StatusCode::Satisfiable
                | &ffi::StatusCode::Unknown
                | &ffi::StatusCode::Canceled,
            ) if unsafe { ffi::get_model_size(self.solver) } > 0 => {
                let m = self.create_model(selection_variables)?;
                Ok(m)
            }
            _ => Err(SolverError::IllegalModelRequest.into()),
        }
    }

    pub(super) fn assignment(
        &mut self,
        selection_variables: &BTreeSet<Variable>,
    ) -> LngResult<Assignment> {
        match (&self.model, &self.status) {
            (Some(model), _) => Ok(model.into()),
            (
                None,
                &ffi::StatusCode::Optimum
                | &ffi::StatusCode::Satisfiable
                | &ffi::StatusCode::Unknown
                | &ffi::StatusCode::Canceled,
            ) if unsafe { ffi::get_model_size(self.solver) } > 0 => {
                let m = self.create_model(selection_variables)?;
                Ok(m.into())
            }
            _ => Err(SolverError::IllegalModelRequest.into()),
        }
    }

    fn create_model(&mut self, selection_variables: &BTreeSet<Variable>) -> LngResult<Model> {
        unsafe {
            let model_size = ffi::get_model_size(self.solver);
            check_error()?;
            if model_size == 0 {
                return Err(SolverError::InvalidExternalResponse.into());
            }

            let model_ptr = ffi::get_model(self.solver);
            check_error()?;
            if model_ptr.is_null() {
                return Err(SolverError::InvalidExternalResponse.into());
            }

            let mut pos_var = Vec::default();
            let mut neg_var = Vec::default();
            let model_slice = std::slice::from_raw_parts(model_ptr, model_size as usize);
            for (var_index, val) in model_slice.iter().enumerate() {
                let variable = self.var_map_up[var_index];
                if selection_variables.contains(&variable) {
                    continue;
                }
                if *val {
                    pos_var.push(variable);
                } else {
                    neg_var.push(variable);
                }
            }
            ffi::drop_model(model_ptr);

            let model = Model::new(pos_var, neg_var);
            self.model = Some(model.clone());
            Ok(model)
        }
    }

    pub(super) fn stats(&self) -> MaxSatStats {
        #[allow(
            clippy::cast_precision_loss,
            clippy::cast_sign_loss,
            clippy::cast_lossless
        )]
        unsafe {
            let ubc = if ffi::get_model_size(self.solver) == 0 {
                None
            } else {
                Some(ffi::ub_cost(self.solver))
            };
            let nbs = ffi::nb_satisfiable(self.solver);
            let nbc = ffi::nb_cores(self.solver);
            let avg_cs = if nbc == 0 {
                0.0
            } else {
                (ffi::sum_size_cores(self.solver) as f64) / (nbc as f64)
            };
            let nbsc = ffi::nb_symmetry_clauses(self.solver);

            MaxSatStats {
                ub_cost: ubc,
                nb_cores: nbc as u64,
                avg_core_size: avg_cs,
                nb_satisfied: nbs as u64,
                nb_sym_clauses: nbsc as u64,
            }
        }
    }
}

impl Drop for OpenWboSolver {
    fn drop(&mut self) {
        unsafe {
            //Dropping the algorithm, will also drop the inherent formula.
            ffi::drop_algorithm(self.solver);
            ffi::drop_formula(self.formula);
        };
    }
}

fn wbo_solver(config: &MaxSatConfig) -> LngResult<*mut ffi::MaxSAT> {
    let (sym, limit) = convert_symmetry(&config.symmetry);
    let verb = convert_verbosity(&config.verbosity);
    let weight = convert_weight(&config.weight_strategy);

    unsafe {
        let solver = ffi::wbo(verb, weight, sym, limit);
        check_error()?;

        if solver.is_null() {
            Err(SolverError::InitializationError.into())
        } else {
            Ok(solver)
        }
    }
}

fn linear_su_solver(config: &MaxSatConfig) -> LngResult<*mut ffi::MaxSAT> {
    let verb = convert_verbosity(&config.verbosity);
    let enc = convert_card_encoding(&config.cardinal_encoding);
    let pb = convert_pb(&config.pb_encoding);

    unsafe {
        let solver = ffi::linear_su(verb, config.bmo, enc, pb);
        check_error()?;

        if solver.is_null() {
            Err(SolverError::InitializationError.into())
        } else {
            Ok(solver)
        }
    }
}

fn oll_solver(config: &MaxSatConfig) -> LngResult<*mut ffi::MaxSAT> {
    let verb = convert_verbosity(&config.verbosity);

    unsafe {
        let solver = ffi::oll(verb, ffi::CardEncoding::Totalizer);
        check_error()?;

        if solver.is_null() {
            return Err(SolverError::InitializationError.into());
        }

        Ok(solver)
    }
}

fn part_msu_3_solver(config: &MaxSatConfig) -> LngResult<*mut ffi::MaxSAT> {
    let verb = convert_verbosity(&config.verbosity);
    let merge = convert_merge_strategy(&config.merge_strategy);
    let graph = convert_graph_type(&config.graph_type);

    unsafe {
        let solver = ffi::part_msu_3(verb, merge, graph, ffi::CardEncoding::Totalizer);
        check_error()?;

        if solver.is_null() {
            return Err(SolverError::InitializationError.into());
        }
        Ok(solver)
    }
}

fn msu_3_solver(config: &MaxSatConfig) -> LngResult<*mut ffi::MaxSAT> {
    let verb = convert_verbosity(&config.verbosity);

    unsafe {
        let solver = ffi::msu_3(verb);
        check_error()?;

        if solver.is_null() {
            return Err(SolverError::InitializationError.into());
        }

        Ok(solver)
    }
}

const fn convert_verbosity(verbosity: &Verbosity) -> ffi::Verbosity {
    match verbosity {
        Verbosity::None => ffi::Verbosity::Minimal,
        Verbosity::Some => ffi::Verbosity::Some,
    }
}

const fn convert_weight(weight: &WeightStrategy) -> ffi::Weight {
    match weight {
        WeightStrategy::None => ffi::Weight::None,
        WeightStrategy::Normal => ffi::Weight::Normal,
        WeightStrategy::Diversify => ffi::Weight::Diversify,
    }
}

const fn convert_symmetry(symmetry: &Symmetry) -> (bool, i32) {
    match symmetry {
        Symmetry::None => (false, i32::MAX),
        Symmetry::Sym(l) => (true, *l),
    }
}

const fn convert_card_encoding(enc: &CardinalEncoding) -> ffi::CardEncoding {
    match enc {
        CardinalEncoding::CNetworks => ffi::CardEncoding::CNetworks,
        CardinalEncoding::Totalizer => ffi::CardEncoding::Totalizer,
        CardinalEncoding::MTotalizer => ffi::CardEncoding::MTotalizer,
    }
}

const fn convert_pb(pb: &PbEncoding) -> ffi::PB {
    match pb {
        PbEncoding::Swc => ffi::PB::Swc,
        PbEncoding::Gte => ffi::PB::Gte,
        PbEncoding::Adder => ffi::PB::Adder,
    }
}

const fn convert_merge_strategy(merge: &MergeStrategy) -> ffi::Merge {
    match merge {
        MergeStrategy::Sequential => ffi::Merge::Sequential,
        MergeStrategy::SequentialSorted => ffi::Merge::SequentialSorted,
        MergeStrategy::Binary => ffi::Merge::Binary,
    }
}

const fn convert_graph_type(graph: &GraphType) -> ffi::GraphType {
    match graph {
        GraphType::Vig => ffi::GraphType::Vig,
        GraphType::CVig => ffi::GraphType::CVig,
        GraphType::Res => ffi::GraphType::Res,
    }
}

fn check_error() -> LngResult<()> {
    unsafe {
        let err = ffi::get_error();
        if err == ffi::OpenWboError::NoError {
            Ok(())
        } else {
            Err(SolverError::ExternalError { error: err }.into())
        }
    }
}
