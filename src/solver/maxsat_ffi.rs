use crate::datastructures::{Assignment, Model};
use crate::formulas::{EncodedFormula, FormulaFactory, Literal, Variable};
use crate::solver::maxsat::MaxSatResult::{Optimum, Undef, Unsatisfiable};
use crate::solver::maxsat::{
    Algorithm, CardinalEncoding, GraphType, MaxSatConfig, MaxSatResult, MaxSatStats, MergeStrategy, PbEncoding, Symmetry, Verbosity,
    WeightStrategy,
};
use logicng_open_wbo_sys::ffi;
use std::collections::{BTreeSet, HashMap};
use std::fmt::{Debug, Display, Formatter};

/// Stores different types of errors that can happen during the setup or search
/// of the MaxSAT problem.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum MaxSatError {
    /// Error thrown by OpenWBO.
    ExternalError(ffi::OpenWboError),
    /// Error thrown if the response of OpenWBO is unexpected.
    InvalidExternalResponse,
    /// Configuration is invalid.
    IllegalConfig,
    /// Configuration does not support weighted clauses.
    IllegalWeightedClause,
    /// Solver does not have a model.
    IllegalModelRequest,
    /// Failed to initialize the solver.
    InitializationError,
}

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
    pub(super) fn new(algorithm: &Algorithm, config: &MaxSatConfig) -> Result<Self, MaxSatError> {
        let solver = match algorithm {
            Algorithm::Wbo => wbo_solver(config),
            Algorithm::Oll => oll_solver(config),
            Algorithm::LinearSu => linear_su_solver(config),
            Algorithm::PartMsu3 => part_msu_3_solver(config),
            Algorithm::Msu3 => msu_3_solver(config),
        }?;

        let formula = unsafe {
            let f = ffi::new_formula();
            check_error()?;
            if f.is_null() {
                Err(MaxSatError::InvalidExternalResponse)
            } else {
                Ok(f)
            }
        }?;

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

    pub(super) fn add_soft_clause(&mut self, weight: u64, formula: &EncodedFormula, f: &FormulaFactory) -> Result<(), MaxSatError> {
        if weight < 1 {
            return Err(MaxSatError::IllegalWeightedClause);
        }
        if weight > 1 && !self.algorithm.weighted(&self.config) {
            return Err(MaxSatError::IllegalWeightedClause);
        }

        let clause = self.convert_clause(formula, f)?;
        unsafe {
            ffi::add_soft_clause(self.formula, weight, clause);
        };
        check_error()
    }

    pub(super) fn add_hard_clause(&mut self, formula: &EncodedFormula, f: &FormulaFactory) -> Result<(), MaxSatError> {
        let clause = self.convert_clause(formula, f)?;
        unsafe { ffi::add_hard_clause(self.formula, clause) };
        check_error()
    }

    fn convert_clause(&mut self, formula: &EncodedFormula, f: &FormulaFactory) -> Result<*mut ffi::Clause, MaxSatError> {
        let clause = unsafe {
            let c = ffi::new_clause();
            check_error()?;
            if c.is_null() {
                Err(MaxSatError::InvalidExternalResponse)
            } else {
                Ok(c)
            }
        }?;

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
                    return Err(MaxSatError::ExternalError(err));
                }
            };
        }
        Ok(clause)
    }

    fn add_var(&mut self, var: Variable) -> i32 {
        if let Some(i) = self.var_map_down.get(&var) {
            return *i;
        }

        #[allow(clippy::cast_precision_loss, clippy::cast_possible_truncation, clippy::cast_possible_wrap)]
        let index = self.var_map_down.len() as i32;
        self.var_map_down.insert(var, index);
        self.var_map_up.push(var);
        index
    }

    pub(super) fn search(&mut self) -> Result<MaxSatResult, MaxSatError> {
        let mut formula = unsafe {
            let l = ffi::new_formula();
            check_error()?;
            if l.is_null() {
                return Err(MaxSatError::InvalidExternalResponse);
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

        let code = unsafe { ffi::search(self.solver) };
        check_error()?;
        self.status = code;
        self.status()
    }

    pub(super) fn status(&self) -> Result<MaxSatResult, MaxSatError> {
        match self.status {
            ffi::StatusCode::Satisfiable | ffi::StatusCode::Optimum => {
                let c = unsafe { ffi::ub_cost(self.solver) };
                check_error()?;
                Ok(Optimum(c))
            }
            ffi::StatusCode::Unsatisfiable => Ok(Unsatisfiable),
            ffi::StatusCode::Unknown => Ok(Undef),
            _ => Err(MaxSatError::InvalidExternalResponse),
        }
    }

    pub(super) fn model(&mut self, selection_variables: &BTreeSet<Variable>) -> Result<Model, MaxSatError> {
        match (&self.model, &self.status) {
            (Some(model), _) => Ok(model.clone()),
            (None, &ffi::StatusCode::Optimum | &ffi::StatusCode::Satisfiable) => {
                let m = self.create_model(selection_variables)?;
                Ok(m)
            }
            _ => Err(MaxSatError::IllegalModelRequest),
        }
    }

    pub(super) fn assignment(&mut self, selection_variables: &BTreeSet<Variable>) -> Result<Assignment, MaxSatError> {
        match (&self.model, &self.status) {
            (Some(model), _) => Ok(model.into()),
            (None, &ffi::StatusCode::Optimum | &ffi::StatusCode::Satisfiable) => {
                let m = self.create_model(selection_variables)?;
                Ok(m.into())
            }
            _ => Err(MaxSatError::IllegalModelRequest),
        }
    }

    fn create_model(&mut self, selection_variables: &BTreeSet<Variable>) -> Result<Model, MaxSatError> {
        unsafe {
            let model_size = ffi::get_model_size(self.solver);
            check_error()?;
            if model_size == 0 {
                return Err(MaxSatError::InvalidExternalResponse);
            }

            let model_ptr = ffi::get_model(self.solver);
            check_error()?;
            if model_ptr.is_null() {
                return Err(MaxSatError::InvalidExternalResponse);
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
        #[allow(clippy::cast_precision_loss, clippy::cast_sign_loss, clippy::cast_lossless)]
        unsafe {
            let ubc = if ffi::get_model_size(self.solver) == 0 { None } else { Some(ffi::ub_cost(self.solver)) };
            let nbs = ffi::nb_satisfiable(self.solver);
            let nbc = ffi::nb_cores(self.solver);
            let avg_cs = if nbc == 0 { 0.0 } else { (ffi::sum_size_cores(self.solver) as f64) / (nbc as f64) };
            let nbsc = ffi::nb_symmetry_clauses(self.solver);

            MaxSatStats { ub_cost: ubc, nb_cores: nbc as u64, avg_core_size: avg_cs, nb_satisfied: nbs as u64, nb_sym_clauses: nbsc as u64 }
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

impl Display for MaxSatError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let msg = match self {
            Self::ExternalError(ie) => format!("OpenWBO crashed internally, the last documented error was: \"{ie}\""),
            Self::IllegalConfig => String::from("The selected maxSAT algorithm doesn't support the given configuration."),
            Self::IllegalWeightedClause => String::from("The selected maxSAT algorithm doesn't support weighted clauses."),
            Self::InitializationError => String::from("Couldn't initialize maxSAT solver in openWBO library."),
            Self::InvalidExternalResponse => String::from("OpenWBO library gave a invalid response."),
            Self::IllegalModelRequest => String::from("The model can only requested if the status is \"Optimal\" or \"Satisfied\""),
        };
        f.write_str(&msg)
    }
}

impl std::error::Error for MaxSatError {}

fn wbo_solver(config: &MaxSatConfig) -> Result<*mut ffi::MaxSAT, MaxSatError> {
    let (sym, limit) = convert_symmetry(&config.symmetry);
    let verb = convert_verbosity(&config.verbosity);
    let weight = convert_weight(&config.weight_strategy);

    unsafe {
        let solver = ffi::wbo(verb, weight, sym, limit);
        check_error()?;

        if solver.is_null() {
            Err(MaxSatError::InitializationError)
        } else {
            Ok(solver)
        }
    }
}

fn linear_su_solver(config: &MaxSatConfig) -> Result<*mut ffi::MaxSAT, MaxSatError> {
    let verb = convert_verbosity(&config.verbosity);
    let enc = convert_card_encoding(&config.cardinal_encoding);
    let pb = convert_pb(&config.pb_encoding);

    unsafe {
        let solver = ffi::linear_su(verb, config.bmo, enc, pb);
        check_error()?;

        if solver.is_null() {
            Err(MaxSatError::InitializationError)
        } else {
            Ok(solver)
        }
    }
}

fn oll_solver(config: &MaxSatConfig) -> Result<*mut ffi::MaxSAT, MaxSatError> {
    let verb = convert_verbosity(&config.verbosity);

    unsafe {
        let solver = ffi::oll(verb, ffi::CardEncoding::Totalizer);
        check_error()?;

        if solver.is_null() {
            return Err(MaxSatError::InitializationError);
        }

        Ok(solver)
    }
}

fn part_msu_3_solver(config: &MaxSatConfig) -> Result<*mut ffi::MaxSAT, MaxSatError> {
    let verb = convert_verbosity(&config.verbosity);
    let merge = convert_merge_strategy(&config.merge_strategy);
    let graph = convert_graph_type(&config.graph_type);

    unsafe {
        let solver = ffi::part_msu_3(verb, merge, graph, ffi::CardEncoding::Totalizer);
        check_error()?;

        if solver.is_null() {
            return Err(MaxSatError::InitializationError);
        }
        Ok(solver)
    }
}

fn msu_3_solver(config: &MaxSatConfig) -> Result<*mut ffi::MaxSAT, MaxSatError> {
    let verb = convert_verbosity(&config.verbosity);

    unsafe {
        let solver = ffi::msu_3(verb);
        check_error()?;

        if solver.is_null() {
            return Err(MaxSatError::InitializationError);
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

fn check_error() -> Result<(), MaxSatError> {
    unsafe {
        let err = ffi::get_error();
        if err == ffi::OpenWboError::NoError {
            Ok(())
        } else {
            Err(MaxSatError::ExternalError(err))
        }
    }
}
