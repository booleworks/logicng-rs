#![allow(clippy::cast_possible_wrap)]

use std::collections::BTreeSet;

use crate::datastructures::Model;
use crate::formulas::{EncodedFormula, FormulaFactory, Literal, Variable};
use crate::solver::lng_core_solver::{mk_lit, LngLit, LngVar, SatSolver};

/// A configuration to adjust the behavior of the model enumeration algorithms.
///
/// # Usage
///
/// `ModelEnumerationConfig` is based on the builder pattern. One starts from
/// the default configuration, which has set everything to `None`, and extends
/// it with new values if needed:
///
/// ```
/// # use logicng::solver::functions::ModelEnumerationConfig;
/// # let my_variables = Vec::new();
/// # let my_additional_variables = Vec::new();
///
/// let configuration = ModelEnumerationConfig::default()
///                     .variables(my_variables)
///                     .additional_variables(my_additional_variables)
///                     .max_models(100);
/// ```
pub struct ModelEnumerationConfig {
    /// Variables over which the model enumeration should iterate.
    pub variables: Box<[Variable]>,

    /// Additional variables which should occur in every model.
    pub additional_variables: Option<Box<[Variable]>>,

    /// The maximal number of models that should be enumerated.
    pub max_models: Option<usize>,
}

impl ModelEnumerationConfig {
    pub fn new(variables: impl Into<Box<[Variable]>>) -> Self {
        Self { variables: variables.into(), additional_variables: None, max_models: None }
    }

    /// Sets an additional set of variables which should occur in every model.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::solver::functions::ModelEnumerationConfig;
    /// # let my_additional_variables = Vec::new();
    /// let configuration = ModelEnumerationConfig::default()
    ///                     //...
    ///                     .additional_variables(my_additional_variables)
    ///                     //...
    ///                     ;
    /// ```
    #[must_use]
    pub fn additional_variables<V: Into<Box<[Variable]>>>(mut self, additional_variables: V) -> Self {
        self.additional_variables = Some(additional_variables.into());
        self
    }

    /// Sets the maximal number of models that should be enumerated.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::solver::functions::ModelEnumerationConfig;
    /// let configuration = ModelEnumerationConfig::default()
    ///                     //...
    ///                     .max_models(100)
    ///                     //...
    ///                     ;
    /// ```
    #[must_use]
    pub const fn max_models(mut self, max_models: usize) -> Self {
        self.max_models = Some(max_models);
        self
    }
}

/// Enumerates all models of a formula and returns it as a vector.
///
/// The default configuration is used.
///
/// Make sure that all models of the formulas fit into your memory. The default
/// configuration does not limit the number of models and the algorithm will
/// continue until there are no more models left.
///
/// # Example
///
/// Basic usage:
/// ```
/// # use logicng::solver::functions::enumerate_models_for_formula;
/// # use logicng::formulas::{FormulaFactory, ToFormula};
/// let f = FormulaFactory::new();
/// let formula = "A <=> B".to_formula(&f);
///
/// let models = enumerate_models_for_formula(formula, &f);
/// ```
pub fn enumerate_models_for_formula(formula: EncodedFormula, variables: impl Into<Box<[Variable]>>, f: &FormulaFactory) -> Vec<Model> {
    enumerate_models_for_formula_with_config(formula, &ModelEnumerationConfig::new(variables), f)
}

/// Enumerates all models of a formula with the given configuration and returns
/// it as a vector.
///
/// Make sure that you limit the number of models in your configuration or that
/// all models of the formulas fit into your memory. If the algorithm is not
/// limited to a number of models, it will continue until there are no more
/// models left.
///
/// # Example
///
/// Basic usage:
/// ```
/// # use logicng::solver::functions::{enumerate_models_for_formula_with_config, ModelEnumerationConfig};
/// # use logicng::formulas::{FormulaFactory, ToFormula};
/// let f = FormulaFactory::new();
/// let formula = "A <=> B".to_formula(&f);
///
/// let config = ModelEnumerationConfig::default();
/// let models = enumerate_models_for_formula_with_config(formula, &f, &config);
/// ```
pub fn enumerate_models_for_formula_with_config(
    formula: EncodedFormula,
    config: &ModelEnumerationConfig,
    f: &FormulaFactory,
) -> Vec<Model> {
    let mut solver: SatSolver<()> = SatSolver::new();
    solver.add_formula(formula, f);
    enumerate_models_with_config(&mut solver, config, f)
}

/// Enumerates all models on the solver and returns it as a vector.
///
/// The default configuration is used.
///
/// Make sure that all models of the formulas fit into your memory. The default
/// configuration does not limit the number of models and the algorithm will
/// continue until there are no more models left.
///
/// # Example
///
/// Basic usage:
/// ```
/// # use logicng::solver::functions::enumerate_models;
/// # use logicng::formulas::{FormulaFactory, ToFormula};
/// # use logicng::solver::minisat::MiniSat;
/// let f = FormulaFactory::new();
/// let mut solver = MiniSat::new();
/// solver.add("A <=> B".to_formula(&f), &f);
///
/// let models = enumerate_models(&mut solver);
/// ```
pub fn enumerate_models<B: Clone>(solver: &mut SatSolver<B>, variables: impl Into<Box<[Variable]>>, f: &FormulaFactory) -> Vec<Model> {
    enumerate_models_with_config(solver, &ModelEnumerationConfig::new(variables), f)
}

/// Enumerates all models on the solver with the given configuration and returns
/// it as a vector.
///
/// Make sure that you limit the number of models in your configuration or that
/// all models of the formulas fit into your memory. If the algorithm is not
/// limited to a number of models, it will continue until there are no more
/// models left.
///
/// # Example
///
/// Basic usage:
/// ```
/// # use logicng::solver::functions::{enumerate_models_with_config, ModelEnumerationConfig};
/// # use logicng::formulas::{FormulaFactory, ToFormula};
/// # use logicng::solver::minisat::MiniSat;
/// let f = FormulaFactory::new();
/// let mut solver = MiniSat::new();
/// solver.add("A <=> B".to_formula(&f), &f);
///
/// let config = ModelEnumerationConfig::default();
/// let models = enumerate_models_with_config(&mut solver, &config);
/// ```
pub fn enumerate_models_with_config<B: Clone>(
    solver: &mut SatSolver<B>,
    config: &ModelEnumerationConfig,
    f: &FormulaFactory,
) -> Vec<Model> {
    let original_state = solver.save_state();
    let mut models: Vec<Model> = Vec::new();
    let relevant_indices = config.variables.iter().filter_map(|&v| solver.underlying_solver().idx_for_variable(v)).collect::<Vec<_>>();
    let mut unique_additional_variables: BTreeSet<Variable> =
        config.additional_variables.as_ref().map_or_else(BTreeSet::new, |vars| vars.iter().copied().collect());
    for var in &config.variables {
        unique_additional_variables.remove(var);
    }
    let additional_variables_not_on_solver: Vec<Literal> = unique_additional_variables
        .iter()
        .filter(|&v| {
            !solver.underlying_solver().known_variables().contains(v)
                && !solver.underlying_solver().materialized_auxiliary_variables().contains(v)
        })
        .map(Variable::neg_lit)
        .collect();
    let relevant_all_indices = if unique_additional_variables.is_empty() {
        #[allow(clippy::redundant_clone)] //Wrong lint
        relevant_indices.clone()
    } else {
        let mut all_indices = Vec::<LngVar>::with_capacity(relevant_indices.len() + unique_additional_variables.len());
        all_indices.extend(&relevant_indices);
        unique_additional_variables
            .iter()
            .filter_map(|&v| solver.underlying_solver().idx_for_variable(v))
            .for_each(|i| all_indices.push(i));
        all_indices
    };

    let max_models = config.max_models.map_or(usize::MAX, |max| max);
    while models.len() < max_models && solver.sat(f) {
        let mut model_lits = solver.underlying_solver().convert_internal_model_on_solver(&relevant_all_indices, f);
        let model_empty = !model_lits.is_empty();
        model_lits.extend(&additional_variables_not_on_solver);
        let model = Model::from_literals(&model_lits);
        models.push(model);
        if model_empty {
            let blocking_clause = generate_blocking_clause(&solver.underlying_solver().model, &relevant_indices);
            solver.underlying_solver().add_clause(blocking_clause, None);
        } else {
            break;
        }
    }
    solver.load_state(&original_state);
    models
}

#[allow(clippy::option_if_let_else)] // proposed change does not improve readability
fn generate_blocking_clause(model_from_solver: &[bool], relevant_vars: &[LngVar]) -> Vec<LngLit> {
    let mut blocking_clause = Vec::<LngLit>::with_capacity(relevant_vars.len());
    for &var_index in relevant_vars {
        blocking_clause.push(mk_lit(var_index, model_from_solver[var_index.0]));
    }
    blocking_clause
}

/// Counts all models on the solver.
///
/// `max_models` is the upper bound of models counted.
///
/// # Example
///
/// Basic usage:
/// ```
/// # use logicng::solver::functions::count_models;
/// # use logicng::formulas::{FormulaFactory, ToFormula};
/// # use logicng::solver::minisat::MiniSat;
/// let f = FormulaFactory::new();
/// let mut solver = MiniSat::new();
/// solver.add("A <=> B".to_formula(&f), &f);
///
/// let count = count_models(&mut solver.underlying_solver, 100);
/// assert_eq!(count, 2);
/// ```
pub fn count_models<B: Clone>(solver: &mut SatSolver<B>, max_models: usize, f: &FormulaFactory) -> usize {
    let mut result = 0;
    while result <= max_models && solver.sat(f) {
        result += 1;
        let mut blocking_clause = Vec::<LngLit>::new();
        for i in 1..=solver.underlying_solver().model.len() {
            let pos = solver.underlying_solver().model[i - 1];
            blocking_clause.push(mk_lit(LngVar(i - 1), pos));
        }
        solver.underlying_solver().add_clause(blocking_clause, None);
    }
    result
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use itertools::Itertools;

    use crate::datastructures::Assignment;
    use crate::formulas::{FormulaFactory, Literal, ToFormula, Variable};
    use crate::solver::lng_core_solver::functions::model_enumeration_function::{
        enumerate_models, enumerate_models_with_config, ModelEnumerationConfig,
    };
    use crate::solver::lng_core_solver::{CnfMethod, LngCoreSolver, SatSolver, SatSolverConfig};

    #[test]
    fn test_model_enumeration_simple() {
        let f = &FormulaFactory::new();
        let mut solver = SatSolver::<()>::new();
        solver.add_formula("A & (B | C)".to_formula(f), f);
        let models = enumerate_models(&mut solver, [f.var("A"), f.var("B"), f.var("C")], f);
        let ass: HashSet<Assignment> = models.iter().map(Assignment::from).collect();
        assert_eq!(
            vec![
                Assignment::from_names(&["A", "B", "C"], &[], f).unwrap(),
                Assignment::from_names(&["A", "B"], &["C"], f).unwrap(),
                Assignment::from_names(&["A", "C"], &["B"], f).unwrap(),
            ]
            .into_iter()
            .collect::<HashSet<Assignment>>(),
            ass
        );
    }

    #[test]
    fn test_model_enumeration_does_not_alter_solver() {
        let f = &FormulaFactory::new();
        let mut solver = SatSolver::<()>::new();
        solver.add_formula("A & (B | C)".to_formula(f), f);
        assert!(solver.sat(f));
        let models1 = enumerate_models(&mut solver, [f.var("A"), f.var("B"), f.var("C")], f);
        let ass1: HashSet<Assignment> = models1.iter().map(Assignment::from).collect();
        assert!(solver.sat(f));
        let models2 = enumerate_models(&mut solver, [f.var("A"), f.var("B"), f.var("C")], f);
        let ass2: HashSet<Assignment> = models2.iter().map(Assignment::from).collect();
        assert!(solver.sat(f));
        assert_eq!(ass1, ass2);
    }

    #[test]
    fn test_variables_removed_by_simplification_occurs_in_models() {
        let f = &FormulaFactory::new();
        let mut solver = SatSolver::<()>::from_core_solver(LngCoreSolver::new_with_config(
            SatSolverConfig::default().with_cnf_method(CnfMethod::PgOnSolver),
        ));
        let formula = "A & B => A".to_formula(f);
        solver.add_formula(formula, f);
        let models = enumerate_models_with_config(
            &mut solver,
            &ModelEnumerationConfig::new(formula.variables(f).iter().copied().collect::<Box<[_]>>()),
            f,
        );
        assert_eq!(4, models.len());
        for model in models {
            assert_eq!(model.literals().iter().map(Literal::variable).sorted().collect::<Vec<Variable>>(), [f.var("A"), f.var("B")]);
        }
    }

    #[test]
    fn test_unknown_variable_not_occurring_in_model() {
        let f = &FormulaFactory::new();
        let mut solver = SatSolver::<()>::new();
        let a = "A".to_formula(f);
        solver.add_formula(a, f);
        let vars: Box<[Variable]> = Box::new([f.var("A"), f.var("X")]);
        let models = enumerate_models_with_config(&mut solver, &ModelEnumerationConfig::new(vars), f);
        assert_eq!(1, models.len());
        assert_eq!(models[0].literals(), vec![f.lit("A", true)]);
    }
}
