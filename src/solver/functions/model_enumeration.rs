#![allow(clippy::cast_possible_wrap)]

use std::collections::BTreeSet;

use crate::datastructures::Model;
use crate::formulas::{EncodedFormula, FormulaFactory, Variable};
use crate::solver::minisat::MiniSat;
use crate::solver::minisat::sat::Tristate::True;
use crate::solver::minisat::sat::{MiniSat2Solver, MsLit, MsVar, mk_lit};

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
    pub variables: Option<Box<[Variable]>>,

    /// Additional variables which should occur in every model.
    pub additional_variables: Option<Box<[Variable]>>,

    /// The maximal number of models that should be enumerated.
    pub max_models: Option<usize>,
}

impl ModelEnumerationConfig {
    /// Sets the set of variables over which the model enumeration should iterate.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::solver::functions::ModelEnumerationConfig;
    /// # let my_variables = Vec::new();
    /// let configuration = ModelEnumerationConfig::default()
    ///                     //...
    ///                     .variables(my_variables)
    ///                     //...
    ///                     ;
    /// ```
    #[must_use]
    pub fn variables<V: Into<Box<[Variable]>>>(mut self, variables: V) -> Self {
        self.variables = Some(variables.into());
        self
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

#[allow(clippy::derivable_impls)] // these defaults are not necessarily trivial and might change in the future or with additional fields
impl Default for ModelEnumerationConfig {
    fn default() -> Self {
        Self { variables: None, additional_variables: None, max_models: None }
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
pub fn enumerate_models_for_formula(formula: EncodedFormula, f: &FormulaFactory) -> Vec<Model> {
    enumerate_models_for_formula_with_config(formula, f, &ModelEnumerationConfig::default())
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
    f: &FormulaFactory,
    config: &ModelEnumerationConfig,
) -> Vec<Model> {
    let mut solver = MiniSat::new();
    solver.add(formula, f);
    enumerate_models_with_config(&mut solver, config)
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
pub fn enumerate_models(solver: &mut MiniSat) -> Vec<Model> {
    enumerate_models_with_config(solver, &ModelEnumerationConfig::default())
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
pub fn enumerate_models_with_config(solver: &mut MiniSat, config: &ModelEnumerationConfig) -> Vec<Model> {
    let original_state = solver.save_state();
    let mut models: Vec<Model> = Vec::new();
    let relevant_indices: Option<Vec<MsVar>>;
    if let Some(relevant_vars) = &config.variables {
        relevant_indices = Some(relevant_vars.iter().filter_map(|&v| solver.underlying_solver.idx_for_variable(v)).collect());
    } else if !solver.config.auxiliary_variables_in_models {
        let mut indices = Vec::<MsVar>::new();
        for entry in &solver.underlying_solver.name2idx {
            if solver.is_relevant_variable(*entry.0) {
                indices.push(*entry.1);
            }
        }
        relevant_indices = Some(indices);
    } else {
        relevant_indices = None;
    }
    let relevant_all_indices: Option<Vec<MsVar>>;
    let mut unique_additional_variables: BTreeSet<Variable> =
        config.additional_variables.as_ref().map_or_else(BTreeSet::new, |vars| vars.iter().copied().collect());
    if let Some(vars) = &config.variables {
        for var in vars {
            unique_additional_variables.remove(var);
        }
    }
    if let Some(indices) = &relevant_indices {
        if unique_additional_variables.is_empty() {
            relevant_all_indices = relevant_indices.clone();
        } else {
            let mut all_indices = Vec::<MsVar>::with_capacity(indices.len() + unique_additional_variables.len());
            all_indices.extend(indices);
            unique_additional_variables
                .iter()
                .filter_map(|&v| solver.underlying_solver.idx_for_variable(v))
                .for_each(|i| all_indices.push(i));
            relevant_all_indices = Some(all_indices);
        }
    } else {
        relevant_all_indices = None;
    }

    let max_models = config.max_models.map_or(usize::MAX, |max| max);
    while models.len() < max_models && solver.sat() == True {
        let model_from_solver = &solver.underlying_solver.model;
        let model = solver.create_assignment(model_from_solver, &relevant_all_indices);
        let model_empty = !model.is_empty();
        models.push(model);
        if model_empty {
            let blocking_clause = generate_blocking_clause(model_from_solver, &relevant_indices);
            solver.underlying_solver.add_clause(blocking_clause, None);
        } else {
            break;
        }
    }
    solver.load_state(&original_state);
    models
}

#[allow(clippy::option_if_let_else, clippy::ref_option)] // proposed change does not improve readability
fn generate_blocking_clause(model_from_solver: &[bool], relevant_vars: &Option<Vec<MsVar>>) -> Vec<MsLit> {
    if let Some(relevant) = relevant_vars {
        let mut blocking_clause = Vec::<MsLit>::with_capacity(relevant.len());
        for &var_index in relevant {
            blocking_clause.push(mk_lit(var_index, model_from_solver[var_index.0]));
        }
        blocking_clause
    } else {
        let mut blocking_clause = Vec::<MsLit>::with_capacity(model_from_solver.len());
        for (i, c) in model_from_solver.iter().enumerate() {
            blocking_clause.push(mk_lit(MsVar(i), *c));
        }
        blocking_clause
    }
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
pub fn count_models<B>(solver: &mut MiniSat2Solver<B>, max_models: usize) -> usize {
    let mut result = 0;
    while result <= max_models && solver.solve() == True {
        result += 1;
        let mut blocking_clause = Vec::<MsLit>::new();
        for i in 1..=solver.model.len() {
            let pos = solver.model[i - 1];
            blocking_clause.push(mk_lit(MsVar(i - 1), pos));
        }
        solver.add_clause(blocking_clause, None);
    }
    result
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use itertools::Itertools;

    use crate::datastructures::Assignment;
    use crate::formulas::{FormulaFactory, Literal, ToFormula, Variable};
    use crate::solver::functions::{ModelEnumerationConfig, enumerate_models, enumerate_models_with_config};
    use crate::solver::minisat::SolverCnfMethod::PgOnSolver;
    use crate::solver::minisat::sat::Tristate::True;
    use crate::solver::minisat::{MiniSat, MiniSatConfig};

    #[test]
    fn test_model_enumeration_simple() {
        let f = &FormulaFactory::new();
        let mut solver = MiniSat::new();
        solver.add("A & (B | C)".to_formula(f), f);
        let models = enumerate_models(&mut solver);
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
        let mut solver = MiniSat::new();
        solver.add("A & (B | C)".to_formula(f), f);
        assert_eq!(True, solver.sat());
        let models1 = enumerate_models(&mut solver);
        let ass1: HashSet<Assignment> = models1.iter().map(Assignment::from).collect();
        assert_eq!(True, solver.sat());
        let models2 = enumerate_models(&mut solver);
        let ass2: HashSet<Assignment> = models2.iter().map(Assignment::from).collect();
        assert_eq!(True, solver.sat());
        assert_eq!(ass1, ass2);
    }

    #[test]
    fn test_variables_removed_by_simplification_occurs_in_models() {
        let f = &FormulaFactory::new();
        let mut solver = MiniSat::from_config(MiniSatConfig::default().cnf_method(PgOnSolver));
        let formula = "A & B => A".to_formula(f);
        solver.add(formula, f);
        let models = enumerate_models_with_config(
            &mut solver,
            &ModelEnumerationConfig::default().variables(formula.variables(f).iter().copied().collect::<Box<[_]>>()),
        );
        assert_eq!(4, models.len());
        for model in models {
            assert_eq!(model.literals().iter().map(Literal::variable).sorted().collect::<Vec<Variable>>(), [f.var("A"), f.var("B")]);
        }
    }

    #[test]
    fn test_unknown_variable_not_occurring_in_model() {
        let f = &FormulaFactory::new();
        let mut solver = MiniSat::new();
        let a = "A".to_formula(f);
        solver.add(a, f);
        let vars: Box<[Variable]> = Box::new([f.var("A"), f.var("X")]);
        let models = enumerate_models_with_config(&mut solver, &ModelEnumerationConfig::default().variables(vars));
        assert_eq!(1, models.len());
        assert_eq!(models[0].literals(), vec![f.lit("A", true)]);
    }
}
