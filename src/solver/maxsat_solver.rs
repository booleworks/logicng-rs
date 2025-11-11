use crate::datastructures::{Assignment, Model};
use crate::formulas::{EncodedFormula, Formula, FormulaFactory, Variable};
use crate::solver::maxsat_config::{MaxSatConfig, PbEncoding};
use crate::solver::maxsat_ffi::{MaxSatError, OpenWboSolver};
use std::collections::BTreeSet;
use std::fmt::Debug;

/// Algorithms support for solving the MaxSAT problem with a [`MaxSatSolver`].
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Algorithm {
    /// Weighted Boolean Optimization
    Wbo,
    /// OLL
    Oll,
    /// Linear Sat-Unsat
    LinearSu,
    /// Partial Seminal-core guided algorithm
    PartMsu3,
    /// Seminal-core guided algorithm
    Msu3,
}

impl Algorithm {
    /// Returns `true` if this algorithm supports with the given configuration
    /// the weighted MaxSAT problem. Otherwise, it returns `false`.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::solver::maxsat::*;
    /// let config = MaxSatConfig::default();
    ///
    /// assert!(Algorithm::Wbo.weighted(&config));
    /// assert!(!Algorithm::Msu3.weighted(&config));
    /// ```
    pub fn weighted(&self, config: &MaxSatConfig) -> bool {
        match self {
            Self::Wbo | Self::Oll => true,
            Self::LinearSu => config.pb_encoding != PbEncoding::Adder,
            Self::PartMsu3 | Self::Msu3 => false,
        }
    }
}

/// Stores different metrics measured during the execution of the MaxSAT
/// algorithm.
#[derive(Debug, Clone, PartialEq)]
pub struct MaxSatStats {
    /// Upper bound cost.
    pub ub_cost: Option<u64>,
    /// Number of satisfiable calls.
    pub nb_satisfied: u64,
    /// Number of cores.
    pub nb_cores: u64,
    /// Average of the sizes of cores.
    pub avg_core_size: f64,
    /// Number of symmetry clauses.
    pub nb_sym_clauses: u64,
}

/// Result returned by an MaxSAT algorithm.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum MaxSatResult {
    /// The hard clauses on the solver are already unsatisfiable, optimization
    /// could not be performed.
    Unsatisfiable,
    /// An optimal solution was found + the result as value.
    Optimum(u64),
    /// If no search has been executed yet or the search was aborted by the
    /// algorithm and yielded no result.
    Undef,
}

const SEL_PREFIX: &str = "@SEL_SOFT_";

/// A solver for the MaxSAT problem.
///
/// [`MaxSatSolver`] does not implement the algorithms itself, but makes use of
/// [OpenWBO](http://sat.inesc-id.pt/open-wbo/) as an library. `OpenWBO` allows
/// you to use different algorithms, depending on your MaxSAT flavor and your
/// specific use case.
///
/// For more information about the general MaxSAT problem read the documentation of the [`maxsat module`](crate::solver::maxsat)
///
/// # Usage
///
/// You can create a new instance by using
/// [`MaxSatSolver::new`](crate::solver::maxsat::MaxSatSolver::new) or
/// [`MaxSatSolver::from_config`](crate::solver::maxsat::MaxSatSolver::from_config).
/// Both constructors take an [`Algorithm`](crate::solver::maxsat::Algorithm) as
/// argument, which will be used by the solver. Additionally, `from_config`
/// takes a `MaxSatConfig`, which allows you to configure certain details
/// (encodings, strategies) of the algorithm. Solver created by `new` use a
/// default configuration. Once you have created a solver, you can no longer
/// modify the algorithm or the configuration.
///
/// ```
/// # use logicng::solver::maxsat::*;
/// # use std::error::Error;
/// # fn main() -> Result<(), Box<dyn Error>> {
/// let solver1 = MaxSatSolver::new(Algorithm::Oll)?; //Solver with default configuration
///
/// let config = MaxSatConfig::default()
///                 .cardinal(CardinalEncoding::MTotalizer)
///                 .pb(PbEncoding::Gte);
/// let solver2 = MaxSatSolver::from_config(Algorithm::LinearSu, config)?; //With custom configuration
/// # Ok(())
/// # }
/// ```
///
/// Hard formulas are added with the method
/// [`MaxSatSolver::add_hard_formula`](crate::solver::maxsat::MaxSatSolver::add_hard_formula),
/// soft clauses are added with
/// [`MaxSatSolver::add_soft_formula`](crate::solver::maxsat::MaxSatSolver::add_soft_formula),
/// which takes a positive weight. For an unweighted clause, use the weight 1.
/// After you added all formulas, you can use the method `MaxSatSolver::solve`
/// to solve the problem.
pub struct MaxSatSolver {
    algorithm: Algorithm,
    config: MaxSatConfig,
    solver: OpenWboSolver,
    selector_variables: BTreeSet<Variable>,
}

impl MaxSatSolver {
    /// Creating a new [`MaxSatSolver`] instance with the given algorithm and the default configuration.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::solver::maxsat::*;
    /// # use std::error::Error;
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// let solver = MaxSatSolver::new(Algorithm::Oll)?;
    /// # Ok(())
    /// # }
    /// ```
    pub fn new(algorithm: Algorithm) -> Result<Self, MaxSatError> {
        Self::from_config(algorithm, MaxSatConfig::default())
    }

    /// Creating a new [`MaxSatSolver`] instance with given algorithm and configuration.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::solver::maxsat::*;
    /// # use std::error::Error;
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// let config = MaxSatConfig::default();
    ///
    /// let solver = MaxSatSolver::from_config(Algorithm::Oll, config);
    /// # Ok(())
    /// # }
    /// ```
    pub fn from_config(algorithm: Algorithm, config: MaxSatConfig) -> Result<Self, MaxSatError> {
        let solver = OpenWboSolver::new(&algorithm, &config)?;

        Ok(Self { algorithm, config, solver, selector_variables: BTreeSet::new() })
    }

    /// Returns `true` if this solver is capable of solving the weighted MaxSAT
    /// problem.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::solver::maxsat::*;
    /// # use std::error::Error;
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// let solver1 = MaxSatSolver::new(Algorithm::Oll)?;
    /// let solver2 = MaxSatSolver::new(Algorithm::Msu3)?;
    ///
    /// assert!(solver1.is_weighted());
    /// assert!(!solver2.is_weighted());
    /// # Ok(())
    /// # }
    /// ```
    pub fn is_weighted(&self) -> bool {
        self.algorithm.weighted(&self.config)
    }

    /// Resets the solver.
    ///
    /// This will keep the algorithm and configuration, but will clear all
    /// results and formulas on the solver.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::solver::maxsat::*;
    /// # use logicng::formulas::{FormulaFactory, ToFormula};
    /// # use std::error::Error;
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// let f = FormulaFactory::new();
    /// let mut solver = MaxSatSolver::new(Algorithm::Oll)?;
    ///
    /// solver.add_hard_formula("A".to_formula(&f), &f)?;
    /// solver.add_soft_formula(1, "~A".to_formula(&f), &f)?;
    /// let res = solver.solve()?;
    /// assert_eq!(res, MaxSatResult::Optimum(1));
    ///
    /// solver.reset();
    ///
    /// solver.add_hard_formula("A".to_formula(&f), &f)?;
    /// let res = solver.solve()?;
    /// assert_eq!(res, MaxSatResult::Optimum(0));
    /// # Ok(())
    /// # }
    /// ```
    pub fn reset(&mut self) {
        // Algorithm and Config can not be changed. Therefore, we can expect that we can create this solver,
        // because otherwise it would have failed in the constructor.
        self.solver = OpenWboSolver::new(&self.algorithm, &self.config).expect("Failed to reset the MaxSAT solver!");
        self.selector_variables.clear();
    }

    /// Adds a hard formula to the solver.
    ///
    /// Every result of a MaxSAT problem must fulfill all hard formulas on the solver.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::solver::maxsat::*;
    /// # use logicng::formulas::{FormulaFactory, ToFormula};
    /// # use std::error::Error;
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// let f = FormulaFactory::new();
    /// let mut solver = MaxSatSolver::new(Algorithm::Oll)?;
    ///
    /// solver.add_hard_formula("A".to_formula(&f), &f)?;
    /// # Ok(())
    /// # }
    /// ```
    pub fn add_hard_formula(&mut self, formula: EncodedFormula, f: &FormulaFactory) -> Result<(), MaxSatError> {
        self.add_cnf(None, f.cnf_of(formula), f)
    }

    /// Adds a soft formula to the solver.
    ///
    /// A soft formula is associated with an weight. The MaxSAT solver minimizes
    /// the sum of weights of unsatisfied soft formula. If an algorithm does not
    /// support the weighted MaxSAT problem, the weight must be equals to 1.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::solver::maxsat::*;
    /// # use logicng::formulas::{FormulaFactory, ToFormula};
    /// # use std::error::Error;
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// let f = FormulaFactory::new();
    /// let mut solver = MaxSatSolver::new(Algorithm::Oll)?;
    ///
    /// solver.add_soft_formula(1, "A".to_formula(&f), &f)?;
    /// solver.add_soft_formula(2, "~A".to_formula(&f), &f)?;
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// Adding a weighted formula to an non-weighted algorithm, will return a
    /// [`MaxSatError::IllegalWeightedClause`](`MaxSatError`) error:
    /// ```
    /// # use logicng::solver::maxsat::*;
    /// # use logicng::formulas::{FormulaFactory, ToFormula};
    /// # use std::error::Error;
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// let f = FormulaFactory::new();
    /// let mut solver = MaxSatSolver::new(Algorithm::Msu3)?;
    /// assert!(!solver.is_weighted());
    ///
    /// let res = solver.add_soft_formula(3, "A".to_formula(&f), &f);
    /// assert_eq!(res, Err(MaxSatError::IllegalWeightedClause));
    /// # Ok(())
    /// # }
    /// ```
    pub fn add_soft_formula(&mut self, weight: u64, formula: EncodedFormula, f: &FormulaFactory) -> Result<(), MaxSatError> {
        if (formula.is_or() || formula.is_literal()) && formula.is_cnf(f) {
            self.add_clause(Some(weight), formula, f)
        } else {
            let sel_var_name = format!("{SEL_PREFIX}{}", self.selector_variables.len());
            let sel_var = f.var(sel_var_name);
            self.selector_variables.insert(sel_var);
            let f1 = f.or([sel_var.negate().into(), formula]);
            let neg_f = f.negate(formula);
            let f2 = f.or([neg_f, sel_var.into()]);
            self.add_hard_formula(f1, f)?;
            self.add_hard_formula(f2, f)?;
            self.add_clause(Some(weight), sel_var.into(), f)
        }
    }

    /// Solves the MaxSAT problem on this solver and returns the result.
    ///
    /// The result of the search is cached. Every additional call to `solve`
    /// will return that cached value. Furthermore, you can also use [`MaxSatSolver::status`]
    /// to get the cached value once there is one.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::solver::maxsat::*;
    /// # use logicng::formulas::{ToFormula, FormulaFactory};
    /// # use std::error::Error;
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// let f = FormulaFactory::new();
    /// let mut solver = MaxSatSolver::new(Algorithm::Oll)?;
    /// solver.add_hard_formula("A & B & (C | D)".to_formula(&f), &f)?;
    /// solver.add_soft_formula(2, "A => ~B".to_formula(&f), &f)?;
    /// solver.add_soft_formula(4, "~C".to_formula(&f), &f)?;
    /// solver.add_soft_formula(8, "~D".to_formula(&f), &f)?;
    ///
    /// let result = solver.solve()?;
    /// assert_eq!(result, MaxSatResult::Optimum(6));
    /// # Ok(())
    /// # }
    /// ```
    pub fn solve(&mut self) -> Result<MaxSatResult, MaxSatError> {
        let status = self.solver.status();
        if status == Ok(MaxSatResult::Undef) { self.solver.search() } else { status }
    }

    /// Returns the result of the last search.
    ///
    /// If there has not been a search yet, it will return
    /// [`MaxSatResult::Undef`](`MaxSatResult`).
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::solver::maxsat::*;
    /// # use logicng::formulas::{ToFormula, FormulaFactory};
    /// # use std::error::Error;
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// let f = FormulaFactory::new();
    /// let mut solver = MaxSatSolver::new(Algorithm::Oll)?;
    /// solver.add_hard_formula("A & B & (C | D)".to_formula(&f), &f)?;
    /// solver.add_soft_formula(2, "A => ~B".to_formula(&f), &f)?;
    /// solver.add_soft_formula(4, "~C".to_formula(&f), &f)?;
    /// solver.add_soft_formula(8, "~D".to_formula(&f), &f)?;
    ///
    /// assert_eq!(solver.solve()?, MaxSatResult::Optimum(6));
    /// assert_eq!(solver.status()?, MaxSatResult::Optimum(6));
    /// # Ok(())
    /// # }
    /// ```
    pub fn status(&self) -> Result<MaxSatResult, MaxSatError> {
        self.solver.status()
    }

    /// Returns a model (as [`Model`]) which yields the optimal result, if there is one.
    ///
    /// If the search has not been executed yet or the result is not an optimum,
    /// this function returns a
    /// [`MaxSatError::IllegalModelRequest`](`MaxSatError`) error.
    ///
    /// If you need an [`Assignment`] you can use [`MaxSatSolver::assignment`].
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::solver::maxsat::*;
    /// # use logicng::formulas::{ToFormula, FormulaFactory};
    /// # use std::error::Error;
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// let f = FormulaFactory::new();
    /// let mut solver = MaxSatSolver::new(Algorithm::Oll)?;
    /// solver.add_hard_formula("A & B & (C | D)".to_formula(&f), &f)?;
    /// solver.add_soft_formula(2, "A => ~B".to_formula(&f), &f)?;
    /// solver.add_soft_formula(4, "~C".to_formula(&f), &f)?;
    /// solver.add_soft_formula(8, "~D".to_formula(&f), &f)?;
    ///
    /// if let MaxSatResult::Optimum(_) = solver.solve()? {
    ///     let model = solver.model()?;
    /// }
    /// # Ok(())
    /// # }
    /// ```
    pub fn model(&mut self) -> Result<Model, MaxSatError> {
        self.solver.model(&self.selector_variables)
    }

    /// Returns a model (as [`Assignment`]) which yields the optimal result, if
    /// there is one.
    ///
    /// If the search has not been executed yet or the result is not an optimum,
    /// this function returns a
    /// [`MaxSatError::IllegalModelRequest`](`MaxSatError`) error.
    ///
    /// If you need a [`Model`] you can use [`MaxSatSolver::model`].
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::solver::maxsat::*;
    /// # use logicng::formulas::{ToFormula, FormulaFactory};
    /// # use std::error::Error;
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// let f = FormulaFactory::new();
    /// let mut solver = MaxSatSolver::new(Algorithm::Oll)?;
    /// solver.add_hard_formula("A & B & (C | D)".to_formula(&f), &f)?;
    /// solver.add_soft_formula(2, "A => ~B".to_formula(&f), &f)?;
    /// solver.add_soft_formula(4, "~C".to_formula(&f), &f)?;
    /// solver.add_soft_formula(8, "~D".to_formula(&f), &f)?;
    ///
    /// if let MaxSatResult::Optimum(_) = solver.solve()? {
    ///     let model = solver.assignment()?;
    /// }
    /// # Ok(())
    /// # }
    /// ```
    pub fn assignment(&mut self) -> Result<Assignment, MaxSatError> {
        self.solver.assignment(&self.selector_variables)
    }

    /// Returns the algorithm used by this solver.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::solver::maxsat::*;
    /// # use std::error::Error;
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// let solver = MaxSatSolver::new(Algorithm::Oll)?;
    /// assert_eq!(solver.algorithm(), Algorithm::Oll);
    /// # Ok(())
    /// # }
    pub fn algorithm(&self) -> Algorithm {
        self.algorithm.clone()
    }

    /// Returns stats measured during the search.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::solver::maxsat::*;
    /// # use std::error::Error;
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// let solver = MaxSatSolver::new(Algorithm::Oll)?;
    /// // ...
    /// // solver.search()?;
    /// // ...
    /// solver.stats();
    /// # Ok(())
    /// # }
    pub fn stats(&self) -> MaxSatStats {
        self.solver.stats()
    }

    fn add_cnf(&mut self, weight: Option<u64>, formula: EncodedFormula, f: &FormulaFactory) -> Result<(), MaxSatError> {
        match formula.unpack(f) {
            Formula::True => Ok(()),
            Formula::False | Formula::Lit(_) | Formula::Or(_) => self.add_clause(weight, formula, f),
            Formula::And(ops) => {
                for op in ops {
                    self.add_clause(weight, op, f)?;
                }
                Ok(())
            }
            _ => panic!("Formula must be in cnf form!"),
        }
    }

    fn add_clause(&mut self, weight: Option<u64>, formula: EncodedFormula, f: &FormulaFactory) -> Result<(), MaxSatError> {
        match weight {
            Some(w) => self.solver.add_soft_clause(w, &formula, f),
            None => self.solver.add_hard_clause(&formula, f),
        }
    }
}
