use std::{
    any::Any,
    collections::BTreeSet,
    ops::{Deref, DerefMut},
};

use crate::{
    backends::{
        BackendId, Capabilities, ComputationContext, MaxSatBackend, MaxSatBackendFactory,
        MaxSatResult,
    },
    errors::LngResult,
    formulas::{EncodedFormula, Formula, FormulaFactory, Variable},
    handlers::{CancelableResult, ComputationHandler, LngComputation, LngEvent, NopHandler},
    solver::maxsat::MaxSatError,
    util::exceptions::panic_unexpected_formula_type,
};

/// A backend-independent MaxSAT solver.
///
/// The solver owns a low-level backend and provides the public convenience
/// operations for formula encoding, solving, cancellation, and reset.
/// Applications usually use [`Self::add_hard_formula`],
/// [`Self::add_soft_formula`], [`Self::solve`], and
/// [`Self::solve_with_handler`].
pub struct MaxSatSolver {
    backend: Box<dyn MaxSatBackend>,
    context: MaxSatContext,
}

impl MaxSatSolver {
    /// Creates a solver which delegates its low-level operations to `backend`.
    pub fn new(backend: Box<dyn MaxSatBackend>) -> Self {
        Self {
            backend,
            context: MaxSatContext::default(),
        }
    }

    /// Creates a solver using a backend factory.
    ///
    /// # Errors
    ///
    /// Returns an error if the backend cannot be initialized.
    pub fn from_factory(factory: &dyn MaxSatBackendFactory) -> LngResult<Self> {
        Ok(Self::new(factory.new_backend()?))
    }

    /// Creates a solver using the MaxSAT backend in a computation context.
    ///
    /// # Errors
    ///
    /// Returns an error if no MaxSAT backend is configured or if the backend
    /// cannot be initialized.
    pub fn from_context(context: &ComputationContext) -> LngResult<Self> {
        let factory = context
            .backends
            .maxsat
            .as_deref()
            // TODO default Rust implementation later
            .ok_or(MaxSatError::NoBackendConfigured)?;
        Self::from_factory(factory)
    }

    /// Returns the identifier of this solver.
    pub fn id(&self) -> BackendId {
        self.backend.backend_id()
    }

    /// Returns the features supported by this solver's current configuration.
    pub fn capabilities(&self) -> Capabilities {
        self.backend.backend_capabilities()
    }

    /// Returns this solver as an incremental/decremental solver, if supported.
    ///
    /// A return value of `None` means that states cannot be saved and restored
    /// for this solver.
    ///
    /// # Example
    ///
    /// ```
    /// # use logicng::solver::maxsat::*;
    /// # fn supports_state_restoration(solver: &mut MaxSatSolver) -> bool {
    /// solver.as_inc_dec().is_some()
    /// # }
    /// ```
    pub fn as_inc_dec(&mut self) -> Option<IncDecMaxSatSolver<'_>> {
        self.backend.as_inc_dec()?;
        Some(IncDecMaxSatSolver { solver: self })
    }

    /// Solves the MaxSAT problem with a computation handler.
    ///
    /// If the computation is canceled after a model was found, the current best
    /// bound and model are returned as a [`CancelableResult::Partial`].
    ///
    /// # Example
    ///
    /// ```
    /// # use logicng::formulas::{FormulaFactory, ToFormula};
    /// # use logicng::handlers::{CancelableResult, NopHandler};
    /// # use logicng::solver::maxsat::*;
    /// # use logicng::errors::LngResult;
    /// # fn solve(solver: &mut MaxSatSolver, f: &FormulaFactory) -> LngResult<()> {
    /// solver.add_soft_formula(1, "A".to_formula(f), f)?;
    ///
    /// let result = solver.solve_with_handler(&mut NopHandler::new())?;
    /// assert!(matches!(
    ///     result,
    ///     CancelableResult::Ok(MaxSatResult::Optimum { bound: 0, .. })
    /// ));
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// # Errors
    ///
    /// Returns an error if the backend fails or returns an invalid response.
    pub fn solve_with_handler(
        &mut self,
        handler: &mut dyn ComputationHandler,
    ) -> LngResult<CancelableResult<MaxSatResult>> {
        let started = LngEvent::ComputationStarted(LngComputation::MaxSat);
        if !handler.should_resume(started.clone()) {
            return Ok(CancelableResult::Canceled(started));
        }

        let result = self.backend.search(handler)?;
        let result = self.without_selectors(result);
        if result.is_success() {
            let finished = LngEvent::ComputationFinished(LngComputation::MaxSat);
            if !handler.should_resume(finished.clone()) {
                return Ok(match result.result() {
                    Some(res) => CancelableResult::Partial(res, finished),
                    _ => CancelableResult::Canceled(finished),
                });
            }
        }
        Ok(result)
    }

    fn without_selectors(
        &self,
        result: CancelableResult<MaxSatResult>,
    ) -> CancelableResult<MaxSatResult> {
        match result {
            CancelableResult::Ok(result) => {
                CancelableResult::Ok(self.result_without_selectors(result))
            }
            CancelableResult::Partial(result, event) => {
                CancelableResult::Partial(self.result_without_selectors(result), event)
            }
            CancelableResult::Canceled(event) => CancelableResult::Canceled(event),
        }
    }

    fn result_without_selectors(&self, result: MaxSatResult) -> MaxSatResult {
        match result {
            MaxSatResult::Optimum { bound, model } => {
                let pos = model
                    .pos()
                    .iter()
                    .filter(|variable| !self.context.selectors.contains(variable))
                    .copied()
                    .collect::<Vec<_>>();
                let neg = model
                    .neg()
                    .iter()
                    .filter(|variable| !self.context.selectors.contains(variable))
                    .copied()
                    .collect::<Vec<_>>();
                MaxSatResult::Optimum {
                    bound,
                    model: crate::datastructures::Model::new(pos, neg),
                }
            }
            other => other,
        }
    }

    /// Solves the MaxSAT problem on this solver and returns the result.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::solver::maxsat::*;
    /// # use logicng::formulas::{ToFormula, FormulaFactory};
    /// # use logicng::errors::LngResult;
    /// # fn solve(solver: &mut MaxSatSolver, f: &FormulaFactory) -> LngResult<()> {
    /// solver.add_hard_formula("A & B & (C | D)".to_formula(f), f)?;
    /// solver.add_soft_formula(2, "A => ~B".to_formula(f), f)?;
    /// solver.add_soft_formula(4, "~C".to_formula(f), f)?;
    /// solver.add_soft_formula(8, "~D".to_formula(f), f)?;
    ///
    /// let result = solver.solve()?;
    /// assert!(matches!(
    ///     result,
    ///     MaxSatResult::Optimum { bound: 6, .. }
    /// ));
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// # Errors
    ///
    /// Returns an error if the solver backend fails or returns an invalid
    /// response.
    pub fn solve(&mut self) -> LngResult<MaxSatResult> {
        Ok(self
            .solve_with_handler(&mut NopHandler::new())?
            .result()
            .expect("nop handler can never abort"))
    }

    /// Adds a hard formula to the solver.
    ///
    /// Every result of a MaxSAT problem must fulfill all hard formulas on the solver.
    ///
    /// # Errors
    ///
    /// Returns an error if the formula cannot be encoded as CNF or if the
    /// solver backend rejects one of the resulting hard clauses.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::solver::maxsat::*;
    /// # use logicng::formulas::{FormulaFactory, ToFormula};
    /// # use logicng::errors::LngResult;
    /// # fn add(solver: &mut MaxSatSolver, f: &FormulaFactory) -> LngResult<()> {
    ///
    /// solver.add_hard_formula("A".to_formula(f), f)?;
    /// # Ok(())
    /// # }
    /// ```
    pub fn add_hard_formula(
        &mut self,
        formula: EncodedFormula,
        f: &FormulaFactory,
    ) -> LngResult<()> {
        add_cnf(self, None, f.cnf_of(formula)?, f)
    }

    /// Adds a soft formula to the solver.
    ///
    /// A soft formula is associated with a weight. The MaxSAT solver minimizes
    /// the sum of the weights of unsatisfied soft formulas. If an algorithm
    /// does not support weighted MaxSAT, every soft formula must have weight 1.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::solver::maxsat::*;
    /// # use logicng::formulas::{FormulaFactory, ToFormula};
    /// # use logicng::errors::LngResult;
    /// # fn add(solver: &mut MaxSatSolver, f: &FormulaFactory) -> LngResult<()> {
    ///
    /// solver.add_soft_formula(1, "A".to_formula(f), f)?;
    /// solver.add_soft_formula(2, "~A".to_formula(f), f)?;
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// Adding a weighted formula to an algorithm which only supports
    /// unweighted MaxSAT returns [`MaxSatError::IllegalWeightedClause`]:
    /// ```
    /// # use logicng::solver::maxsat::*;
    /// # use logicng::formulas::{FormulaFactory, ToFormula};
    /// # use logicng::solver::maxsat::MaxSatError;
    /// # fn check(solver: &mut MaxSatSolver, f: &FormulaFactory) {
    /// if !solver.capabilities().weights {
    ///     let result = solver.add_soft_formula(3, "A".to_formula(f), f);
    ///     assert_eq!(result, Err(MaxSatError::IllegalWeightedClause.into()));
    /// }
    /// # }
    /// ```
    ///
    /// # Errors
    ///
    /// Returns an error if the weight is invalid for the selected algorithm, if
    /// the formula cannot be encoded as CNF, or if the solver backend rejects
    /// one of the resulting clauses.
    pub fn add_soft_formula(
        &mut self,
        weight: u64,
        formula: EncodedFormula,
        f: &FormulaFactory,
    ) -> LngResult<()> {
        if weight != 1 && !self.backend.backend_capabilities().weights {
            return Err(MaxSatError::IllegalWeightedClause.into());
        }
        if (formula.is_or() || formula.is_literal()) && formula.is_cnf(f) {
            add_clause(self, Some(weight), formula, f)
        } else {
            let sel_var = f.new_auxiliary_variable("AUX_MAXSAT");
            self.context.selectors.insert(sel_var);
            let f1 = f.or([sel_var.negate().into(), formula]);
            let neg_f = f.negate(formula);
            let f2 = f.or([neg_f, sel_var.into()]);
            self.add_hard_formula(f1, f)?;
            self.add_hard_formula(f2, f)?;
            add_clause(self, Some(weight), sel_var.into(), f)
        }
    }

    /// Clears all formulas, auxiliary state, and results from this solver.
    ///
    /// The concrete solver type and its configuration are retained.
    ///
    /// # Example
    ///
    /// ```
    /// # use logicng::formulas::{FormulaFactory, ToFormula};
    /// # use logicng::solver::maxsat::*;
    /// # use logicng::errors::LngResult;
    /// # fn reuse(solver: &mut MaxSatSolver, f: &FormulaFactory) -> LngResult<()> {
    /// solver.add_hard_formula("A".to_formula(f), f)?;
    ///
    /// solver.reset();
    /// solver.add_hard_formula("~A".to_formula(f), f)?;
    /// assert!(matches!(solver.solve()?, MaxSatResult::Optimum { .. }));
    /// # Ok(())
    /// # }
    /// ```
    pub fn reset(&mut self) {
        self.backend.reset();
        self.context.clear();
    }
}

/// State owned by the backend-independent MaxSAT convenience layer.
#[derive(Clone, Default)]
struct MaxSatContext {
    selectors: BTreeSet<Variable>,
}

impl MaxSatContext {
    fn clear(&mut self) {
        self.selectors.clear();
    }
}

/// Opaque snapshot of an incremental/decremental MaxSAT solver.
///
/// A state is created with [`IncDecMaxSatSolver::save_state`] and can later be
/// passed to [`IncDecMaxSatSolver::load_state`]. The payload is owned and
/// interpreted by the backend identified by [`Self::backend`].
pub struct MaxSatState {
    backend: BackendId,
    payload: Box<dyn Any + Send>,
    context: MaxSatContext,
}

impl MaxSatState {
    /// Returns the identifier of the backend which created this state.
    pub const fn backend(&self) -> BackendId {
        self.backend
    }
}

/// A temporary view of a solver whose backend supports saving and restoring
/// state.
pub struct IncDecMaxSatSolver<'a> {
    solver: &'a mut MaxSatSolver,
}

impl IncDecMaxSatSolver<'_> {
    /// Saves the current solver state.
    ///
    /// The returned state can be used to discard formulas added afterwards by
    /// restoring it with [`Self::load_state`].
    ///
    /// # Example
    ///
    /// ```
    /// # use logicng::errors::LngResult;
    /// # use logicng::formulas::{FormulaFactory, ToFormula};
    /// # use logicng::solver::maxsat::*;
    /// # fn temporarily_add_formula(
    /// #     solver: &mut IncDecMaxSatSolver<'_>,
    /// #     f: &FormulaFactory,
    /// # ) -> LngResult<()> {
    /// let state = solver.save_state();
    /// solver.add_hard_formula("A".to_formula(f), f)?;
    ///
    /// solver.load_state(&state)?;
    /// # Ok(())
    /// # }
    /// ```
    pub fn save_state(&mut self) -> MaxSatState {
        let backend = self.solver.backend.backend_id();
        let payload = self
            .solver
            .backend
            .as_inc_dec()
            .expect("incremental capability was checked when creating the view")
            .save_state();
        MaxSatState {
            backend,
            payload,
            context: self.solver.context.clone(),
        }
    }

    /// Restores a previously saved solver state.
    ///
    /// Formulas and solver data introduced after the corresponding call to
    /// [`Self::save_state`] are discarded.
    ///
    /// # Errors
    ///
    /// Returns an error if the state was produced by an incompatible backend,
    /// is invalid for this solver configuration, or cannot be restored.
    pub fn load_state(&mut self, state: &MaxSatState) -> LngResult<()> {
        if state.backend != self.solver.backend.backend_id() {
            return Err(MaxSatError::InvalidState {
                expected: self.solver.backend.backend_id(),
                actual: state.backend,
            }
            .into());
        }
        self.solver
            .backend
            .as_inc_dec()
            .expect("incremental capability was checked when creating the view")
            .load_state(state.payload.as_ref())?;
        self.solver.context = state.context.clone();
        Ok(())
    }
}

impl Deref for IncDecMaxSatSolver<'_> {
    type Target = MaxSatSolver;

    fn deref(&self) -> &Self::Target {
        self.solver
    }
}

impl DerefMut for IncDecMaxSatSolver<'_> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.solver
    }
}

fn add_cnf(
    solver: &mut MaxSatSolver,
    weight: Option<u64>,
    formula: EncodedFormula,
    f: &FormulaFactory,
) -> LngResult<()> {
    match formula.unpack(f) {
        Formula::True => Ok(()),
        Formula::False | Formula::Lit(_) | Formula::Or(_) => add_clause(solver, weight, formula, f),
        Formula::And(ops) => {
            for op in ops {
                add_clause(solver, weight, op, f)?;
            }
            Ok(())
        }
        _ => panic_unexpected_formula_type(formula, Some(f)),
    }
}

fn add_clause(
    solver: &mut MaxSatSolver,
    weight: Option<u64>,
    formula: EncodedFormula,
    f: &FormulaFactory,
) -> LngResult<()> {
    match weight {
        Some(w) => solver.backend.add_soft_clause(w, formula, f),
        None => solver.backend.add_hard_clause(formula, f),
    }
}
