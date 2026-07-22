use std::borrow::Borrow;

use crate::{
    collections::LNG_VEC_INIT_SIZE,
    datastructures::Model,
    errors::LngResult,
    explanations::UnsatCore,
    formulas::{EncodedFormula, FormulaFactory, Literal, Variable},
    handlers::{CancelableResult, ComputationHandler, NopHandler},
    propositions::Proposition,
};

use super::{
    SatSolver, SolverState, functions::unsat_core_function::compute_unsat_core,
    generate_clause_vector_wo_config,
};

/// Scoped SAT call whose temporary assumptions and formulas are reverted on drop.
pub struct SatCall<'s, B> {
    solver: &'s mut SatSolver<B>,
    initial_state: Option<SolverState>,
    pg_original_clauses_length: Option<usize>,
    sat_result: LngResult<CancelableResult<bool>>,
}

impl<'s, B> SatCall<'s, B> {
    fn init(
        solver: &'s mut SatSolver<B>,
        handler: Option<&mut dyn ComputationHandler>,
        additional_propositions: Vec<Proposition<B>>,
        selection_order: Option<&[Literal]>,
        f: &FormulaFactory,
    ) -> LngResult<Self> {
        let mut initial_state = None;
        let mut pg_original_clauses_length = None;
        if solver.config().proof_generation {
            pg_original_clauses_length =
                Some(solver.underlying_solver().pg_original_clauses().len());
        }
        let additionals =
            Additionals::split_props_into_literals_and_formulas(additional_propositions);
        if !additionals.additional_literals.is_empty() {
            solver.underlying_solver().assumptions = generate_clause_vector_wo_config(
                &additionals.additional_literals,
                solver.underlying_solver(),
            );
            solver.underlying_solver().assumption_propositions =
                additionals.propositions_for_literals;
        }
        if !additionals.additional_formulas.is_empty() {
            initial_state = Some(solver.save_state()?);
            for additional_formula in additionals.additional_formulas {
                solver.add_proposition(additional_formula, f)?;
            }
        }
        if let Some(selection_order) = selection_order {
            solver
                .underlying_solver()
                .set_selection_order(selection_order);
        }
        let sat_result = if let Some(handler) = handler {
            solver.underlying_solver().internal_solve(handler)
        } else {
            solver
                .underlying_solver()
                .internal_solve(&mut NopHandler::new())
        };
        Ok(Self {
            solver,
            initial_state,
            pg_original_clauses_length,
            sat_result: Ok(sat_result),
        })
    }

    /// Creates a builder for a scoped call on `solver`.
    pub fn builder(solver: &mut SatSolver<B>) -> SatCallBuilder<'_, '_, B> {
        SatCallBuilder {
            solver,
            handler: None,
            additional_propositions: Vec::new(),
            selection_order: None,
        }
    }

    /// Returns the cancelable Boolean result of this SAT call.
    pub fn get_sat_result(&self) -> LngResult<CancelableResult<bool>> {
        self.sat_result.clone()
    }

    /// Returns a model projected onto `variables` when the call was satisfiable.
    pub fn model(
        &mut self,
        variables: &[Variable],
        f: &FormulaFactory,
    ) -> LngResult<Option<Model>> {
        if !matches!(
            self.sat_result.as_ref().map_err(Clone::clone)?.result_ref(),
            Some(true)
        ) {
            Ok(None)
        } else {
            let mut unknowns = Vec::new();
            let mut relevant_indices = Vec::with_capacity(variables.len());
            for &var in variables {
                let element = self.solver.underlying_solver().idx_for_variable(var);
                if let Some(element) = element {
                    relevant_indices.push(element);
                } else {
                    unknowns.push(var.negate());
                }
            }
            let mut final_model = self
                .solver
                .underlying_solver()
                .convert_internal_model_on_solver(&relevant_indices, f);
            final_model.extend(unknowns);
            Ok(Some(Model::from_literals(&final_model)))
        }
    }
}

impl<'s, B: PartialEq> SatCall<'s, B> {
    /// Returns the unsatisfiable core when proof generation is enabled and the call was unsatisfiable.
    pub fn unsat_core(&mut self, f: &FormulaFactory) -> LngResult<Option<UnsatCore<B>>> {
        if !self.solver.config().proof_generation {
            Err(crate::solver::SolverError::ProofGenerationRequired.into())
        } else if !matches!(
            self.sat_result.as_ref().map_err(Clone::clone)?.result_ref(),
            Some(false)
        ) {
            Ok(None)
        } else {
            Ok(Some(compute_unsat_core(self.solver, f)?))
        }
    }
}

impl<'s, B> Drop for SatCall<'s, B> {
    fn drop(&mut self) {
        self.solver.underlying_solver().assumptions = Vec::with_capacity(LNG_VEC_INIT_SIZE);
        self.solver.underlying_solver().assumption_propositions =
            Vec::with_capacity(LNG_VEC_INIT_SIZE);
        if let Some(pg_original_clauses_length) = self.pg_original_clauses_length {
            self.solver
                .underlying_solver()
                .pg_original_clauses_mut()
                .truncate(pg_original_clauses_length);
        }
        self.solver.underlying_solver().set_selection_order(&[]);
        if let Some(initial_state) = &self.initial_state {
            let _ = self.solver.load_state(initial_state);
        }
    }
}

struct Additionals<B> {
    additional_literals: Vec<Literal>,
    propositions_for_literals: Vec<Proposition<B>>,
    additional_formulas: Vec<Proposition<B>>,
}

impl<B> Additionals<B> {
    fn split_props_into_literals_and_formulas(
        additional_propositions: Vec<Proposition<B>>,
    ) -> Self {
        let mut additional_literals = Vec::new();
        let mut propositions_for_literals = Vec::new();
        let mut additional_formulas = Vec::new();
        for prop in additional_propositions {
            if let Some(literal) = prop.formula.as_literal() {
                additional_literals.push(literal);
                propositions_for_literals.push(prop);
            } else {
                additional_formulas.push(prop);
            }
        }
        Self {
            additional_literals,
            propositions_for_literals,
            additional_formulas,
        }
    }
}

/// Builder for configuring and executing a scoped [`SatCall`].
pub struct SatCallBuilder<'s, 'h, B> {
    solver: &'s mut SatSolver<B>,
    handler: Option<Box<&'h mut dyn ComputationHandler>>,
    additional_propositions: Vec<Proposition<B>>,
    selection_order: Option<Vec<Literal>>,
}

impl<'s, 'h, B> SatCallBuilder<'s, 'h, B> {
    /// Executes the configured call and returns its scoped result object.
    pub fn solve(self, f: &FormulaFactory) -> LngResult<SatCall<'s, B>> {
        SatCall::init(
            self.solver,
            self.handler.map(|b| *b),
            self.additional_propositions,
            self.selection_order.as_ref().map(|s| s.as_slice()),
            f,
        )
    }

    /// Executes the call and returns both the call and its computation handler.
    pub fn solve_and_get_handler(
        self,
        f: &FormulaFactory,
    ) -> LngResult<(SatCall<'s, B>, Option<&'h mut dyn ComputationHandler>)> {
        if let Some(h) = self.handler {
            let handler = *h;
            let sat_call = SatCall::init(
                self.solver,
                Some(handler),
                self.additional_propositions,
                self.selection_order.as_ref().map(|s| s.as_slice()),
                f,
            )?;
            Ok((sat_call, Some(handler)))
        } else {
            let sat_call = SatCall::init(
                self.solver,
                None,
                self.additional_propositions,
                self.selection_order.as_ref().map(|s| s.as_slice()),
                f,
            )?;
            Ok((sat_call, None))
        }
    }

    /// Sets the handler used to cancel the SAT computation.
    pub fn handler(mut self, handler: &'h mut dyn ComputationHandler) -> Self {
        self.handler = Some(Box::new(handler));
        self
    }

    /// Adds formulas that are active only for this call.
    pub fn add_formulas<E, I>(mut self, formulas: I) -> Self
    where
        E: Into<EncodedFormula>,
        I: IntoIterator<Item = E>,
    {
        for formula in formulas.into_iter() {
            self.additional_propositions
                .push(Proposition::new(*formula.into().borrow()));
        }
        self
    }

    /// Adds propositions that are active only for this call.
    pub fn add_propositions<I>(mut self, propositions: I) -> Self
    where
        I: IntoIterator<Item = Proposition<B>>,
    {
        self.additional_propositions.extend(propositions);
        self
    }

    /// Sets an optional preferred variable and phase order.
    pub fn selection_order(mut self, selection_order: Option<Vec<Literal>>) -> Self {
        self.selection_order = selection_order;
        self
    }

    /// Executes the call and returns only its satisfiability result.
    pub fn sat(self, f: &FormulaFactory) -> LngResult<CancelableResult<bool>> {
        let call = self.solve(f)?;
        call.get_sat_result()
    }

    /// Executes the call and returns a projected model when satisfiable.
    pub fn model(self, variables: &[Variable], f: &FormulaFactory) -> LngResult<Option<Model>> {
        let mut call = self.solve(f)?;
        call.model(variables, f)
    }
}

impl<'s, 'h, B: PartialEq> SatCallBuilder<'s, 'h, B> {
    /// Executes the call and returns an unsatisfiable core when available.
    pub fn unsat_core(self, f: &FormulaFactory) -> LngResult<Option<UnsatCore<B>>> {
        let mut call = self.solve(f)?;
        call.unsat_core(f)
    }
}
