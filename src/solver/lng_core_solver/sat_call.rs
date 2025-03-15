use std::borrow::Borrow;

use crate::{
    collections::LNG_VEC_INIT_SIZE,
    datastructures::Model,
    explanations::UnsatCore,
    formulas::{EncodedFormula, FormulaFactory, Literal, Variable},
    handlers::{ComputationHandler, LngResult, NopHandler},
    propositions::Proposition,
};

use super::{functions::unsat_core_function::compute_unsat_core, generate_clause_vector_wo_config, SatSolver, SolverState};

pub struct SatCall<'s, B> {
    solver: &'s mut SatSolver<B>,
    initial_state: Option<SolverState>,
    pg_original_clauses_length: Option<usize>,
    sat_result: LngResult<bool>,
}

impl<'s, B: Clone> SatCall<'s, B> {
    fn init(
        solver: &'s mut SatSolver<B>,
        handler: Option<&mut dyn ComputationHandler>,
        additional_propositions: Vec<Proposition<B>>,
        selection_order: Option<&[Literal]>,
        f: &FormulaFactory,
    ) -> Self {
        let mut initial_state = None;
        let mut pg_original_clauses_length = None;
        if solver.config().proof_generation {
            pg_original_clauses_length = Some(solver.underlying_solver().pg_original_clauses().len());
        }
        let additionals = Additionals::split_props_into_literals_and_formulas(additional_propositions);
        if !additionals.additional_literals.is_empty() {
            solver.underlying_solver().assumptions =
                generate_clause_vector_wo_config(&additionals.additional_literals, solver.underlying_solver());
            solver.underlying_solver().assumption_propositions = additionals.propositions_for_literals;
        }
        if !additionals.additional_formulas.is_empty() {
            initial_state = Some(solver.save_state());
            for additional_formula in additionals.additional_formulas {
                solver.add_proposition(additional_formula, f);
            }
        }
        if let Some(selection_order) = selection_order {
            solver.underlying_solver().set_selection_order(selection_order);
        }
        let sat_result = if let Some(handler) = handler {
            solver.underlying_solver().internal_solve(handler)
        } else {
            solver.underlying_solver().internal_solve(&mut NopHandler::new())
        };
        Self { solver, initial_state, pg_original_clauses_length, sat_result }
    }

    pub fn builder(solver: &mut SatSolver<B>) -> SatCallBuilder<B> {
        SatCallBuilder { solver, handler: None, additional_propositions: Vec::new(), selection_order: None }
    }

    pub fn get_sat_result(&self) -> LngResult<bool> {
        self.sat_result.clone()
    }

    pub fn model(&mut self, variables: &[Variable], f: &FormulaFactory) -> Option<Model> {
        if !self.sat_result.is_success() || !*self.sat_result.result_ref().unwrap() {
            None
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
            let mut final_model = self.solver.underlying_solver().convert_internal_model_on_solver(&relevant_indices, f);
            final_model.extend(unknowns);
            Some(Model::from_literals(&final_model))
        }
    }
}

impl<'s, B: PartialEq> SatCall<'s, B> {
    pub fn unsat_core(&mut self, f: &FormulaFactory) -> Option<UnsatCore<B>> {
        if !self.solver.config().proof_generation {
            panic!("Cannot generate an unsat core if proof generation is not turned on");
        } else if !self.sat_result.is_success() || *self.sat_result.result_ref().unwrap() {
            None
        } else {
            Some(compute_unsat_core(self.solver, f))
        }
    }
}

impl<'s, B> Drop for SatCall<'s, B> {
    fn drop(&mut self) {
        self.solver.underlying_solver().assumptions = Vec::with_capacity(LNG_VEC_INIT_SIZE);
        self.solver.underlying_solver().assumption_propositions = Vec::with_capacity(LNG_VEC_INIT_SIZE);
        if let Some(pg_original_clauses_length) = self.pg_original_clauses_length {
            self.solver.underlying_solver().pg_original_clauses_mut().truncate(pg_original_clauses_length);
        }
        self.solver.underlying_solver().set_selection_order(&[]);
        if let Some(initial_state) = &self.initial_state {
            self.solver.load_state(initial_state);
        }
    }
}

struct Additionals<B> {
    additional_literals: Vec<Literal>,
    propositions_for_literals: Vec<Proposition<B>>,
    additional_formulas: Vec<Proposition<B>>,
}

impl<B> Additionals<B> {
    fn split_props_into_literals_and_formulas(additional_propositions: Vec<Proposition<B>>) -> Self {
        let mut additional_literals = Vec::new();
        let mut propositions_for_literals = Vec::new();
        let mut additional_formulas = Vec::new();
        for prop in additional_propositions {
            if prop.formula.is_literal() {
                additional_literals.push(prop.formula.as_literal().unwrap());
                propositions_for_literals.push(prop);
            } else {
                additional_formulas.push(prop);
            }
        }
        Self { additional_literals, propositions_for_literals, additional_formulas }
    }
}

pub struct SatCallBuilder<'s, 'h, B> {
    solver: &'s mut SatSolver<B>,
    handler: Option<Box<&'h mut dyn ComputationHandler>>,
    additional_propositions: Vec<Proposition<B>>,
    selection_order: Option<Vec<Literal>>,
}

impl<'s, 'h, B: Clone> SatCallBuilder<'s, 'h, B> {
    pub fn solve(self, f: &FormulaFactory) -> SatCall<'s, B> {
        SatCall::init(
            self.solver,
            self.handler.map(|b| *b),
            self.additional_propositions,
            self.selection_order.as_ref().map(|s| s.as_slice()),
            f,
        )
    }

    pub fn solve_and_get_handler(self, f: &FormulaFactory) -> (SatCall<'s, B>, Option<&'h mut dyn ComputationHandler>) {
        if let Some(h) = self.handler {
            let handler = *h;
            let sat_call = SatCall::init(
                self.solver,
                Some(handler),
                self.additional_propositions,
                self.selection_order.as_ref().map(|s| s.as_slice()),
                f,
            );
            (sat_call, Some(handler))
        } else {
            let sat_call =
                SatCall::init(self.solver, None, self.additional_propositions, self.selection_order.as_ref().map(|s| s.as_slice()), f);
            (sat_call, None)
        }
    }

    pub fn handler(mut self, handler: &'h mut dyn ComputationHandler) -> Self {
        self.handler = Some(Box::new(handler));
        self
    }

    pub fn add_formulas<E, I>(mut self, formulas: I) -> Self
    where
        E: Into<EncodedFormula>,
        I: IntoIterator<Item = E>,
    {
        for formula in formulas.into_iter() {
            self.additional_propositions.push(Proposition::new(*formula.into().borrow()));
        }
        self
    }

    pub fn add_propositions<I>(mut self, propositions: I) -> Self
    where
        I: IntoIterator<Item = Proposition<B>>,
    {
        self.additional_propositions.extend(propositions);
        self
    }

    pub fn selection_order(mut self, selection_order: Option<Vec<Literal>>) -> Self {
        self.selection_order = selection_order;
        self
    }

    pub fn sat(self, f: &FormulaFactory) -> LngResult<bool> {
        let call = self.solve(f);
        call.get_sat_result()
    }

    pub fn model(self, variables: &[Variable], f: &FormulaFactory) -> Option<Model> {
        let mut call = self.solve(f);
        call.model(variables, f)
    }
}

impl<'s, 'h, B: PartialEq + Clone> SatCallBuilder<'s, 'h, B> {
    pub fn unsat_core(self, f: &FormulaFactory) -> Option<UnsatCore<B>> {
        let mut call = self.solve(f);
        call.unsat_core(f)
    }
}
