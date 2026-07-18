use std::collections::{BTreeSet, HashMap, HashSet};

use crate::{
    backbones::Backbone,
    datastructures::{EncodingResultSatSolver, Model},
    encodings::{CcEncoder, CcIncrementalData, PbEncoder},
    errors::LngResult,
    formulas::{
        CType, CardinalityConstraint, EncodedFormula, Formula, FormulaFactory, Literal, Variable,
    },
    handlers::{CancelableResult, ComputationHandler, NopHandler},
    operations::transformations::{PgOnSolverConfig, VarCacheEntry, add_cnf_to_solver},
    propositions::Proposition,
};

use super::{
    CnfMethod, LngCoreSolver, SatCall, SatCallBuilder, SatSolverConfig, SolverState, Tristate,
    functions::{
        backbone_function::{BackboneType, compute_backbone},
        formula_on_solver_function::formula_on_solver,
        model_enumeration_function::enumerate_models,
    },
    generate_clause_vector_wo_config,
};

pub struct SatSolver<B = ()> {
    pub underlying_solver: LngCoreSolver<B>,
    pub config: SatSolverConfig,
    last_result: Tristate,
    pg_variable_cache: HashMap<EncodedFormula, VarCacheEntry>,
    full_pg_variable_cache: HashMap<EncodedFormula, VarCacheEntry>,
}

impl<B> SatSolver<B> {
    pub fn new_with_backpack() -> Self {
        Self::from_config_with_backpack(SatSolverConfig::default())
    }

    pub fn from_core_solver(core_solver: LngCoreSolver<B>) -> Self {
        let config = core_solver.config().clone();
        Self {
            underlying_solver: core_solver,
            config,
            last_result: Tristate::Undef,
            pg_variable_cache: HashMap::new(),
            full_pg_variable_cache: HashMap::new(),
        }
    }

    pub fn from_config_with_backpack(config: SatSolverConfig) -> Self {
        Self::from_core_solver(LngCoreSolver::new_with_config(config))
    }

    pub(crate) fn add_clause_set(
        &mut self,
        formula: EncodedFormula,
        proposition: Option<Proposition<B>>,
        f: &FormulaFactory,
    ) -> LngResult<()> {
        match formula.unpack(f) {
            Formula::False | Formula::Lit(_) | Formula::Or(_) => {
                self.add_clause(formula, proposition, f)?
            }
            Formula::And(nary_iterator) => {
                for op in nary_iterator {
                    self.add_clause(op, proposition.clone(), f)?;
                }
            }
            Formula::True => {}
            _ => return Err(crate::solver::SolverError::NotInCnf { formula }.into()),
        };
        Ok(())
    }

    pub(crate) fn add_clause(
        &mut self,
        formula: EncodedFormula,
        proposition: Option<Proposition<B>>,
        f: &FormulaFactory,
    ) -> LngResult<()> {
        let literals = formula.literals_for_clause_or_term(f)?;
        let ps = generate_clause_vector_wo_config(&literals, &mut self.underlying_solver);
        self.underlying_solver.add_clause(ps, proposition);
        Ok(())
    }

    pub fn save_state(&mut self) -> LngResult<SolverState> {
        if !self.config().incremental {
            return Err(crate::solver::SolverError::StateRequiresIncrementalMode.into());
        }
        Ok(self.underlying_solver.save_state())
    }

    pub fn load_state(&mut self, state: &SolverState) -> LngResult<()> {
        if !self.config().incremental {
            return Err(crate::solver::SolverError::StateRequiresIncrementalMode.into());
        }
        self.underlying_solver
            .load_state(state)
            .map_err(|_| crate::solver::SolverError::InvalidSolverState)?;
        self.pg_variable_cache.clear();
        self.full_pg_variable_cache.clear();
        Ok(())
    }

    pub fn backbone<I, V>(
        &mut self,
        relevant_variables: I,
        backbone_type: BackboneType,
    ) -> LngResult<Backbone>
    where
        I: IntoIterator<Item = V> + Clone,
        V: Into<Variable>,
    {
        let result = compute_backbone(
            self,
            relevant_variables,
            backbone_type,
            &mut NopHandler::new(),
        )?;
        result
            .result()
            .ok_or_else(|| crate::solver::SolverError::InvalidExternalResponse.into())
    }

    pub fn backbone_with_handler<I, V>(
        &mut self,
        relevant_variables: I,
        backbone_type: BackboneType,
        handler: &mut dyn ComputationHandler,
    ) -> LngResult<CancelableResult<Backbone>>
    where
        I: IntoIterator<Item = V> + Clone,
        V: Into<Variable>,
    {
        compute_backbone(self, relevant_variables, backbone_type, handler)
    }

    pub fn config(&self) -> &SatSolverConfig {
        &self.config
    }

    pub fn underlying_solver(&mut self) -> &mut LngCoreSolver<B> {
        &mut self.underlying_solver
    }

    pub(crate) fn add_formula_as_cnf(
        &mut self,
        formula: EncodedFormula,
        proposition: Option<Proposition<B>>,
        f: &FormulaFactory,
    ) -> LngResult<()> {
        match self.config().configured_cnf_method() {
            CnfMethod::FactoryCnf => {
                self.add_clause_set(f.cnf_of(formula)?, proposition, f)?;
            }
            CnfMethod::PgOnSolver => {
                let config = PgOnSolverConfig::default()
                    .perform_nnf(true)
                    .initial_phase(self.config().initial_phase);
                add_cnf_to_solver(
                    &mut self.underlying_solver,
                    formula,
                    proposition,
                    f,
                    &mut self.pg_variable_cache,
                    config,
                )?;
            }
            CnfMethod::FullPgOnSolver => {
                let config = PgOnSolverConfig::default()
                    .perform_nnf(false)
                    .initial_phase(self.config().initial_phase);
                add_cnf_to_solver(
                    &mut self.underlying_solver,
                    formula,
                    proposition,
                    f,
                    &mut self.full_pg_variable_cache,
                    config,
                )?;
            }
        }
        Ok(())
    }
}

impl SatSolver<()> {
    pub fn new() -> Self {
        Self::new_with_backpack()
    }

    pub fn from_config(config: SatSolverConfig) -> Self {
        Self::from_config_with_backpack(config)
    }
}

impl<B: Clone> SatSolver<B> {
    pub fn add_formulas<E, I>(&mut self, formulas: I, f: &FormulaFactory) -> LngResult<()>
    where
        E: Into<EncodedFormula>,
        I: IntoIterator<Item = E>,
    {
        for formula in formulas {
            self.add_formula(formula.into(), f)?;
        }
        Ok(())
    }

    pub fn add_all(&mut self, formulas: &[EncodedFormula], f: &FormulaFactory) -> LngResult<()>
    where
        B: Clone,
    {
        self.add_formulas(formulas.iter().copied(), f)
    }

    pub fn add_formula(&mut self, formula: EncodedFormula, f: &FormulaFactory) -> LngResult<()> {
        self.add_intern(formula, None, f)
    }

    pub fn add_with_proposition(
        &mut self,
        formula: EncodedFormula,
        proposition: Proposition<B>,
        f: &FormulaFactory,
    ) -> LngResult<()> {
        self.add_intern(formula, Some(proposition), f)
    }

    /// Adds a formula without proposition metadata.
    pub fn add(&mut self, formula: EncodedFormula, f: &FormulaFactory) -> LngResult<()> {
        self.add_formula(formula, f)
    }

    pub(crate) fn add_intern(
        &mut self,
        formula: EncodedFormula,
        proposition: Option<Proposition<B>>,
        f: &FormulaFactory,
    ) -> LngResult<()> {
        // Keep every user variable visible to model-related operations even when
        // the selected CNF transformation simplifies it out completely.
        for variable in formula.variables(f).iter().copied() {
            super::solver_literal_default(variable.pos_lit(), &mut self.underlying_solver);
        }
        match formula.unpack(f) {
            Formula::Cc(cc) => {
                if self.config().configured_use_at_most_clauses() {
                    if cc.comparator == CType::LE {
                        let ops = cc
                            .variables
                            .iter()
                            .copied()
                            .map(|v| v.pos_lit())
                            .collect::<Box<[_]>>();
                        let c = generate_clause_vector_wo_config(&ops, &mut self.underlying_solver);
                        self.underlying_solver.add_at_most(c, cc.rhs as usize);
                    } else if cc.comparator == CType::LT && cc.rhs > 3 {
                        let ops = cc
                            .variables
                            .iter()
                            .copied()
                            .map(|v| v.pos_lit())
                            .collect::<Box<[_]>>();
                        let c = generate_clause_vector_wo_config(&ops, &mut self.underlying_solver);
                        self.underlying_solver.add_at_most(c, cc.rhs as usize - 1);
                    } else if cc.comparator == CType::EQ && cc.rhs == 1 {
                        let ops = cc
                            .variables
                            .iter()
                            .copied()
                            .map(|v| v.pos_lit())
                            .collect::<Box<[_]>>();
                        let c = generate_clause_vector_wo_config(&ops, &mut self.underlying_solver);
                        self.underlying_solver
                            .add_at_most(c.clone(), cc.rhs as usize);
                        self.underlying_solver.add_clause(c, proposition);
                    } else {
                        let mut dest = EncodingResultSatSolver::new(self, proposition, f);
                        CcEncoder::default().encode_on(&mut dest, cc)?;
                    }
                } else {
                    let mut dest = EncodingResultSatSolver::new(self, proposition, f);
                    CcEncoder::default().encode_on(&mut dest, cc)?;
                }
            }
            Formula::Pbc(pbc) => {
                let mut dest = EncodingResultSatSolver::new(self, proposition, f);
                PbEncoder::default().encode_on(pbc, &mut dest, f)?;
            }
            _ => self.add_formula_as_cnf(formula, proposition, f)?,
        }
        Ok(())
    }

    pub fn add_propositions<I>(&mut self, propositions: I, f: &FormulaFactory) -> LngResult<()>
    where
        I: IntoIterator<Item = Proposition<B>>,
    {
        for p in propositions {
            self.add_proposition(p, f)?;
        }
        Ok(())
    }

    pub fn add_proposition(
        &mut self,
        proposition: Proposition<B>,
        f: &FormulaFactory,
    ) -> LngResult<()> {
        self.add_intern(proposition.formula, Some(proposition), f)
    }

    pub fn add_formula_with_relaxation(
        &mut self,
        relaxation_var: Variable,
        formula: EncodedFormula,
        f: &FormulaFactory,
    ) -> LngResult<()> {
        self.add_formula(f.or([relaxation_var.into(), formula]), f)
    }

    pub fn add_formulas_with_relaxation(
        &mut self,
        relaxation_var: Variable,
        formulas: &[EncodedFormula],
        f: &FormulaFactory,
    ) -> LngResult<()> {
        for &formula in formulas {
            self.add_formula_with_relaxation(relaxation_var, formula, f)?;
        }
        Ok(())
    }

    pub fn add_incremental_cc(
        &mut self,
        cc: &CardinalityConstraint,
        f: &FormulaFactory,
    ) -> LngResult<Option<CcIncrementalData>> {
        let mut result = EncodingResultSatSolver::new(self, None, f);
        CcEncoder::default().encode_incremental_on(&mut result, cc)
    }

    pub fn sat_call(&mut self) -> SatCallBuilder<B> {
        SatCall::builder(self)
    }

    pub fn sat(&mut self) -> LngResult<Tristate> {
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            self.underlying_solver
                .internal_solve(&mut NopHandler::new())
        }))
        .map_err(|_| crate::solver::SolverError::InternalInvariant)?;
        self.last_result = match result.result() {
            Some(true) => Tristate::True,
            Some(false) => Tristate::False,
            None => Tristate::Undef,
        };
        Ok(self.last_result)
    }

    pub fn sat_with(&mut self, builder: &SatBuilder<'_, '_>) -> LngResult<Tristate> {
        if let Some(assumptions) = builder.assumptions {
            self.underlying_solver.assumptions =
                generate_clause_vector_wo_config(assumptions, &mut self.underlying_solver);
        }
        if let Some(order) = builder.selection_order {
            self.underlying_solver.set_selection_order(order);
        }
        let result = self.sat();
        self.underlying_solver.assumptions.clear();
        self.underlying_solver.set_selection_order(&[]);
        result
    }

    pub fn model(&mut self, variables: Option<&[Variable]>) -> LngResult<Option<Model>> {
        match self.last_result {
            Tristate::False => Ok(None),
            Tristate::Undef => Err(crate::solver::SolverError::NotSolved.into()),
            Tristate::True => {
                let requested: Vec<Variable> = variables.map_or_else(
                    || {
                        self.underlying_solver
                            .known_variables()
                            .iter()
                            .copied()
                            .collect()
                    },
                    <[Variable]>::to_vec,
                );
                let mut call_model = Vec::new();
                for variable in requested {
                    if let Some(index) = self.underlying_solver.idx_for_variable(variable) {
                        call_model.push(Literal::new(
                            variable,
                            self.underlying_solver.model()[index.0],
                        ));
                    }
                }
                Ok(Some(Model::from_literals(&call_model)))
            }
        }
    }

    pub fn known_variables(&self) -> Vec<Variable> {
        self.underlying_solver
            .known_variables()
            .iter()
            .copied()
            .collect()
    }

    pub fn reset(&mut self) {
        let config = self.config().clone();
        *self = Self::from_config_with_backpack(config);
    }

    pub fn set_solver_to_undef(&mut self) {
        self.last_result = Tristate::Undef;
    }

    pub fn optimize(
        &mut self,
        f: &FormulaFactory,
        function: &super::functions::optimization_function::OptimizationFunction,
    ) -> LngResult<Option<Model>> {
        let result = function.optimize(self, &mut NopHandler::new(), f)?;
        Ok(result.result().map(|model| (*model).clone()))
    }

    pub fn enumerate_all_models(
        &mut self,
        variables: &[Variable],
        f: &FormulaFactory,
    ) -> LngResult<Vec<Model>> {
        enumerate_models(self, variables, f)
    }

    pub fn formula_on_solver(&mut self, f: &FormulaFactory) -> LngResult<HashSet<EncodedFormula>> {
        formula_on_solver(self, f)
    }

    pub fn up_zero_literals(&mut self) -> LngResult<Option<BTreeSet<Literal>>> {
        match self.last_result {
            Tristate::Undef => Err(crate::solver::SolverError::NotSolved.into()),
            Tristate::False => Ok(None),
            Tristate::True => {
                let mut result = BTreeSet::new();
                for lit in self.underlying_solver.up_zero_literals() {
                    if let Some(variable) = self.underlying_solver.idx2var.get(&super::var(lit)) {
                        result.insert(Literal::new(*variable, !super::sign(lit)));
                    }
                }
                Ok(Some(result))
            }
        }
    }
}

pub struct SatBuilder<'a, 'o> {
    assumptions: Option<&'a [Literal]>,
    selection_order: Option<&'o [Literal]>,
}

impl<'a, 'o> SatBuilder<'a, 'o> {
    pub const fn new() -> Self {
        Self {
            assumptions: None,
            selection_order: None,
        }
    }

    #[must_use]
    pub fn assumptions(mut self, assumptions: &'a [Literal]) -> Self {
        self.assumptions = Some(assumptions);
        self
    }

    #[must_use]
    pub const fn selection_order(mut self, selection_order: &'o [Literal]) -> Self {
        self.selection_order = Some(selection_order);
        self
    }
}

impl Default for SatBuilder<'_, '_> {
    fn default() -> Self {
        Self::new()
    }
}

impl<B: Clone + PartialEq> SatSolver<B> {
    pub fn unsat_core(
        &mut self,
        f: &FormulaFactory,
    ) -> LngResult<crate::explanations::UnsatCore<B>> {
        if self.last_result == Tristate::True {
            return Err(crate::solver::SolverError::UnsatCoreOnSatFormula.into());
        }
        if self.last_result == Tristate::Undef {
            return Err(crate::solver::SolverError::NotSolved.into());
        }
        super::functions::unsat_core_function::compute_unsat_core(self, f)
    }
}
