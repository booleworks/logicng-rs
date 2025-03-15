use std::collections::{BTreeSet, HashMap};

use crate::{
    backbones::Backbone,
    datastructures::Model,
    encodings::{CcEncoder, CcIncrementalData, PbEncoder},
    formulas::{CType, CardinalityConstraint, EncodedFormula, Formula, FormulaFactory, Literal, Variable},
    handlers::{ComputationHandler, LngResult, NopHandler},
    operations::transformations::{add_cnf_to_solver, PgOnSolverConfig, VarCacheEntry},
    propositions::Proposition,
};

use super::{
    functions::{
        backbone_function::{compute_backbone, BackboneType},
        formula_on_solver_function::formula_on_solver,
        model_enumeration_function::enumerate_models,
        up_zero_literals_function::up_zero_literals,
    },
    generate_clause_vector_wo_config, CnfMethod, EncodingResultSatSolver, LngCoreSolver, SatCall, SatCallBuilder, SatSolverConfig,
    SolverState,
};

pub struct SatSolver<B = ()> {
    solver: LngCoreSolver<B>,
    pg_variable_cache: HashMap<EncodedFormula, VarCacheEntry>,
    full_pg_variable_cache: HashMap<EncodedFormula, VarCacheEntry>,
}

impl<B> SatSolver<B> {
    pub fn new() -> Self {
        Self::from_config(SatSolverConfig::default())
    }

    pub fn from_core_solver(core_solver: LngCoreSolver<B>) -> Self {
        Self { solver: core_solver, pg_variable_cache: HashMap::new(), full_pg_variable_cache: HashMap::new() }
    }

    pub fn from_config(config: SatSolverConfig) -> Self {
        Self::from_core_solver(LngCoreSolver::new_with_config(config))
    }

    pub(crate) fn add_clause_set(&mut self, formula: EncodedFormula, proposition: Option<Proposition<B>>, f: &FormulaFactory) {
        match formula.unpack(f) {
            Formula::False | Formula::Lit(_) | Formula::Or(_) => self.add_clause(formula, proposition, f),
            Formula::And(nary_iterator) => {
                for op in nary_iterator {
                    self.add_clause(op, proposition.clone(), f);
                }
            }
            Formula::True => {}
            _ => panic!("Input formula is not a valid CNF: {}", formula.to_string(f)),
        };
    }

    pub(crate) fn add_clause(&mut self, formula: EncodedFormula, proposition: Option<Proposition<B>>, f: &FormulaFactory) {
        let ps = generate_clause_vector_wo_config(&formula.literals_for_clause_or_term(f), &mut self.solver);
        self.solver.add_clause(ps, proposition);
    }

    pub fn save_state(&mut self) -> SolverState {
        self.solver.save_state()
    }

    pub fn load_state(&mut self, state: &SolverState) {
        self.solver.load_state(state).expect("Loaded invalid state");
        self.pg_variable_cache.clear();
        self.full_pg_variable_cache.clear();
    }

    pub fn backbone<I, V>(&mut self, relevant_variables: I, backbone_type: BackboneType) -> Backbone
    where
        I: IntoIterator<Item = V> + Copy,
        V: Into<Variable>,
    {
        compute_backbone(self, relevant_variables, backbone_type, &mut NopHandler::new()).result().expect("Nop handler does not interrupt")
    }

    pub fn backbone_with_handler<I, V>(
        &mut self,
        relevant_variables: I,
        backbone_type: BackboneType,
        handler: &mut dyn ComputationHandler,
    ) -> LngResult<Backbone>
    where
        I: IntoIterator<Item = V> + Copy,
        V: Into<Variable>,
    {
        compute_backbone(self, relevant_variables, backbone_type, handler)
    }

    pub fn config(&self) -> &SatSolverConfig {
        self.solver.config()
    }

    pub fn underlying_solver(&mut self) -> &mut LngCoreSolver<B> {
        &mut self.solver
    }

    pub(crate) fn add_formula_as_cnf(&mut self, formula: EncodedFormula, proposition: Option<Proposition<B>>, f: &FormulaFactory) {
        match self.config().cnf_method() {
            CnfMethod::FactoryCnf => {
                self.add_clause_set(f.cnf_of(formula), proposition, f);
            }
            CnfMethod::PgOnSolver => {
                let config = PgOnSolverConfig::default().perform_nnf(true).initial_phase(self.config().initial_phase);
                add_cnf_to_solver(&mut self.solver, formula, proposition, f, &mut self.pg_variable_cache, config);
            }
            CnfMethod::FullPgOnSolver => {
                let config = PgOnSolverConfig::default().perform_nnf(false).initial_phase(self.config().initial_phase);
                add_cnf_to_solver(&mut self.solver, formula, proposition, f, &mut self.full_pg_variable_cache, config);
            }
        }
    }
}

impl<B: Clone> SatSolver<B> {
    pub fn add_formulas<E, I>(&mut self, formulas: I, f: &FormulaFactory)
    where
        E: Into<EncodedFormula>,
        I: IntoIterator<Item = E>,
    {
        for formula in formulas {
            self.add_formula(formula.into(), f);
        }
    }

    pub fn add_formula(&mut self, formula: EncodedFormula, f: &FormulaFactory) {
        self.add_intern(formula, None, f);
    }

    pub fn add(&mut self, formula: EncodedFormula, proposition: Proposition<B>, f: &FormulaFactory) {
        self.add_intern(formula, Some(proposition), f);
    }

    pub(crate) fn add_intern(&mut self, formula: EncodedFormula, proposition: Option<Proposition<B>>, f: &FormulaFactory) {
        match formula.unpack(f) {
            Formula::Cc(cc) => {
                if self.config().use_at_most_clauses() {
                    if cc.comparator == CType::LE {
                        let ops = cc.variables.iter().copied().map(Literal::from).collect::<Box<[_]>>();
                        let c = generate_clause_vector_wo_config(&ops, &mut self.solver);
                        self.solver.add_at_most(c, cc.rhs as usize);
                    } else if cc.comparator == CType::LT && cc.rhs > 3 {
                        let ops = cc.variables.iter().copied().map(Literal::from).collect::<Box<[_]>>();
                        let c = generate_clause_vector_wo_config(&ops, &mut self.solver);
                        self.solver.add_at_most(c, cc.rhs as usize - 1);
                    } else if cc.comparator == CType::EQ && cc.rhs == 1 {
                        let ops = cc.variables.iter().copied().map(Literal::from).collect::<Box<[_]>>();
                        let c = generate_clause_vector_wo_config(&ops, &mut self.solver);
                        self.solver.add_at_most(c.clone(), cc.rhs as usize);
                        self.solver.add_clause(c, proposition);
                    } else {
                        let mut dest = EncodingResultSatSolver::new(self, proposition);
                        CcEncoder::default().encode_on(&mut dest, cc);
                    }
                } else {
                    let mut dest = EncodingResultSatSolver::new(self, proposition);
                    CcEncoder::default().encode_on(&mut dest, cc);
                }
            }
            Formula::Pbc(pbc) => {
                let mut dest = EncodingResultSatSolver::new(self, proposition);
                PbEncoder::default().encode_on(pbc, &mut dest, f);
            }
            _ => self.add_formula_as_cnf(formula, proposition, f),
        }
    }

    pub fn add_propositions<I>(&mut self, propositions: I, f: &FormulaFactory)
    where
        I: IntoIterator<Item = Proposition<B>>,
    {
        for p in propositions {
            self.add_proposition(p, f);
        }
    }

    pub fn add_proposition(&mut self, proposition: Proposition<B>, f: &FormulaFactory) {
        self.add_intern(proposition.formula, Some(proposition), f);
    }

    pub fn add_formula_with_relaxation(&mut self, relaxation_var: Variable, formula: EncodedFormula, f: &FormulaFactory) {
        self.add_formula(f.or([relaxation_var.into(), formula]), f);
    }

    pub fn add_formulas_with_relaxation(&mut self, relaxation_var: Variable, formulas: &[EncodedFormula], f: &FormulaFactory) {
        for &formula in formulas {
            self.add_formula_with_relaxation(relaxation_var, formula, f);
        }
    }

    pub fn add_incremental_cc(&mut self, cc: CardinalityConstraint) -> Option<CcIncrementalData> {
        let mut result = EncodingResultSatSolver::new(self, None);
        CcEncoder::default().encode_incremental(&mut result, &cc)
    }

    pub fn sat_call(&mut self) -> SatCallBuilder<B> {
        SatCall::builder(self)
    }

    pub fn sat(&mut self, f: &FormulaFactory) -> bool {
        let call = self.sat_call().solve(f);
        call.get_sat_result().result().expect("nop handler")
    }

    pub fn enumerate_all_models(&mut self, variables: &[Variable], f: &FormulaFactory) -> Vec<Model> {
        enumerate_models(self, variables, f)
    }

    pub fn formula_on_solver(&mut self, f: &FormulaFactory) -> BTreeSet<EncodedFormula> {
        formula_on_solver(self, f)
    }

    pub fn up_zero_literals(&mut self, f: &FormulaFactory) -> BTreeSet<Literal> {
        up_zero_literals(self, f)
    }
}
