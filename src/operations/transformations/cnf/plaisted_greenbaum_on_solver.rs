use std::collections::HashMap;

use Literal::{Neg, Pos};

use crate::formulas::{EncodedFormula, Formula, FormulaFactory, Literal, Variable};
use crate::operations::predicates::contains_pbc;
use crate::propositions::Proposition;
use crate::solver::minisat::sat::{mk_lit, MiniSat2Solver};
use crate::util::exceptions::panic_unexpected_formula_type;

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct PgOnSolverConfig {
    perform_nnf: bool,
    initial_phase: bool,
}

impl PgOnSolverConfig {
    pub const fn new(perform_nnf: bool, initial_phase: bool) -> Self {
        Self { perform_nnf, initial_phase }
    }

    #[must_use]
    pub const fn perform_nnf(mut self, perform_nnf: bool) -> Self {
        self.perform_nnf = perform_nnf;
        self
    }

    #[must_use]
    pub const fn initial_phase(mut self, initial_phase: bool) -> Self {
        self.initial_phase = initial_phase;
        self
    }
}

impl Default for PgOnSolverConfig {
    fn default() -> Self {
        Self::new(true, true)
    }
}

pub fn add_cnf_to_solver(
    solver: &mut MiniSat2Solver,
    formula: EncodedFormula,
    proposition: &Option<Proposition>,
    f: &FormulaFactory,
    cache: &mut HashMap<EncodedFormula, VarCacheEntry>,
    config: PgOnSolverConfig,
) {
    let working_formula = if config.perform_nnf || contains_pbc(formula, f) { f.nnf_of(formula) } else { formula };
    if working_formula.is_cnf(f) {
        add_cnf(solver, working_formula, proposition, f, config);
    } else if let Some(top_level_vars) = compute_transformation(working_formula, proposition, solver, f, cache, config, true, true) {
        add_clause(solver, &top_level_vars, proposition, config);
    }
}

fn add_cnf(
    solver: &mut MiniSat2Solver,
    cnf: EncodedFormula,
    proposition: &Option<Proposition>,
    f: &FormulaFactory,
    config: PgOnSolverConfig,
) {
    use Formula::{And, False, Lit, Or, True};
    match cnf.unpack(f) {
        True => {}
        False | Lit(_) | Or(_) => {
            let clause_vec = (*cnf.literals(f)).iter().copied().collect::<Vec<Literal>>();
            add_clause(solver, &clause_vec, proposition, config);
        }
        And(operands) => {
            for clause in operands {
                let clause_vec = (*clause.literals(f)).iter().copied().collect::<Vec<Literal>>();
                add_clause(solver, &clause_vec, proposition, config);
            }
        }
        _ => panic!("Unexpected formula type: {}", cnf.to_string(f)),
    }
}

#[allow(clippy::too_many_arguments)]
fn compute_transformation(
    formula: EncodedFormula,
    proposition: &Option<Proposition>,
    solver: &mut MiniSat2Solver,
    f: &FormulaFactory,
    cache: &mut HashMap<EncodedFormula, VarCacheEntry>,
    config: PgOnSolverConfig,
    polarity: bool,
    top_level: bool,
) -> Option<Vec<Literal>> {
    use Formula::{And, Equiv, Impl, Lit, Not, Or};
    match formula.unpack(f) {
        Lit(Pos(var)) => Some(vec![Literal::new(var, polarity)]),
        Lit(Neg(var)) => Some(vec![Literal::new(var, !polarity)]),
        Not(op) => compute_transformation(op, proposition, solver, f, cache, config, !polarity, top_level),
        Or(_) | And(_) => handle_nary(formula, proposition, solver, f, cache, config, polarity, top_level),
        Impl(_) => handle_impl(formula, proposition, solver, f, cache, config, polarity, top_level),
        Equiv(_) => handle_equiv(formula, proposition, solver, f, cache, config, polarity, top_level),
        _ => panic_unexpected_formula_type(formula, Some(f)),
    }
}

#[allow(clippy::too_many_arguments)]
fn handle_equiv(
    equiv: EncodedFormula,
    proposition: &Option<Proposition>,
    solver: &mut MiniSat2Solver,
    f: &FormulaFactory,
    cache: &mut HashMap<EncodedFormula, VarCacheEntry>,
    config: PgOnSolverConfig,
    polarity: bool,
    top_level: bool,
) -> Option<Vec<Literal>> {
    let skip_pg = top_level;
    let (was_cached, pg_lit) = if skip_pg { (false, None) } else { get_pg_var(equiv, f, polarity, cache) };
    if was_cached {
        if polarity {
            Some(vec![pg_lit.unwrap()])
        } else {
            Some(vec![pg_lit.unwrap().negate()])
        }
    } else {
        let mut left_pos = compute_transformation(equiv.left(f).unwrap(), proposition, solver, f, cache, config, true, false).unwrap();
        let mut left_neg = compute_transformation(equiv.left(f).unwrap(), proposition, solver, f, cache, config, false, false).unwrap();
        let right_pos = compute_transformation(equiv.right(f).unwrap(), proposition, solver, f, cache, config, true, false).unwrap();
        let right_neg = compute_transformation(equiv.right(f).unwrap(), proposition, solver, f, cache, config, false, false).unwrap();
        if polarity {
            left_neg.extend(right_pos);
            left_pos.extend(right_neg);
            if top_level {
                add_clause(solver, &left_neg, proposition, config);
                add_clause(solver, &left_pos, proposition, config);
                None
            } else {
                add_clause(solver, &vector(pg_lit.unwrap().negate(), left_neg), proposition, config);
                add_clause(solver, &vector(pg_lit.unwrap().negate(), left_pos), proposition, config);
                Some(vec![pg_lit.unwrap()])
            }
        } else {
            left_pos.extend(right_pos);
            left_neg.extend(right_neg);
            if top_level {
                add_clause(solver, &left_pos, proposition, config);
                add_clause(solver, &left_neg, proposition, config);
                None
            } else {
                add_clause(solver, &vector(pg_lit.unwrap(), left_pos), proposition, config);
                add_clause(solver, &vector(pg_lit.unwrap(), left_neg), proposition, config);
                Some(vec![pg_lit.unwrap().negate()])
            }
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn handle_impl(
    implication: EncodedFormula,
    proposition: &Option<Proposition>,
    solver: &mut MiniSat2Solver,
    f: &FormulaFactory,
    cache: &mut HashMap<EncodedFormula, VarCacheEntry>,
    config: PgOnSolverConfig,
    polarity: bool,
    top_level: bool,
) -> Option<Vec<Literal>> {
    let skip_pg = polarity || top_level;
    let (was_cached, pg_lit) = if skip_pg { (false, None) } else { get_pg_var(implication, f, polarity, cache) };
    if was_cached {
        if polarity {
            Some(vec![pg_lit.unwrap()])
        } else {
            Some(vec![pg_lit.unwrap().negate()])
        }
    } else if polarity {
        // pg => (~left | right) = ~pg | ~left | right
        let mut left = compute_transformation(implication.left(f).unwrap(), proposition, solver, f, cache, config, false, false).unwrap();
        let right = compute_transformation(implication.right(f).unwrap(), proposition, solver, f, cache, config, true, false).unwrap();
        left.extend(right);
        Some(left)
    } else {
        // (~left | right) => pg = (left & ~right) | pg = (left | pg) & (~right | pg)
        let left = compute_transformation(implication.left(f).unwrap(), proposition, solver, f, cache, config, true, top_level);
        let right = compute_transformation(implication.right(f).unwrap(), proposition, solver, f, cache, config, false, top_level);
        if top_level {
            if let Some(l) = left {
                add_clause(solver, &l, proposition, config);
            }
            if let Some(r) = right {
                add_clause(solver, &r, proposition, config);
            }
            None
        } else {
            add_clause(solver, &vector(pg_lit.unwrap(), left.unwrap()), proposition, config);
            add_clause(solver, &vector(pg_lit.unwrap(), right.unwrap()), proposition, config);
            Some(vec![pg_lit.unwrap().negate()])
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn handle_nary(
    formula: EncodedFormula,
    proposition: &Option<Proposition>,
    solver: &mut MiniSat2Solver,
    f: &FormulaFactory,
    cache: &mut HashMap<EncodedFormula, VarCacheEntry>,
    config: PgOnSolverConfig,
    polarity: bool,
    top_level: bool,
) -> Option<Vec<Literal>> {
    let skip_pg = top_level || formula.is_and() && !polarity || formula.is_or() && polarity;
    let (was_cached, pg_lit) = if skip_pg { (false, None) } else { get_pg_var(formula, f, polarity, cache) };
    if was_cached {
        if polarity {
            Some(vec![pg_lit.unwrap()])
        } else {
            Some(vec![pg_lit.unwrap().negate()])
        }
    } else if formula.is_and() {
        if polarity {
            // pg => (v1 & ... & vk) = (~pg | v1) & ... & (~pg | vk)
            for &op in &*formula.operands(f) {
                let op_pg_vars = compute_transformation(op, proposition, solver, f, cache, config, true, top_level);
                if top_level {
                    if let Some(lits) = op_pg_vars {
                        add_clause(solver, &lits, proposition, config);
                    }
                } else {
                    add_clause(solver, &vector(pg_lit.unwrap().negate(), op_pg_vars.unwrap()), proposition, config);
                }
            }
            if top_level {
                None
            } else {
                Some(vec![pg_lit.unwrap()])
            }
        } else {
            // (v1 & ... & vk) => pg = ~v1 | ... | ~vk | pg
            // Speed-Up: Skip pg var
            let mut single_clause = Vec::new();
            for &op in &*formula.operands(f) {
                single_clause.extend(compute_transformation(op, proposition, solver, f, cache, config, false, false).unwrap());
            }
            Some(single_clause)
        }
    } else if formula.is_or() {
        if polarity {
            // pg => (v1 | ... | vk) = ~pg | v1 | ... | vk
            // Speed-Up: Skip pg var
            let mut single_clause = Vec::new();
            for &op in &*formula.operands(f) {
                single_clause.extend(compute_transformation(op, proposition, solver, f, cache, config, true, false).unwrap());
            }
            Some(single_clause)
        } else {
            // (v1 | ... | vk) => pg = (~v1 | pg) & ... & (~vk | pg)
            for &op in &*formula.operands(f) {
                let op_pg_lits = compute_transformation(op, proposition, solver, f, cache, config, false, top_level);
                if top_level {
                    if let Some(lits) = op_pg_lits {
                        add_clause(solver, &lits, proposition, config);
                    }
                } else {
                    add_clause(solver, &vector(pg_lit.unwrap(), op_pg_lits.unwrap()), proposition, config);
                }
            }
            if top_level {
                None
            } else {
                Some(vec![pg_lit.unwrap().negate()])
            }
        }
    } else {
        panic_unexpected_formula_type(formula, Some(f));
    }
}

fn add_clause(solver: &mut MiniSat2Solver, clause: &[Literal], proposition: &Option<Proposition>, config: PgOnSolverConfig) {
    let clause_vec = clause
        .iter()
        .map(|lit| {
            let variable = lit.variable();
            let index = solver.idx_for_variable(variable).unwrap_or_else(|| {
                let new_index = solver.new_var(!config.initial_phase, true);
                solver.add_variable(variable, new_index);
                new_index
            });
            mk_lit(index, !lit.phase())
        })
        .collect();
    solver.add_clause(clause_vec, proposition);
}

fn get_pg_var(
    formula: EncodedFormula,
    f: &FormulaFactory,
    polarity: bool,
    variable_cache: &mut HashMap<EncodedFormula, VarCacheEntry>,
) -> (bool, Option<Literal>) {
    if let Some(cache) = variable_cache.get_mut(&formula) {
        (cache.set_polarity_cached(polarity), Some(cache.variable.pos_lit()))
    } else {
        let pg_var = f.new_cnf_variable();
        let mut new = VarCacheEntry::new(pg_var);
        new.set_polarity_cached(polarity);
        variable_cache.insert(formula, new);
        (false, Some(pg_var.pos_lit()))
    }
}

fn vector(elt: Literal, a: Vec<Literal>) -> Vec<Literal> {
    let mut result = Vec::with_capacity(a.len() + 1);
    result.push(elt);
    result.extend(a);
    result
}

pub struct VarCacheEntry {
    variable: Variable,
    pos_polarity_cached: bool,
    neg_polarity_cached: bool,
}

impl VarCacheEntry {
    const fn new(variable: Variable) -> Self {
        Self { variable, pos_polarity_cached: false, neg_polarity_cached: false }
    }

    fn set_polarity_cached(&mut self, polarity: bool) -> bool {
        if polarity {
            let was_cached = self.pos_polarity_cached;
            self.pos_polarity_cached = true;
            was_cached
        } else {
            let was_cached = self.neg_polarity_cached;
            self.neg_polarity_cached = true;
            was_cached
        }
    }
}

#[allow(non_snake_case)]
#[cfg(test)]
mod tests {
    use crate::formulas::{ToFormula, Variable};
    use crate::solver::functions::{enumerate_models_for_formula_with_config, ModelEnumerationConfig};
    use crate::solver::minisat::{MiniSat, MiniSatConfig, SolverCnfMethod};
    use crate::util::test_util::F;
    use std::collections::BTreeSet;

    use super::*;

    fn pg_on_solver(formula: EncodedFormula, f: &FormulaFactory, method: SolverCnfMethod) -> EncodedFormula {
        let mut solver = MiniSat::new_with_config(MiniSatConfig::default().cnf_method(method));
        solver.add(formula, f);
        let clauses = solver.formula_on_solver(f);
        f.and(clauses.iter())
    }

    fn test_formula(f: &FormulaFactory, formula: EncodedFormula) {
        let pg = pg_on_solver(formula, f, SolverCnfMethod::PgOnSolver);
        let full_pg = pg_on_solver(formula, f, SolverCnfMethod::FullPgOnSolver);
        assert!(pg.is_cnf(f));
        assert!(full_pg.is_cnf(f));
        println!("formula: {}", formula.to_string(f));
        println!("pg: {}", pg.to_string(f));
        println!("full_pg: {}", full_pg.to_string(f));
        let vars: Box<[Variable]> = formula.variables(f).iter().copied().collect();
        let config = ModelEnumerationConfig::default().variables(vars.clone());
        let original_models = enumerate_models_for_formula_with_config(formula, f, &config);
        let pg_models = enumerate_models_for_formula_with_config(pg, f, &config);
        let full_pg_models = enumerate_models_for_formula_with_config(full_pg, f, &config);
        let pg_vars = pg.variables(f);
        let full_pg_vars = full_pg.variables(f);
        let pg_missed_vars = missed_vars(&vars, &pg_vars);
        let full_pg_missed_vars = missed_vars(&vars, &full_pg_vars);
        assert_eq!(original_models.len(), pg_models.len() * 2_usize.pow(pg_missed_vars));
        assert_eq!(original_models.len(), full_pg_models.len() * 2_usize.pow(full_pg_missed_vars));
    }

    #[allow(clippy::cast_possible_truncation)]
    fn missed_vars(original_vars: &[Variable], pg_vars: &BTreeSet<Variable>) -> u32 {
        (original_vars.len() - pg_vars.iter().filter(|v| matches!(v, Variable::FF(_))).count()) as u32
    }

    fn test_formula_eq(f: &FormulaFactory, formula: EncodedFormula, expected: EncodedFormula) {
        let pg = pg_on_solver(formula, f, SolverCnfMethod::PgOnSolver);
        let full_pg = pg_on_solver(formula, f, SolverCnfMethod::FullPgOnSolver);
        assert_eq!(pg, expected);
        assert_eq!(full_pg, expected);
    }

    #[test]
    fn test_constants() {
        let F = F::new();
        let f = &F.f;
        test_formula_eq(f, F.TRUE, F.TRUE);
        test_formula_eq(f, F.FALSE, F.FALSE);
    }

    #[test]
    fn test_literals() {
        let F = F::new();
        let f = &F.f;
        test_formula_eq(f, F.A, F.A);
        test_formula_eq(f, F.NA, F.NA);
    }

    #[test]
    fn test_binary_operators() {
        let F = F::new();
        let f = &F.f;
        test_formula(f, F.IMP1);
        test_formula(f, F.IMP2);
        test_formula(f, F.IMP3);
        test_formula(f, F.EQ1);
        test_formula(f, F.EQ2);
        test_formula(f, F.EQ3);
        test_formula(f, F.EQ4);
    }

    #[test]
    fn test_nary_operators() {
        let F = F::new();
        let f = &F.f;
        test_formula_eq(f, F.AND1, F.AND1);
        test_formula_eq(f, F.OR1, F.OR1);
        let f1 = "(a & b & x) | (c & d & ~y)".to_formula(f);
        let f2 = "(a & b & x) | (c & d & ~y) | (~z | (c & d & ~y)) ".to_formula(f);
        let f3 = "a | b | (~x & ~y)".to_formula(f);
        test_formula(f, f1);
        test_formula(f, f2);
        test_formula(f, f3);
    }

    #[test]
    fn test_not_nary() {
        let f = &FormulaFactory::new();
        let f1 = "~(~a | b)".to_formula(f);
        let f2 = "~((a | b) | ~(x | y))".to_formula(f);
        let f3 = "~(a & b | ~a & ~b)".to_formula(f);
        let f4 = "~(~(a | b) & ~(x | y) | (a | b) & (x | y))".to_formula(f);
        let f5 = "~(a & b & ~x & ~y)".to_formula(f);
        let f6 = "~(a | b | ~x | ~y)".to_formula(f);
        let f7 = "~(a & b) & (c | (a & b))".to_formula(f);
        test_formula(f, f1);
        test_formula(f, f2);
        test_formula(f, f3);
        test_formula(f, f4);
        test_formula(f, f5);
        test_formula(f, f6);
        test_formula(f, f7);
    }

    #[test]
    fn test_not_binary() {
        let f = &FormulaFactory::new();
        let f1 = "~(~(a | b) => ~(x | y))".to_formula(f);
        let f2 = "~(a <=> b)".to_formula(f);
        let f3 = "~(~(a | b) <=> ~(x | y))".to_formula(f);
        test_formula(f, f1);
        test_formula(f, f2);
        test_formula(f, f3);
    }

    #[test]
    fn test_cc() {
        let f = &FormulaFactory::with_id("");
        let f1 = "a <=> (1 * b <= 1)".to_formula(f);
        let f2 = "~(1 * b <= 1)".to_formula(f);
        let f3 = "(1 * b + 1 * c + 1 * d <= 1)".to_formula(f);
        let f4 = "~(1 * b + 1 * c + 1 * d <= 1)".to_formula(f);
        test_formula(f, f1);
        test_formula(f, f2);
        test_formula(f, f3);
        test_formula(f, f4);
    }

    #[test]
    fn test_formulas() {
        let f = &FormulaFactory::with_id("");
        let f1 = "(a | b) => c".to_formula(f);
        let f2 = "~x & ~y".to_formula(f);
        let f3 = "d & ((a | b) => c)".to_formula(f);
        let f4 = "d & ((a | b) => c) | ~x & ~y".to_formula(f);
        test_formula(f, f1);
        test_formula(f, f2);
        test_formula(f, f3);
        test_formula(f, f4);
    }
}
