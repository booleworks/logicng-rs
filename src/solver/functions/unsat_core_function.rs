use itertools::Itertools;

use crate::explanations::{UnsatCore, drup_compute};
use crate::formulas::{EncodedFormula, FormulaFactory, Literal};
use crate::propositions::Proposition;
use crate::solver::minisat::MiniSat;
use crate::solver::minisat::sat::MsVar;
use crate::solver::minisat::sat::Tristate::{True, Undef};
use std::collections::HashMap;

/// Computes the [`UnsatCore`] if the formula is unsatisfiable.
pub fn compute_unsat_core<B: PartialEq>(solver: &MiniSat<B>, f: &FormulaFactory) -> UnsatCore<B> {
    assert!(solver.config.proof_generation, "Cannot generate an unsat core if proof generation is not turned on");
    assert_ne!(solver.result, True, "An unsat core can only be generated if the formula is solved and is UNSAT");
    assert_ne!(solver.result, Undef, "Cannot generate an unsat core before the formula was solved.");
    assert!(!solver.last_computation_with_assumptions, "Cannot compute an unsat core for a computation with assumptions.");

    let mut clause2propositions = HashMap::new();
    let mut clauses = Vec::with_capacity(solver.underlying_solver.pg_original_clauses.len());
    for pi in solver.underlying_solver.pg_original_clauses.clone() {
        let clause = get_formula_for_vector(solver, &pi.clause, f);
        let proposition = pi.proposition.unwrap_or_else(|| Proposition::new(clause));
        clauses.push(pi.clause);
        clause2propositions.insert(clause, proposition);
    }

    if clauses.iter().any(Vec::is_empty) {
        let empty_clause = clause2propositions.remove(&f.falsum()).unwrap();
        return UnsatCore::new(vec![empty_clause], true);
    }

    let result = drup_compute(clauses, solver.underlying_solver.pg_proof.clone());

    if result.trivial_unsat {
        handle_trivial_case(solver, f)
    } else {
        UnsatCore::new(
            result
                .unsat_core
                .iter()
                .map(|c| clause2propositions.get(&get_formula_for_vector(solver, c, f)).unwrap().clone())
                .dedup()
                .collect(),
            false,
        )
    }
}

fn handle_trivial_case<B: PartialEq>(solver: &MiniSat<B>, f: &FormulaFactory) -> UnsatCore<B> {
    let clauses = &solver.underlying_solver.pg_original_clauses;
    for i in 0..clauses.len() {
        let ci = &clauses[i];
        for cj in clauses.iter().skip(i + 1) {
            if ci.clause.len() == 1 && cj.clause.len() == 1 && ci.clause[0] + cj.clause[0] == 0 {
                let ci_clone = ci.clone();
                let cj_clone = cj.clone();
                let pi = if let Some(prop) = ci_clone.proposition {
                    prop
                } else {
                    Proposition::new(get_formula_for_vector(solver, &ci_clone.clause, f))
                };
                let pj = if let Some(prop) = cj_clone.proposition {
                    prop
                } else {
                    Proposition::new(get_formula_for_vector(solver, &cj_clone.clause, f))
                };
                return UnsatCore::new(if pi == pj { vec![pi] } else { vec![pi, pj] }, false);
            }
        }
    }
    panic!("Should be a trivial unsat core, but did not found one.");
}

fn get_formula_for_vector<B>(solver: &MiniSat<B>, vector: &Vec<isize>, f: &FormulaFactory) -> EncodedFormula {
    let mut literals = Vec::with_capacity(vector.len());
    for &lit in vector {
        let var = *solver.underlying_solver.idx2name.get(&MsVar(lit.unsigned_abs() - 1)).unwrap();
        literals.push(Literal::new(var, lit > 0).into());
    }
    f.or(&literals)
}
