use itertools::Itertools;

use crate::errors::LngResult;
use crate::explanations::{UnsatCore, drup_compute};
use crate::formulas::{EncodedFormula, FormulaFactory, Literal};
use crate::propositions::Proposition;
use crate::solver::SolverError;
use std::collections::HashMap;
use crate::solver::lng_core_solver::{MiniSat, MsVar};
use crate::solver::lng_core_solver::Tristate::{True, Undef};

/// Computes the [`UnsatCore`] if the formula is unsatisfiable.
///
/// # Errors
///
/// Returns an error if proof generation is disabled, the solver has not been
/// solved yet, the formula is satisfiable, or the last computation used
/// assumptions.
pub fn compute_unsat_core<B: PartialEq>(
    solver: &MiniSat<B>,
    f: &FormulaFactory,
) -> LngResult<UnsatCore<B>> {
    if !solver.config.proof_generation {
        return Err(SolverError::ProofGenerationRequired.into());
    }
    if solver.result == Undef {
        return Err(SolverError::NotSolved.into());
    }
    if solver.result == True {
        return Err(SolverError::UnsatCoreOnSatFormula.into());
    }
    if solver.last_computation_with_assumptions {
        return Err(SolverError::UnsatCoreWithAssumptions.into());
    }

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
        return Ok(UnsatCore::new(vec![empty_clause], true));
    }

    let result = drup_compute(clauses, solver.underlying_solver.pg_proof.clone());

    if result.trivial_unsat {
        Ok(handle_trivial_case(solver, f))
    } else {
        Ok(UnsatCore::new(
            result
                .unsat_core
                .iter()
                .map(|c| {
                    clause2propositions
                        .get(&get_formula_for_vector(solver, c, f))
                        .unwrap()
                        .clone()
                })
                .dedup()
                .collect(),
            false,
        ))
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
    panic!("Should be a trivial unsat core, but did not find one.");
}

fn get_formula_for_vector<B>(
    solver: &MiniSat<B>,
    vector: &Vec<isize>,
    f: &FormulaFactory,
) -> EncodedFormula {
    let mut literals = Vec::with_capacity(vector.len());
    for &lit in vector {
        let var = *solver
            .underlying_solver
            .idx2name
            .get(&MsVar(lit.unsigned_abs() - 1))
            .unwrap();
        literals.push(Literal::new(var, lit > 0).into());
    }
    f.or(&literals)
}
