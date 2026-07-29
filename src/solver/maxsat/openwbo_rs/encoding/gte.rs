use std::collections::BTreeMap;

use crate::solver::lng_core_solver::{LngCoreSolver, LngLit, not, var};

use super::clauses::{add_binary_clause, add_ternary_clause, add_unit_clause, new_lit};

pub(super) struct Gte {
    output_lits: BTreeMap<usize, LngLit>,
    current_rhs: Option<usize>,
    has_encoding: bool,
}

#[derive(Clone, Copy)]
struct WeightedLit {
    lit: LngLit,
    weight: usize,
}

impl Gte {
    pub(super) fn new() -> Self {
        Self {
            output_lits: BTreeMap::new(),
            current_rhs: None,
            has_encoding: false,
        }
    }

    pub(super) fn has_created_encoding(&self) -> bool {
        self.has_encoding
    }

    pub(super) fn encode(
        &mut self,
        s: &mut LngCoreSolver,
        lits: &mut Vec<LngLit>,
        coeffs: &mut Vec<usize>,
        rhs: usize,
    ) {
        self.output_lits.clear();
        self.current_rhs = None;
        self.has_encoding = false;

        let simp_lits = std::mem::take(lits);
        let simp_coeffs = std::mem::take(coeffs);

        for (lit, coeff) in simp_lits.into_iter().zip(simp_coeffs) {
            if coeff == 0 {
                continue;
            }
            if coeff <= rhs {
                lits.push(lit);
                coeffs.push(coeff);
            } else {
                add_unit_clause(s, not(lit));
            }
        }

        if lits.len() <= 1 {
            return;
        }

        let mut input_lits = lits
            .iter()
            .zip(coeffs.iter())
            .map(|(&lit, &weight)| WeightedLit { lit, weight })
            .collect::<Vec<_>>();
        input_lits.sort_by_key(|weighted_lit| weighted_lit.weight);

        Self::encode_leq(s, rhs + 1, &input_lits, &mut self.output_lits);

        for (&weight, &lit) in self.output_lits.iter().rev() {
            if weight > rhs {
                add_unit_clause(s, not(lit));
            } else {
                break;
            }
        }

        self.current_rhs = Some(rhs);
        self.has_encoding = true;
    }

    pub(super) fn update(&mut self, s: &mut LngCoreSolver, rhs: usize) {
        let current_rhs = self.current_rhs.unwrap_or(0);
        for (&weight, &lit) in self.output_lits.iter().rev() {
            if weight > current_rhs {
                continue;
            }
            if weight > rhs {
                add_unit_clause(s, not(lit));
            } else {
                break;
            }
        }
        self.current_rhs = Some(rhs);
    }

    pub(super) fn predict(
        &mut self,
        s: &mut LngCoreSolver,
        lits: &mut Vec<LngLit>,
        coeffs: &mut Vec<usize>,
        rhs: usize,
    ) -> usize {
        const MAX_CLAUSES: usize = 3_000_000;

        let simp_lits = std::mem::take(lits);
        let simp_coeffs = std::mem::take(coeffs);
        let mut clauses = 0;

        for (lit, coeff) in simp_lits.into_iter().zip(simp_coeffs) {
            if coeff == 0 {
                continue;
            }
            if coeff <= rhs {
                lits.push(lit);
                coeffs.push(coeff);
            } else {
                clauses += 1;
            }
        }

        if lits.len() <= 1 {
            return clauses;
        }

        let mut input_lits = lits
            .iter()
            .zip(coeffs.iter())
            .map(|(&lit, &weight)| WeightedLit { lit, weight })
            .collect::<Vec<_>>();
        input_lits.sort_by_key(|weighted_lit| weighted_lit.weight);

        let mut output_lits = BTreeMap::new();
        let mut next_var = s.vars.len();
        Self::predict_encode_leq(
            rhs + 1,
            &input_lits,
            &mut output_lits,
            &mut clauses,
            &mut next_var,
            MAX_CLAUSES,
        );
        clauses
    }

    fn encode_leq(
        s: &mut LngCoreSolver,
        k: usize,
        input_lits: &[WeightedLit],
        output_lits: &mut BTreeMap<usize, LngLit>,
    ) -> bool {
        if input_lits.is_empty() || k == 0 {
            return false;
        }

        if input_lits.len() == 1 {
            output_lits
                .entry(input_lits[0].weight)
                .or_insert(input_lits[0].lit);
            return true;
        }

        let split = input_lits.len() >> 1;
        let (left_inputs, right_inputs) = input_lits.split_at(split);
        let left_k = left_inputs
            .iter()
            .map(|weighted_lit| weighted_lit.weight)
            .sum::<usize>()
            .min(k);
        let right_k = right_inputs
            .iter()
            .map(|weighted_lit| weighted_lit.weight)
            .sum::<usize>()
            .min(k);

        let mut left_outputs = BTreeMap::new();
        let mut right_outputs = BTreeMap::new();
        if !Self::encode_leq(s, left_k, left_inputs, &mut left_outputs) {
            return false;
        }
        if !Self::encode_leq(s, right_k, right_inputs, &mut right_outputs) {
            return false;
        }

        for (&weight, &lit) in &left_outputs {
            let output = Self::get_var(s, output_lits, weight.min(k));
            add_binary_clause(s, not(lit), output);
        }

        for (&weight, &lit) in &right_outputs {
            let output = Self::get_var(s, output_lits, weight.min(k));
            add_binary_clause(s, not(lit), output);
        }

        for (&left_weight, &left_lit) in &left_outputs {
            for (&right_weight, &right_lit) in &right_outputs {
                let output = Self::get_var(s, output_lits, (left_weight + right_weight).min(k));
                add_ternary_clause(s, not(left_lit), not(right_lit), output);
            }
        }

        true
    }

    fn get_var(
        s: &mut LngCoreSolver,
        output_lits: &mut BTreeMap<usize, LngLit>,
        weight: usize,
    ) -> LngLit {
        if let Some(&lit) = output_lits.get(&weight) {
            lit
        } else {
            let lit = new_lit(s);
            output_lits.insert(weight, lit);
            lit
        }
    }

    fn predict_encode_leq(
        k: usize,
        input_lits: &[WeightedLit],
        output_lits: &mut BTreeMap<usize, usize>,
        clauses: &mut usize,
        next_var: &mut usize,
        max_clauses: usize,
    ) -> bool {
        if *clauses >= max_clauses {
            return false;
        }

        if input_lits.is_empty() || k == 0 {
            return false;
        }

        if input_lits.len() == 1 {
            output_lits
                .entry(input_lits[0].weight)
                .or_insert(var(input_lits[0].lit).0);
            return true;
        }

        let split = input_lits.len() >> 1;
        let (left_inputs, right_inputs) = input_lits.split_at(split);
        let left_k = left_inputs
            .iter()
            .map(|weighted_lit| weighted_lit.weight)
            .sum::<usize>()
            .min(k);
        let right_k = right_inputs
            .iter()
            .map(|weighted_lit| weighted_lit.weight)
            .sum::<usize>()
            .min(k);

        let mut left_outputs = BTreeMap::new();
        let mut right_outputs = BTreeMap::new();
        if !Self::predict_encode_leq(
            left_k,
            left_inputs,
            &mut left_outputs,
            clauses,
            next_var,
            max_clauses,
        ) {
            return false;
        }
        if !Self::predict_encode_leq(
            right_k,
            right_inputs,
            &mut right_outputs,
            clauses,
            next_var,
            max_clauses,
        ) {
            return false;
        }

        for &weight in left_outputs.keys() {
            Self::get_var_predict(output_lits, weight.min(k), next_var);
            *clauses += 1;
            if *clauses >= max_clauses {
                return false;
            }
        }

        for &weight in right_outputs.keys() {
            Self::get_var_predict(output_lits, weight.min(k), next_var);
            *clauses += 1;
            if *clauses >= max_clauses {
                return false;
            }
        }

        for &left_weight in left_outputs.keys() {
            for &right_weight in right_outputs.keys() {
                Self::get_var_predict(output_lits, (left_weight + right_weight).min(k), next_var);
                *clauses += 1;
                if *clauses >= max_clauses {
                    return false;
                }
            }
        }

        true
    }

    fn get_var_predict(
        output_lits: &mut BTreeMap<usize, usize>,
        weight: usize,
        next_var: &mut usize,
    ) -> usize {
        if let Some(&lit) = output_lits.get(&weight) {
            lit
        } else {
            let lit = *next_var;
            *next_var += 1;
            output_lits.insert(weight, lit);
            lit
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::handlers::NopHandler;
    use crate::solver::lng_core_solver::{LngVar, mk_lit};

    fn new_solver_with_lits(n: usize) -> (LngCoreSolver, Vec<LngLit>) {
        let mut solver = LngCoreSolver::new();
        let lits = (0..n)
            .map(|_| {
                let var = solver.new_var(true, true);
                mk_lit(var, false)
            })
            .collect();
        (solver, lits)
    }

    fn assumptions_for_assignment(values: &[bool]) -> Vec<LngLit> {
        values
            .iter()
            .enumerate()
            .map(|(idx, &value)| mk_lit(LngVar(idx), !value))
            .collect()
    }

    fn assignments(n: usize) -> Vec<Vec<bool>> {
        (0..(1usize << n))
            .map(|mask| (0..n).map(|idx| (mask & (1usize << idx)) != 0).collect())
            .collect()
    }

    fn assert_weighted_at_most(solver: &mut LngCoreSolver, coeffs: &[usize], rhs: usize) {
        for assignment in assignments(coeffs.len()) {
            let sum = assignment
                .iter()
                .zip(coeffs.iter())
                .filter_map(|(&value, &coeff)| value.then_some(coeff))
                .sum::<usize>();
            let expected = sum <= rhs;
            let result = solver
                .internal_solve_with_assumptions(
                    &mut NopHandler::new(),
                    assumptions_for_assignment(&assignment),
                )
                .result()
                .unwrap();
            assert_eq!(
                result, expected,
                "assignment={assignment:?}, sum={sum}, rhs={rhs}"
            );
        }
    }

    #[test]
    fn test_encode_rhs_zero_forces_positive_weight_inputs_false() {
        let (mut solver, mut lits) = new_solver_with_lits(3);
        let original_coeffs = vec![1, 2, 3];
        let mut coeffs = original_coeffs.clone();
        let mut gte = Gte::new();

        gte.encode(&mut solver, &mut lits, &mut coeffs, 0);

        assert!(!gte.has_created_encoding());
        assert!(lits.is_empty());
        assert!(coeffs.is_empty());
        assert_weighted_at_most(&mut solver, &original_coeffs, 0);
    }

    #[test]
    fn test_encode_weighted_bound() {
        let (mut solver, mut lits) = new_solver_with_lits(4);
        let original_coeffs = vec![1, 2, 3, 4];
        let mut coeffs = original_coeffs.clone();
        let mut gte = Gte::new();

        gte.encode(&mut solver, &mut lits, &mut coeffs, 5);

        assert!(gte.has_created_encoding());
        assert_eq!(coeffs, original_coeffs);
        assert_weighted_at_most(&mut solver, &original_coeffs, 5);
    }

    #[test]
    fn test_encode_with_non_power_of_two_rhs() {
        let (mut solver, mut lits) = new_solver_with_lits(4);
        let original_coeffs = vec![2, 5, 7, 9];
        let mut coeffs = original_coeffs.clone();
        let mut gte = Gte::new();

        gte.encode(&mut solver, &mut lits, &mut coeffs, 11);

        assert!(gte.has_created_encoding());
        assert_eq!(coeffs, original_coeffs);
        assert_weighted_at_most(&mut solver, &original_coeffs, 11);
    }

    #[test]
    fn test_encode_simplifies_inputs_above_rhs() {
        let (mut solver, mut lits) = new_solver_with_lits(4);
        let original_coeffs = vec![1, 4, 6, 8];
        let mut coeffs = original_coeffs.clone();
        let mut gte = Gte::new();

        gte.encode(&mut solver, &mut lits, &mut coeffs, 5);

        assert_eq!(lits.len(), 2);
        assert_eq!(coeffs, vec![1, 4]);
        assert_weighted_at_most(&mut solver, &original_coeffs, 5);
    }

    #[test]
    fn test_update_tightens_bound() {
        let (mut solver, mut lits) = new_solver_with_lits(4);
        let original_coeffs = vec![1, 2, 3, 4];
        let mut coeffs = original_coeffs.clone();
        let mut gte = Gte::new();

        gte.encode(&mut solver, &mut lits, &mut coeffs, 7);
        assert_weighted_at_most(&mut solver, &original_coeffs, 7);

        gte.update(&mut solver, 3);
        assert_weighted_at_most(&mut solver, &original_coeffs, 3);
    }

    #[test]
    fn test_predict_simplifies_inputs_and_estimates_nontrivial_encoding() {
        let (mut solver, mut lits) = new_solver_with_lits(4);
        let mut coeffs = vec![1, 2, 6, 7];
        let mut gte = Gte::new();

        let clauses = gte.predict(&mut solver, &mut lits, &mut coeffs, 5);

        assert_eq!(lits.len(), 2);
        assert_eq!(coeffs, vec![1, 2]);
        assert!(clauses >= 2);
        assert!(!gte.has_created_encoding());
    }
}
