use crate::solver::lng_core_solver::{LngCoreSolver, LngLit, not};
use std::collections::VecDeque;

use super::clauses::{
    add_binary_clause, add_quaternary_clause, add_ternary_clause, add_unit_clause, new_lit,
};

pub(super) struct Adder {
    output: Vec<Option<LngLit>>,
    buckets: Vec<VecDeque<LngLit>>,
    has_encoding: bool,
}

impl Adder {
    pub(super) fn new() -> Self {
        Self {
            output: Vec::new(),
            buckets: Vec::new(),
            has_encoding: false,
        }
    }

    pub(super) fn has_created_encoding(&self) -> bool {
        self.has_encoding
    }

    pub(super) fn encode(
        &mut self,
        s: &mut LngCoreSolver,
        lits: &[LngLit],
        coeffs: &[usize],
        rhs: usize,
    ) {
        self.output.clear();
        self.buckets.clear();
        self.has_encoding = false;

        if rhs == 0 {
            for (&lit, &coeff) in lits.iter().zip(coeffs.iter()) {
                if coeff > 0 {
                    add_unit_clause(s, not(lit));
                }
            }
            return;
        }

        let bits = Self::bit_width(rhs);
        for bit in 0..bits {
            let mut bucket = VecDeque::new();
            for (&lit, &coeff) in lits.iter().zip(coeffs.iter()) {
                if ((1usize << bit) & coeff) != 0 {
                    bucket.push_back(lit);
                }
            }
            self.buckets.push(bucket);
            self.output.push(None);
        }

        Self::adder_tree(s, &mut self.buckets, &mut self.output);
        let rhs_bits = Self::num_to_bits(self.buckets.len(), rhs);
        Self::less_than_or_equal(s, &self.output, &rhs_bits);
        self.has_encoding = true;
    }

    pub(super) fn update(&mut self, s: &mut LngCoreSolver, rhs: usize) {
        let rhs_bits = Self::num_to_bits(self.buckets.len(), rhs);
        Self::less_than_or_equal(s, &self.output, &rhs_bits);
    }

    fn fa_extra(
        s: &mut LngCoreSolver,
        carry: LngLit,
        sum: LngLit,
        a: LngLit,
        b: LngLit,
        c: LngLit,
    ) {
        add_ternary_clause(s, not(carry), not(sum), a);
        add_ternary_clause(s, not(carry), not(sum), b);
        add_ternary_clause(s, not(carry), not(sum), c);
        add_ternary_clause(s, carry, sum, not(a));
        add_ternary_clause(s, carry, sum, not(b));
        add_ternary_clause(s, carry, sum, not(c));
    }

    fn fa_carry(s: &mut LngCoreSolver, a: LngLit, b: LngLit, c: LngLit) -> LngLit {
        let x = new_lit(s);
        add_ternary_clause(s, b, c, not(x));
        add_ternary_clause(s, a, c, not(x));
        add_ternary_clause(s, a, b, not(x));
        add_ternary_clause(s, not(b), not(c), x);
        add_ternary_clause(s, not(a), not(c), x);
        add_ternary_clause(s, not(a), not(b), x);
        x
    }

    fn fa_sum(s: &mut LngCoreSolver, a: LngLit, b: LngLit, c: LngLit) -> LngLit {
        let x = new_lit(s);
        add_quaternary_clause(s, a, b, c, not(x));
        add_quaternary_clause(s, a, not(b), not(c), not(x));
        add_quaternary_clause(s, not(a), b, not(c), not(x));
        add_quaternary_clause(s, not(a), not(b), c, not(x));
        add_quaternary_clause(s, not(a), not(b), not(c), x);
        add_quaternary_clause(s, not(a), b, c, x);
        add_quaternary_clause(s, a, not(b), c, x);
        add_quaternary_clause(s, a, b, not(c), x);
        x
    }

    fn ha_carry(s: &mut LngCoreSolver, a: LngLit, b: LngLit) -> LngLit {
        let x = new_lit(s);
        add_binary_clause(s, a, not(x));
        add_binary_clause(s, b, not(x));
        add_ternary_clause(s, not(a), not(b), x);
        x
    }

    fn ha_sum(s: &mut LngCoreSolver, a: LngLit, b: LngLit) -> LngLit {
        let x = new_lit(s);
        add_ternary_clause(s, not(a), not(b), not(x));
        add_ternary_clause(s, a, b, not(x));
        add_ternary_clause(s, not(a), b, x);
        add_ternary_clause(s, a, not(b), x);
        x
    }

    fn adder_tree(
        s: &mut LngCoreSolver,
        buckets: &mut Vec<VecDeque<LngLit>>,
        output: &mut Vec<Option<LngLit>>,
    ) {
        let mut i = 0;
        while i < buckets.len() {
            if buckets[i].is_empty() {
                i += 1;
                continue;
            }

            if i == buckets.len() - 1 && buckets[i].len() >= 2 {
                buckets.push(VecDeque::new());
                output.push(None);
            }

            while buckets[i].len() >= 3 {
                let x = buckets[i].pop_front().unwrap();
                let y = buckets[i].pop_front().unwrap();
                let z = buckets[i].pop_front().unwrap();
                let sum = Self::fa_sum(s, x, y, z);
                let carry = Self::fa_carry(s, x, y, z);
                buckets[i].push_back(sum);
                buckets[i + 1].push_back(carry);
                Self::fa_extra(s, carry, sum, x, y, z);
            }

            if buckets[i].len() == 2 {
                let x = buckets[i].pop_front().unwrap();
                let y = buckets[i].pop_front().unwrap();
                buckets[i].push_back(Self::ha_sum(s, x, y));
                buckets[i + 1].push_back(Self::ha_carry(s, x, y));
            }

            output[i] = buckets[i].pop_front();
            i += 1;
        }
    }

    fn less_than_or_equal(s: &mut LngCoreSolver, xs: &[Option<LngLit>], ys: &[u8]) {
        for i in 0..xs.len() {
            let Some(xi) = xs[i] else {
                continue;
            };
            if ys[i] == 1 {
                continue;
            }

            let mut clause = Vec::new();
            let mut skip = false;

            for j in i + 1..xs.len() {
                match (ys[j], xs[j]) {
                    (1, Some(xj)) => clause.push(not(xj)),
                    (1, None) => {
                        skip = true;
                        break;
                    }
                    (0, Some(xj)) => clause.push(xj),
                    (0, None) => {}
                    _ => unreachable!("rhs bits are binary"),
                }
            }

            if !skip {
                clause.push(not(xi));
                s.add_clause(clause, None);
            }
        }
    }

    fn num_to_bits(width: usize, mut number: usize) -> Vec<u8> {
        let mut bits = Vec::with_capacity(width);
        for i in (0..width).rev() {
            let bit = 1usize << i;
            if number < bit {
                bits.push(0);
            } else {
                bits.push(1);
                number -= bit;
            }
        }
        bits.reverse();
        bits
    }

    fn bit_width(number: usize) -> usize {
        usize::BITS as usize - number.leading_zeros() as usize
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
        let (mut solver, lits) = new_solver_with_lits(3);
        let coeffs = vec![1, 2, 3];
        let mut adder = Adder::new();

        adder.encode(&mut solver, &lits, &coeffs, 0);

        assert!(!adder.has_created_encoding());
        assert_weighted_at_most(&mut solver, &coeffs, 0);
    }

    #[test]
    fn test_encode_weighted_bound() {
        let (mut solver, lits) = new_solver_with_lits(4);
        let coeffs = vec![1, 2, 3, 4];
        let mut adder = Adder::new();

        adder.encode(&mut solver, &lits, &coeffs, 5);

        assert!(adder.has_created_encoding());
        assert_weighted_at_most(&mut solver, &coeffs, 5);
    }

    #[test]
    fn test_encode_with_non_power_of_two_rhs() {
        let (mut solver, lits) = new_solver_with_lits(4);
        let coeffs = vec![2, 5, 7, 9];
        let mut adder = Adder::new();

        adder.encode(&mut solver, &lits, &coeffs, 11);

        assert!(adder.has_created_encoding());
        assert_weighted_at_most(&mut solver, &coeffs, 11);
    }

    #[test]
    fn test_update_tightens_bound() {
        let (mut solver, lits) = new_solver_with_lits(4);
        let coeffs = vec![1, 2, 3, 4];
        let mut adder = Adder::new();

        adder.encode(&mut solver, &lits, &coeffs, 7);
        assert_weighted_at_most(&mut solver, &coeffs, 7);

        adder.update(&mut solver, 3);
        assert_weighted_at_most(&mut solver, &coeffs, 3);
    }
}
