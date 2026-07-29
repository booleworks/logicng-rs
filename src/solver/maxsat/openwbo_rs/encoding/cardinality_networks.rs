use crate::solver::lng_core_solver::{LngCoreSolver, LngLit, not};

use super::clauses::{add_binary_clause, add_ternary_clause, add_unit_clause, new_lit};

pub(super) struct CNetworks {
    out_lits: Vec<LngLit>,
    current_rhs: Option<usize>,
    has_encoding: bool,
}

impl CNetworks {
    pub(super) fn new() -> Self {
        Self {
            out_lits: Vec::new(),
            current_rhs: None,
            has_encoding: false,
        }
    }

    pub(super) fn has_created_encoding(&self) -> bool {
        self.has_encoding
    }

    pub(super) fn encode(&mut self, s: &mut LngCoreSolver, lits: &[LngLit], rhs: usize) {
        self.current_rhs = Some(rhs);
        self.out_lits.clear();
        self.has_encoding = false;

        if rhs == 0 {
            for &lit in lits {
                add_unit_clause(s, not(lit));
            }
            return;
        }

        let mut lits_copy = lits.to_vec();
        let mut units = Vec::new();
        let new_rhs = (rhs + 1).next_power_of_two();
        let padding = lits_copy.len().div_ceil(new_rhs) * new_rhs - lits_copy.len();

        for _ in 0..padding {
            let lit = new_lit(s);
            lits_copy.push(lit);
            units.push(not(lit));
        }

        for _ in 0..new_rhs {
            self.out_lits.push(new_lit(s));
        }

        for &out_lit in self.out_lits.iter().skip(rhs) {
            units.push(not(out_lit));
        }

        let out_lits = std::mem::take(&mut self.out_lits);
        self.cn_encode(s, &lits_copy, &out_lits, new_rhs);
        self.out_lits = out_lits;

        for unit in units {
            add_unit_clause(s, unit);
        }
        self.has_encoding = true;
    }

    pub(super) fn update(&mut self, s: &mut LngCoreSolver, rhs: usize) {
        for &out_lit in &self.out_lits[rhs..self.current_rhs.unwrap()] {
            add_unit_clause(s, not(out_lit));
        }
        self.current_rhs = Some(rhs);
    }

    fn cn_hmerge(
        &mut self,
        s: &mut LngCoreSolver,
        left: &[LngLit],
        right: &[LngLit],
        output: &[LngLit],
    ) {
        if left.len() == 1 {
            add_ternary_clause(s, not(left[0]), not(right[0]), output[1]);
            add_binary_clause(s, not(left[0]), output[0]);
            add_binary_clause(s, not(right[0]), output[0]);
        } else {
            let odd_left = left.iter().step_by(2).copied().collect::<Vec<_>>();
            let even_left = left.iter().skip(1).step_by(2).copied().collect::<Vec<_>>();
            let odd_right = right.iter().step_by(2).copied().collect::<Vec<_>>();
            let even_right = right.iter().skip(1).step_by(2).copied().collect::<Vec<_>>();

            let mut d = Vec::with_capacity(left.len());
            let mut e = Vec::with_capacity(left.len());
            d.push(output[0]);
            for _ in 1..left.len() {
                d.push(new_lit(s));
            }
            for _ in 0..left.len() - 1 {
                e.push(new_lit(s));
            }
            e.push(output[output.len() - 1]);

            for i in 1..left.len() {
                add_ternary_clause(s, not(d[i]), not(e[i - 1]), output[2 * i]);
                add_binary_clause(s, not(d[i]), output[2 * i - 1]);
                add_binary_clause(s, not(e[i - 1]), output[2 * i - 1]);
            }

            self.cn_hmerge(s, &odd_left, &odd_right, &d);
            self.cn_hmerge(s, &even_left, &even_right, &e);
        }
    }

    fn cn_hsort(&mut self, s: &mut LngCoreSolver, input: &[LngLit], output: &[LngLit]) {
        if input.len() == 2 {
            self.cn_hmerge(s, &[input[0]], &[input[1]], output);
        } else {
            let split = input.len() / 2;
            let lower_input = &input[..split];
            let upper_input = &input[split..];
            let mut lower_output = Vec::with_capacity(split);
            let mut upper_output = Vec::with_capacity(split);
            for _ in 0..split {
                upper_output.push(new_lit(s));
                lower_output.push(new_lit(s));
            }

            self.cn_hsort(s, lower_input, &lower_output);
            self.cn_hsort(s, upper_input, &upper_output);
            self.cn_hmerge(s, &lower_output, &upper_output, output);
        }
    }

    fn cn_smerge(
        &mut self,
        s: &mut LngCoreSolver,
        left: &[LngLit],
        right: &[LngLit],
        output: &[LngLit],
    ) {
        if left.len() == 1 {
            add_ternary_clause(s, not(left[0]), not(right[0]), output[1]);
            add_binary_clause(s, not(left[0]), output[0]);
            add_binary_clause(s, not(right[0]), output[0]);
        } else {
            let odd_left = left.iter().step_by(2).copied().collect::<Vec<_>>();
            let even_left = left.iter().skip(1).step_by(2).copied().collect::<Vec<_>>();
            let odd_right = right.iter().step_by(2).copied().collect::<Vec<_>>();
            let even_right = right.iter().skip(1).step_by(2).copied().collect::<Vec<_>>();

            let half = left.len() / 2;
            let mut d = Vec::with_capacity(half + 1);
            let mut e = Vec::with_capacity(half + 1);
            d.push(output[0]);
            for _ in 1..half + 1 {
                d.push(new_lit(s));
            }
            for _ in 0..half + 1 {
                e.push(new_lit(s));
            }

            for i in 1..=half {
                add_ternary_clause(s, not(d[i]), not(e[i - 1]), output[2 * i]);
                add_binary_clause(s, not(d[i]), output[2 * i - 1]);
                add_binary_clause(s, not(e[i - 1]), output[2 * i - 1]);
            }

            self.cn_smerge(s, &odd_left, &odd_right, &d);
            self.cn_smerge(s, &even_left, &even_right, &e);
        }
    }

    fn cn_encode(
        &mut self,
        s: &mut LngCoreSolver,
        input: &[LngLit],
        output: &[LngLit],
        rhs: usize,
    ) {
        if input.len() == rhs {
            self.cn_hsort(s, input, output);
        } else {
            let lower_input = &input[..rhs];
            let upper_input = &input[rhs..];
            let mut lower_output = Vec::with_capacity(rhs);
            let mut upper_output = Vec::with_capacity(rhs);
            for _ in 0..rhs {
                lower_output.push(new_lit(s));
                upper_output.push(new_lit(s));
            }

            let mut next_output = output.to_vec();
            next_output.push(new_lit(s));

            self.cn_encode(s, lower_input, &lower_output, rhs);
            self.cn_encode(s, upper_input, &upper_output, rhs);
            self.cn_smerge(s, &lower_output, &upper_output, &next_output);
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

    fn assert_at_most(solver: &mut LngCoreSolver, n: usize, rhs: usize) {
        for assignment in assignments(n) {
            let expected = assignment.iter().filter(|&&value| value).count() <= rhs;
            let result = solver
                .internal_solve_with_assumptions(
                    &mut NopHandler::new(),
                    assumptions_for_assignment(&assignment),
                )
                .result()
                .unwrap();
            assert_eq!(result, expected, "assignment={assignment:?}, rhs={rhs}");
        }
    }

    #[test]
    fn test_encode_rhs_zero_forces_all_inputs_false() {
        let (mut solver, lits) = new_solver_with_lits(3);
        let mut networks = CNetworks::new();

        networks.encode(&mut solver, &lits, 0);

        assert!(!networks.has_created_encoding());
        assert_at_most(&mut solver, lits.len(), 0);
    }

    #[test]
    fn test_encode_at_most_one() {
        let (mut solver, lits) = new_solver_with_lits(4);
        let mut networks = CNetworks::new();

        networks.encode(&mut solver, &lits, 1);

        assert!(networks.has_created_encoding());
        assert_eq!(networks.out_lits.len(), 2);
        assert_at_most(&mut solver, lits.len(), 1);
    }

    #[test]
    fn test_encode_at_most_two() {
        let (mut solver, lits) = new_solver_with_lits(5);
        let mut networks = CNetworks::new();

        networks.encode(&mut solver, &lits, 2);

        assert!(networks.has_created_encoding());
        assert_eq!(networks.out_lits.len(), 4);
        assert_at_most(&mut solver, lits.len(), 2);
    }

    #[test]
    fn test_update_tightens_bound() {
        let (mut solver, lits) = new_solver_with_lits(5);
        let mut networks = CNetworks::new();

        networks.encode(&mut solver, &lits, 3);
        assert_at_most(&mut solver, lits.len(), 3);

        networks.update(&mut solver, 1);
        assert_at_most(&mut solver, lits.len(), 1);
    }
}
