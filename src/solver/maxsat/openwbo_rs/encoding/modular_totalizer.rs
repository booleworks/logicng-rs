use crate::solver::lng_core_solver::{LngCoreSolver, LngLit, not};

use super::clauses::{
    add_binary_clause, add_quaternary_clause, add_ternary_clause, add_unit_clause, new_lit,
};

pub(super) struct MTotalizer {
    modulo: Option<usize>,
    current_rhs: Option<usize>,
    in_lits: Vec<LngLit>,
    upper_out_lits: Vec<Option<LngLit>>,
    lower_out_lits: Vec<LngLit>,
    has_encoding: bool,
}

impl MTotalizer {
    pub(super) fn new() -> Self {
        Self {
            modulo: None,
            current_rhs: None,
            in_lits: Vec::new(),
            upper_out_lits: Vec::new(),
            lower_out_lits: Vec::new(),
            has_encoding: false,
        }
    }

    pub(super) fn set_modulo(&mut self, modulo: usize) {
        self.modulo = Some(modulo);
    }

    pub(super) fn has_created_encoding(&self) -> bool {
        self.has_encoding
    }

    pub(super) fn encode(&mut self, s: &mut LngCoreSolver, lits: &[LngLit], rhs: usize) {
        self.has_encoding = false;
        self.upper_out_lits.clear();
        self.lower_out_lits.clear();

        if rhs == 0 {
            for &lit in lits {
                add_unit_clause(s, not(lit));
            }
            return;
        }

        if rhs == lits.len() {
            return;
        }

        self.has_encoding = true;
        let modulo = *self
            .modulo
            .get_or_insert_with(|| ((rhs + 1) as f64).sqrt().ceil() as usize);

        for _ in 0..lits.len() / modulo {
            self.upper_out_lits.push(Some(new_lit(s)));
        }
        for _ in 0..modulo - 1 {
            self.lower_out_lits.push(new_lit(s));
        }

        self.in_lits = lits.to_vec();
        self.current_rhs = Some(rhs + 1);
        if self.upper_out_lits.is_empty() {
            self.upper_out_lits.push(None);
        }

        let upper = std::mem::take(&mut self.upper_out_lits);
        let lower = std::mem::take(&mut self.lower_out_lits);
        self.to_cnf(s, modulo, &upper, &lower, lits.len());
        self.upper_out_lits = upper;
        self.lower_out_lits = lower;
        self.update(s, rhs);
    }

    pub(super) fn update(&mut self, s: &mut LngCoreSolver, rhs: usize) {
        self.encode_output(s, rhs);
        self.current_rhs = Some(rhs + 1);
    }

    fn encode_output(&self, s: &mut LngCoreSolver, rhs: usize) {
        let modulo = self.modulo.unwrap();
        let ulimit = (rhs + 1) / modulo;
        let llimit = (rhs + 1) - ulimit * modulo;

        for upper in self.upper_out_lits.iter().skip(ulimit).flatten() {
            add_unit_clause(s, not(*upper));
        }

        if ulimit != 0 && llimit != 0 {
            let upper = self.upper_out_lits[ulimit - 1].unwrap();
            for &lower in self.lower_out_lits.iter().skip(llimit - 1) {
                add_binary_clause(s, not(upper), not(lower));
            }
        } else if ulimit == 0 {
            for &lower in self.lower_out_lits.iter().skip(llimit - 1) {
                add_unit_clause(s, not(lower));
            }
        } else {
            let upper = self.upper_out_lits[ulimit - 1].unwrap();
            add_unit_clause(s, not(upper));
        }
    }

    fn to_cnf(
        &mut self,
        s: &mut LngCoreSolver,
        modulo: usize,
        upper: &[Option<LngLit>],
        lower: &[LngLit],
        rhs: usize,
    ) {
        let mut left_upper = Vec::new();
        let mut left_lower = Vec::new();
        let mut right_upper = Vec::new();
        let mut right_lower = Vec::new();

        let split = rhs / 2;

        if split == 1 {
            left_upper.push(None);
            left_lower.push(self.in_lits.pop().unwrap());
        } else {
            let left = split / modulo;
            for _ in 0..left {
                left_upper.push(Some(new_lit(s)));
            }
            let mut limit = modulo - 1;
            if left % modulo == 0 && split < modulo - 1 {
                limit = split;
            }
            for _ in 0..limit {
                left_lower.push(new_lit(s));
            }
        }

        if rhs - split == 1 {
            right_upper.push(None);
            right_lower.push(self.in_lits.pop().unwrap());
        } else {
            let right = (rhs - split) / modulo;
            for _ in 0..right {
                right_upper.push(Some(new_lit(s)));
            }
            let mut limit = modulo - 1;
            if right % modulo == 0 && rhs - split < modulo - 1 {
                limit = rhs - split;
            }
            for _ in 0..limit {
                right_lower.push(new_lit(s));
            }
        }

        if left_upper.is_empty() {
            left_upper.push(None);
        }
        if right_upper.is_empty() {
            right_upper.push(None);
        }

        let left_size = split;
        let right_size = rhs - split;

        self.adder(
            s,
            modulo,
            upper,
            lower,
            &right_upper,
            &right_lower,
            &left_upper,
            &left_lower,
        );

        if left_size > 1 {
            self.to_cnf(s, modulo, &left_upper, &left_lower, left_size);
        }
        if right_size > 1 {
            self.to_cnf(s, modulo, &right_upper, &right_lower, right_size);
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn adder(
        &self,
        s: &mut LngCoreSolver,
        modulo: usize,
        upper: &[Option<LngLit>],
        lower: &[LngLit],
        left_upper: &[Option<LngLit>],
        left_lower: &[LngLit],
        right_upper: &[Option<LngLit>],
        right_lower: &[LngLit],
    ) {
        let carry = upper[0].map(|_| new_lit(s));
        let current_rhs = self.current_rhs.unwrap();

        for i in 0..=left_lower.len() {
            for j in 0..=right_lower.len() {
                if i + j > current_rhs + 1 && current_rhs + 1 < modulo {
                    continue;
                }

                if i + j < modulo {
                    if i == 0 && j != 0 {
                        if let Some(carry) = carry {
                            add_ternary_clause(s, not(right_lower[j - 1]), lower[i + j - 1], carry);
                        } else {
                            add_binary_clause(s, not(right_lower[j - 1]), lower[i + j - 1]);
                        }
                    } else if j == 0 && i != 0 {
                        if let Some(carry) = carry {
                            add_ternary_clause(s, not(left_lower[i - 1]), lower[i + j - 1], carry);
                        } else {
                            add_binary_clause(s, not(left_lower[i - 1]), lower[i + j - 1]);
                        }
                    } else if i != 0 {
                        if let Some(carry) = carry {
                            add_quaternary_clause(
                                s,
                                not(left_lower[i - 1]),
                                not(right_lower[j - 1]),
                                lower[i + j - 1],
                                carry,
                            );
                        } else {
                            add_ternary_clause(
                                s,
                                not(left_lower[i - 1]),
                                not(right_lower[j - 1]),
                                lower[i + j - 1],
                            );
                        }
                    }
                } else if i + j > modulo {
                    add_ternary_clause(
                        s,
                        not(left_lower[i - 1]),
                        not(right_lower[j - 1]),
                        lower[(i + j) % modulo - 1],
                    );
                } else {
                    if let Some(carry) = carry {
                        add_ternary_clause(
                            s,
                            not(left_lower[i - 1]),
                            not(right_lower[j - 1]),
                            carry,
                        );
                    }
                }
            }
        }

        let Some(carry) = carry else {
            return;
        };

        for i in 0..=left_upper.len() {
            for j in 0..=right_upper.len() {
                let a = (i != 0).then(|| left_upper[i - 1]).flatten();
                let b = (j != 0).then(|| right_upper[j - 1]).flatten();
                let c = (i + j != 0 && i + j - 1 < upper.len())
                    .then(|| upper[i + j - 1])
                    .flatten();
                let d = (i + j < upper.len()).then(|| upper[i + j]).flatten();

                let mut close_mod = current_rhs / modulo;
                if current_rhs % modulo != 0 {
                    close_mod += 1;
                }
                if modulo * (i + j) > close_mod * modulo {
                    continue;
                }

                if let Some(c) = c {
                    let mut clause = Vec::new();
                    if let Some(a) = a {
                        clause.push(not(a));
                    }
                    if let Some(b) = b {
                        clause.push(not(b));
                    }
                    clause.push(c);
                    if clause.len() > 1 {
                        s.add_clause(clause, None);
                    }
                }

                let mut clause = vec![not(carry)];
                if let Some(a) = a {
                    clause.push(not(a));
                }
                if let Some(b) = b {
                    clause.push(not(b));
                }
                if let Some(d) = d {
                    clause.push(d);
                }
                if clause.len() > 1 {
                    s.add_clause(clause, None);
                }
            }
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
        let mut totalizer = MTotalizer::new();

        totalizer.encode(&mut solver, &lits, 0);

        assert!(!totalizer.has_created_encoding());
        assert_at_most(&mut solver, lits.len(), 0);
    }

    #[test]
    fn test_encode_trivial_rhs_creates_no_encoding() {
        let (mut solver, lits) = new_solver_with_lits(3);
        let mut totalizer = MTotalizer::new();

        totalizer.encode(&mut solver, &lits, lits.len());

        assert!(!totalizer.has_created_encoding());
        assert!(
            solver
                .internal_solve(&mut NopHandler::new())
                .result()
                .unwrap()
        );
    }

    #[test]
    fn test_encode_at_most_one() {
        let (mut solver, lits) = new_solver_with_lits(4);
        let mut totalizer = MTotalizer::new();

        totalizer.encode(&mut solver, &lits, 1);

        assert!(totalizer.has_created_encoding());
        assert_at_most(&mut solver, lits.len(), 1);
    }

    #[test]
    fn test_encode_at_most_two() {
        let (mut solver, lits) = new_solver_with_lits(5);
        let mut totalizer = MTotalizer::new();

        totalizer.encode(&mut solver, &lits, 2);

        assert!(totalizer.has_created_encoding());
        assert_at_most(&mut solver, lits.len(), 2);
    }

    #[test]
    fn test_update_tightens_bound() {
        let (mut solver, lits) = new_solver_with_lits(5);
        let mut totalizer = MTotalizer::new();

        totalizer.encode(&mut solver, &lits, 3);
        assert_at_most(&mut solver, lits.len(), 3);

        totalizer.update(&mut solver, 1);
        assert_at_most(&mut solver, lits.len(), 1);
    }
}
