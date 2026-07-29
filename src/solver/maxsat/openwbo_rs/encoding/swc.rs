use crate::solver::lng_core_solver::{LngCoreSolver, LngLit, not};

use super::clauses::{
    add_binary_clause, add_binary_clause_blocking, add_ternary_clause, add_unit_clause, new_lit,
};

pub(super) struct Swc {
    pb_out_lits: Vec<LngLit>,
    unit_lits: Vec<LngLit>,
    unit_coeffs: Vec<usize>,
    current_rhs: Option<usize>,
    current_blocking_lit: Option<LngLit>,
    seq_auxiliary_inc: Vec<Vec<Option<LngLit>>>,
    lits_inc: Vec<LngLit>,
    coeffs_inc: Vec<usize>,
    has_encoding: bool,
}

impl Swc {
    pub(super) fn new() -> Self {
        Self {
            pb_out_lits: Vec::new(),
            unit_lits: Vec::new(),
            unit_coeffs: Vec::new(),
            current_rhs: None,
            current_blocking_lit: None,
            seq_auxiliary_inc: Vec::new(),
            lits_inc: Vec::new(),
            coeffs_inc: Vec::new(),
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
        self.pb_out_lits.clear();
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

        let seq_auxiliary = Self::build(s, lits, coeffs, rhs, None);
        self.pb_out_lits = (1..=rhs)
            .map(|j| Self::lit_at(&seq_auxiliary, lits.len(), j))
            .collect();
        self.current_rhs = Some(rhs);
        self.has_encoding = true;
    }

    pub(super) fn encode_incremental(
        &mut self,
        s: &mut LngCoreSolver,
        lits: &mut Vec<LngLit>,
        coeffs: &mut Vec<usize>,
        rhs: usize,
        assumptions: &mut Vec<LngLit>,
        size: usize,
    ) {
        self.has_encoding = false;

        let simp_lits = std::mem::take(lits);
        let simp_coeffs = std::mem::take(coeffs);
        self.reconsider_unit_lits(lits, coeffs, rhs);

        for (lit, coeff) in simp_lits.into_iter().zip(simp_coeffs) {
            if coeff <= rhs {
                lits.push(lit);
                coeffs.push(coeff);
            } else {
                self.unit_lits.push(lit);
                self.unit_coeffs.push(coeff);
            }
        }

        if lits.len() == 1 {
            self.add_unit_assumptions(assumptions);
            self.unit_lits.push(lits[0]);
            self.unit_coeffs.push(coeffs[0]);
            return;
        }

        if lits.is_empty() {
            self.add_unit_assumptions(assumptions);
            return;
        }

        let n = lits.len();
        self.seq_auxiliary_inc = vec![Vec::new(); size.max(n) + 1];
        for row in self.seq_auxiliary_inc.iter_mut().take(n + 1) {
            *row = vec![None; rhs + 1];
        }
        Self::allocate_auxiliary(s, &mut self.seq_auxiliary_inc, 1, n, 1, rhs);

        let blocking = new_lit(s);
        self.current_blocking_lit = Some(blocking);
        assumptions.push(not(blocking));

        Self::encode_clauses(
            s,
            &self.seq_auxiliary_inc,
            lits,
            coeffs,
            rhs,
            Some(blocking),
        );

        self.add_unit_assumptions(assumptions);
        self.current_rhs = Some(rhs);
        self.has_encoding = true;
        self.lits_inc.clone_from(lits);
        self.coeffs_inc.clone_from(coeffs);
    }

    pub(super) fn update(&mut self, s: &mut LngCoreSolver, rhs: usize) {
        let current_rhs = self.current_rhs.unwrap_or(0);
        for i in rhs..current_rhs {
            add_unit_clause(s, not(self.pb_out_lits[i]));
        }
        self.current_rhs = Some(rhs);
    }

    pub(super) fn update_incremental(&mut self, s: &mut LngCoreSolver, rhs: usize) {
        if let Some(blocking) = self.current_blocking_lit {
            add_unit_clause(s, blocking);
        }

        let n = self.lits_inc.len();
        let offset = self.current_rhs.unwrap_or(0) + 1;
        for row in self.seq_auxiliary_inc.iter_mut().take(n + 1).skip(1) {
            row.resize(rhs + 1, None);
        }
        Self::allocate_auxiliary(s, &mut self.seq_auxiliary_inc, 1, n, offset, rhs);

        let blocking = new_lit(s);
        self.current_blocking_lit = Some(blocking);

        for i in 1..=n {
            let wi = self.coeffs_inc[i - 1];
            for j in 1..=rhs {
                if i >= 2 && j >= offset {
                    add_binary_clause(
                        s,
                        not(Self::lit_at(&self.seq_auxiliary_inc, i - 1, j)),
                        Self::lit_at(&self.seq_auxiliary_inc, i, j),
                    );
                }
                if i >= 2 && j <= rhs - wi && j + wi >= offset {
                    add_ternary_clause(
                        s,
                        not(Self::lit_at(&self.seq_auxiliary_inc, i - 1, j)),
                        not(self.lits_inc[i - 1]),
                        Self::lit_at(&self.seq_auxiliary_inc, i, j + wi),
                    );
                }
            }

            if i >= 2 {
                add_binary_clause_blocking(
                    s,
                    not(Self::lit_at(&self.seq_auxiliary_inc, i - 1, rhs + 1 - wi)),
                    not(self.lits_inc[i - 1]),
                    Some(blocking),
                );
            }
        }

        self.current_rhs = Some(rhs);
    }

    pub(super) fn join(&mut self, s: &mut LngCoreSolver, lits: &[LngLit], coeffs: &[usize]) {
        let rhs = self.current_rhs.unwrap_or(0);
        let lhs_join = self.lits_inc.len();
        self.reconsider_unit_lits_inc(rhs);

        for (&lit, &coeff) in lits.iter().zip(coeffs.iter()) {
            if coeff <= rhs {
                self.lits_inc.push(lit);
                self.coeffs_inc.push(coeff);
            } else {
                self.unit_lits.push(lit);
                self.unit_coeffs.push(coeff);
            }
        }

        if self.lits_inc.len() == lhs_join {
            return;
        }

        let n = self.lits_inc.len();
        if self.seq_auxiliary_inc.len() <= n {
            self.seq_auxiliary_inc.resize_with(n + 1, Vec::new);
        }
        for i in lhs_join + 1..=n {
            self.seq_auxiliary_inc[i] = vec![None; rhs + 1];
        }
        Self::allocate_auxiliary(s, &mut self.seq_auxiliary_inc, lhs_join + 1, n, 1, rhs);

        let blocking = self.current_blocking_lit;
        for i in lhs_join..=n {
            let wi = self.coeffs_inc[i - 1];
            for j in 1..=rhs {
                add_binary_clause(
                    s,
                    not(Self::lit_at(&self.seq_auxiliary_inc, i - 1, j)),
                    Self::lit_at(&self.seq_auxiliary_inc, i, j),
                );
                if j <= wi {
                    add_binary_clause(
                        s,
                        not(self.lits_inc[i - 1]),
                        Self::lit_at(&self.seq_auxiliary_inc, i, j),
                    );
                }
                if j <= rhs - wi {
                    add_ternary_clause(
                        s,
                        not(Self::lit_at(&self.seq_auxiliary_inc, i - 1, j)),
                        not(self.lits_inc[i - 1]),
                        Self::lit_at(&self.seq_auxiliary_inc, i, j + wi),
                    );
                }
            }

            if i > lhs_join {
                add_binary_clause_blocking(
                    s,
                    not(Self::lit_at(&self.seq_auxiliary_inc, i - 1, rhs + 1 - wi)),
                    not(self.lits_inc[i - 1]),
                    blocking,
                );
            }
        }
    }

    pub(super) fn update_assumptions(&self, assumptions: &mut Vec<LngLit>) {
        if let Some(blocking) = self.current_blocking_lit {
            assumptions.push(not(blocking));
        }
        for &lit in &self.unit_lits {
            assumptions.push(not(lit));
        }
    }

    fn build(
        s: &mut LngCoreSolver,
        lits: &[LngLit],
        coeffs: &[usize],
        rhs: usize,
        blocking: Option<LngLit>,
    ) -> Vec<Vec<Option<LngLit>>> {
        let n = lits.len();
        let mut seq_auxiliary = vec![vec![None; rhs + 1]; n + 1];
        Self::allocate_auxiliary(s, &mut seq_auxiliary, 1, n, 1, rhs);
        Self::encode_clauses(s, &seq_auxiliary, lits, coeffs, rhs, blocking);
        seq_auxiliary
    }

    fn encode_clauses(
        s: &mut LngCoreSolver,
        seq_auxiliary: &[Vec<Option<LngLit>>],
        lits: &[LngLit],
        coeffs: &[usize],
        rhs: usize,
        blocking: Option<LngLit>,
    ) {
        for i in 1..=lits.len() {
            let wi = coeffs[i - 1];
            for j in 1..=rhs {
                if i >= 2 {
                    add_binary_clause(
                        s,
                        not(Self::lit_at(seq_auxiliary, i - 1, j)),
                        Self::lit_at(seq_auxiliary, i, j),
                    );
                }
                if j <= wi {
                    add_binary_clause(s, not(lits[i - 1]), Self::lit_at(seq_auxiliary, i, j));
                }
                if i >= 2 && j <= rhs - wi {
                    add_ternary_clause(
                        s,
                        not(Self::lit_at(seq_auxiliary, i - 1, j)),
                        not(lits[i - 1]),
                        Self::lit_at(seq_auxiliary, i, j + wi),
                    );
                }
            }

            if i >= 2 {
                add_binary_clause_blocking(
                    s,
                    not(Self::lit_at(seq_auxiliary, i - 1, rhs + 1 - wi)),
                    not(lits[i - 1]),
                    blocking,
                );
            }
        }
    }

    fn allocate_auxiliary(
        s: &mut LngCoreSolver,
        seq_auxiliary: &mut [Vec<Option<LngLit>>],
        row_start: usize,
        row_end: usize,
        col_start: usize,
        col_end: usize,
    ) {
        if col_start > col_end {
            return;
        }
        for row in seq_auxiliary.iter_mut().take(row_end + 1).skip(row_start) {
            if row.len() <= col_end {
                row.resize(col_end + 1, None);
            }
            for cell in row.iter_mut().take(col_end + 1).skip(col_start) {
                *cell = Some(new_lit(s));
            }
        }
    }

    fn lit_at(seq_auxiliary: &[Vec<Option<LngLit>>], row: usize, col: usize) -> LngLit {
        seq_auxiliary[row][col].unwrap()
    }

    fn reconsider_unit_lits(
        &mut self,
        lits: &mut Vec<LngLit>,
        coeffs: &mut Vec<usize>,
        rhs: usize,
    ) {
        let old_unit_lits = std::mem::take(&mut self.unit_lits);
        let old_unit_coeffs = std::mem::take(&mut self.unit_coeffs);
        for (lit, coeff) in old_unit_lits.into_iter().zip(old_unit_coeffs) {
            if coeff <= rhs {
                lits.push(lit);
                coeffs.push(coeff);
            } else {
                self.unit_lits.push(lit);
                self.unit_coeffs.push(coeff);
            }
        }
    }

    fn reconsider_unit_lits_inc(&mut self, rhs: usize) {
        let old_unit_lits = std::mem::take(&mut self.unit_lits);
        let old_unit_coeffs = std::mem::take(&mut self.unit_coeffs);
        for (lit, coeff) in old_unit_lits.into_iter().zip(old_unit_coeffs) {
            if coeff <= rhs {
                self.lits_inc.push(lit);
                self.coeffs_inc.push(coeff);
            } else {
                self.unit_lits.push(lit);
                self.unit_coeffs.push(coeff);
            }
        }
    }

    fn add_unit_assumptions(&self, assumptions: &mut Vec<LngLit>) {
        for &lit in &self.unit_lits {
            assumptions.push(not(lit));
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

    fn assert_weighted_at_most(
        solver: &mut LngCoreSolver,
        coeffs: &[usize],
        rhs: usize,
        extra_assumptions: &[LngLit],
    ) {
        for assignment in assignments(coeffs.len()) {
            let sum = assignment
                .iter()
                .zip(coeffs.iter())
                .filter_map(|(&value, &coeff)| value.then_some(coeff))
                .sum::<usize>();
            let expected = sum <= rhs;
            let mut assumptions = assumptions_for_assignment(&assignment);
            assumptions.extend_from_slice(extra_assumptions);
            let result = solver
                .internal_solve_with_assumptions(&mut NopHandler::new(), assumptions)
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
        let mut swc = Swc::new();

        swc.encode(&mut solver, &mut lits, &mut coeffs, 0);

        assert!(!swc.has_created_encoding());
        assert!(lits.is_empty());
        assert!(coeffs.is_empty());
        assert_weighted_at_most(&mut solver, &original_coeffs, 0, &[]);
    }

    #[test]
    fn test_encode_weighted_bound() {
        let (mut solver, mut lits) = new_solver_with_lits(4);
        let original_coeffs = vec![1, 2, 3, 4];
        let mut coeffs = original_coeffs.clone();
        let mut swc = Swc::new();

        swc.encode(&mut solver, &mut lits, &mut coeffs, 5);

        assert!(swc.has_created_encoding());
        assert_eq!(coeffs, original_coeffs);
        assert_weighted_at_most(&mut solver, &original_coeffs, 5, &[]);
    }

    #[test]
    fn test_encode_simplifies_inputs_above_rhs() {
        let (mut solver, mut lits) = new_solver_with_lits(4);
        let original_coeffs = vec![1, 4, 6, 8];
        let mut coeffs = original_coeffs.clone();
        let mut swc = Swc::new();

        swc.encode(&mut solver, &mut lits, &mut coeffs, 5);

        assert_eq!(lits.len(), 2);
        assert_eq!(coeffs, vec![1, 4]);
        assert_weighted_at_most(&mut solver, &original_coeffs, 5, &[]);
    }

    #[test]
    fn test_update_tightens_bound() {
        let (mut solver, mut lits) = new_solver_with_lits(4);
        let original_coeffs = vec![1, 2, 3, 4];
        let mut coeffs = original_coeffs.clone();
        let mut swc = Swc::new();

        swc.encode(&mut solver, &mut lits, &mut coeffs, 7);
        assert_weighted_at_most(&mut solver, &original_coeffs, 7, &[]);

        swc.update(&mut solver, 3);
        assert_weighted_at_most(&mut solver, &original_coeffs, 3, &[]);
    }

    #[test]
    fn test_incremental_encode_uses_assumptions() {
        let (mut solver, mut lits) = new_solver_with_lits(4);
        let original_coeffs = vec![1, 2, 3, 4];
        let mut coeffs = original_coeffs.clone();
        let mut swc = Swc::new();
        let mut assumptions = Vec::new();

        swc.encode_incremental(&mut solver, &mut lits, &mut coeffs, 3, &mut assumptions, 4);

        assert!(swc.has_created_encoding());
        assert_eq!(coeffs, vec![1, 2, 3]);
        assert_weighted_at_most(&mut solver, &original_coeffs, 3, &assumptions);
    }

    #[test]
    fn test_incremental_update_weakens_bound_with_new_assumptions() {
        let (mut solver, mut lits) = new_solver_with_lits(3);
        let original_coeffs = vec![1, 2, 3];
        let mut coeffs = original_coeffs.clone();
        let mut swc = Swc::new();
        let mut assumptions = Vec::new();

        swc.encode_incremental(&mut solver, &mut lits, &mut coeffs, 3, &mut assumptions, 3);
        assert_weighted_at_most(&mut solver, &original_coeffs, 3, &assumptions);

        swc.update_incremental(&mut solver, 4);
        assumptions.clear();
        swc.update_assumptions(&mut assumptions);

        assert_weighted_at_most(&mut solver, &original_coeffs, 4, &assumptions);
    }

    #[test]
    fn test_join_extends_incremental_constraint() {
        let (mut solver, all_lits) = new_solver_with_lits(4);
        let mut lits = all_lits[..2].to_vec();
        let mut coeffs = vec![1, 2];
        let join_lits = all_lits[2..].to_vec();
        let join_coeffs = vec![2, 3];
        let all_coeffs = vec![1, 2, 2, 3];
        let mut swc = Swc::new();
        let mut assumptions = Vec::new();

        swc.encode_incremental(&mut solver, &mut lits, &mut coeffs, 3, &mut assumptions, 4);
        swc.join(&mut solver, &join_lits, &join_coeffs);
        assumptions.clear();
        swc.update_assumptions(&mut assumptions);

        assert_weighted_at_most(&mut solver, &all_coeffs, 3, &assumptions);
    }

    #[test]
    fn test_join_activates_deferred_unit_lits_after_incremental_update() {
        let (mut solver, mut lits) = new_solver_with_lits(3);
        let original_coeffs = vec![1, 2, 4];
        let mut coeffs = original_coeffs.clone();
        let mut swc = Swc::new();
        let mut assumptions = Vec::new();

        swc.encode_incremental(&mut solver, &mut lits, &mut coeffs, 3, &mut assumptions, 3);
        swc.update_incremental(&mut solver, 4);
        swc.join(&mut solver, &[], &[]);
        assumptions.clear();
        swc.update_assumptions(&mut assumptions);

        assert_weighted_at_most(&mut solver, &original_coeffs, 4, &assumptions);
    }
}
