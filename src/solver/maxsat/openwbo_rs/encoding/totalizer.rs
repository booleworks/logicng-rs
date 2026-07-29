use crate::solver::lng_core_solver::{LngCoreSolver, LngLit, not};
use crate::solver::maxsat::IncrementalStrategy;

use super::clauses::{
    add_binary_clause_blocking, add_ternary_clause_blocking, add_unit_clause, new_lit,
};

pub(super) struct Totalizer {
    iterative_left: Vec<Vec<LngLit>>,
    iterative_right: Vec<Vec<LngLit>>,
    iterative_output: Vec<Vec<LngLit>>,
    iterative_rhs: Vec<usize>,
    in_lits: Vec<LngLit>,
    out_lits: Vec<LngLit>,
    lits: Vec<LngLit>,
    current_rhs: Option<usize>,
    blocking: Option<LngLit>,
    disable_lits: Vec<LngLit>,
    join_mode: bool,
    has_encoding: bool,
    incremental: IncrementalStrategy,
}

impl Totalizer {
    pub(super) fn new(incremental: IncrementalStrategy) -> Self {
        Self {
            iterative_left: Vec::new(),
            iterative_right: Vec::new(),
            iterative_output: Vec::new(),
            iterative_rhs: Vec::new(),
            in_lits: Vec::new(),
            out_lits: Vec::new(),
            lits: Vec::new(),
            current_rhs: None,
            blocking: None,
            disable_lits: Vec::new(),
            join_mode: false,
            has_encoding: false,
            incremental,
        }
    }

    pub(super) fn set_incremental(&mut self, incremental: IncrementalStrategy) {
        self.incremental = incremental;
    }

    pub(super) fn has_created_encoding(&self) -> bool {
        self.has_encoding
    }

    pub(super) fn build(&mut self, s: &mut LngCoreSolver, lits: &[LngLit], rhs: usize) {
        self.out_lits.clear();
        self.has_encoding = false;

        if rhs == 0 {
            for &lit in lits {
                add_unit_clause(s, not(lit));
            }
            return;
        }

        if self.incremental == IncrementalStrategy::None && rhs == lits.len() {
            return;
        }

        if rhs == lits.len() && !self.join_mode {
            return;
        }

        self.out_lits = (0..lits.len()).map(|_| new_lit(s)).collect();
        self.in_lits = lits.to_vec();
        self.current_rhs = Some(rhs);

        if self.incremental == IncrementalStrategy::Blocking {
            let blocking = new_lit(s);
            if let Some(previous_blocking) = self.blocking {
                self.disable_lits.push(previous_blocking);
            }
            self.blocking = Some(blocking);
        }

        let out_lits = std::mem::take(&mut self.out_lits);
        self.to_cnf(s, &out_lits);
        self.out_lits = out_lits;

        if !self.join_mode {
            self.join_mode = true;
        }
        self.has_encoding = true;
        self.lits = lits.to_vec();
    }

    pub(super) fn update(&mut self, s: &mut LngCoreSolver, rhs: usize) {
        let mut assumptions = Vec::new();
        self.update_with_assumptions(s, &[], rhs, &mut assumptions);
    }

    pub(super) fn update_with_assumptions(
        &mut self,
        s: &mut LngCoreSolver,
        lits: &[LngLit],
        rhs: usize,
        assumptions: &mut Vec<LngLit>,
    ) {
        match self.incremental {
            IncrementalStrategy::None => {
                for &lit in &self.out_lits[rhs..] {
                    add_unit_clause(s, not(lit));
                }
            }
            IncrementalStrategy::Blocking => {
                assumptions.clear();
                for &lit in &self.disable_lits {
                    add_unit_clause(s, lit);
                }
                self.build(s, lits, rhs);
                if let Some(blocking) = self.blocking {
                    assumptions.push(not(blocking));
                }
                for &lit in &self.out_lits[rhs..] {
                    add_unit_clause(s, not(lit));
                }
            }
            IncrementalStrategy::Weakening => {
                assumptions.clear();
                assumptions.extend(self.out_lits[rhs..].iter().map(|&lit| not(lit)));
            }
            IncrementalStrategy::Iterative => {
                self.incremental(s, rhs);
                assumptions.clear();
                assumptions.extend(self.out_lits[rhs..].iter().map(|&lit| not(lit)));
            }
        }
    }

    pub(super) fn join(&mut self, s: &mut LngCoreSolver, lits: &[LngLit], rhs: usize) {
        let left_out_lits = self.out_lits.clone();
        let old_rhs = self.current_rhs;

        if lits.len() > 1 {
            self.build(s, lits, rhs.min(lits.len()));
        } else {
            self.out_lits.clear();
            self.out_lits.push(lits[0]);
        }

        let right_out_lits = std::mem::take(&mut self.out_lits);
        let out_lits: Vec<LngLit> = (0..left_out_lits.len() + right_out_lits.len())
            .map(|_| new_lit(s))
            .collect();

        self.current_rhs = Some(rhs);
        self.adder(s, &left_out_lits, &right_out_lits, &out_lits);
        self.current_rhs = old_rhs;
        self.out_lits = out_lits;

        self.lits.extend_from_slice(lits);
    }

    pub(super) fn add(&mut self, s: &mut LngCoreSolver, other: &mut Totalizer, rhs: usize) {
        let left_idx = self.iterative_rhs.len().checked_sub(1).unwrap();

        self.iterative_left
            .extend(other.iterative_left.iter().cloned());
        self.iterative_right
            .extend(other.iterative_right.iter().cloned());
        self.iterative_output
            .extend(other.iterative_output.iter().cloned());
        self.iterative_rhs
            .extend(other.iterative_rhs.iter().copied());

        let right_idx = self.iterative_rhs.len().checked_sub(1).unwrap();

        let left = self.iterative_output[left_idx].clone();
        let right = self.iterative_output[right_idx].clone();
        let out_lits: Vec<LngLit> = (0..left.len() + right.len()).map(|_| new_lit(s)).collect();
        self.current_rhs = Some(rhs);
        self.adder(s, &left, &right, &out_lits);
        self.out_lits = out_lits;
    }

    pub(super) fn lits(&self) -> &[LngLit] {
        &self.lits
    }

    pub(super) fn outputs(&self) -> &[LngLit] {
        &self.out_lits
    }

    fn to_cnf(&mut self, s: &mut LngCoreSolver, lits: &[LngLit]) {
        let mut left = Vec::new();
        let mut right = Vec::new();
        let split = lits.len() / 2;

        for i in 0..lits.len() {
            if i < split {
                if split == 1 {
                    left.push(self.in_lits.pop().unwrap());
                } else {
                    left.push(new_lit(s));
                }
            } else if lits.len() - split == 1 {
                right.push(self.in_lits.pop().unwrap());
            } else {
                right.push(new_lit(s));
            }
        }

        self.adder(s, &left, &right, lits);
        if left.len() > 1 {
            self.to_cnf(s, &left);
        }
        if right.len() > 1 {
            self.to_cnf(s, &right);
        }
    }

    fn adder(
        &mut self,
        s: &mut LngCoreSolver,
        left: &[LngLit],
        right: &[LngLit],
        output: &[LngLit],
    ) {
        let current_rhs = self.current_rhs.unwrap();
        if self.incremental == IncrementalStrategy::Iterative {
            self.iterative_left.push(left.to_vec());
            self.iterative_right.push(right.to_vec());
            self.iterative_output.push(output.to_vec());
            self.iterative_rhs.push(current_rhs);
        }

        for i in 0..=left.len() {
            for j in 0..=right.len() {
                if i == 0 && j == 0 {
                    continue;
                }
                if i + j > current_rhs + 1 {
                    continue;
                }
                if i == 0 {
                    add_binary_clause_blocking(s, not(right[j - 1]), output[j - 1], self.blocking);
                } else if j == 0 {
                    add_binary_clause_blocking(s, not(left[i - 1]), output[i - 1], self.blocking);
                } else {
                    add_ternary_clause_blocking(
                        s,
                        not(left[i - 1]),
                        not(right[j - 1]),
                        output[i + j - 1],
                        self.blocking,
                    );
                }
            }
        }
    }

    fn incremental(&mut self, s: &mut LngCoreSolver, rhs: usize) {
        let blocking = self.blocking;
        for z in 0..self.iterative_rhs.len() {
            let left = &self.iterative_left[z];
            let right = &self.iterative_right[z];
            let output = &self.iterative_output[z];
            let old_rhs = self.iterative_rhs[z];

            for i in 0..=left.len() {
                for j in 0..=right.len() {
                    if i == 0 && j == 0 {
                        continue;
                    }
                    if i + j > rhs + 1 || i + j <= old_rhs + 1 {
                        continue;
                    }
                    if i == 0 {
                        add_binary_clause_blocking(s, not(right[j - 1]), output[j - 1], blocking);
                    } else if j == 0 {
                        add_binary_clause_blocking(s, not(left[i - 1]), output[i - 1], blocking);
                    } else {
                        add_ternary_clause_blocking(
                            s,
                            not(left[i - 1]),
                            not(right[j - 1]),
                            output[i + j - 1],
                            blocking,
                        );
                    }
                }
            }
            self.iterative_rhs[z] = rhs;
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

    fn assert_at_most(
        solver: &mut LngCoreSolver,
        n: usize,
        rhs: usize,
        extra_assumptions: &[LngLit],
    ) {
        for assignment in assignments(n) {
            let mut assumptions = assumptions_for_assignment(&assignment);
            assumptions.extend_from_slice(extra_assumptions);
            let expected = assignment.iter().filter(|&&value| value).count() <= rhs;
            let result = solver
                .internal_solve_with_assumptions(&mut NopHandler::new(), assumptions)
                .result()
                .unwrap();
            assert_eq!(result, expected, "assignment={assignment:?}, rhs={rhs}");
        }
    }

    #[test]
    fn test_build_rhs_zero_forces_all_inputs_false() {
        let (mut solver, lits) = new_solver_with_lits(3);
        let mut totalizer = Totalizer::new(IncrementalStrategy::None);

        totalizer.build(&mut solver, &lits, 0);

        assert!(!totalizer.has_created_encoding());
        assert!(totalizer.outputs().is_empty());
        assert_at_most(&mut solver, lits.len(), 0, &[]);
    }

    #[test]
    fn test_build_trivial_rhs_without_incrementality_creates_no_encoding() {
        let (mut solver, lits) = new_solver_with_lits(3);
        let mut totalizer = Totalizer::new(IncrementalStrategy::None);

        totalizer.build(&mut solver, &lits, lits.len());

        assert!(!totalizer.has_created_encoding());
        assert!(totalizer.outputs().is_empty());
        assert!(
            solver
                .internal_solve(&mut NopHandler::new())
                .result()
                .unwrap()
        );
    }

    #[test]
    fn test_build_then_update_encodes_at_most_one() {
        let (mut solver, lits) = new_solver_with_lits(4);
        let mut totalizer = Totalizer::new(IncrementalStrategy::None);

        totalizer.build(&mut solver, &lits, 1);
        assert!(totalizer.has_created_encoding());
        assert_eq!(totalizer.outputs().len(), lits.len());
        assert_eq!(totalizer.lits(), lits.as_slice());

        totalizer.update(&mut solver, 1);
        assert_at_most(&mut solver, lits.len(), 1, &[]);
    }

    #[test]
    fn test_build_then_update_encodes_at_most_two() {
        let (mut solver, lits) = new_solver_with_lits(4);
        let mut totalizer = Totalizer::new(IncrementalStrategy::None);

        totalizer.build(&mut solver, &lits, 2);
        totalizer.update(&mut solver, 2);

        assert_at_most(&mut solver, lits.len(), 2, &[]);
    }

    #[test]
    fn test_tightening_non_incremental_update_adds_permanent_bound() {
        let (mut solver, lits) = new_solver_with_lits(4);
        let mut totalizer = Totalizer::new(IncrementalStrategy::None);

        totalizer.build(&mut solver, &lits, 2);
        totalizer.update(&mut solver, 2);
        assert_at_most(&mut solver, lits.len(), 2, &[]);

        totalizer.update(&mut solver, 1);
        assert_at_most(&mut solver, lits.len(), 1, &[]);
    }

    #[test]
    fn test_iterative_update_uses_assumptions_for_bound() {
        let (mut solver, lits) = new_solver_with_lits(4);
        let mut totalizer = Totalizer::new(IncrementalStrategy::Iterative);
        let mut assumptions = Vec::new();

        totalizer.build(&mut solver, &lits, 2);
        totalizer.update_with_assumptions(&mut solver, &lits, 1, &mut assumptions);

        assert!(!assumptions.is_empty());
        assert_at_most(&mut solver, lits.len(), 1, &assumptions);
    }
}
