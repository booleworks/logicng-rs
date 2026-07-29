use crate::solver::lng_core_solver::{LngCoreSolver, LngLit, not};

use super::clauses::{add_binary_clause, add_ternary_clause, add_unit_clause, new_lit};

/// Ladder encoding for AMO constraints.
pub(super) fn encode_ladder(s: &mut LngCoreSolver, lits: &[LngLit]) {
    if lits.len() == 1 {
        add_unit_clause(s, lits[0]);
    } else {
        let mut seq_auxiliary = Vec::new();
        for _ in 0..lits.len() - 1 {
            seq_auxiliary.push(new_lit(s));
        }
        for i in 0..lits.len() {
            if i == 0 {
                add_binary_clause(s, lits[i], not(seq_auxiliary[i]));
                add_binary_clause(s, not(lits[i]), seq_auxiliary[i]);
            } else if i == lits.len() - 1 {
                add_binary_clause(s, lits[i], seq_auxiliary[i - 1]);
                add_binary_clause(s, not(lits[i]), not(seq_auxiliary[i - 1]));
            } else {
                add_binary_clause(s, not(seq_auxiliary[i - 1]), seq_auxiliary[i]);
                add_ternary_clause(s, lits[i], not(seq_auxiliary[i]), seq_auxiliary[i - 1]);
                add_binary_clause(s, not(lits[i]), seq_auxiliary[i]);
                add_binary_clause(s, not(lits[i]), not(seq_auxiliary[i - 1]));
            }
        }
    }
}
