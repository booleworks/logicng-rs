use crate::solver::lng_core_solver::{LngCoreSolver, LngLit, LngVar, mk_lit};

pub(super) fn new_lit(s: &mut LngCoreSolver) -> LngLit {
    let lit = mk_lit(LngVar(s.vars.len()), false);
    s.new_var(true, true);
    lit
}

pub(super) fn add_unit_clause(s: &mut LngCoreSolver, a: LngLit) {
    add_unit_clause_blocking(s, a, None);
}

pub(super) fn add_unit_clause_blocking(s: &mut LngCoreSolver, a: LngLit, blocking: Option<LngLit>) {
    if let Some(blocking) = blocking {
        s.add_clause(vec![a, blocking], None);
    } else {
        s.add_clause(vec![a], None);
    }
}

pub(super) fn add_binary_clause(s: &mut LngCoreSolver, a: LngLit, b: LngLit) {
    add_binary_clause_blocking(s, a, b, None);
}

pub(super) fn add_binary_clause_blocking(
    s: &mut LngCoreSolver,
    a: LngLit,
    b: LngLit,
    blocking: Option<LngLit>,
) {
    if let Some(blocking) = blocking {
        s.add_clause(vec![a, b, blocking], None);
    } else {
        s.add_clause(vec![a, b], None);
    }
}

pub(super) fn add_ternary_clause(s: &mut LngCoreSolver, a: LngLit, b: LngLit, c: LngLit) {
    add_ternary_clause_blocking(s, a, b, c, None);
}

pub(super) fn add_ternary_clause_blocking(
    s: &mut LngCoreSolver,
    a: LngLit,
    b: LngLit,
    c: LngLit,
    blocking: Option<LngLit>,
) {
    if let Some(blocking) = blocking {
        s.add_clause(vec![a, b, c, blocking], None);
    } else {
        s.add_clause(vec![a, b, c], None);
    }
}

pub(super) fn add_quaternary_clause(
    s: &mut LngCoreSolver,
    a: LngLit,
    b: LngLit,
    c: LngLit,
    d: LngLit,
) {
    add_quaternary_clause_blocking(s, a, b, c, d, None);
}

pub(super) fn add_quaternary_clause_blocking(
    s: &mut LngCoreSolver,
    a: LngLit,
    b: LngLit,
    c: LngLit,
    d: LngLit,
    blocking: Option<LngLit>,
) {
    if let Some(blocking) = blocking {
        s.add_clause(vec![a, b, c, d, blocking], None);
    } else {
        s.add_clause(vec![a, b, c, d], None);
    }
}
