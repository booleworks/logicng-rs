use crate::datastructures::Assignment;
use crate::formulas::{EncodedFormula, Formula, FormulaFactory, Literal};

/// Restricts this formula with the give assignment.
///
/// [`FormulaFactory`] also provides this transformation as a method. So you
/// can also use `f.restrict(formula, assignment)` instead of `restrict(formula,
/// assignment, f)`.
///
/// # Examples
///
/// Basic usage:
///
/// ```
/// # use logicng::formulas::{FormulaFactory, ToFormula};
/// # use logicng::datastructures::Assignment;
/// # use logicng::operations::transformations::restrict;
///
/// let f = FormulaFactory::new();
///
/// let a = f.var("a");
/// let b = f.var("b");
/// let formula = "a & b".to_formula(&f);
///
/// let assignment1 = Assignment::from_variables(&[a], &[]);
/// let assignment2 = Assignment::from_variables(&[], &[a]);
///
/// let restricted1 = restrict(formula, &assignment1, &f);
/// let restricted2 = restrict(formula, &assignment2, &f);
///
/// assert_eq!(restricted1.to_string(&f), "b");
/// assert_eq!(restricted2.to_string(&f), "$false");
/// ```
pub fn restrict(formula: EncodedFormula, assignment: &Assignment, f: &FormulaFactory) -> EncodedFormula {
    use Formula::{And, Cc, Equiv, False, Impl, Lit, Not, Or, Pbc, True};
    match formula.unpack(f) {
        Lit(lit) => assignment.restrict_lit(lit),
        Equiv((left, right)) => {
            let rec_left = restrict(left, assignment, f);
            let rec_right = restrict(right, assignment, f);
            f.equivalence(rec_left, rec_right)
        }
        Impl((left, right)) => {
            let rec_left = restrict(left, assignment, f);
            let rec_right = restrict(right, assignment, f);
            f.implication(rec_left, rec_right)
        }
        Or(ops) => {
            let rec_ops = ops.map(|op| restrict(op, assignment, f));
            f.or(rec_ops)
        }
        And(ops) => {
            let rec_ops = ops.map(|op| restrict(op, assignment, f));
            f.and(rec_ops)
        }
        Not(op) => {
            let rec_op = restrict(op, assignment, f);
            f.not(rec_op)
        }
        True | False => formula,
        Pbc(pbc) => pbc.clone().restrict(assignment, f),
        Cc(cc) => cc.clone().restrict(assignment, f),
    }
}

pub fn restrict_lit(formula: EncodedFormula, lit: Literal, f: &FormulaFactory) -> EncodedFormula {
    use Formula::{And, Cc, Equiv, False, Impl, Lit, Not, Or, Pbc, True};
    match formula.unpack(f) {
        Lit(this_lit) => {
            if this_lit.variable() != lit.variable() {
                formula
            } else if this_lit.phase() == lit.phase() {
                f.verum()
            } else {
                f.falsum()
            }
        }
        Equiv((left, right)) => {
            let rec_left = restrict_lit(left, lit, f);
            let rec_right = restrict_lit(right, lit, f);
            f.equivalence(rec_left, rec_right)
        }
        Impl((left, right)) => {
            let rec_left = restrict_lit(left, lit, f);
            let rec_right = restrict_lit(right, lit, f);
            f.implication(rec_left, rec_right)
        }
        Or(ops) => {
            let rec_ops = ops.map(|op| restrict_lit(op, lit, f));
            f.or(rec_ops)
        }
        And(ops) => {
            let rec_ops = ops.map(|op| restrict_lit(op, lit, f));
            f.and(rec_ops)
        }
        Not(op) => {
            let rec_op = restrict_lit(op, lit, f);
            f.not(rec_op)
        }
        True | False => formula,
        Pbc(pbc) => pbc.clone().restrict(&Assignment::from_lit(lit), f),
        Cc(cc) => cc.clone().restrict(&Assignment::from_lit(lit), f),
    }
}
