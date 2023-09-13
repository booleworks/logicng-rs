use crate::formulas::{EncodedFormula, Formula, FormulaFactory};

/// Returns a vector of all operands of this formula.
///
/// _n-ary_ operators return all their operands, _binary_ operators return
/// their `left` and `right` operands, `Not` returns a vector with only its
/// inner formula, and all other formulas return an empty vector.
///
/// # Examples
///
/// Basic usage:
///
/// ```
/// # use logicng::formulas::FormulaFactory;
/// # use logicng::formulas::ToFormula;
/// # use logicng::operations::functions::operands;
/// let f = FormulaFactory::new();
///
/// let a = f.variable("a");
/// let b = f.variable("b");
/// let c = f.variable("c");
///
/// let formula1 = "a & b & c".to_formula(&f);
/// let formula2 = "a => b".to_formula(&f);
/// let formula3 = f.not(formula2);
///
/// assert_eq!(operands(a, &f), vec![]);
/// assert_eq!(operands(formula1, &f), vec![a, b, c]);
/// assert_eq!(operands(formula2, &f), vec![a, b]);
/// assert_eq!(operands(formula3, &f), vec![formula2]);
/// ```
pub fn operands(formula: EncodedFormula, f: &FormulaFactory) -> Vec<EncodedFormula> {
    use Formula::{And, Cc, Equiv, False, Impl, Lit, Not, Or, Pbc, True};
    match formula.unpack(f) {
        Pbc(_) | Cc(_) | Lit(_) | True | False => vec![],
        Equiv((left, right)) | Impl((left, right)) => vec![left, right],
        Or(ops) | And(ops) => ops.collect(),
        Not(op) => vec![op],
    }
}
