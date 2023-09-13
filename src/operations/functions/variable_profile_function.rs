use std::collections::HashMap;

use crate::formulas::{EncodedFormula, Formula, FormulaFactory, Variable};

/// A function that computes the variable profile for a given formula, i.e. it
/// counts the number of occurrences for each variable and returns it as a
/// mapping from variable to number of occurrences.
///
/// # Example
///
/// Basic usage:
///
/// ```
/// # use logicng::formulas::{FormulaFactory, ToFormula};
/// # use logicng::operations::functions::variable_profile;
/// # let f = FormulaFactory::new();
///
/// let formula = "a & ~b => a | b | c & (a => (b | c))".to_formula(&f);
///
/// let profile = variable_profile(formula, &f);
///
/// assert_eq!(profile[&f.var("a")], 3);
/// assert_eq!(profile[&f.var("b")], 3);
/// assert_eq!(profile[&f.var("c")], 2);
/// ```
pub fn variable_profile(formula: EncodedFormula, f: &FormulaFactory) -> HashMap<Variable, usize> {
    let mut result = HashMap::new();
    variable_profile_rec(formula, f, &mut result);
    result
}

fn variable_profile_rec(formula: EncodedFormula, f: &FormulaFactory, result: &mut HashMap<Variable, usize>) {
    match formula.unpack(f) {
        Formula::Lit(lit) => {
            result.entry(lit.variable()).and_modify(|counter| *counter += 1).or_insert(1);
        }
        Formula::Cc(cc) => {
            cc.variables.iter().for_each(|var| variable_profile_rec(EncodedFormula::from(*var), f, result));
        }
        Formula::Pbc(pbc) => {
            pbc.literals.iter().for_each(|lit| variable_profile_rec(EncodedFormula::from(*lit), f, result));
        }
        _ => formula.operands(f).iter().for_each(|op| variable_profile_rec(*op, f, result)),
    }
}

#[cfg(test)]
mod tests {
    use crate::formulas::FormulaFactory;

    use super::variable_profile;

    #[test]
    #[allow(clippy::cognitive_complexity)]
    fn test_variable_profile_simple() {
        let f = FormulaFactory::new();
        let va = f.var("a");
        let vb = f.var("b");
        let vc = f.var("c");

        assert!(variable_profile(f.verum(), &f).is_empty());
        assert!(variable_profile(f.falsum(), &f).is_empty());

        let prof_var = variable_profile(f.variable("a"), &f);
        assert_eq!(prof_var.len(), 1);
        assert_eq!(prof_var[&va], 1);

        let prof_lit = variable_profile(f.literal("a", false), &f);
        assert_eq!(prof_lit.len(), 1);
        assert_eq!(prof_lit[&va], 1);

        let prof_impl = variable_profile(f.parse("a => b").unwrap(), &f);
        assert_eq!(prof_impl.len(), 2);
        assert_eq!(prof_impl[&va], 1);
        assert_eq!(prof_impl[&vb], 1);

        let prof_equiv = variable_profile(f.parse("a <=> ~c").unwrap(), &f);
        assert_eq!(prof_equiv.len(), 2);
        assert_eq!(prof_equiv[&va], 1);
        assert_eq!(prof_equiv[&vc], 1);

        let prof_or = variable_profile(f.parse("a | b | ~c").unwrap(), &f);
        assert_eq!(prof_or.len(), 3);
        assert_eq!(prof_or[&va], 1);
        assert_eq!(prof_or[&vb], 1);
        assert_eq!(prof_or[&vc], 1);

        let prof_and = variable_profile(f.parse("a & b & ~c").unwrap(), &f);
        assert_eq!(prof_and.len(), 3);
        assert_eq!(prof_and[&va], 1);
        assert_eq!(prof_and[&vb], 1);
        assert_eq!(prof_and[&vc], 1);

        let prof_cc = variable_profile(f.parse("a + b + c < 1").unwrap(), &f);
        assert_eq!(prof_cc.len(), 3);
        assert_eq!(prof_cc[&va], 1);
        assert_eq!(prof_cc[&vb], 1);
        assert_eq!(prof_cc[&vc], 1);

        let prof_pbc = variable_profile(f.parse("3*a + b + -4*c < 3").unwrap(), &f);
        assert_eq!(prof_pbc.len(), 3);
        assert_eq!(prof_pbc[&va], 1);
        assert_eq!(prof_pbc[&vb], 1);
        assert_eq!(prof_pbc[&vc], 1);
    }

    #[test]
    fn test_variable_profile_complex() {
        let f = FormulaFactory::new();
        let formula1 = f.parse("(a & (b | c) & (~b | ~c)) => c").unwrap();
        let formula2 = f.parse("(a => ~b) & ((a & c) | (d & ~c)) & (a | y | x) & (y <=> (x | (w + a + f < 1)))").unwrap();
        let prof1 = variable_profile(formula1, &f);
        let prof2 = variable_profile(formula2, &f);

        assert_eq!(prof1.len(), 3);
        assert_eq!(prof1[&f.var("a")], 1);
        assert_eq!(prof1[&f.var("b")], 2);
        assert_eq!(prof1[&f.var("c")], 3);

        assert_eq!(prof2.len(), 8);
        assert_eq!(prof2[&f.var("a")], 4);
        assert_eq!(prof2[&f.var("b")], 1);
        assert_eq!(prof2[&f.var("c")], 2);
        assert_eq!(prof2[&f.var("d")], 1);
        assert_eq!(prof2[&f.var("y")], 2);
        assert_eq!(prof2[&f.var("x")], 2);
        assert_eq!(prof2[&f.var("w")], 1);
        assert_eq!(prof2[&f.var("f")], 1);
    }
}
