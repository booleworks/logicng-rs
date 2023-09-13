use crate::formulas::{EncodedFormula, FormulaFactory};

/// A function that returns the depth of a formula's abstract syntax tree. The
/// depth of a formula indicates how many levels of nested sub-formulas a
/// formula has. For example,
///
/// - `A` has depth zero,
/// - `A & B` has depth one,
/// - `(A & B) | C` has depth two,
/// - `(A & B) | C & (E | F)` has depth three.
///
/// Intuitively speaking, the formula depth is the maximal depth of a formula's
/// abstract syntax tree.
///
/// # Example
///
/// Basic usage:
///
/// ```
/// # use logicng::formulas::{FormulaFactory, ToFormula};
/// # use logicng::operations::functions::formula_depth;
/// # let f = FormulaFactory::new();
///
/// let formula1 = "a".to_formula(&f);
/// let formula2 = "a & b".to_formula(&f);
/// let formula3 = "(a & b) | c".to_formula(&f);
/// let formula4 = "(a & b) | c & (e | f)".to_formula(&f);
///
/// assert_eq!(formula_depth(formula1, &f), 0);
/// assert_eq!(formula_depth(formula2, &f), 1);
/// assert_eq!(formula_depth(formula3, &f), 2);
/// assert_eq!(formula_depth(formula4, &f), 3);
/// ```
pub fn formula_depth(formula: EncodedFormula, f: &FormulaFactory) -> u64 {
    f.caches.formula_depth.get(formula).unwrap_or_else(|| {
        let result = if formula.is_atomic() {
            0
        } else {
            1 + formula
                .operands(f)
                .iter()
                .map(|&op| formula_depth(op, f))
                .max()
                .expect("Operands must not be empty for non-atomic formulas.")
        };

        if f.config.caches.formula_depth {
            f.caches.formula_depth.insert(formula, result);
        }
        result
    })
}

#[cfg(test)]
mod test {
    use crate::formulas::{FormulaFactory, ToFormula};
    use crate::operations::functions::formula_depth;
    use crate::util::test_util::F;

    #[test]
    fn test_atoms() {
        let ff = F::new();
        assert_eq!(0, formula_depth(ff.TRUE, &ff.f));
        assert_eq!(0, formula_depth(ff.FALSE, &ff.f));
        assert_eq!(0, formula_depth(ff.A, &ff.f));
        assert_eq!(0, formula_depth(ff.NA, &ff.f));
        assert_eq!(0, formula_depth(ff.PBC1, &ff.f));
        assert_eq!(0, formula_depth(ff.PBC2, &ff.f));
        assert_eq!(0, formula_depth(ff.PBC3, &ff.f));
        assert_eq!(0, formula_depth(ff.PBC4, &ff.f));
        assert_eq!(0, formula_depth(ff.PBC5, &ff.f));
    }

    #[test]
    fn test_deep_formulas() {
        let ff = F::new();
        assert_eq!(1, formula_depth(ff.AND1, &ff.f));
        assert_eq!(1, formula_depth(ff.AND2, &ff.f));
        assert_eq!(2, formula_depth(ff.AND3, &ff.f));
        assert_eq!(1, formula_depth(ff.OR1, &ff.f));
        assert_eq!(1, formula_depth(ff.OR2, &ff.f));
        assert_eq!(2, formula_depth(ff.OR3, &ff.f));
        assert_eq!(2, formula_depth(ff.NOT1, &ff.f));
        assert_eq!(2, formula_depth(ff.NOT2, &ff.f));
        assert_eq!(1, formula_depth(ff.IMP1, &ff.f));
        assert_eq!(1, formula_depth(ff.IMP2, &ff.f));
        assert_eq!(2, formula_depth(ff.IMP3, &ff.f));
        assert_eq!(2, formula_depth(ff.IMP4, &ff.f));
        assert_eq!(1, formula_depth(ff.EQ1, &ff.f));
        assert_eq!(1, formula_depth(ff.EQ2, &ff.f));
        assert_eq!(2, formula_depth(ff.EQ3, &ff.f));
        assert_eq!(2, formula_depth(ff.EQ4, &ff.f));
    }

    #[test]
    fn test_deeper_formulas() {
        let ff = F::new();
        let mut formula = ff.PBC1;
        for i in 0..10 {
            let var = ff.f.variable(&format!("X{i}"));
            formula = if i % 2 == 0 { ff.f.or(&[formula, var]) } else { ff.f.and(&[formula, var]) }
        }
        assert_eq!(10, formula_depth(formula, &ff.f));
    }

    #[test]
    fn test_cache() {
        let f = &FormulaFactory::new();
        let formula = "A & B | C".to_formula(f);
        let a = "A".to_formula(f);
        assert!(f.caches.formula_depth.get(formula).is_none());
        assert_eq!(2, formula_depth(formula, f));
        assert_eq!(Some(2), f.caches.formula_depth.get(formula));
        assert_eq!(Some(0), f.caches.formula_depth.get(a));
    }
}
