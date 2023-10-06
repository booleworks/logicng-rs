use crate::formulas::{EncodedFormula, Formula, FormulaFactory};

use super::term::is_minterm;

/// DNF predicate. Indicates whether a formula is in DNF or not.
///
/// [`EncodedFormula`] also directly provides this function as method. So you instead
/// of `is_dnf(formula, &f)`, you can also call `formula.is_dnf(&f)`.
///
/// # Example
///
/// Basic usage:
///
/// ```
/// # use logicng::formulas::{FormulaFactory, ToFormula};
/// # use logicng::operations::predicates::is_dnf;
/// # let f = FormulaFactory::new();
///
/// let formula1 = "a".to_formula(&f);
/// let formula2 = "a | ~b | (b & c)".to_formula(&f);
/// let formula3 = "a & b & c".to_formula(&f);
/// let formula4 = "a | ~b => (b & c)".to_formula(&f);
///
/// assert_eq!(is_dnf(formula1, &f), true);
/// assert_eq!(is_dnf(formula2, &f), true);
/// assert_eq!(is_dnf(formula3, &f), true);
/// assert_eq!(is_dnf(formula4, &f), false);
/// ```
pub fn is_dnf(formula: EncodedFormula, f: &FormulaFactory) -> bool {
    f.caches.is_dnf.get(formula).unwrap_or_else(|| {
        use Formula::{And, Cc, Equiv, False, Impl, Lit, Not, Or, Pbc, True};
        let res = match formula.unpack(f) {
            Lit(_) | True | False => true,
            Pbc(_) | Cc(_) | Equiv(_) | Impl(_) | Not(_) => false,
            And(mut ops) => ops.all(EncodedFormula::is_literal),
            Or(mut ops) => ops.all(|op| is_minterm(op, f)),
        };

        if f.config.caches.is_dnf {
            f.caches.is_dnf.insert(formula, res);
        }
        res
    })
}

#[cfg(test)]
#[allow(non_snake_case)]
mod tests {
    use crate::util::test_util::F;

    #[test]
    fn test() {
        let F = F::new();
        let f = &F.f;
        assert!(f.verum().is_dnf(f));
        assert!(f.falsum().is_dnf(f));
        assert!(F.A.is_dnf(f));
        assert!(F.NA.is_dnf(f));
        assert!(F.OR1.is_dnf(f));
        assert!(F.AND1.is_dnf(f));
        assert!(F.OR3.is_dnf(f));
        assert!(f.or([F.AND1, F.AND2, F.A, F.NY]).is_dnf(f));
        assert!(!F.AND3.is_dnf(f));
        assert!(!F.IMP1.is_dnf(f));
        assert!(!F.EQ1.is_dnf(f));
        assert!(!F.NOT1.is_dnf(f));
        assert!(!F.NOT2.is_dnf(f));
        assert!(!f.and([F.OR1, F.EQ1]).is_dnf(f));
    }
}
