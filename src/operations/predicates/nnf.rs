use crate::formulas::{EncodedFormula, Formula, FormulaFactory};

/// NNF predicate. Indicates whether a formula is in NNF or not.
///
/// [`EncodedFormula`] also directly provides this function as method. So you instead
/// of `is_nnf(formula, &f)`, you can also call `formula.is_nnf(&f)`.
///
/// # Example
///
/// Basic usage:
///
/// ```
/// # use logicng::formulas::{FormulaFactory, ToFormula};
/// # use logicng::operations::predicates::is_nnf;
/// # let f = FormulaFactory::new();
///
/// let formula1 = "a & ~b".to_formula(&f);
/// let formula2 = "(a & (~b | c) & ~c) | d".to_formula(&f);
/// let formula3 = "a => b".to_formula(&f);
/// let formula4 = "~(a | b)".to_formula(&f);
///
/// assert_eq!(is_nnf(formula1, &f), true);
/// assert_eq!(is_nnf(formula2, &f), true);
/// assert_eq!(is_nnf(formula3, &f), false);
/// assert_eq!(is_nnf(formula4, &f), false);
/// ```
pub fn is_nnf(formula: EncodedFormula, f: &FormulaFactory) -> bool {
    f.caches.is_nnf.get(formula).unwrap_or_else(|| {
        use Formula::{And, Cc, Equiv, False, Impl, Lit, Not, Or, Pbc, True};
        let result = match formula.unpack(f) {
            Lit(_) | True | False => true,
            Pbc(_) | Cc(_) | Equiv(_) | Impl(_) | Not(_) => false,
            Or(mut ops) | And(mut ops) => ops.all(|op| is_nnf(op, f)),
        };

        if f.config.caches.is_nnf {
            f.caches.is_nnf.insert(formula, result);
        }
        result
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
        assert!(f.verum().is_nnf(f));
        assert!(f.falsum().is_nnf(f));
        assert!(F.A.is_nnf(f));
        assert!(F.NA.is_nnf(f));
        assert!(F.OR1.is_nnf(f));
        assert!(F.AND1.is_nnf(f));
        assert!(F.AND3.is_nnf(f));
        assert!(f.and(&[F.OR1, F.OR2, F.A, F.NY]).is_nnf(f));
        assert!(f.and(&[F.OR1, F.OR2, F.AND1, F.AND2, F.AND3, F.A, F.NY]).is_nnf(f));
        assert!(F.OR3.is_nnf(f));
        assert!(!F.IMP1.is_nnf(f));
        assert!(!F.EQ1.is_nnf(f));
        assert!(!F.NOT1.is_nnf(f));
        assert!(!F.NOT2.is_nnf(f));
        let not = f.not(F.OR2);
        assert!(!f.and(&[F.OR1, not, F.A, F.NY]).is_nnf(f));
        assert!(!f.and(&[F.OR1, F.EQ1]).is_nnf(f));
        assert!(!f.and(&[F.OR1, F.IMP1, F.AND1]).is_nnf(f));
    }
}
