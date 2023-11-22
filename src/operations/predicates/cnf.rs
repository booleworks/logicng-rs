use crate::formulas::{EncodedFormula, FormulaFactory, FormulaType};

/// CNF predicate. Indicates whether a formula is in CNF or not.
///
/// [`EncodedFormula`] also directly provides this function as method. So you instead
/// of `is_cnf(formula, &f)`, you can also call `formula.is_cnf(&f)`.
///
/// # Example
///
/// Basic usage:
///
/// ```
/// # use logicng::formulas::{FormulaFactory, ToFormula};
/// # use logicng::operations::predicates::is_cnf;
/// # let f = FormulaFactory::new();
///
/// let formula1 = "a".to_formula(&f);
/// let formula2 = "a & ~b & (b | c)".to_formula(&f);
/// let formula3 = "a | b | c".to_formula(&f);
/// let formula4 = "a & ~b => (b | c)".to_formula(&f);
///
/// assert_eq!(is_cnf(formula1, &f), true);
/// assert_eq!(is_cnf(formula2, &f), true);
/// assert_eq!(is_cnf(formula3, &f), true);
/// assert_eq!(is_cnf(formula4, &f), false);
/// ```
pub fn is_cnf(formula: EncodedFormula, f: &FormulaFactory) -> bool {
    use FormulaType as FT;
    match formula.formula_type() {
        FT::Lit(_) | FT::True | FT::False => true,
        FT::Pbc | FT::Cc | FT::Equiv | FT::Impl | FT::Not => false,
        FT::And | FT::Or => f.caches.is_cnf.get(formula).is_some(),
    }
}

#[cfg(test)]
#[allow(non_snake_case)]
mod tests {
    use crate::util::test_util::F;

    #[test]
    fn test() {
        let F = F::new();
        let f = &F.f;
        assert!(f.verum().is_cnf(f));
        assert!(f.falsum().is_cnf(f));
        assert!(F.A.is_cnf(f));
        assert!(F.NA.is_cnf(f));
        assert!(F.OR1.is_cnf(f));
        assert!(F.AND1.is_cnf(f));
        assert!(F.AND3.is_cnf(f));
        assert!(f.and([F.OR1, F.OR2, F.A, F.NY]).is_cnf(f));
        assert!(!F.OR3.is_cnf(f));
        assert!(!F.IMP1.is_cnf(f));
        assert!(!F.EQ1.is_cnf(f));
        assert!(!F.NOT1.is_cnf(f));
        assert!(!F.NOT2.is_cnf(f));
        assert!(!f.and([F.OR1, F.EQ1]).is_cnf(f));
    }
}
