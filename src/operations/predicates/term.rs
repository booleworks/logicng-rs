use crate::formulas::{EncodedFormula, Formula, FormulaFactory};

/// Term predicate. Indicates whether a formula is a clause ( = maxterm = disjunction of literals).
///
/// # Example
///
/// Basic usage:
///
/// ```
/// # use logicng::formulas::{FormulaFactory, ToFormula};
/// # use logicng::operations::predicates::is_clause;
/// # let f = FormulaFactory::new();
///
/// let formula1 = "a".to_formula(&f);
/// let formula2 = "a | ~b".to_formula(&f);
/// let formula3 = "a & b".to_formula(&f);
/// let formula4 = "a | ~b => (b & c)".to_formula(&f);
///
/// assert_eq!(is_clause(formula1, &f), true);
/// assert_eq!(is_clause(formula2, &f), true);
/// assert_eq!(is_clause(formula3, &f), false);
/// assert_eq!(is_clause(formula4, &f), false);
/// ```
pub fn is_clause(formula: EncodedFormula, f: &FormulaFactory) -> bool {
    is_maxterm(formula, f)
}

/// Term predicate. Indicates whether a formula is a maxterm (disjunction of literals).
///
/// # Example
///
/// Basic usage:
///
/// ```
/// # use logicng::formulas::{FormulaFactory, ToFormula};
/// # use logicng::operations::predicates::is_maxterm;
/// # let f = FormulaFactory::new();
///
/// let formula1 = "a".to_formula(&f);
/// let formula2 = "a | ~b".to_formula(&f);
/// let formula3 = "a & b".to_formula(&f);
/// let formula4 = "a | ~b => (b & c)".to_formula(&f);
///
/// assert_eq!(is_maxterm(formula1, &f), true);
/// assert_eq!(is_maxterm(formula2, &f), true);
/// assert_eq!(is_maxterm(formula3, &f), false);
/// assert_eq!(is_maxterm(formula4, &f), false);
/// ```
pub fn is_maxterm(formula: EncodedFormula, f: &FormulaFactory) -> bool {
    match formula.unpack(f) {
        Formula::False | Formula::True | Formula::Lit(_) => true,
        Formula::Or(mut ops) => ops.all(EncodedFormula::is_literal),
        _ => false,
    }
}

/// Term predicate. Indicates whether a formula is a minterm (conjunctions of literals).
///
/// # Example
///
/// Basic usage:
///
/// ```
/// # use logicng::formulas::{FormulaFactory, ToFormula};
/// # use logicng::operations::predicates::is_minterm;
/// # let f = FormulaFactory::new();
///
/// let formula1 = "a".to_formula(&f);
/// let formula2 = "a | ~b".to_formula(&f);
/// let formula3 = "a & b".to_formula(&f);
/// let formula4 = "a | ~b => (b & c)".to_formula(&f);
///
/// assert_eq!(is_minterm(formula1, &f), true);
/// assert_eq!(is_minterm(formula2, &f), false);
/// assert_eq!(is_minterm(formula3, &f), true);
/// assert_eq!(is_minterm(formula4, &f), false);
/// ```
pub fn is_minterm(formula: EncodedFormula, f: &FormulaFactory) -> bool {
    match formula.unpack(f) {
        Formula::False | Formula::True | Formula::Lit(_) => true,
        Formula::And(mut ops) => ops.all(EncodedFormula::is_literal),
        _ => false,
    }
}

#[cfg(test)]
#[allow(non_snake_case)]
mod tests {
    use crate::util::test_util::F;

    use super::*;

    #[test]
    fn test_minterm() {
        let F = F::new();
        let f = &F.f;
        assert!(is_minterm(f.verum(), f));
        assert!(is_minterm(f.falsum(), f));
        assert!(is_minterm(F.A, f));
        assert!(is_minterm(F.NA, f));
        assert!(is_minterm(F.AND1, f));
        assert!(is_minterm(F.AND2, f));
        assert!(is_minterm(f.and(&[F.AND1, F.A, F.C, F.NX]), f));
        assert!(!is_minterm(F.OR1, f));
        assert!(!is_minterm(F.OR2, f));
        assert!(!is_minterm(F.OR3, f));
        assert!(!is_minterm(F.AND3, f));
        assert!(!is_minterm(f.and(&[F.OR1, F.OR2, F.A, F.NY]), f));
        assert!(!is_minterm(F.IMP1, f));
        assert!(!is_minterm(F.EQ1, f));
        assert!(!is_minterm(F.NOT1, f));
        assert!(!is_minterm(F.NOT2, f));
        assert!(!is_minterm(f.or(&[F.OR1, F.EQ1]), f));
    }

    #[test]
    fn test_maxterm() {
        let F = F::new();
        let f = &F.f;
        assert!(is_maxterm(f.verum(), f));
        assert!(is_maxterm(f.falsum(), f));
        assert!(is_maxterm(F.A, f));
        assert!(is_maxterm(F.NA, f));
        assert!(is_maxterm(F.OR1, f));
        assert!(is_maxterm(F.OR2, f));
        assert!(is_maxterm(f.or(&[F.OR1, F.NA, F.C, F.X]), f));
        assert!(!is_maxterm(F.AND1, f));
        assert!(!is_maxterm(F.AND3, f));
        assert!(!is_maxterm(f.and(&[F.OR1, F.OR2, F.A, F.NY]), f));
        assert!(!is_maxterm(F.OR3, f));
        assert!(!is_maxterm(F.IMP1, f));
        assert!(!is_maxterm(F.EQ1, f));
        assert!(!is_maxterm(F.NOT1, f));
        assert!(!is_maxterm(F.NOT2, f));
        assert!(!is_maxterm(f.and(&[F.OR1, F.EQ1]), f));
    }

    #[test]
    fn test_clause() {
        let F = F::new();
        let f = &F.f;
        assert!(is_clause(f.verum(), f));
        assert!(is_clause(f.falsum(), f));
        assert!(is_clause(F.A, f));
        assert!(is_clause(F.NA, f));
        assert!(is_clause(F.OR1, f));
        assert!(is_clause(F.OR2, f));
        assert!(is_clause(f.or(&[F.OR1, F.NA, F.C, F.X]), f));
        assert!(!is_clause(F.AND1, f));
        assert!(!is_clause(F.AND3, f));
        assert!(!is_clause(f.and(&[F.OR1, F.OR2, F.A, F.NY]), f));
        assert!(!is_clause(F.OR3, f));
        assert!(!is_clause(F.IMP1, f));
        assert!(!is_clause(F.EQ1, f));
        assert!(!is_clause(F.NOT1, f));
        assert!(!is_clause(F.NOT2, f));
        assert!(!is_clause(f.and(&[F.OR1, F.EQ1]), f));
    }
}
