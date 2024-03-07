use crate::formulas::Literal::{Neg, Pos};
use crate::formulas::{
    evaluate_comparator, CardinalityConstraint, EncodedFormula, Formula, FormulaFactory, FormulaType, LitType, PbConstraint, Variable,
};
use std::collections::HashMap;

/// A `Substitution` maps variables to formulas.
pub type Substitution = HashMap<Variable, EncodedFormula>;

/// Substitutes variables of the given formulas with specified formulas.
///
/// # Examples
///
/// Basic usage:
///
/// ```
/// # use logicng::formulas::{FormulaFactory, ToFormula};
/// # use logicng::operations::transformations::substitute;
/// # use std::collections::HashMap;
///
/// let f = FormulaFactory::new();
///
/// let formula = "a & b".to_formula(&f);
///
/// let mut substitutions = HashMap::new();
/// substitutions.insert(f.var("a"), "c => d".to_formula(&f));
///
/// let substituted = substitute(formula, &substitutions, &f);
///
/// assert_eq!(substituted.to_string(&f), "(c => d) & b");
/// ```
pub fn substitute(formula: EncodedFormula, substitution: &Substitution, f: &FormulaFactory) -> EncodedFormula {
    use Formula::{And, Cc, Equiv, False, Impl, Lit, Not, Or, Pbc, True};
    match formula.unpack(f) {
        True | False => formula,
        Lit(Pos(var)) => *substitution.get(&var).unwrap_or(&formula),
        Lit(Neg(var)) => substitution.get(&var).map_or(formula, |subst| f.negate(*subst)),
        Not(op) => {
            let formula = substitute(op, substitution, f);
            f.negate(formula)
        }
        And(ops) => {
            let new_ops = ops.map(|op| substitute(op, substitution, f));
            f.and(new_ops)
        }
        Or(ops) => {
            let new_ops = ops.map(|op| substitute(op, substitution, f));
            f.or(new_ops)
        }
        Impl((left, right)) => {
            let new_left = substitute(left, substitution, f);
            let new_right = substitute(right, substitution, f);
            f.implication(new_left, new_right)
        }
        Equiv((left, right)) => {
            let new_left = substitute(left, substitution, f);
            let new_right = substitute(right, substitution, f);
            f.equivalence(new_left, new_right)
        }
        Cc(cc_ref) => handle_cc(cc_ref, substitution, f),
        Pbc(pbc_ref) => handle_pbc(pbc_ref, substitution, f),
    }
}

fn handle_cc(cc: &CardinalityConstraint, substitution: &Substitution, f: &FormulaFactory) -> EncodedFormula {
    let mut new_lits = vec![];
    let mut lhs_fixed = 0;
    for &var in &*cc.variables {
        let subst = substitute(var.into(), substitution, f);
        if subst == var.into() {
            new_lits.push(var.pos_lit());
        } else {
            match subst.formula_type() {
                FormulaType::True => {
                    lhs_fixed += 1;
                }
                FormulaType::False => {}
                FormulaType::Lit(LitType::Pos(_)) => {
                    new_lits.push(subst.as_literal().unwrap());
                }
                _ => panic!("Cannot substitute a formula for a variable in a cardinality constraint"),
            }
        }
    }
    #[allow(clippy::cast_possible_wrap)]
    if new_lits.is_empty() {
        f.constant(evaluate_comparator(lhs_fixed, cc.comparator, cc.rhs.into()))
    } else {
        let coeffs = vec![1; new_lits.len()];
        f.pbc(cc.comparator, i64::from(cc.rhs) - lhs_fixed, new_lits, coeffs)
    }
}

fn handle_pbc(pbc: &PbConstraint, substitution: &Substitution, f: &FormulaFactory) -> EncodedFormula {
    let mut new_lits = vec![];
    let mut new_coeffs = vec![];
    let mut lhs_fixed = 0;
    for i in 0..pbc.literals.len() {
        let lit = pbc.literals[i];
        let subst = substitute(lit.into(), substitution, f);
        if subst == EncodedFormula::from(lit) {
            new_lits.push(lit);
            new_coeffs.push(pbc.coefficients[i]);
        } else {
            match subst.formula_type() {
                FormulaType::True => {
                    lhs_fixed += pbc.coefficients[i];
                }
                FormulaType::False => {}
                FormulaType::Lit(_) => {
                    new_lits.push(subst.as_literal().unwrap());
                    new_coeffs.push(pbc.coefficients[i]);
                }
                _ => panic!("Cannot substitute a formula for a literal in a pseudo-Boolean constraint"),
            }
        }
    }
    if new_lits.is_empty() {
        f.constant(evaluate_comparator(lhs_fixed, pbc.comparator, pbc.rhs))
    } else {
        f.pbc(pbc.comparator, pbc.rhs - lhs_fixed, new_lits, new_coeffs)
    }
}

#[cfg(test)]
mod tests {
    use crate::formulas::CType::{EQ, LE};
    use crate::formulas::{EncodedFormula, FormulaFactory, Literal, ToFormula, Variable};
    use crate::operations::transformations::substitution::Substitution;
    use crate::util::test_util::F;
    use std::collections::HashMap;

    #[test]
    fn test_constant() {
        let ff = F::new();
        let subst = create_substitution(&ff);
        let f = &ff.f;
        assert_eq!(f.verum(), f.substitute(EncodedFormula::constant(true), &subst));
        assert_eq!(f.falsum(), f.substitute(EncodedFormula::constant(false), &subst));
    }

    #[test]
    fn test_literal() {
        let ff = F::new();
        let subst = create_substitution(&ff);
        let f = &ff.f;
        assert_eq!(ff.C, f.substitute(ff.C, &subst));
        assert_eq!(ff.NA, f.substitute(ff.A, &subst));
        assert_eq!(ff.OR1, f.substitute(ff.B, &subst));
        assert_eq!(ff.AND1, f.substitute(ff.X, &subst));
        assert_eq!(ff.A, f.substitute(ff.NA, &subst));
        assert_eq!(ff.NOT2, f.substitute(ff.NB, &subst));
        assert_eq!(ff.NOT1, f.substitute(ff.NX, &subst));
    }

    #[test]
    fn test_not() {
        let ff = F::new();
        let subst = create_substitution(&ff);
        let f = &ff.f;
        assert_eq!("~(~a & (x | y))".to_formula(f), f.substitute(ff.NOT1, &subst));
        assert_eq!("~(a & b | y)".to_formula(f), f.substitute(ff.NOT2, &subst));
    }

    #[test]
    fn test_binary() {
        let ff = F::new();
        let subst = create_substitution(&ff);
        let f = &ff.f;
        assert_eq!("~a => (x | y)".to_formula(f), f.substitute(ff.IMP1, &subst));
        assert_eq!("(~a <=> (x | y)) => (~(a & b) <=> ~y)".to_formula(f), f.substitute(ff.IMP4, &subst));
        assert_eq!("a <=> ~(x | y)".to_formula(f), f.substitute(ff.EQ2, &subst));
        assert_eq!("(~a & (x | y)) <=> (a & b | y)".to_formula(f), f.substitute(ff.EQ3, &subst));
    }

    #[test]
    fn test_nary() {
        let ff = F::new();
        let subst = create_substitution(&ff);
        let f = &ff.f;
        assert_eq!("(a & b | y) & (~(a & b) | ~y)".to_formula(f), f.substitute(ff.AND3, &subst));
        let formula1 = f.and([ff.NB, ff.C, ff.X, ff.NY]);
        assert_eq!("~(x | y) & c & a & b & ~y".to_formula(f), f.substitute(formula1, &subst));
        assert_eq!("(~a & (x | y)) | (a & ~(x | y))".to_formula(f), f.substitute(ff.OR3, &subst));
        let formula2 = f.or([ff.A, ff.NB, ff.C, ff.X, ff.NY]);
        assert_eq!("~a | ~(x | y) | c | a & b | ~y".to_formula(f), f.substitute(formula2, &subst));
    }

    #[test]
    fn test_cc() {
        let f = &FormulaFactory::new();
        let vars: Box<[Variable]> = Box::new([f.var("a"), f.var("b"), f.var("c")]);
        let vars_s1: Box<[Variable]> = Box::new([f.var("b"), f.var("c")]);
        let vars_s2: Box<[Variable]> = Box::new([f.var("c")]);
        let vars_s5: Box<[Variable]> = Box::new([f.var("a2"), f.var("b2"), f.var("c2")]);
        let vars_s6: Box<[Variable]> = Box::new([f.var("a2"), f.var("c")]);
        let s1 = HashMap::from([(f.var("a"), f.verum())]);
        let s2 = HashMap::from([(f.var("a"), f.verum()), (f.var("b"), f.falsum())]);
        let s3 = HashMap::from([(f.var("a"), f.verum()), (f.var("b"), f.falsum()), (f.var("c"), f.verum())]);
        let s4 = HashMap::from([(f.var("a"), f.falsum()), (f.var("b"), f.verum()), (f.var("c"), f.falsum())]);
        let s5 = HashMap::from([
            (f.var("a"), f.variable("a2")),
            (f.var("b"), f.variable("b2")),
            (f.var("c"), f.variable("c2")),
            (f.var("d"), f.variable("d2")),
        ]);
        let s6 = HashMap::from([(f.var("a"), f.variable("a2")), (f.var("b"), f.falsum())]);
        let cc1 = f.cc(EQ, 2, vars.clone());
        let cc2 = f.cc(LE, 8, vars);
        assert_eq!(f.cc(EQ, 1, vars_s1), f.substitute(cc1, &s1));
        assert_eq!(f.cc(EQ, 1, vars_s2), f.substitute(cc1, &s2));
        assert_eq!(f.verum(), f.substitute(cc1, &s3));
        assert_eq!(f.falsum(), f.substitute(cc1, &s4));
        assert_eq!(f.verum(), f.substitute(cc2, &s3));
        assert_eq!(f.verum(), f.substitute(cc2, &s4));
        assert_eq!(f.cc(EQ, 2, vars_s5), f.substitute(cc1, &s5));
        assert_eq!(f.cc(EQ, 2, vars_s6), f.substitute(cc1, &s6));
    }

    #[test]
    fn test_pbc() {
        let f = &FormulaFactory::new();
        let lits: Box<[Literal]> = Box::new([f.lit("a", true), f.lit("b", false), f.lit("c", true)]);
        let lits_s1: Box<[Literal]> = Box::new([f.lit("b", false), f.lit("c", true)]);
        let lits_s2: Box<[Literal]> = Box::new([f.lit("c", true)]);
        let lits_s5: Box<[Literal]> = Box::new([f.lit("a2", true), f.lit("b2", false), f.lit("c2", true)]);
        let lits_s6: Box<[Literal]> = Box::new([f.lit("a2", true), f.lit("c", true)]);
        let coeffs: Box<[i64]> = Box::new([2, -2, 3]);
        let coeffs2: Box<[i64]> = Box::new([3, -2, 7]);
        let coeff_s1: Box<[i64]> = Box::new([-2, 3]);
        let coeff_s2: Box<[i64]> = Box::new([3]);
        let coeff_s6: Box<[i64]> = Box::new([2, 3]);
        let s1 = HashMap::from([(f.var("a"), f.verum())]);
        let s2 = HashMap::from([(f.var("a"), f.verum()), (f.var("b"), f.falsum())]);
        let s3 = HashMap::from([(f.var("a"), f.verum()), (f.var("b"), f.falsum()), (f.var("c"), f.verum())]);
        let s4 = HashMap::from([(f.var("a"), f.falsum()), (f.var("b"), f.verum()), (f.var("c"), f.falsum())]);
        let s5 = HashMap::from([
            (f.var("a"), f.variable("a2")),
            (f.var("b"), f.variable("b2")),
            (f.var("c"), f.variable("c2")),
            (f.var("d"), f.variable("d2")),
        ]);
        let s6 = HashMap::from([(f.var("a"), f.variable("a2")), (f.var("b"), f.falsum())]);
        let pb1 = f.pbc(EQ, 2, lits.clone(), coeffs.clone());
        let pb2 = f.pbc(LE, 8, lits, coeffs2);
        assert_eq!(f.pbc(EQ, 0, lits_s1, coeff_s1), f.substitute(pb1, &s1));
        assert_eq!(f.pbc(EQ, 2, lits_s2, coeff_s2), f.substitute(pb1, &s2));
        assert_eq!(f.falsum(), f.substitute(pb1, &s3));
        assert_eq!(f.verum(), f.substitute(pb2, &s3));
        assert_eq!(f.falsum(), f.substitute(pb1, &s4));
        assert_eq!(f.verum(), f.substitute(pb2, &s4));
        assert_eq!(f.pbc(EQ, 2, lits_s5, coeffs), f.substitute(pb1, &s5));
        assert_eq!(f.pbc(EQ, 4, lits_s6, coeff_s6), f.substitute(pb1, &s6));
    }

    #[test]
    fn test_substitute_var() {
        let ff = F::new();
        let f = &ff.f;
        assert_eq!("x | y".to_formula(f), f.substitute_var(ff.A, ff.A.as_variable().unwrap(), ff.OR1));
        assert_eq!("~(x | y)".to_formula(f), f.substitute_var(ff.NA, ff.A.as_variable().unwrap(), ff.OR1));
        assert_eq!("a => (x | y)".to_formula(f), f.substitute_var(ff.IMP1, ff.B.as_variable().unwrap(), ff.OR1));
        assert_eq!("~a <=> ~(x | y)".to_formula(f), f.substitute_var(ff.EQ2, ff.B.as_variable().unwrap(), ff.OR1));
        let formula1 = f.and([ff.A, ff.NB, ff.C, ff.NX, ff.NY]);
        assert_eq!("a & ~b & c & ~x".to_formula(f), f.substitute_var(formula1, ff.Y.as_variable().unwrap(), ff.X));
        let formula2 = f.or([ff.A, ff.NB, ff.C, ff.NX, ff.NY]);
        assert_eq!("a | ~b | c | ~x".to_formula(f), f.substitute_var(formula2, ff.Y.as_variable().unwrap(), ff.X));
        let formula3 = "a + b + c + d < 3".to_formula(f);
        assert_eq!("a + b + x + d < 3".to_formula(f), f.substitute_var(formula3, ff.C.as_variable().unwrap(), ff.X));
        let formula4 = "2 * a + -3 * b + 4 * ~c + 5 * d < 3".to_formula(f);
        assert_eq!("2 * a + -3 * b + 4 * ~x + 5 * d < 3".to_formula(f), f.substitute_var(formula4, ff.C.as_variable().unwrap(), ff.X));
    }

    fn create_substitution(ff: &F) -> Substitution {
        let mut subst = HashMap::new();
        subst.insert(ff.A.as_variable().unwrap(), ff.NA);
        subst.insert(ff.B.as_variable().unwrap(), ff.OR1);
        subst.insert(ff.X.as_variable().unwrap(), ff.AND1);
        subst
    }
}
