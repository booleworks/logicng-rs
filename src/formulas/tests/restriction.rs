mod restriction_tests {
    use crate::datastructures::Assignment;
    use crate::formulas::{CType, FormulaFactory, Literal, ToFormula};
    use crate::util::test_util::F;

    fn ass(ff: &F) -> Assignment {
        Assignment::from_variables(&[ff.A.as_variable().unwrap()], &[ff.B.as_variable().unwrap(), ff.X.as_variable().unwrap()])
    }

    #[test]
    fn test_constant_restrict() {
        let ff = F::new();
        assert_eq!(ff.f.restrict(ff.TRUE, &ass(&ff)), ff.TRUE);
        assert_eq!(ff.f.restrict(ff.FALSE, &ass(&ff)), ff.FALSE);
    }

    #[test]
    fn test_literal_restrict() {
        let ff = F::new();
        assert_eq!(ff.f.restrict(ff.A, &ass(&ff)), ff.TRUE);
        assert_eq!(ff.f.restrict(ff.NA, &ass(&ff)), ff.FALSE);
        assert_eq!(ff.f.restrict(ff.X, &ass(&ff)), ff.FALSE);
        assert_eq!(ff.f.restrict(ff.NX, &ass(&ff)), ff.TRUE);
        assert_eq!(ff.f.restrict(ff.C, &ass(&ff)), ff.C);
        assert_eq!(ff.f.restrict(ff.NY, &ass(&ff)), ff.NY);
    }

    #[test]
    fn test_not_restrict() {
        let ff = F::new();
        assert_eq!(ff.f.restrict(ff.NOT1, &ass(&ff)), ff.TRUE);
        assert_eq!(ff.f.restrict(ff.NOT2, &ass(&ff)), ff.NY);
    }

    #[test]
    fn test_binary_restrict() {
        let ff = F::new();
        let implication1 = ff.f.implication(ff.NA, ff.C);
        let implication2 = ff.f.implication(ff.A, ff.C);
        assert_eq!(ff.f.restrict(ff.IMP1, &ass(&ff)), ff.FALSE);
        assert_eq!(ff.f.restrict(ff.IMP2, &ass(&ff)), ff.TRUE);
        assert_eq!(ff.f.restrict(implication1, &ass(&ff)), ff.TRUE);
        assert_eq!(ff.f.restrict(ff.IMP3, &ass(&ff)), ff.TRUE);
        assert_eq!(ff.f.restrict(implication2, &ass(&ff)), ff.C);

        assert_eq!(ff.f.restrict(ff.EQ1, &ass(&ff)), ff.FALSE);
        assert_eq!(ff.f.restrict(ff.EQ2, &ass(&ff)), ff.FALSE);
        assert_eq!(ff.f.restrict(ff.EQ3, &ass(&ff)), ff.NY);
        assert_eq!(ff.f.restrict(ff.EQ4, &ass(&ff)), ff.FALSE);
    }

    #[test]
    fn test_nary_restrict() {
        let ff = F::new();
        let formula1 = "~a | b | ~c | x | y".to_formula(&ff.f);
        let formula2 = "~a | b | ~c | ~x | ~y".to_formula(&ff.f);
        let formula3 = "a & ~b & c & ~x & ~y".to_formula(&ff.f);
        let formula4 = "a & b & c & ~x & y".to_formula(&ff.f);
        assert_eq!(ff.f.restrict(ff.OR1, &ass(&ff)), ff.Y);
        assert_eq!(ff.f.restrict(ff.OR2, &ass(&ff)), ff.TRUE);
        assert_eq!(ff.f.restrict(ff.OR3, &ass(&ff)), ff.FALSE);
        assert_eq!(ff.f.restrict(formula1, &ass(&ff)), "~c | y".to_formula(&ff.f));
        assert_eq!(ff.f.restrict(formula2, &ass(&ff)), ff.TRUE);

        assert_eq!(ff.f.restrict(ff.AND1, &ass(&ff)), ff.FALSE);
        assert_eq!(ff.f.restrict(ff.AND2, &ass(&ff)), ff.FALSE);
        assert_eq!(ff.f.restrict(ff.AND3, &ass(&ff)), ff.Y);
        assert_eq!(ff.f.restrict(formula3, &ass(&ff)), "c & ~y".to_formula(&ff.f));
        assert_eq!(ff.f.restrict(formula4, &ass(&ff)), ff.FALSE);
    }

    #[test]
    fn test_restrict_pbc() {
        let f = &FormulaFactory::new();
        let lits: Box<[Literal]> = Box::new([f.lit("a", true), f.lit("b", false), f.lit("c", true)]);
        let lits_a1: Box<[Literal]> = Box::new([f.lit("b", false), f.lit("c", true)]);
        let lits_a2: Box<[Literal]> = Box::new([f.lit("c", true)]);
        let coeffs: Box<[i64]> = Box::new([2, -2, 3]);
        let coeffs_a1: Box<[i64]> = Box::new([-2, 3]);
        let coeffs_a2: Box<[i64]> = Box::new([3]);
        let a1 = Assignment::from_variables(&[f.var("a")], &[]);
        let a2 = Assignment::from_variables(&[f.var("a")], &[f.var("b")]);
        let a3 = Assignment::from_variables(&[f.var("a"), f.var("c")], &[f.var("b")]);
        let a4 = Assignment::from_variables(&[f.var("b")], &[f.var("a"), f.var("c")]);
        let pb1 = f.pbc(CType::EQ, 2, lits, coeffs);
        assert_eq!(f.restrict(pb1, &a1), f.pbc(CType::EQ, 0, lits_a1, coeffs_a1));
        assert_eq!(f.restrict(pb1, &a2), f.pbc(CType::EQ, 2, lits_a2, coeffs_a2));
        assert_eq!(f.restrict(pb1, &a3), f.falsum());
        assert_eq!(f.restrict(pb1, &a4), f.falsum());
    }

    #[test]
    fn test_restrict_pbc_inequality() {
        let f = &FormulaFactory::new();
        let lits: Box<[Literal]> =
            Box::new([f.lit("a", true), f.lit("b", false), f.lit("c", true), f.lit("d", true), f.lit("e", true), f.lit("f", false)]);
        let coeffs: Box<[i64]> = Box::new([75, 50, 201, -3, -24, 1]);
        let pb1 = f.pbc(CType::GE, -24, lits.clone(), coeffs.clone());
        let pb2 = f.pbc(CType::LE, 150, lits, coeffs);
        let a1 = Assignment::from_variables(&[f.var("c")], &[f.var("b")]);
        let a2 = Assignment::from_variables(&[f.var("b"), f.var("d"), f.var("e")], &[f.var("a"), f.var("c")]);
        let a3 = Assignment::from_variables(&[], &[f.var("c")]);

        assert_eq!(f.restrict(pb1, &a1), f.verum());
        assert_eq!(f.restrict(pb2, &a1), f.falsum());
        assert_eq!(f.restrict(pb1, &a2), f.falsum());
        assert_eq!(f.restrict(pb2, &a3), f.verum());
    }
}
