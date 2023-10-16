mod formula_factory_tests {
    use crate::formulas::formula_cache::formula_encoding::{Encoding, FormulaEncoding};
    use crate::formulas::FormulaType::{And, Equiv, False, Impl, Lit, Not, Or, True};
    use crate::formulas::{EncodedFormula, FormulaFactory, FormulaType, LitType, VarType};
    use crate::util::test_util::string_vars;
    use std::collections::BTreeSet;

    #[test]
    fn test() {
        let f = FormulaFactory::new();
        let a = f.variable("a");
        let b = f.variable("b");
        let ab = f.and([a, b]);
        let ba = f.and([b, a]);
        println!("{:?}, {}", ab, ab.to_string(&f));
        println!("{:?}, {}", ba, ba.to_string(&f));
    }

    #[test]
    #[allow(clippy::many_single_char_names)]
    fn test_formula_creation() {
        let f = FormulaFactory::new();
        let a = f.variable("a");
        let b = f.variable("b");
        let c = f.variable("c");
        let d = f.variable("d");
        let e = f.variable("e");
        let g = f.variable("g");
        let na = f.literal("a", false);
        let nh = f.literal("nh", false);
        let ab = f.and([a, b]);
        let ab_c_d = f.or([ab, c, d]);
        let ab_c_d2 = f.or([ab, c, d]);
        let nab = f.not(ab);
        let ab_z_ab_c_d = f.implication(ab, ab_c_d);
        let d_e = f.or([d, e]);
        let ab_eq_d_e = f.equivalence(ab, d_e);
        let ab_eq_d_e2 = f.equivalence(ab, d_e);
        let de = f.and([d, ab_eq_d_e]);
        let de2 = f.and([d, ab_eq_d_e]);
        assert_eq!(f.verum(), EncodedFormula::from(FormulaEncoding::encode_type(FormulaType::True)));
        assert_eq!(f.falsum(), EncodedFormula::from(FormulaEncoding::encode_type(False)));
        assert_eq!(a, ff_lit(0, true));
        assert_eq!(b, ff_lit(1, true));
        assert_eq!(c, ff_lit(2, true));
        assert_eq!(d, ff_lit(3, true));
        assert_eq!(e, ff_lit(4, true));
        assert_eq!(g, ff_lit(5, true));
        assert_eq!(na, ff_lit(0, false));
        assert_eq!(nh, ff_lit(6, false));
        assert_eq!(ab, df(0, And));
        assert_eq!(ab_c_d, df(0, Or));
        assert_eq!(ab_c_d2, df(0, Or));
        assert_eq!(nab, df(0, Not));
        assert_eq!(ab_z_ab_c_d, df(0, Impl));
        assert_eq!(d_e, df(1, Or));
        assert_eq!(ab_eq_d_e, df(0, Equiv));
        assert_eq!(ab_eq_d_e2, df(0, Equiv));
        assert_eq!(de, df(1, And));
        assert_eq!(de2, df(1, And));
    }

    #[test]
    #[allow(clippy::many_single_char_names)]
    fn test_operands() {
        let f = FormulaFactory::new();
        let verum = f.verum();
        let falsum = f.falsum();
        let a = f.variable("a");
        let b = f.variable("b");
        let c = f.variable("c");
        let d = f.variable("d");
        let e = f.variable("e");
        let g = f.variable("g");
        let na = f.literal("a", false);
        let nh = f.literal("nh", false);
        let ab = f.and([a, b]);
        let ab_c_d = f.or([ab, c, d]);
        let nab = f.not(ab);
        let ab_z_ab_c_d = f.implication(ab, ab_c_d);
        let d_e = f.or([d, e]);
        let ab_eq_d_e = f.equivalence(ab, d_e);
        let de = f.and([d, ab_eq_d_e]);
        assert_eq!(verum.operands(&f), vec![]);
        assert_eq!(falsum.operands(&f), vec![]);
        assert_eq!(a.operands(&f), vec![]);
        assert_eq!(b.operands(&f), vec![]);
        assert_eq!(c.operands(&f), vec![]);
        assert_eq!(d.operands(&f), vec![]);
        assert_eq!(e.operands(&f), vec![]);
        assert_eq!(g.operands(&f), vec![]);
        assert_eq!(na.operands(&f), vec![]);
        assert_eq!(nh.operands(&f), vec![]);
        assert_eq!(ab.operands(&f), vec![ff_lit(0, true), ff_lit(1, true)]);
        assert_eq!(ab_c_d.operands(&f), vec![df(0, And), ff_lit(2, true), ff_lit(3, true)]);
        assert_eq!(nab.operands(&f), vec![df(0, And)]);
        assert_eq!(ab_z_ab_c_d.operands(&f), vec![df(0, And), df(0, Or)]);
        assert_eq!(d_e.operands(&f), vec![ff_lit(3, true), ff_lit(4, true)]);
        assert_eq!(ab_eq_d_e.operands(&f), vec![df(0, And), df(1, Or)]);
        assert_eq!(de.operands(&f), vec![ff_lit(3, true), df(0, Equiv)]);
    }

    #[test]
    #[allow(clippy::many_single_char_names, clippy::cognitive_complexity)]
    fn test_simplification() {
        let f = FormulaFactory::new();
        let a = f.variable("a");
        let b = f.variable("b");
        let c = f.variable("c");
        let d = f.variable("d");
        let e = f.variable("e");
        let g = f.variable("g");
        let na = f.not(a);
        let a2 = f.not(na);
        let ab = f.and([a, f.verum(), b, f.verum()]);
        let ab2 = f.and([a, f.falsum(), b, f.verum()]);
        let and3 = f.and([a, f.verum()]);
        let ab_c_d = f.or([f.falsum(), ab, c, f.falsum(), d]);
        let ab_c_d2 = f.or([ab, f.falsum(), c, d, f.verum()]);
        let or3 = f.or([ab, f.falsum()]);
        let nverum = f.not(f.verum());
        let nfalsum = f.not(f.falsum());
        let impl1 = f.implication(f.verum(), ab_c_d);
        let impl2 = f.implication(f.falsum(), ab_c_d);
        let impl3 = f.implication(ab_c_d, f.verum());
        let impl4 = f.implication(ab_c_d, f.falsum());
        let impl5 = f.implication(ab_c_d, ab_c_d);
        let equiv1 = f.equivalence(f.verum(), ab_c_d);
        let equiv2 = f.equivalence(f.falsum(), ab_c_d);
        let equiv3 = f.equivalence(ab_c_d, f.verum());
        let equiv4 = f.equivalence(ab_c_d, f.falsum());
        let equiv5 = f.equivalence(ab_c_d, ab_c_d);
        let nab_c_d = f.not(ab_c_d);
        let equiv6 = f.equivalence(ab_c_d, nab_c_d);
        let equiv7 = f.equivalence(a, na);
        assert_eq!(f.verum(), EncodedFormula::from(FormulaEncoding::encode_type(True)));
        assert_eq!(f.falsum(), EncodedFormula::from(FormulaEncoding::encode_type(False)));
        assert_eq!(a, ff_lit(0, true));
        assert_eq!(b, ff_lit(1, true));
        assert_eq!(c, ff_lit(2, true));
        assert_eq!(d, ff_lit(3, true));
        assert_eq!(e, ff_lit(4, true));
        assert_eq!(g, ff_lit(5, true));
        assert_eq!(na, ff_lit(0, false));
        assert_eq!(a2, ff_lit(0, true));
        assert_eq!(ab, df(0, And));
        assert_eq!(ab2, EncodedFormula::from(FormulaEncoding::encode_type(False)));
        assert_eq!(and3, ff_lit(0, true));
        assert_eq!(ab_c_d, df(0, Or));
        assert_eq!(ab_c_d2, EncodedFormula::from(FormulaEncoding::encode_type(True)));
        assert_eq!(or3, df(0, And));
        assert_eq!(nverum, EncodedFormula::from(FormulaEncoding::encode_type(False)));
        assert_eq!(nfalsum, EncodedFormula::from(FormulaEncoding::encode_type(True)));
        assert_eq!(impl1, df(0, Or));
        assert_eq!(impl2, EncodedFormula::from(FormulaEncoding::encode_type(True)));
        assert_eq!(impl3, EncodedFormula::from(FormulaEncoding::encode_type(True)));
        assert_eq!(impl4, df(0, Not));
        assert_eq!(impl5, EncodedFormula::from(FormulaEncoding::encode_type(True)));
        assert_eq!(equiv1, ab_c_d);
        assert_eq!(equiv2, f.not(ab_c_d));
        assert_eq!(equiv3, ab_c_d);
        assert_eq!(equiv4, f.not(ab_c_d));
        assert_eq!(equiv5, EncodedFormula::from(FormulaEncoding::encode_type(True)));
        assert_eq!(equiv6, EncodedFormula::from(FormulaEncoding::encode_type(False)));
        assert_eq!(equiv7, EncodedFormula::from(FormulaEncoding::encode_type(False)));
    }

    #[test]
    #[allow(clippy::many_single_char_names)]
    fn test_variables() {
        let f = FormulaFactory::new();
        let a = f.variable("a");
        let b = f.variable("b");
        let c = f.variable("c");
        let d = f.variable("d");
        let e = f.variable("e");
        let g = f.variable("g");
        let na = f.literal("a", false);
        let nh = f.literal("h", false);
        let ab = f.and([a, b]);
        let ab_c_d = f.or([ab, c, d]);
        let ab_c_d2 = f.or([ab, c, d]);
        let nab = f.not(ab);
        let ab_z_ab_c_d = f.implication(ab, ab_c_d);
        let d_e = f.or([d, e]);
        let ab_eq_d_e = f.equivalence(ab, d_e);
        let ab_eq_d_e2 = f.equivalence(ab, d_e);
        let de = f.and([d, ab_eq_d_e]);
        let de2 = f.and([d, ab_eq_d_e]);

        assert_eq!(f.verum().string_variables(&f), BTreeSet::new());
        assert_eq!(f.falsum().string_variables(&f), BTreeSet::new());
        assert_eq!(a.string_variables(&f), string_vars("a"));
        assert_eq!(b.string_variables(&f), string_vars("b"));
        assert_eq!(c.string_variables(&f), string_vars("c"));
        assert_eq!(d.string_variables(&f), string_vars("d"));
        assert_eq!(e.string_variables(&f), string_vars("e"));
        assert_eq!(g.string_variables(&f), string_vars("g"));
        assert_eq!(na.string_variables(&f), string_vars("a"));
        assert_eq!(nh.string_variables(&f), string_vars("h"));
        assert_eq!(ab.string_variables(&f), string_vars("a b"));
        assert_eq!(ab_c_d.string_variables(&f), string_vars("a b c d"));
        assert_eq!(ab_c_d2.string_variables(&f), string_vars("a b c d"));
        assert_eq!(nab.string_variables(&f), string_vars("a b"));
        assert_eq!(ab_z_ab_c_d.string_variables(&f), string_vars("a b c d"));
        assert_eq!(d_e.string_variables(&f), string_vars("d e"));
        assert_eq!(ab_eq_d_e.string_variables(&f), string_vars("a b d e"));
        assert_eq!(ab_eq_d_e2.string_variables(&f), string_vars("a b d e"));
        assert_eq!(de.string_variables(&f), string_vars("a b d e"));
        assert_eq!(de2.string_variables(&f), string_vars("a b d e"));
    }

    #[test]
    fn test_ordering() {
        let f = FormulaFactory::new();
        let a = f.variable("a");
        let b = f.variable("b");
        let c = f.variable("c");
        assert_eq!(f.and([a, b]), f.and([b, a]));
        assert_eq!(f.and([a, b, c]), f.and([a, c, b]));
        assert_eq!(f.and([a, b, c]), f.and([b, a, c]));
        assert_eq!(f.and([a, b, c]), f.and([b, c, a]));
        assert_eq!(f.and([a, b, c]), f.and([c, a, b]));
        assert_eq!(f.and([a, b, c]), f.and([c, b, a]));
        assert_eq!(f.or([a, b]), f.or([b, a]));
        assert_eq!(f.or([a, b, c]), f.or([a, c, b]));
        assert_eq!(f.or([a, b, c]), f.or([b, a, c]));
        assert_eq!(f.or([a, b, c]), f.or([b, c, a]));
        assert_eq!(f.or([a, b, c]), f.or([c, a, b]));
        assert_eq!(f.or([a, b, c]), f.or([c, b, a]));

        assert_eq!(f.equivalence(a, b), f.equivalence(b, a));
        let abc = f.and([a, b, c]);
        let bca = f.and([b, c, a]);
        let a_b_c = f.or([a, b, c]);
        let b_c_a = f.or([b, c, a]);
        assert_eq!(f.equivalence(abc, b_c_a), f.equivalence(a_b_c, bca));
        assert_eq!(f.equivalence(abc, b_c_a), f.equivalence(bca, a_b_c));

        assert_ne!(f.implication(a, b), f.implication(b, a));
        assert_ne!(f.implication(abc, b_c_a), f.implication(a_b_c, bca));
        assert_eq!(f.implication(abc, b_c_a), f.implication(bca, a_b_c));
    }

    fn ff_lit(n: u64, phase: bool) -> EncodedFormula {
        if phase {
            EncodedFormula::from(FormulaEncoding::encode(n, Lit(LitType::Pos(VarType::FF)), true))
        } else {
            EncodedFormula::from(FormulaEncoding::encode(n, Lit(LitType::Neg(VarType::FF)), true))
        }
    }

    fn df(n: u64, ty: FormulaType) -> EncodedFormula {
        EncodedFormula::from(FormulaEncoding::encode(n, ty, false))
    }
}
