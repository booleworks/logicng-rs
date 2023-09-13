mod tests {
    use num_bigint::ToBigUint;

    use crate::datastructures::{Assignment, Model};
    use crate::formulas::{EncodedFormula, FormulaFactory};
    use crate::knowledge_compilation::bdd::bdd_handler::{BddError, NumberOfNodesBddHandler};
    use crate::knowledge_compilation::bdd::bdd_kernel::BddKernel;
    use crate::knowledge_compilation::bdd::bdd_main::Bdd;
    use crate::knowledge_compilation::bdd::tests::bdd_test_fixtures::B;
    use crate::util::formula_randomizer::{FormulaRandomizer, FormulaRandomizerConfig};
    use std::collections::BTreeSet;

    #[test]
    fn test_tautology() {
        let b = B::new();
        assert!(!b.FALSE.is_tautology());
        assert!(b.TRUE.is_tautology());
        assert!(!b.VAR.is_tautology());
        assert!(!b.LIT.is_tautology());
        assert!(!b.IMPL.is_tautology());
        assert!(!b.EQUIV.is_tautology());
        assert!(!b.OR.is_tautology());
        assert!(!b.AND.is_tautology());
        assert!(!b.FORMULA.is_tautology());
        assert!(!b.CC.is_tautology());
    }

    #[test]
    fn test_contradiction() {
        let b = B::new();
        assert!(b.FALSE.is_contradicion());
        assert!(!b.TRUE.is_contradicion());
        assert!(!b.VAR.is_contradicion());
        assert!(!b.LIT.is_contradicion());
        assert!(!b.IMPL.is_contradicion());
        assert!(!b.EQUIV.is_contradicion());
        assert!(!b.OR.is_contradicion());
        assert!(!b.AND.is_contradicion());
        assert!(!b.FORMULA.is_contradicion());
        assert!(!b.CC.is_contradicion());
    }

    #[test]
    fn test_model() {
        let b = B::new();
        let mut k = b.K;
        let f = b.F;

        let va = f.var("A");
        let vb = f.var("B");
        let vc = f.var("C");

        assert!(b.FALSE.model(&mut k).is_none());
        assert!(Assignment::from(b.TRUE.model(&mut k).unwrap()).is_empty());
        assert!(Assignment::from(b.VAR.model(&mut k).unwrap()).contains_pos(va));
        assert!(Assignment::from(b.LIT.model(&mut k).unwrap()).contains_neg(va));
        assert!(Assignment::from(b.IMPL.model(&mut k).unwrap()).contains_neg(va));

        let model_equiv = Assignment::from(b.EQUIV.model(&mut k).unwrap());
        assert!(model_equiv.contains_neg(va));
        assert!(model_equiv.contains_pos(vb));

        let model_or = Assignment::from(b.OR.model(&mut k).unwrap());
        assert!(model_or.contains_neg(va));
        assert!(model_or.contains_neg(vb));
        assert!(model_or.contains_neg(vc));

        let model_and = Assignment::from(b.AND.model(&mut k).unwrap());
        assert!(model_and.contains_pos(va));
        assert!(model_and.contains_pos(vb));
        assert!(model_and.contains_neg(vc));

        assert!(Assignment::from(b.FORMULA.model(&mut k).unwrap()).contains_neg(f.var("A")));

        let model_cc = Assignment::from(b.CC.model(&mut k).unwrap());
        assert!(model_cc.contains_neg(va));
        assert!(model_cc.contains_neg(vb));
        assert!(model_cc.contains_pos(vc));
    }

    #[test]
    fn test_model_for_variables() {
        let b = B::new();
        let mut k = b.K;
        let f = b.F;

        let va = f.var("A");
        let vb = f.var("B");
        let vc = f.var("C");

        let ab = vec![va, vb];
        let abc = vec![va, vb, vc];

        assert!(b.FALSE.model_for_variables(true, &Vec::new(), &f, &mut k).is_none());
        assert!(b.TRUE.model_for_variables(true, &Vec::new(), &f, &mut k).unwrap().is_empty());

        let model_var = Assignment::from(b.VAR.model_for_variables(true, &ab, &f, &mut k).unwrap());
        assert!(model_var.contains_pos(va));
        assert!(model_var.contains_pos(vb));

        let model_lit = Assignment::from(b.LIT.model_for_variables(false, &abc, &f, &mut k).unwrap());
        assert!(model_lit.contains_neg(va));
        assert!(model_lit.contains_neg(vb));
        assert!(model_lit.contains_neg(vc));

        let model_impl = Assignment::from(b.IMPL.model_for_variables(true, &ab, &f, &mut k).unwrap());
        assert!(model_impl.contains_neg(va));
        assert!(model_impl.contains_pos(vb));

        let model_equiv = Assignment::from(b.EQUIV.model_for_variables(true, &Vec::new(), &f, &mut k).unwrap());
        assert!(model_equiv.contains_neg(va));
        assert!(model_equiv.contains_pos(vb));

        let model_or = Assignment::from(b.OR.model_for_variables(true, &ab, &f, &mut k).unwrap());
        assert!(model_or.contains_neg(va));
        assert!(model_or.contains_neg(vb));
        assert!(model_or.contains_neg(vc));

        let model_and = Assignment::from(b.AND.model_for_variables(true, &abc, &f, &mut k).unwrap());
        assert!(model_and.contains_pos(va));
        assert!(model_and.contains_pos(vb));
        assert!(model_and.contains_neg(vc));

        assert!(Assignment::from(b.FORMULA.model_for_variables(false, &ab, &f, &mut k).unwrap()).contains_neg(f.var("A")));

        let model_cc = Assignment::from(b.CC.model_for_variables(true, &abc, &f, &mut k).unwrap());
        assert!(model_cc.contains_neg(va));
        assert!(model_cc.contains_neg(vb));
        assert!(model_cc.contains_pos(vc));
    }

    #[test]
    #[allow(clippy::cognitive_complexity)]
    fn test_full_model() {
        let b = B::new();
        let mut k = b.K;
        let f = b.F;

        let va = f.var("A");
        let vb = f.var("B");
        let vc = f.var("C");

        assert!(b.FALSE.full_model(&mut k).is_none());
        let model_true = Assignment::from(b.TRUE.full_model(&mut k).unwrap());
        assert!(model_true.contains_neg(va));
        assert!(model_true.contains_neg(vb));
        assert!(model_true.contains_neg(vc));

        let model_var = Assignment::from(b.VAR.full_model(&mut k).unwrap());
        assert!(model_var.contains_pos(va));
        assert!(model_var.contains_neg(vb));
        assert!(model_var.contains_neg(vc));

        let model_lit = Assignment::from(b.LIT.full_model(&mut k).unwrap());
        assert!(model_lit.contains_neg(va));
        assert!(model_lit.contains_neg(vb));
        assert!(model_lit.contains_neg(vc));

        let model_impl = Assignment::from(b.IMPL.full_model(&mut k).unwrap());
        assert!(model_impl.contains_neg(va));
        assert!(model_impl.contains_neg(vb));
        assert!(model_impl.contains_neg(vc));

        let model_equiv = Assignment::from(b.EQUIV.full_model(&mut k).unwrap());
        assert!(model_equiv.contains_neg(va));
        assert!(model_equiv.contains_pos(vb));
        assert!(model_equiv.contains_neg(vc));

        let model_or = Assignment::from(b.OR.full_model(&mut k).unwrap());
        assert!(model_or.contains_neg(va));
        assert!(model_or.contains_neg(vb));
        assert!(model_or.contains_neg(vc));

        let model_and = Assignment::from(b.AND.full_model(&mut k).unwrap());
        assert!(model_and.contains_pos(va));
        assert!(model_and.contains_pos(vb));
        assert!(model_and.contains_neg(vc));

        let model_formula = Assignment::from(b.FORMULA.full_model(&mut k).unwrap());
        assert!(model_formula.contains_neg(va));
        assert!(model_formula.contains_neg(vb));
        assert!(model_formula.contains_neg(vc));

        let model_cc = Assignment::from(b.CC.full_model(&mut k).unwrap());
        assert!(model_cc.contains_neg(va));
        assert!(model_cc.contains_neg(vb));
        assert!(model_cc.contains_pos(vc));
    }

    #[test]
    fn test_enumerate_all_models() {
        let b = B::new();
        let mut k = b.K;
        let f = b.F;
        assert!(b.FALSE.enumerate_all_models(&mut k).is_empty());

        let models_true = b.TRUE.enumerate_all_models(&mut k);
        assert_eq!(models_true.len(), 8);
        verify_models(f.verum(), models_true, &f);

        let models_var = b.VAR.enumerate_all_models(&mut k);
        assert_eq!(models_var.len(), 4);
        verify_models(b.VAR_F, models_var, &f);

        let models_lit = b.LIT.enumerate_all_models(&mut k);
        assert_eq!(models_lit.len(), 4);
        verify_models(b.LIT_F, models_lit, &f);

        let models_impl = b.IMPL.enumerate_all_models(&mut k);
        assert_eq!(models_impl.len(), 6);
        verify_models(b.IMPL_F, models_impl, &f);

        let models_equiv = b.EQUIV.enumerate_all_models(&mut k);
        assert_eq!(models_equiv.len(), 4);
        verify_models(b.EQUIV_F, models_equiv, &f);

        let models_or = b.OR.enumerate_all_models(&mut k);
        assert_eq!(models_or.len(), 7);
        verify_models(b.OR_F, models_or, &f);

        let models_and = b.AND.enumerate_all_models(&mut k);
        assert_eq!(models_and.len(), 1);
        verify_models(b.AND_F, models_and, &f);

        let models_formula = b.FORMULA.enumerate_all_models(&mut k);
        assert_eq!(models_formula.len(), 6);
        verify_models(b.FORMULA_F, models_formula, &f);

        let models_cc = b.CC.enumerate_all_models(&mut k);
        assert_eq!(models_cc.len(), 3);
        verify_models(b.CC_F, models_cc, &f);
    }

    #[test]
    fn test_enumerate_all_models_projected() {
        let b = B::new();
        let mut k = b.K;
        let f = b.F;

        let va = f.var("A");
        let vb = f.var("B");

        let ab = vec![va, vb];

        assert!(b.FALSE.enumerate_all_models_projected(&ab, &mut k).is_empty());

        let models_true = b.TRUE.enumerate_all_models_projected(&ab, &mut k);
        assert_eq!(models_true.len(), 4);
        verify_models(f.verum(), models_true, &f);

        let models_var = b.VAR.enumerate_all_models_projected(&ab, &mut k);
        assert_eq!(models_var.len(), 2);
        verify_models(b.VAR_F, models_var, &f);

        let models_lit = b.LIT.enumerate_all_models_projected(&ab, &mut k);
        assert_eq!(models_lit.len(), 2);
        verify_models(b.LIT_F, models_lit, &f);

        let models_impl = b.IMPL.enumerate_all_models_projected(&ab, &mut k);
        assert_eq!(models_impl.len(), 3);
        verify_models(b.IMPL_F, models_impl, &f);

        let models_equiv = b.EQUIV.enumerate_all_models_projected(&ab, &mut k);
        assert_eq!(models_equiv.len(), 2);
        verify_models(b.EQUIV_F, models_equiv, &f);

        let models_or = b.OR.enumerate_all_models_projected(&ab, &mut k);
        assert_eq!(models_or.len(), 4);
        verify_models(b.OR_F, models_or, &f);

        let models_and = b.AND.enumerate_all_models_projected(&ab, &mut k);
        assert_eq!(models_and.len(), 1);
        verify_models(b.AND_F, models_and, &f);

        let models_formula = b.FORMULA.enumerate_all_models_projected(&ab, &mut k);
        assert_eq!(models_formula.len(), 4);
        verify_models(b.FORMULA_F, models_formula, &f);

        let models_cc = b.CC.enumerate_all_models_projected(&ab, &mut k);
        assert_eq!(models_cc.len(), 3);
    }

    #[test]
    fn test_node_count() {
        let b = B::new();
        let mut k = b.K;
        assert_eq!(b.FALSE.node_count(&mut k), 0);
        assert_eq!(b.TRUE.node_count(&mut k), 0);
        assert_eq!(b.VAR.node_count(&mut k), 1);
        assert_eq!(b.LIT.node_count(&mut k), 1);
        assert_eq!(b.IMPL.node_count(&mut k), 2);
        assert_eq!(b.EQUIV.node_count(&mut k), 3);
        assert_eq!(b.OR.node_count(&mut k), 3);
        assert_eq!(b.AND.node_count(&mut k), 3);
        assert_eq!(b.FORMULA.node_count(&mut k), 2);
        assert_eq!(b.CC.node_count(&mut k), 5);
    }

    #[test]
    fn test_model_count() {
        let b = B::new();
        let mut k = b.K;
        assert_eq!(b.FALSE.model_count(&mut k), 0.to_biguint().unwrap());
        assert_eq!(b.TRUE.model_count(&mut k), 8.to_biguint().unwrap());
        assert_eq!(b.VAR.model_count(&mut k), 4.to_biguint().unwrap());
        assert_eq!(b.LIT.model_count(&mut k), 4.to_biguint().unwrap());
        assert_eq!(b.IMPL.model_count(&mut k), 6.to_biguint().unwrap());
        assert_eq!(b.EQUIV.model_count(&mut k), 4.to_biguint().unwrap());
        assert_eq!(b.OR.model_count(&mut k), 7.to_biguint().unwrap());
        assert_eq!(b.AND.model_count(&mut k), 1.to_biguint().unwrap());
        assert_eq!(b.FORMULA.model_count(&mut k), 6.to_biguint().unwrap());
        assert_eq!(b.CC.model_count(&mut k), 3.to_biguint().unwrap());
    }

    #[test]
    fn test_path_count() {
        let b = B::new();
        let mut k = b.K;
        assert_eq!(b.FALSE.number_of_terms_dnf(&mut k), 0.to_biguint().unwrap());
        assert_eq!(b.FALSE.number_of_clauses_cnf(&mut k), 1.to_biguint().unwrap());
        assert_eq!(b.TRUE.number_of_terms_dnf(&mut k), 1.to_biguint().unwrap());
        assert_eq!(b.TRUE.number_of_clauses_cnf(&mut k), 0.to_biguint().unwrap());
        assert_eq!(b.VAR.number_of_terms_dnf(&mut k), 1.to_biguint().unwrap());
        assert_eq!(b.VAR.number_of_clauses_cnf(&mut k), 1.to_biguint().unwrap());
        assert_eq!(b.LIT.number_of_terms_dnf(&mut k), 1.to_biguint().unwrap());
        assert_eq!(b.LIT.number_of_clauses_cnf(&mut k), 1.to_biguint().unwrap());
        assert_eq!(b.IMPL.number_of_terms_dnf(&mut k), 2.to_biguint().unwrap());
        assert_eq!(b.IMPL.number_of_clauses_cnf(&mut k), 1.to_biguint().unwrap());
        assert_eq!(b.EQUIV.number_of_terms_dnf(&mut k), 2.to_biguint().unwrap());
        assert_eq!(b.EQUIV.number_of_clauses_cnf(&mut k), 2.to_biguint().unwrap());
        assert_eq!(b.OR.number_of_terms_dnf(&mut k), 3.to_biguint().unwrap());
        assert_eq!(b.OR.number_of_clauses_cnf(&mut k), 1.to_biguint().unwrap());
        assert_eq!(b.AND.number_of_terms_dnf(&mut k), 1.to_biguint().unwrap());
        assert_eq!(b.AND.number_of_clauses_cnf(&mut k), 3.to_biguint().unwrap());
        assert_eq!(b.FORMULA.number_of_terms_dnf(&mut k), 2.to_biguint().unwrap());
        assert_eq!(b.FORMULA.number_of_clauses_cnf(&mut k), 1.to_biguint().unwrap());
        assert_eq!(b.CC.number_of_terms_dnf(&mut k), 3.to_biguint().unwrap());
        assert_eq!(b.CC.number_of_clauses_cnf(&mut k), 4.to_biguint().unwrap());
    }

    #[test]
    fn test_cnf() {
        let b = B::new();
        let f = b.F;
        let mut k = b.K;
        assert_eq!(b.FALSE.cnf(&f, &mut k), f.falsum());
        assert_eq!(b.TRUE.cnf(&f, &mut k), f.verum());
        assert_eq!(b.VAR.cnf(&f, &mut k), f.variable("A"));
        assert_eq!(b.LIT.cnf(&f, &mut k), f.literal("A", false));
        assert_eq!(b.IMPL.cnf(&f, &mut k), f.parse("~A | ~B").unwrap());
        assert_eq!(b.EQUIV.cnf(&f, &mut k), f.parse("(A | B) & (~A | ~B)").unwrap());
        assert_eq!(b.OR.cnf(&f, &mut k), f.parse("A | B | ~C").unwrap());
        assert_eq!(b.AND.cnf(&f, &mut k), f.parse("A & (~A | B) & (~A | ~B | ~C)").unwrap());
        assert_eq!(b.FORMULA.cnf(&f, &mut k), f.parse("~A | ~C").unwrap());
        assert_eq!(b.CC.cnf(&f, &mut k), f.parse("(A | B | C) & (A | ~B | ~C) & (~A | B | ~C) & (~A | ~B)").unwrap());
    }

    #[test]
    fn test_dnf() {
        let b = B::new();
        let f = b.F;
        let mut k = b.K;
        assert_eq!(b.FALSE.dnf(&f, &mut k), f.falsum());
        assert_eq!(b.TRUE.dnf(&f, &mut k), f.verum());
        assert_eq!(b.VAR.dnf(&f, &mut k), f.variable("A"));
        assert_eq!(b.LIT.dnf(&f, &mut k), f.literal("A", false));
        assert_eq!(b.IMPL.dnf(&f, &mut k), f.parse("~A | A & ~B").unwrap());
        assert_eq!(b.EQUIV.dnf(&f, &mut k), f.parse("~A & B | A & ~B").unwrap());
        assert_eq!(b.OR.dnf(&f, &mut k), f.parse("~A & ~B & ~C | ~A & B | A").unwrap());
        assert_eq!(b.AND.dnf(&f, &mut k), f.parse("A & B & ~C").unwrap());
        assert_eq!(b.FORMULA.dnf(&f, &mut k), f.parse("~A | A & ~C").unwrap());
        assert_eq!(b.CC.dnf(&f, &mut k), f.parse("~A & ~B & C | ~A & B & ~C | A & ~B & ~C").unwrap());
    }

    #[test]
    fn test_variable_profile() {
        let b = B::new();
        let f = b.F;
        let mut k = b.K;

        let va = f.var("A");
        let vb = f.var("B");
        let vc = f.var("C");

        assert_eq!(b.FALSE.variable_profile(&mut k).get(&va).unwrap(), &0);
        assert_eq!(b.FALSE.variable_profile(&mut k).get(&vb).unwrap(), &0);
        assert_eq!(b.FALSE.variable_profile(&mut k).get(&vc).unwrap(), &0);

        assert_eq!(b.TRUE.variable_profile(&mut k).get(&va).unwrap(), &0);
        assert_eq!(b.TRUE.variable_profile(&mut k).get(&vb).unwrap(), &0);
        assert_eq!(b.TRUE.variable_profile(&mut k).get(&vc).unwrap(), &0);

        assert_eq!(b.VAR.variable_profile(&mut k).get(&va).unwrap(), &1);
        assert_eq!(b.VAR.variable_profile(&mut k).get(&vb).unwrap(), &0);
        assert_eq!(b.VAR.variable_profile(&mut k).get(&vc).unwrap(), &0);

        assert_eq!(b.LIT.variable_profile(&mut k).get(&va).unwrap(), &1);
        assert_eq!(b.LIT.variable_profile(&mut k).get(&vb).unwrap(), &0);
        assert_eq!(b.LIT.variable_profile(&mut k).get(&vc).unwrap(), &0);

        assert_eq!(b.IMPL.variable_profile(&mut k).get(&va).unwrap(), &1);
        assert_eq!(b.IMPL.variable_profile(&mut k).get(&vb).unwrap(), &1);
        assert_eq!(b.IMPL.variable_profile(&mut k).get(&vc).unwrap(), &0);

        assert_eq!(b.EQUIV.variable_profile(&mut k).get(&va).unwrap(), &1);
        assert_eq!(b.EQUIV.variable_profile(&mut k).get(&vb).unwrap(), &2);
        assert_eq!(b.EQUIV.variable_profile(&mut k).get(&vc).unwrap(), &0);

        assert_eq!(b.OR.variable_profile(&mut k).get(&va).unwrap(), &1);
        assert_eq!(b.OR.variable_profile(&mut k).get(&vb).unwrap(), &1);
        assert_eq!(b.OR.variable_profile(&mut k).get(&vc).unwrap(), &1);

        assert_eq!(b.AND.variable_profile(&mut k).get(&va).unwrap(), &1);
        assert_eq!(b.AND.variable_profile(&mut k).get(&vb).unwrap(), &1);
        assert_eq!(b.AND.variable_profile(&mut k).get(&vc).unwrap(), &1);
    }

    #[test]
    fn test_to_formula() {
        let b = B::new();
        let f = b.F;
        let mut k = b.K;
        assert_eq!(b.FALSE.to_formula(&f, &mut k), f.falsum());
        assert_eq!(b.TRUE.to_formula(&f, &mut k), f.verum());
        assert_eq!(b.VAR.to_formula(&f, &mut k), f.variable("A"));
        assert_eq!(b.LIT.to_formula(&f, &mut k), f.literal("A", false));
        assert_eq!(b.IMPL.to_formula(&f, &mut k), f.parse("~A | A & ~B").unwrap());
        assert_eq!(b.EQUIV.to_formula(&f, &mut k), f.parse("~A & B | A & ~B").unwrap());
        assert_eq!(b.OR.to_formula(&f, &mut k), f.parse("A | ~A & (B | ~B & ~C)").unwrap());
        assert_eq!(b.AND.to_formula(&f, &mut k), f.parse("A & B & ~C").unwrap());
        assert_eq!(b.FORMULA.to_formula(&f, &mut k), f.parse("A & ~C | ~A").unwrap());
        assert_eq!(b.CC.to_formula(&f, &mut k), f.parse("A & ~B & ~C | ~A & (B & ~C | ~B & C)").unwrap());
    }

    #[test]
    fn test_restrict() {
        let b = B::new();
        let f = b.F;
        let mut k = b.K;

        let res_a = vec![f.lit("A", true)];
        let res_not_a = vec![f.lit("A", false)];
        let res_ab = vec![f.lit("A", true), f.lit("B", true)];

        assert_eq!(b.TRUE.restrict(&res_a, &f, &mut k), b.TRUE);
        assert_eq!(b.TRUE.restrict(&res_not_a, &f, &mut k), b.TRUE);
        assert_eq!(b.TRUE.restrict(&res_ab, &f, &mut k), b.TRUE);

        assert_eq!(b.FALSE.restrict(&res_a, &f, &mut k), b.FALSE);
        assert_eq!(b.FALSE.restrict(&res_not_a, &f, &mut k), b.FALSE);
        assert_eq!(b.FALSE.restrict(&res_ab, &f, &mut k), b.FALSE);

        assert_eq!(b.VAR.restrict(&res_a, &f, &mut k), b.TRUE);
        assert_eq!(b.VAR.restrict(&res_not_a, &f, &mut k), b.FALSE);
        assert_eq!(b.VAR.restrict(&res_ab, &f, &mut k), b.TRUE);

        assert_eq!(b.LIT.restrict(&res_a, &f, &mut k), b.FALSE);
        assert_eq!(b.LIT.restrict(&res_not_a, &f, &mut k), b.TRUE);
        assert_eq!(b.LIT.restrict(&res_ab, &f, &mut k), b.FALSE);

        let bdd_not_b = Bdd::from_formula(f.parse("~B").unwrap(), &f, &mut k);
        assert_eq!(b.IMPL.restrict(&res_a, &f, &mut k), bdd_not_b);
        assert_eq!(b.IMPL.restrict(&res_not_a, &f, &mut k), b.TRUE);
        assert_eq!(b.IMPL.restrict(&res_ab, &f, &mut k), b.FALSE);

        let bdd_b = Bdd::from_formula(f.parse("B").unwrap(), &f, &mut k);
        assert_eq!(b.EQUIV.restrict(&res_a, &f, &mut k), bdd_not_b);
        assert_eq!(b.EQUIV.restrict(&res_not_a, &f, &mut k), bdd_b);
        assert_eq!(b.EQUIV.restrict(&res_ab, &f, &mut k), b.FALSE);

        let bdd_b_or_nc = Bdd::from_formula(f.parse("B | ~C").unwrap(), &f, &mut k);
        assert_eq!(b.OR.restrict(&res_a, &f, &mut k), b.TRUE);
        assert_eq!(b.OR.restrict(&res_not_a, &f, &mut k), bdd_b_or_nc);
        assert_eq!(b.OR.restrict(&res_ab, &f, &mut k), b.TRUE);

        let bdd_b_and_nc = Bdd::from_formula(f.parse("B & ~C").unwrap(), &f, &mut k);
        let bdd_not_c = Bdd::from_formula(f.parse("~C").unwrap(), &f, &mut k);
        assert_eq!(b.AND.restrict(&res_a, &f, &mut k), bdd_b_and_nc);
        assert_eq!(b.AND.restrict(&res_not_a, &f, &mut k), b.FALSE);
        assert_eq!(b.AND.restrict(&res_ab, &f, &mut k), bdd_not_c);
    }

    #[test]
    fn test_exists() {
        let b = B::new();
        let f = b.F;
        let mut k = b.K;

        let res_a = vec![f.var("A")];
        let res_ab = vec![f.var("A"), f.var("B")];

        assert_eq!(b.TRUE.exists(&res_a, &f, &mut k), b.TRUE);
        assert_eq!(b.TRUE.exists(&res_ab, &f, &mut k), b.TRUE);

        assert_eq!(b.FALSE.exists(&res_a, &f, &mut k), b.FALSE);
        assert_eq!(b.FALSE.exists(&res_ab, &f, &mut k), b.FALSE);

        assert_eq!(b.VAR.exists(&res_a, &f, &mut k), b.TRUE);
        assert_eq!(b.VAR.exists(&res_ab, &f, &mut k), b.TRUE);

        assert_eq!(b.LIT.exists(&res_a, &f, &mut k), b.TRUE);
        assert_eq!(b.LIT.exists(&res_ab, &f, &mut k), b.TRUE);

        assert_eq!(b.IMPL.exists(&res_a, &f, &mut k), b.TRUE);
        assert_eq!(b.IMPL.exists(&res_ab, &f, &mut k), b.TRUE);

        assert_eq!(b.EQUIV.exists(&res_a, &f, &mut k), b.TRUE);
        assert_eq!(b.EQUIV.exists(&res_ab, &f, &mut k), b.TRUE);

        assert_eq!(b.OR.exists(&res_a, &f, &mut k), b.TRUE);
        assert_eq!(b.OR.exists(&res_ab, &f, &mut k), b.TRUE);

        let bdd_b_and_nc = Bdd::from_formula(f.parse("B & ~C").unwrap(), &f, &mut k);
        let bdd_not_c = Bdd::from_formula(f.parse("~C").unwrap(), &f, &mut k);
        assert_eq!(b.AND.exists(&res_a, &f, &mut k), bdd_b_and_nc);
        assert_eq!(b.AND.exists(&res_ab, &f, &mut k), bdd_not_c);
    }

    #[test]
    fn test_forall() {
        let b = B::new();
        let f = b.F;
        let mut k = b.K;

        let res_a = vec![f.var("A")];
        let res_ab = vec![f.var("A"), f.var("B")];

        assert_eq!(b.TRUE.for_all(&res_a, &f, &mut k), b.TRUE);
        assert_eq!(b.TRUE.for_all(&res_ab, &f, &mut k), b.TRUE);

        assert_eq!(b.FALSE.for_all(&res_a, &f, &mut k), b.FALSE);
        assert_eq!(b.FALSE.for_all(&res_ab, &f, &mut k), b.FALSE);

        assert_eq!(b.VAR.for_all(&res_a, &f, &mut k), b.FALSE);
        assert_eq!(b.VAR.for_all(&res_ab, &f, &mut k), b.FALSE);

        assert_eq!(b.LIT.for_all(&res_a, &f, &mut k), b.FALSE);
        assert_eq!(b.LIT.for_all(&res_ab, &f, &mut k), b.FALSE);

        let bdd_not_b = Bdd::from_formula(f.parse("~B").unwrap(), &f, &mut k);
        assert_eq!(b.IMPL.for_all(&res_a, &f, &mut k), bdd_not_b);
        assert_eq!(b.IMPL.for_all(&res_ab, &f, &mut k), b.FALSE);

        assert_eq!(b.EQUIV.for_all(&res_a, &f, &mut k), b.FALSE);
        assert_eq!(b.EQUIV.for_all(&res_ab, &f, &mut k), b.FALSE);

        let bdd_b_or_nc = Bdd::from_formula(f.parse("B | ~C").unwrap(), &f, &mut k);
        let bdd_not_c = Bdd::from_formula(f.parse("~C").unwrap(), &f, &mut k);
        assert_eq!(b.OR.for_all(&res_a, &f, &mut k), bdd_b_or_nc);
        assert_eq!(b.OR.for_all(&res_ab, &f, &mut k), bdd_not_c);

        assert_eq!(b.AND.for_all(&res_a, &f, &mut k), b.FALSE);
        assert_eq!(b.AND.for_all(&res_ab, &f, &mut k), b.FALSE);
    }

    #[test]
    fn test_support() {
        let b = B::new();
        let f = b.F;
        let mut k = b.K;

        let va = f.var("A");
        let vb = f.var("B");
        let vc = f.var("C");
        let mut set_a = BTreeSet::new();
        set_a.insert(va);
        let mut set_ab = BTreeSet::new();
        set_ab.insert(va);
        set_ab.insert(vb);
        let mut set_ac = BTreeSet::new();
        set_ac.insert(va);
        set_ac.insert(vc);
        let mut set_abc = BTreeSet::new();
        set_abc.insert(va);
        set_abc.insert(vb);
        set_abc.insert(vc);

        assert!(b.FALSE.support(&mut k).is_empty());
        assert!(b.TRUE.support(&mut k).is_empty());
        assert_eq!(b.VAR.support(&mut k), set_a);
        assert_eq!(b.LIT.support(&mut k), set_a);
        assert_eq!(b.IMPL.support(&mut k), set_ab);
        assert_eq!(b.EQUIV.support(&mut k), set_ab);
        assert_eq!(b.OR.support(&mut k), set_abc);
        assert_eq!(b.AND.support(&mut k), set_abc);
        assert_eq!(b.FORMULA.support(&mut k), set_ac);
        assert_eq!(b.CC.support(&mut k), set_abc);
    }

    #[test]
    fn test_with_handler() {
        let f = FormulaFactory::new();
        let mut k = BddKernel::new_with_num_vars(20, 200, 2000);
        let mut rnd = FormulaRandomizer::new(FormulaRandomizerConfig::default_with_num_vars(20));
        let formula = rnd.formula(&f, 5);

        let mut handler_50 = NumberOfNodesBddHandler::new(40);
        let mut handler_5000 = NumberOfNodesBddHandler::new(5000);

        let bdd_err = Bdd::from_formula_with_handler(formula, &f, &mut k, &mut handler_50);
        let bdd_ok = Bdd::from_formula_with_handler(formula, &f, &mut k, &mut handler_5000);

        assert!(bdd_err.is_err());
        assert_eq!(bdd_err.err().unwrap(), BddError::NodeLimitReached);
        assert!(bdd_ok.is_ok());
    }

    fn verify_models(formula: EncodedFormula, models: Vec<Model>, f: &FormulaFactory) {
        for model in models {
            assert!(f.evaluate(formula, &model.into()));
        }
    }
}
