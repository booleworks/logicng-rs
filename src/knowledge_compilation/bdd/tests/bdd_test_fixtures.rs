#![allow(non_snake_case)]

use crate::formulas::{EncodedFormula, FormulaFactory};
use crate::knowledge_compilation::bdd::bdd_kernel::BddKernel;
use crate::knowledge_compilation::bdd::bdd_main::Bdd;

pub struct B {
    pub(crate) F: FormulaFactory,
    pub(crate) K: BddKernel,
    pub(crate) TRUE: Bdd,
    pub(crate) FALSE: Bdd,
    pub(crate) VAR: Bdd,
    pub(crate) LIT: Bdd,
    pub(crate) IMPL: Bdd,
    pub(crate) EQUIV: Bdd,
    pub(crate) OR: Bdd,
    pub(crate) AND: Bdd,
    pub(crate) FORMULA: Bdd,
    pub(crate) CC: Bdd,

    pub(crate) VAR_F: EncodedFormula,
    pub(crate) LIT_F: EncodedFormula,
    pub(crate) IMPL_F: EncodedFormula,
    pub(crate) EQUIV_F: EncodedFormula,
    pub(crate) OR_F: EncodedFormula,
    pub(crate) AND_F: EncodedFormula,
    pub(crate) FORMULA_F: EncodedFormula,
    pub(crate) CC_F: EncodedFormula,
}

impl B {
    pub(crate) fn new() -> Self {
        let f = FormulaFactory::new();
        let mut kernel = BddKernel::new_with_num_vars(3, 100, 1000);

        let verum = f.verum();
        let falsum = f.falsum();
        let var = f.variable("A");
        let lit = f.literal("A", false);
        let impli = f.parse("A => ~B").unwrap();
        let equiv = f.parse("A <=> ~B").unwrap();
        let or = f.parse("A | B | ~C").unwrap();
        let and = f.parse("A & B & ~C").unwrap();
        let formula = f.parse("(A => ~C) | (B & ~C)").unwrap();
        let cc = f.parse("A + B + C = 1").unwrap();

        let bdd_true = Bdd::from_formula(verum, &f, &mut kernel);
        let bdd_false = Bdd::from_formula(falsum, &f, &mut kernel);
        let bdd_var = Bdd::from_formula(var, &f, &mut kernel);
        let bdd_lit = Bdd::from_formula(lit, &f, &mut kernel);
        let bdd_impl = Bdd::from_formula(impli, &f, &mut kernel);
        let bdd_equiv = Bdd::from_formula(equiv, &f, &mut kernel);
        let bdd_or = Bdd::from_formula(or, &f, &mut kernel);
        let bdd_and = Bdd::from_formula(and, &f, &mut kernel);
        let bdd_formula = Bdd::from_formula(formula, &f, &mut kernel);
        let bdd_cc = Bdd::from_formula(cc, &f, &mut kernel);

        Self {
            F: f,
            K: kernel,
            TRUE: bdd_true,
            FALSE: bdd_false,
            VAR: bdd_var,
            LIT: bdd_lit,
            IMPL: bdd_impl,
            EQUIV: bdd_equiv,
            OR: bdd_or,
            AND: bdd_and,
            FORMULA: bdd_formula,
            CC: bdd_cc,

            VAR_F: var,
            LIT_F: lit,
            IMPL_F: impli,
            EQUIV_F: equiv,
            OR_F: or,
            AND_F: and,
            FORMULA_F: formula,
            CC_F: cc,
        }
    }
}
