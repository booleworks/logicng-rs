#![allow(non_snake_case)]
#![allow(dead_code)]

use std::borrow::Cow;
use std::collections::BTreeSet;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

use crate::formulas::CType::{EQ, GE, GT, LE, LT};
use crate::formulas::{EncodedFormula, FormulaFactory, Literal, StringLiteral, ToFormula, ToStringLiteral, Variable};

pub fn string_vars(elements: &'static str) -> BTreeSet<Cow<str>> {
    elements.split(' ').map(Cow::from).collect()
}

pub fn string_lits(elements: &str) -> BTreeSet<StringLiteral> {
    elements.split(' ').map(|x| x.to_string().to_string_literal()).collect()
}

pub fn vars(elements: &'static str, f: &FormulaFactory) -> BTreeSet<Variable> {
    string_vars(elements).iter().map(|v| v.to_formula(f).as_variable().unwrap()).collect()
}

pub fn vars_list(elements: &'static str, f: &FormulaFactory) -> Vec<Variable> {
    elements.split(' ').map(|v| v.to_formula(f).as_variable().unwrap()).collect()
}

pub fn lits(elements: &str, f: &FormulaFactory) -> BTreeSet<Literal> {
    string_lits(elements).iter().map(|v| v.to_formula(f).as_literal().unwrap()).collect()
}

pub fn lits_list(elements: &str, f: &FormulaFactory) -> Vec<Literal> {
    elements.split(' ').map(|v| v.to_formula(f).as_literal().unwrap()).collect()
}

pub fn hash<H>(element: H) -> u64
where H: Hash {
    let mut hasher = DefaultHasher::new();
    element.hash(&mut hasher);
    hasher.finish()
}

#[allow(clippy::struct_field_names)]
pub struct F {
    pub(crate) f: FormulaFactory,
    pub(crate) g: FormulaFactory,

    // Constants
    pub(crate) TRUE: EncodedFormula,
    pub(crate) FALSE: EncodedFormula,

    // Literals
    pub(crate) A: EncodedFormula,
    pub(crate) B: EncodedFormula,
    pub(crate) C: EncodedFormula,
    pub(crate) D: EncodedFormula,
    pub(crate) X: EncodedFormula,
    pub(crate) Y: EncodedFormula,
    pub(crate) Z: EncodedFormula,
    pub(crate) NA: EncodedFormula,
    pub(crate) NB: EncodedFormula,
    pub(crate) NX: EncodedFormula,
    pub(crate) NY: EncodedFormula,

    // Disjunctions
    pub(crate) OR1: EncodedFormula,
    pub(crate) OR2: EncodedFormula,
    pub(crate) OR3: EncodedFormula,

    // Conjunctions
    pub(crate) AND1: EncodedFormula,
    pub(crate) AND2: EncodedFormula,
    pub(crate) AND3: EncodedFormula,

    // Negations
    pub(crate) NOT1: EncodedFormula,
    pub(crate) NOT2: EncodedFormula,

    // Implications
    pub(crate) IMP1: EncodedFormula,
    pub(crate) IMP2: EncodedFormula,
    pub(crate) IMP3: EncodedFormula,
    pub(crate) IMP4: EncodedFormula,

    // Equivalences
    pub(crate) EQ1: EncodedFormula,
    pub(crate) EQ2: EncodedFormula,
    pub(crate) EQ3: EncodedFormula,
    pub(crate) EQ4: EncodedFormula,

    // PBCs
    pub(crate) PBC1: EncodedFormula,
    pub(crate) PBC2: EncodedFormula,
    pub(crate) PBC3: EncodedFormula,
    pub(crate) PBC4: EncodedFormula,
    pub(crate) PBC5: EncodedFormula,
}

impl F {
    pub(crate) fn new() -> Self {
        let f = FormulaFactory::with_id("");
        let ff = &f;
        let g = FormulaFactory::with_id("g");
        let TRUE = ff.verum();
        let FALSE = ff.falsum();

        let A = ff.variable("a");
        let B = ff.variable("b");
        let C = ff.variable("c");
        let D = ff.variable("d");
        let X = ff.variable("x");
        let Y = ff.variable("y");
        let Z = ff.variable("z");
        let NA = ff.literal("a", false);
        let NB = ff.literal("b", false);
        let NX = ff.literal("x", false);
        let NY = ff.literal("y", false);

        let OR1 = f.or([X, Y]);
        let OR2 = f.or([NX, NY]);
        let AND1 = f.and([A, B]);
        let AND2 = f.and([NA, NB]);

        let OR3 = f.or([AND1, AND2]);
        let AND3 = f.and([OR1, OR2]);

        let NOT1 = f.not(AND1);
        let NOT2 = f.not(OR1);

        let IMP1 = f.implication(A, B);
        let EQ1 = f.equivalence(A, B);
        let IMP2 = f.implication(NA, NB);
        let IMP3 = f.implication(AND1, OR1);

        let EQ5 = f.equivalence(NX, NY);
        let IMP4 = f.implication(EQ1, EQ5);

        let EQ2 = f.equivalence(NA, NB);
        let EQ3 = f.equivalence(AND1, OR1);
        let EQ4 = f.equivalence(IMP1, IMP2);

        let literals: Box<[Literal]> = Box::new([A, B, C].map(|lit| lit.as_literal().unwrap()));
        let coefficients: Box<[i64]> = Box::new([2_i64, -4, 3]);
        let PBC1 = f.pbc(EQ, 2, literals.clone(), coefficients.clone());
        let PBC2 = f.pbc(GT, 2, literals.clone(), coefficients.clone());
        let PBC3 = f.pbc(GE, 2, literals.clone(), coefficients.clone());
        let PBC4 = f.pbc(LT, 2, literals.clone(), coefficients.clone());
        let PBC5 = f.pbc(LE, 2, literals, coefficients);
        Self {
            f,
            g,
            TRUE,
            FALSE,
            A,
            B,
            C,
            D,
            X,
            Y,
            Z,
            NA,
            NB,
            NX,
            NY,
            OR1,
            OR2,
            OR3,
            AND1,
            AND2,
            AND3,
            NOT1,
            NOT2,
            IMP1,
            IMP2,
            IMP3,
            IMP4,
            EQ1,
            EQ2,
            EQ3,
            EQ4,
            PBC1,
            PBC2,
            PBC3,
            PBC4,
            PBC5,
        }
    }
}
