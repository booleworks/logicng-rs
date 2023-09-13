use crate::datastructures::Assignment;
use crate::formulas::{EncodedFormula, Formula, FormulaFactory, FormulaType, Literal};
use crate::operations::transformations::cnf::factorization::factorization_cnf;
use crate::util::exceptions::panic_unexpected_formula_type;

use super::PGState;

pub(super) fn pg_on_formula(
    formula: EncodedFormula,
    f: &FormulaFactory,
    boundary_for_factorization: u64,
    state: &mut PGState,
) -> EncodedFormula {
    let nnf = f.nnf_of(formula);
    if nnf.is_cnf(f) {
        nnf
    } else if nnf.number_of_atoms(f) < boundary_for_factorization {
        factorization_cnf(nnf, f)
    } else {
        let pg = compute_transformation(nnf, f, state);
        let top_level = Assignment::from_lit(state.variable[&nnf]);
        f.restrict(pg, &top_level)
    }
}

fn compute_transformation(formula: EncodedFormula, f: &FormulaFactory, state: &mut PGState) -> EncodedFormula {
    use FormulaType::{And, Lit, Or};
    match formula.formula_type() {
        Or | And => {
            #[allow(clippy::cast_possible_truncation)]
            let mut nops = Vec::with_capacity(formula.number_of_atoms(f) as usize + 1);
            nops.push(compute_pos_polarity(formula, f, state));
            formula.operands(f).iter().for_each(|&op| nops.push(compute_transformation(op, f, state)));
            f.and(&nops)
        }
        Lit(_) => f.verum(),
        _ => panic_unexpected_formula_type(formula, Some(f)),
    }
}

fn compute_pos_polarity(formula: EncodedFormula, f: &FormulaFactory, state: &mut PGState) -> EncodedFormula {
    let cached = state.formula.get(&formula).copied();
    if let Some(result) = cached {
        return result;
    }
    let pg_var = pg_variable(formula, f, state);
    let result = match formula.unpack(f) {
        Formula::And(ops) => {
            let mut nops = Vec::with_capacity(formula.number_of_operands(f));
            for op in ops {
                let op_pg = pg_variable(op, f, state);
                nops.push(f.clause(&[pg_var.negate(), op_pg]));
            }
            f.and(&nops)
        }
        Formula::Or(ops) => {
            let mut nops = Vec::with_capacity(formula.number_of_operands(f) + 1);
            nops.push(pg_var.negate());
            ops.for_each(|op| nops.push(pg_variable(op, f, state)));
            f.clause(&nops)
        }
        _ => panic_unexpected_formula_type(formula, Some(f)),
    };
    state.formula.insert(formula, result);
    result
}

fn pg_variable(formula: EncodedFormula, f: &FormulaFactory, state: &mut PGState) -> Literal {
    if let Some(lit) = formula.as_literal() {
        lit
    } else if let Some(lit) = state.variable.get(&formula).copied() {
        lit
    } else {
        let lit = f.new_cnf_variable().pos_lit();
        state.variable.insert(formula, lit);
        lit
    }
}

#[allow(non_snake_case)]
#[cfg(test)]
mod tests {
    use crate::formulas::{ToFormula, Variable};
    use crate::operations::transformations::cnf::CnfAlgorithm;
    use crate::operations::transformations::cnf::CnfAlgorithm::PlaistedGreenbaum;
    use crate::operations::transformations::CnfEncoder;
    use crate::solver::functions::{enumerate_models_for_formula_with_config, ModelEnumerationConfig};
    use crate::util::test_util::F;

    use super::*;

    fn pg_transformer() -> CnfEncoder {
        CnfEncoder::new(CnfAlgorithm::PlaistedGreenbaumWithBoundary(0))
    }

    fn test_formula(f: &FormulaFactory, formula: EncodedFormula) {
        let mut transformer = pg_transformer();
        let pg = transformer.transform(formula, f);
        assert!(pg.is_cnf(f));
        let vars: Box<[Variable]> = formula.variables(f).iter().copied().collect();
        let config = ModelEnumerationConfig::default().variables(vars);
        let original_models = enumerate_models_for_formula_with_config(formula, f, &config);
        let pg_models = enumerate_models_for_formula_with_config(pg, f, &config);
        assert_eq!(original_models.len(), pg_models.len());
    }

    #[test]
    fn test_constants() {
        let F = F::new();
        let f = &F.f;
        let mut pg = pg_transformer();
        assert_eq!(pg.transform(F.TRUE, f), F.TRUE);
        assert_eq!(pg.transform(F.FALSE, f), F.FALSE);
    }

    #[test]
    fn test_literals() {
        let F = F::new();
        let f = &F.f;
        let mut pg = pg_transformer();
        assert_eq!(pg.transform(F.A, f), F.A);
        assert_eq!(pg.transform(F.NA, f), F.NA);
    }

    #[test]
    fn test_binary_operators() {
        let F = F::new();
        let f = &F.f;
        test_formula(f, F.IMP1);
        test_formula(f, F.IMP2);
        test_formula(f, F.IMP3);
        test_formula(f, F.EQ1);
        test_formula(f, F.EQ2);
        test_formula(f, F.EQ3);
        test_formula(f, F.EQ4);
    }

    #[test]
    fn test_nary_operators() {
        let F = F::new();
        let f = &F.f;
        let mut pg = pg_transformer();
        assert_eq!(pg.transform(F.AND1, f), F.AND1);
        assert_eq!(pg.transform(F.OR1, f), F.OR1);
        let f1 = "(a & b & x) | (c & d & ~y)".to_formula(f);
        let f2 = "(a & b & x) | (c & d & ~y) | (~z | (c & d & ~y)) ".to_formula(f);
        let f3 = "a | b | (~x & ~y)".to_formula(f);
        test_formula(f, f1);
        test_formula(f, f2);
        test_formula(f, f3);
    }

    #[test]
    fn test_not_nary() {
        let f = &FormulaFactory::new();
        let f1 = "~(~a | b)".to_formula(f);
        let f2 = "~((a | b) | ~(x | y))".to_formula(f);
        let f3 = "~(a & b | ~a & ~b)".to_formula(f);
        let f4 = "~(~(a | b) & ~(x | y) | (a | b) & (x | y))".to_formula(f);
        let f5 = "~(a & b & ~x & ~y)".to_formula(f);
        let f6 = "~(a | b | ~x | ~y)".to_formula(f);
        let f7 = "~(a & b) & (c | (a & b))".to_formula(f);
        test_formula(f, f1);
        test_formula(f, f2);
        test_formula(f, f3);
        test_formula(f, f4);
        test_formula(f, f5);
        test_formula(f, f6);
        test_formula(f, f7);
    }

    #[test]
    fn test_not_binary() {
        let f = &FormulaFactory::new();
        let f1 = "~(~(a | b) => ~(x | y))".to_formula(f);
        let f2 = "~(a <=> b)".to_formula(f);
        let f3 = "~(~(a | b) <=> ~(x | y))".to_formula(f);
        test_formula(f, f1);
        test_formula(f, f2);
        test_formula(f, f3);
    }

    #[test]
    fn test_cc() {
        let f = &FormulaFactory::with_id("");
        let mut pg = pg_transformer();
        assert_eq!(pg.transform("a <=> (1 * b <= 1)".to_formula(f), f), "a".to_formula(f));
        assert_eq!(pg.transform("~(1 * b <= 1)".to_formula(f), f), "$false".to_formula(f));
        assert_eq!(pg.transform("(1 * b + 1 * c + 1 * d <= 1)".to_formula(f), f), "(~b | ~c) & (~b | ~d) & (~c | ~d)".to_formula(f));
        assert_eq!(pg.transform("~(1 * b + 1 * c + 1 * d <= 1)".to_formula(f), f),"(d | @RESERVED__CC_1 | @RESERVED__CC_4) & (~@RESERVED__CC_3 | @RESERVED__CC_1 | @RESERVED__CC_4) & (~@RESERVED__CC_3 | d | @RESERVED__CC_4) & (~@RESERVED__CC_4 | @RESERVED__CC_0) & (~@RESERVED__CC_2 | @RESERVED__CC_0) & (~@RESERVED__CC_4 | ~@RESERVED__CC_2) & (c | @RESERVED__CC_3 | @RESERVED__CC_5) & (b | @RESERVED__CC_3 | @RESERVED__CC_5) & (b | c | @RESERVED__CC_5) & (~@RESERVED__CC_5 | @RESERVED__CC_2) & ~@RESERVED__CC_0".to_formula(f));
    }

    #[test]
    fn test_formulas() {
        let f = &FormulaFactory::with_id("");
        let f1 = "(a | b) => c".to_formula(f);
        let f2 = "~x & ~y".to_formula(f);
        let f3 = "d & ((a | b) => c)".to_formula(f);
        let f4 = "d & ((a | b) => c) | ~x & ~y".to_formula(f);
        let mut pg = pg_transformer();
        let pg1 = pg.transform(f1, f).to_string(f);
        let pg2 = pg.transform(f2, f).to_string(f);
        let pg3 = pg.transform(f3, f).to_string(f);
        let pg4 = pg.transform(f4, f).to_string(f);
        let expected1 = "(@RESERVED__CNF_1 | c) & (~@RESERVED__CNF_1 | ~a) & (~@RESERVED__CNF_1 | ~b)".to_formula(f);
        let expected2 = "~x & ~y".to_formula(f);
        let expected3 =
            "d & @RESERVED__CNF_0 & (~@RESERVED__CNF_0 | @RESERVED__CNF_1 | c) & (~@RESERVED__CNF_1 | ~a) & (~@RESERVED__CNF_1 | ~b)"
                .to_formula(f);
        let expected4 =  "(@RESERVED__CNF_2 | @RESERVED__CNF_4) & (~@RESERVED__CNF_2 | d) & (~@RESERVED__CNF_2 | @RESERVED__CNF_0) & (~@RESERVED__CNF_0 | @RESERVED__CNF_1 | c) & (~@RESERVED__CNF_1 | ~a) & (~@RESERVED__CNF_1 | ~b) & (~@RESERVED__CNF_4 | ~x) & (~@RESERVED__CNF_4 | ~y)".to_formula(f);
        assert_eq!(pg1, expected1.to_string(f));
        assert_eq!(pg2, expected2.to_string(f));
        assert_eq!(pg3, expected3.to_string(f));
        assert_eq!(pg4, expected4.to_string(f));
        test_formula(f, f1);
        test_formula(f, f2);
        test_formula(f, f3);
        test_formula(f, f4);
    }

    #[test]
    fn test_factorization() {
        let f = &FormulaFactory::with_id("");
        let f1 = "(a | b) => c".to_formula(f);
        let f2 = "~x & ~y".to_formula(f);
        let f3 = "d & ((a | b) => c)".to_formula(f);
        let f4 = "d & ((a | b) => c) | ~x & ~y".to_formula(f);
        let mut cnf_transformator = CnfEncoder::new(PlaistedGreenbaum);
        assert_eq!(cnf_transformator.transform(f1, f), "(~a | c) & (~b | c)".to_formula(f));
        assert_eq!(cnf_transformator.transform(f2, f), f2);
        assert_eq!(cnf_transformator.transform(f3, f), "d & (~a | c) & (~b | c)".to_formula(f));
        assert_eq!(
            cnf_transformator.transform(f4, f),
            "(d | ~x) & (~a | c | ~x) & (~b | c | ~x) & (d | ~y) & (~a | c | ~y) & (~b | c | ~y)".to_formula(f)
        );
    }
}
