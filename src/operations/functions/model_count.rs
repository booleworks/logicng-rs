use std::collections::BTreeSet;

use num_bigint::BigUint;

use crate::datastructures::Assignment;
use crate::formulas::{EncodedFormula, Formula, FormulaFactory, Variable};
use crate::knowledge_compilation::bdd::orderings::force_ordering;
use crate::knowledge_compilation::bdd::{Bdd, BddKernel};
use crate::knowledge_compilation::dnnf::compile_dnnf;
use crate::operations::transformations::{AdvancedFactorizationConfig, CnfAlgorithm, CnfEncoder, pure_expansion};

#[cfg(feature = "sharp_sat")]
use crate::solver::sharpsat::SharpSatSolver;

/// Algorithms available for model counting.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ModelCountAlgorithm {
    /// Dnnf based model counting.
    Dnnf,
    /// Bdd based model counting. Uses force ordering and initializes Bdd kernel
    /// with `node_size` and `cache_size`.
    Bdd {
        /// Node size of the Bdd kernel.
        node_size: usize,
        /// Cache size of the Bdd kernel.
        cache_size: usize,
    },
    #[cfg(feature = "sharp_sat")]
    /// Model counting using the sharp-sat libary. Requires `sharp_sat` feature to be activiated.
    SharpSat,
}

/// Computes the model count for a given formula.
pub fn count_models(formula: EncodedFormula, algorithm: ModelCountAlgorithm, f: &FormulaFactory) -> BigUint {
    count_models_with_vars(formula, algorithm, &formula.variables(f), f)
}

/// Computes the model count for a given formula and a set of relevant
/// variables. This set can only be a superset of the original formula's
/// variables.
pub fn count_models_with_vars(
    formula: EncodedFormula,
    algorithm: ModelCountAlgorithm,
    relevant_vars: &BTreeSet<Variable>,
    f: &FormulaFactory,
) -> BigUint {
    let vars = formula.variables(f);
    assert!(vars.is_subset(relevant_vars), "Expected variables to contain all of the formula's variables");

    if vars.is_empty() {
        return if formula.is_verum() { BigUint::from(1_usize) } else { BigUint::from(0_usize) };
    }

    let mut cnf_encoder =
        CnfEncoder::new(CnfAlgorithm::Advanced(AdvancedFactorizationConfig::default().fallback_algorithm(CnfAlgorithm::Tseitin)));
    let cnf = cnf_encoder.transform(pure_expansion(formula, f), f);
    let mut count = count_formula(cnf, algorithm, f);

    let dont_care_vars = relevant_vars.difference(&cnf.variables(f)).count();
    let factor = BigUint::from(2_usize).pow(u32::try_from(dont_care_vars).expect("Too many dont-care variables"));
    count *= factor;
    count
}

/// Computes the model count for a given set of formulas (interpreted as conjunction).
pub fn count_models_conjunction(formulas: &[EncodedFormula], algorithm: ModelCountAlgorithm, f: &FormulaFactory) -> BigUint {
    let vars = formulas.iter().fold(BTreeSet::default(), |mut akk, formula| {
        akk.extend((*formula.variables(f)).clone());
        akk
    });
    count_models_internal(formulas, algorithm, &vars, &vars, f)
}

/// Computes the model count for a given set of formulas (interpreted as conjunction)
/// and a set of relevant variables.  This set can only be a superset of the original
/// formulas' variables.
pub fn count_models_conjunction_with_vars<I>(
    formulas: &[EncodedFormula],
    algorithm: ModelCountAlgorithm,
    relevant_vars: &BTreeSet<Variable>,
    f: &FormulaFactory,
) -> BigUint {
    let vars = formulas.iter().fold(BTreeSet::default(), |mut akk, formula| {
        akk.extend((*formula.variables(f)).clone());
        akk
    });
    count_models_internal(formulas, algorithm, relevant_vars, &vars, f)
}

fn count_models_internal(
    formulas: &[EncodedFormula],
    algorithm: ModelCountAlgorithm,
    relevant_vars: &BTreeSet<Variable>,
    all_vars: &BTreeSet<Variable>,
    f: &FormulaFactory,
) -> BigUint {
    assert!(all_vars.is_subset(relevant_vars), "Expected variables to contain all of the formulas' variables");

    if all_vars.is_empty() {
        let all_verum = formulas.iter().all(|formula| formula.is_verum());
        return if all_verum { BigUint::from(1_usize) } else { BigUint::from(0_usize) };
    }

    let cnfs = encode_as_cnf(formulas, f);
    let (backbone_variables, simplified) = simplify(&cnfs, f);
    let count = count(&simplified, algorithm, f);
    let factor = dont_care_factor(backbone_variables, &simplified, relevant_vars, f);
    count * factor
}

fn count(formulas: &[EncodedFormula], algorithm: ModelCountAlgorithm, f: &FormulaFactory) -> BigUint {
    count_formula(f.and(formulas), algorithm, f)
}

fn count_formula(formula: EncodedFormula, algorithm: ModelCountAlgorithm, f: &FormulaFactory) -> BigUint {
    match algorithm {
        ModelCountAlgorithm::Dnnf => {
            let dnnf = compile_dnnf(formula, f);
            crate::knowledge_compilation::dnnf::count(&dnnf, f)
        }
        ModelCountAlgorithm::Bdd { node_size, cache_size } => {
            let mut kernel = BddKernel::new_with_var_ordering(&force_ordering(formula, f), node_size, cache_size);
            Bdd::from_formula(formula, f, &mut kernel).model_count(&mut kernel)
        }
        #[cfg(feature = "sharp_sat")]
        ModelCountAlgorithm::SharpSat => {
            let mut solver = SharpSatSolver::new();
            solver.add_cnf(formula, f);
            solver.solve()
        }
    }
}

fn dont_care_factor(
    backbone_variables: BTreeSet<Variable>,
    simplified: &[EncodedFormula],
    relevant_vars: &BTreeSet<Variable>,
    f: &FormulaFactory,
) -> BigUint {
    let used_vars = simplified.iter().fold(backbone_variables, |mut akk, formula| {
        akk.extend((*formula.variables(f)).clone());
        akk
    });
    let dont_care_vars = relevant_vars.difference(&used_vars).count();
    BigUint::from(2_usize).pow(u32::try_from(dont_care_vars).expect("Too many dont-care variables"))
}

fn encode_as_cnf(formulas: &[EncodedFormula], f: &FormulaFactory) -> Vec<EncodedFormula> {
    let mut cnf_encoder =
        CnfEncoder::new(CnfAlgorithm::Advanced(AdvancedFactorizationConfig::default().fallback_algorithm(CnfAlgorithm::Tseitin)));

    formulas.iter().map(|&formula| pure_expansion(formula, f)).map(|formula| cnf_encoder.transform(formula, f)).collect()
}

fn simplify(formulas: &[EncodedFormula], f: &FormulaFactory) -> (BTreeSet<Variable>, Vec<EncodedFormula>) {
    let mut simple_backbone = Assignment::from_literals(&[]);
    let mut backbone_variables = BTreeSet::new();
    for formula in formulas {
        if let Formula::Lit(lit) = formula.unpack(f) {
            simple_backbone.add_literal(lit);
            backbone_variables.insert(lit.variable());
        }
    }
    let mut simplified = Vec::new();
    for &formula in formulas {
        let restrict = f.restrict(formula, &simple_backbone);
        if !restrict.is_verum() {
            simplified.push(restrict);
        }
    }
    (backbone_variables, simplified)
}

#[cfg(test)]
mod tests {
    mod dnnf {
        use crate::formulas::FormulaFactory;
        use crate::operations::functions::{ModelCountAlgorithm, count_models};
        use crate::util::read_model_counting_examples::{read_cnf, read_normal};
        use num_bigint::BigUint;

        #[test]
        fn test_verum() {
            let f = FormulaFactory::new();
            let count = count_models(f.verum(), ModelCountAlgorithm::Dnnf, &f);
            assert_eq!(count, BigUint::from(1_u64));
        }

        #[test]
        fn test_falsum() {
            let f = FormulaFactory::new();
            let count = count_models(f.falsum(), ModelCountAlgorithm::Dnnf, &f);
            assert_eq!(count, BigUint::from(0_u64));
        }

        #[test]
        fn test_normal_formulas() {
            let f = FormulaFactory::new();
            let tests = read_normal(&f);
            for (formula, expected) in tests {
                let count = count_models(formula, ModelCountAlgorithm::Dnnf, &f);
                assert_eq!(count, expected);
            }
        }

        #[test]
        fn test_cnf_formulas() {
            let f = FormulaFactory::new();
            let tests = read_cnf(&f);
            for (formula, expected) in tests {
                let count = count_models(formula, ModelCountAlgorithm::Dnnf, &f);
                assert_eq!(count, expected);
            }
        }
    }

    mod bdd {
        use crate::formulas::FormulaFactory;
        use crate::operations::functions::{ModelCountAlgorithm, count_models};
        use crate::util::read_model_counting_examples::{read_cnf, read_normal};
        use num_bigint::BigUint;

        #[test]
        fn test_verum() {
            let f = FormulaFactory::new();
            let count = count_models(f.verum(), ModelCountAlgorithm::Bdd { node_size: 1000, cache_size: 1000 }, &f);
            assert_eq!(count, BigUint::from(1_u64));
        }

        #[test]
        fn test_falsum() {
            let f = FormulaFactory::new();
            let count = count_models(f.falsum(), ModelCountAlgorithm::Bdd { node_size: 1000, cache_size: 1000 }, &f);
            assert_eq!(count, BigUint::from(0_u64));
        }

        #[test]
        fn test_normal_formulas() {
            let f = FormulaFactory::new();
            let tests = read_normal(&f);
            for (formula, expected) in tests {
                let count = count_models(formula, ModelCountAlgorithm::Bdd { node_size: 1000, cache_size: 1000 }, &f);
                assert_eq!(count, expected);
            }
        }

        #[test]
        fn test_cnf_formulas() {
            let f = FormulaFactory::new();
            let tests = read_cnf(&f);
            for (formula, expected) in tests {
                let count = count_models(formula, ModelCountAlgorithm::Bdd { node_size: 1000, cache_size: 1000 }, &f);
                assert_eq!(count, expected);
            }
        }

        #[cfg(feature = "sharp_sat")]
        mod sharp_sat {
            use crate::formulas::FormulaFactory;
            use crate::operations::functions::{ModelCountAlgorithm, count_models};
            use crate::util::read_model_counting_examples::{read_cnf, read_normal};
            use num_bigint::BigUint;

            #[test]
            fn test_verum() {
                let f = FormulaFactory::new();
                let count = count_models(f.verum(), ModelCountAlgorithm::SharpSat, &f);
                assert_eq!(count, BigUint::from(1_u64));
            }

            #[test]
            fn test_falsum() {
                let f = FormulaFactory::new();
                let count = count_models(f.falsum(), ModelCountAlgorithm::SharpSat, &f);
                assert_eq!(count, BigUint::from(0_u64));
            }

            #[test]
            fn test_normal_formulas() {
                let f = FormulaFactory::new();
                let tests = read_normal(&f);
                for (formula, expected) in tests {
                    let count = count_models(formula, ModelCountAlgorithm::SharpSat, &f);
                    assert_eq!(count, expected);
                }
            }

            #[test]
            fn test_cnf_formulas() {
                let f = FormulaFactory::new();
                let tests = read_cnf(&f);
                for (formula, expected) in tests {
                    let count = count_models(formula, ModelCountAlgorithm::SharpSat, &f);
                    assert_eq!(count, expected);
                }
            }
        }
    }
}
