use crate::formulas::operation_cache::{FormulaCache, OperationCache};
use crate::formulas::{EncodedFormula, Literal, Variable};
use std::collections::BTreeSet;
use std::sync::Arc;

pub struct FormulaFactoryCaches {
    pub number_of_atoms: OperationCache<u64>,
    pub number_of_nodes: OperationCache<u64>,
    pub formula_depth: OperationCache<u64>,
    pub variables: OperationCache<Arc<BTreeSet<Variable>>>,
    pub literals: OperationCache<Arc<BTreeSet<Literal>>>,
    pub sub_nodes: OperationCache<Arc<[EncodedFormula]>>,
    pub cc_encoding: FormulaCache<Arc<[EncodedFormula]>>,
    pub pbc_encoding: FormulaCache<Arc<[EncodedFormula]>>,
    pub nnf: OperationCache<EncodedFormula>,
    pub dnf: OperationCache<EncodedFormula>,
    pub factorization_cnf: OperationCache<EncodedFormula>,
    pub sat: OperationCache<bool>,
    pub is_nnf: OperationCache<bool>,
    pub is_dnf: OperationCache<bool>,
    pub is_cnf: OperationCache<()>,
    pub contains_pbc: OperationCache<bool>,
    pub backbone_simps: OperationCache<EncodedFormula>,
}

impl FormulaFactoryCaches {
    pub fn new() -> Self {
        Self {
            number_of_atoms: OperationCache::new(),
            number_of_nodes: OperationCache::new(),
            formula_depth: OperationCache::new(),
            variables: OperationCache::new(),
            literals: OperationCache::new(),
            sub_nodes: OperationCache::new(),
            cc_encoding: FormulaCache::new(),
            pbc_encoding: FormulaCache::new(),
            nnf: OperationCache::new(),
            dnf: OperationCache::new(),
            sat: OperationCache::new(),
            is_nnf: OperationCache::new(),
            is_dnf: OperationCache::new(),
            is_cnf: OperationCache::new(),
            contains_pbc: OperationCache::new(),
            factorization_cnf: OperationCache::new(),
            backbone_simps: OperationCache::new(),
        }
    }
}

impl Default for FormulaFactoryCaches {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod test {
    mod config {
        use crate::formulas::{FormulaFactory, ToFormula};
        use crate::operations::{functions, predicates, transformations};

        #[test]
        fn enable_number_of_atoms() {
            let mut f = FormulaFactory::new();
            f.config.caches.number_of_atoms = true;

            let formula1 = "a & (b | c)".to_formula(&f);
            let formula2 = "d & (b | c)".to_formula(&f);

            let number1 = functions::number_of_atoms(formula1, &f);
            assert_eq!(number1, 3);
            assert_eq!(f.caches.number_of_atoms.len(), 2);

            let number2 = functions::number_of_atoms(formula2, &f);
            assert_eq!(number2, 3);
            assert_eq!(f.caches.number_of_atoms.len(), 3);
        }

        #[test]
        fn disable_number_of_atoms() {
            let mut f = FormulaFactory::new();
            f.config.caches.number_of_atoms = false;

            let formula1 = "a & (b | c)".to_formula(&f);
            let formula2 = "d & (b | c)".to_formula(&f);

            let number1 = functions::number_of_atoms(formula1, &f);
            assert_eq!(number1, 3);
            assert_eq!(f.caches.number_of_atoms.len(), 0);

            let number2 = functions::number_of_atoms(formula2, &f);
            assert_eq!(number2, 3);
            assert_eq!(f.caches.number_of_atoms.len(), 0);
        }

        #[test]
        fn enable_number_of_nodes() {
            let mut f = FormulaFactory::new();
            f.config.caches.number_of_nodes = true;

            let formula1 = "a & (b | c)".to_formula(&f);
            let formula2 = "d & (b | c)".to_formula(&f);

            let number1 = functions::number_of_nodes(formula1, &f);
            assert_eq!(number1, 5);
            assert_eq!(f.caches.number_of_nodes.len(), 2);

            let number2 = functions::number_of_nodes(formula2, &f);
            assert_eq!(number2, 5);
            assert_eq!(f.caches.number_of_nodes.len(), 3);
        }

        #[test]
        fn disable_number_of_nodes() {
            let mut f = FormulaFactory::new();
            f.config.caches.number_of_nodes = false;

            let formula1 = "a & (b | c)".to_formula(&f);
            let formula2 = "d & (b | c)".to_formula(&f);

            let number1 = functions::number_of_nodes(formula1, &f);
            assert_eq!(number1, 5);
            assert_eq!(f.caches.number_of_nodes.len(), 0);

            let number2 = functions::number_of_nodes(formula2, &f);
            assert_eq!(number2, 5);
            assert_eq!(f.caches.number_of_nodes.len(), 0);
        }

        #[test]
        fn enable_formula_depth() {
            let mut f = FormulaFactory::new();
            f.config.caches.formula_depth = true;

            let formula1 = "a & (b | c)".to_formula(&f);
            let formula2 = "d & (b | c)".to_formula(&f);

            let number1 = functions::formula_depth(formula1, &f);
            assert_eq!(number1, 2);
            assert_eq!(f.caches.formula_depth.len(), 5);

            let number2 = functions::formula_depth(formula2, &f);
            assert_eq!(number2, 2);
            assert_eq!(f.caches.formula_depth.len(), 7);
        }

        #[test]
        fn disable_formula_depth() {
            let mut f = FormulaFactory::new();
            f.config.caches.formula_depth = false;

            let formula1 = "a & (b | c)".to_formula(&f);
            let formula2 = "d & (b | c)".to_formula(&f);

            let number1 = functions::formula_depth(formula1, &f);
            assert_eq!(number1, 2);
            assert_eq!(f.caches.formula_depth.len(), 0);

            let number2 = functions::formula_depth(formula2, &f);
            assert_eq!(number2, 2);
            assert_eq!(f.caches.formula_depth.len(), 0);
        }

        #[test]
        fn enable_variables() {
            let mut f = FormulaFactory::new();
            f.config.caches.variables = true;

            let formula1 = "a & (b | c)".to_formula(&f);
            let formula2 = "d & (b | c)".to_formula(&f);

            let vars1 = functions::variables(formula1, &f);
            assert_eq!(vars1.len(), 3);
            assert_eq!(f.caches.variables.len(), 5);

            let vars2 = functions::variables(formula2, &f);
            assert_eq!(vars2.len(), 3);
            assert_eq!(f.caches.variables.len(), 7);
        }

        #[test]
        fn disable_variables() {
            let mut f = FormulaFactory::new();
            f.config.caches.variables = false;

            let formula1 = "a & (b | c)".to_formula(&f);
            let formula2 = "d & (b | c)".to_formula(&f);

            let vars1 = functions::variables(formula1, &f);
            assert_eq!(vars1.len(), 3);
            assert_eq!(f.caches.variables.len(), 0);

            let vars2 = functions::variables(formula2, &f);
            assert_eq!(vars2.len(), 3);
            assert_eq!(f.caches.variables.len(), 0);
        }

        #[test]
        fn enable_literals() {
            let mut f = FormulaFactory::new();
            f.config.caches.literals = true;

            let formula1 = "a & (b | ~c)".to_formula(&f);
            let formula2 = "d & (b | ~c)".to_formula(&f);

            let lits1 = functions::literals(formula1, &f);
            assert_eq!(lits1.len(), 3);
            assert_eq!(f.caches.literals.len(), 5);

            let lits2 = functions::literals(formula2, &f);
            assert_eq!(lits2.len(), 3);
            assert_eq!(f.caches.literals.len(), 7);
        }

        #[test]
        fn disable_literals() {
            let mut f = FormulaFactory::new();
            f.config.caches.literals = false;

            let formula1 = "a & (b | ~c)".to_formula(&f);
            let formula2 = "d & (b | ~c)".to_formula(&f);

            let lits1 = functions::literals(formula1, &f);
            assert_eq!(lits1.len(), 3);
            assert_eq!(f.caches.literals.len(), 0);

            let lits2 = functions::literals(formula2, &f);
            assert_eq!(lits2.len(), 3);
            assert_eq!(f.caches.literals.len(), 0);
        }

        #[test]
        fn enable_sub_nodes() {
            let mut f = FormulaFactory::new();
            f.config.caches.sub_nodes = true;

            let formula1 = "a & (b | ~c)".to_formula(&f);
            let formula2 = "d & (b | ~c)".to_formula(&f);

            let nodes1 = functions::sub_nodes(formula1, &f);
            assert_eq!(nodes1.len(), 5);
            assert_eq!(f.caches.sub_nodes.len(), 5);

            let nodes2 = functions::sub_nodes(formula2, &f);
            assert_eq!(nodes2.len(), 5);
            assert_eq!(f.caches.sub_nodes.len(), 7);
        }

        #[test]
        fn disable_sub_nodes() {
            let mut f = FormulaFactory::new();
            f.config.caches.sub_nodes = false;

            let formula1 = "a & (b | ~c)".to_formula(&f);
            let formula2 = "d & (b | ~c)".to_formula(&f);

            let nodes1 = functions::sub_nodes(formula1, &f);
            assert_eq!(nodes1.len(), 5);
            assert_eq!(f.caches.sub_nodes.len(), 0);

            let nodes2 = functions::sub_nodes(formula2, &f);
            assert_eq!(nodes2.len(), 5);
            assert_eq!(f.caches.sub_nodes.len(), 0);
        }

        #[test]
        fn enable_cc_encoding() {
            let mut f = FormulaFactory::new();
            f.config.caches.cc_encoding = true;

            let formula1 = "a + b = 1".to_formula(&f);
            let formula2 = "a + c = 1".to_formula(&f);

            formula1.as_cc(&f).unwrap().encode(&f);
            assert_eq!(f.caches.cc_encoding.len(), 1);

            formula2.as_cc(&f).unwrap().encode(&f);
            assert_eq!(f.caches.cc_encoding.len(), 2);

            formula1.as_cc(&f).unwrap().encode(&f);
            assert_eq!(f.caches.cc_encoding.len(), 2);
        }

        #[test]
        fn disable_cc_encoding() {
            let mut f = FormulaFactory::new();
            f.config.caches.cc_encoding = false;

            let formula1 = "a + b = 1".to_formula(&f);
            let formula2 = "a + c = 1".to_formula(&f);

            formula1.as_cc(&f).unwrap().encode(&f);
            assert_eq!(f.caches.cc_encoding.len(), 0);

            formula2.as_cc(&f).unwrap().encode(&f);
            assert_eq!(f.caches.cc_encoding.len(), 0);

            formula1.as_cc(&f).unwrap().encode(&f);
            assert_eq!(f.caches.cc_encoding.len(), 0);
        }

        #[test]
        fn enable_pbc_encoding() {
            let mut f = FormulaFactory::new();
            f.config.caches.pbc_encoding = true;

            let formula1 = "2 * a + b = 1".to_formula(&f);
            let formula2 = "2 * a + c = 1".to_formula(&f);

            formula1.as_pbc(&f).unwrap().encode(&f);
            assert_eq!(f.caches.pbc_encoding.len(), 1);

            formula2.as_pbc(&f).unwrap().encode(&f);
            assert_eq!(f.caches.pbc_encoding.len(), 2);

            formula1.as_pbc(&f).unwrap().encode(&f);
            assert_eq!(f.caches.pbc_encoding.len(), 2);
        }

        #[test]
        fn disable_pbc_encoding() {
            let mut f = FormulaFactory::new();
            f.config.caches.pbc_encoding = false;

            let formula1 = "2 * a + b = 1".to_formula(&f);
            let formula2 = "2 * a + c = 1".to_formula(&f);

            formula1.as_pbc(&f).unwrap().encode(&f);
            assert_eq!(f.caches.pbc_encoding.len(), 0);

            formula2.as_pbc(&f).unwrap().encode(&f);
            assert_eq!(f.caches.pbc_encoding.len(), 0);

            formula1.as_pbc(&f).unwrap().encode(&f);
            assert_eq!(f.caches.pbc_encoding.len(), 0);
        }

        #[test]
        fn enable_nnf() {
            let mut f = FormulaFactory::new();
            f.config.caches.nnf = true;

            let formula1 = "~(b | ~a)".to_formula(&f);
            let formula2 = "~(b | ~(a & c))".to_formula(&f);

            transformations::nnf(formula1, &f);
            assert_eq!(f.caches.nnf.len(), 1);

            transformations::nnf(formula2, &f);
            assert!(f.caches.nnf.len() > 1);

            let s = f.caches.nnf.len();
            transformations::nnf(formula1, &f);
            assert_eq!(f.caches.nnf.len(), s);
        }

        #[test]
        fn disable_nnf() {
            let mut f = FormulaFactory::new();
            f.config.caches.nnf = false;

            let formula1 = "~(b | ~a)".to_formula(&f);
            let formula2 = "~(b | ~(a & c))".to_formula(&f);

            transformations::nnf(formula1, &f);
            assert_eq!(f.caches.nnf.len(), 0);

            transformations::nnf(formula2, &f);
            assert_eq!(f.caches.nnf.len(), 0);

            transformations::nnf(formula1, &f);
            assert_eq!(f.caches.nnf.len(), 0);
        }

        #[test]
        fn enable_dnf() {
            let mut f = FormulaFactory::new();
            f.config.caches.dnf = true;

            let formula1 = "~(b => ~a)".to_formula(&f);

            transformations::factorization_dnf(formula1, &f);
            assert!(f.caches.dnf.len() > 0);
        }

        #[test]
        fn disable_dnf() {
            let mut f = FormulaFactory::new();
            f.config.caches.dnf = false;

            let formula1 = "~(b => ~a)".to_formula(&f);

            transformations::factorization_dnf(formula1, &f);
            assert_eq!(f.caches.dnf.len(), 0);
        }

        #[test]
        fn enable_factorization_cnf() {
            let mut f = FormulaFactory::new();
            f.config.caches.factorization_cnf = true;

            let formula1 = "~(b => ~a)".to_formula(&f);

            transformations::CnfEncoder::new(transformations::CnfAlgorithm::Factorization).transform(formula1, &f);
            assert!(f.caches.factorization_cnf.len() > 0);
        }

        #[test]
        fn disable_factorization_cnf() {
            let mut f = FormulaFactory::new();
            f.config.caches.factorization_cnf = false;

            let formula1 = "~(b => ~a)".to_formula(&f);

            transformations::CnfEncoder::new(transformations::CnfAlgorithm::Factorization).transform(formula1, &f);
            assert_eq!(f.caches.factorization_cnf.len(), 0);
        }

        #[test]
        fn enable_sat() {
            let mut f = FormulaFactory::new();
            f.config.caches.sat = true;

            let formula1 = "~(b => ~a)".to_formula(&f);
            let formula2 = "~(b => (a | b))".to_formula(&f);
            let formula3 = "b => ~a".to_formula(&f);

            let sat1 = predicates::is_sat(formula1, &f);
            assert!(sat1);
            assert_eq!(f.caches.sat.len(), 1);

            let sat2 = predicates::is_tautology(formula2, &f);
            assert!(!sat2);
            assert_eq!(f.caches.sat.len(), 2);

            let sat3 = predicates::is_tautology(formula3, &f);
            assert!(!sat3);
            assert_eq!(f.caches.sat.len(), 2);
        }

        #[test]
        fn disable_sat() {
            let mut f = FormulaFactory::new();
            f.config.caches.sat = false;

            let formula1 = "~(b => ~a)".to_formula(&f);
            let formula2 = "~(b => (a | b))".to_formula(&f);
            let formula3 = "b => ~a".to_formula(&f);

            let sat1 = predicates::is_sat(formula1, &f);
            assert!(sat1);
            assert_eq!(f.caches.sat.len(), 0);

            let sat2 = predicates::is_tautology(formula2, &f);
            assert!(!sat2);
            assert_eq!(f.caches.sat.len(), 0);

            let sat3 = predicates::is_tautology(formula3, &f);
            assert!(!sat3);
            assert_eq!(f.caches.sat.len(), 0);
        }

        #[test]
        fn enable_is_nnf() {
            let mut f = FormulaFactory::new();
            f.config.caches.is_nnf = true;

            let formula1 = "~(a | b)".to_formula(&f);

            assert!(!predicates::is_nnf(formula1, &f));
            let s1 = f.caches.is_nnf.len();
            assert!(s1 > 0);

            let formula2 = transformations::nnf(formula1, &f);
            let s2 = f.caches.is_nnf.len();
            assert!(s2 > s1);
            assert!(predicates::is_nnf(formula2, &f));
            assert_eq!(f.caches.is_nnf.len(), s2);
        }

        #[test]
        fn disable_is_nnf() {
            let mut f = FormulaFactory::new();
            f.config.caches.is_nnf = false;

            let formula1 = "~(a | b)".to_formula(&f);

            assert!(!predicates::is_nnf(formula1, &f));
            assert_eq!(f.caches.is_nnf.len(), 0);

            let formula2 = transformations::nnf(formula1, &f);
            assert_eq!(f.caches.is_nnf.len(), 0);
            assert!(predicates::is_nnf(formula2, &f));
            assert_eq!(f.caches.is_nnf.len(), 0);
        }

        #[test]
        fn enable_is_dnf() {
            let mut f = FormulaFactory::new();
            f.config.caches.is_dnf = true;

            let formula1 = "~(a | b)".to_formula(&f);

            assert!(!predicates::is_dnf(formula1, &f));
            let s1 = f.caches.is_dnf.len();
            assert!(s1 > 0);

            let formula2 = transformations::factorization_dnf(formula1, &f);
            let s2 = f.caches.is_dnf.len();
            assert!(s2 > s1);
            assert!(predicates::is_dnf(formula2, &f));
            assert_eq!(f.caches.is_dnf.len(), s2);
        }

        #[test]
        fn disable_is_dnf() {
            let mut f = FormulaFactory::new();
            f.config.caches.is_dnf = false;

            let formula1 = "~(a | b)".to_formula(&f);

            assert!(!predicates::is_dnf(formula1, &f));
            assert_eq!(f.caches.is_dnf.len(), 0);

            let formula2 = transformations::factorization_dnf(formula1, &f);
            assert_eq!(f.caches.is_dnf.len(), 0);
            assert!(predicates::is_dnf(formula2, &f));
            assert_eq!(f.caches.is_dnf.len(), 0);
        }

        #[test]
        fn enable_contains_pbc() {
            let mut f = FormulaFactory::new();
            f.config.caches.contains_pbc = true;

            let formula1 = "(c | d + e = 1)".to_formula(&f);
            let formula2 = "(a | b) & (c | d + e = 1)".to_formula(&f);

            assert!(predicates::contains_pbc(formula1, &f));
            assert_eq!(f.caches.contains_pbc.len(), 1);
            assert!(predicates::contains_pbc(formula2, &f));
            assert_eq!(f.caches.contains_pbc.len(), 2);
        }

        #[test]
        fn disable_contains_pbc() {
            let mut f = FormulaFactory::new();
            f.config.caches.contains_pbc = false;

            let formula1 = "(c | d + e = 1)".to_formula(&f);
            let formula2 = "(a | b) & (c | d + e = 1)".to_formula(&f);

            assert!(predicates::contains_pbc(formula1, &f));
            assert_eq!(f.caches.contains_pbc.len(), 0);
            assert!(predicates::contains_pbc(formula2, &f));
            assert_eq!(f.caches.contains_pbc.len(), 0);
        }

        #[test]
        fn enable_backbone_simps() {
            let mut f = FormulaFactory::new();
            f.config.caches.backbone_simps = true;

            let formula = "a => b".to_formula(&f);

            let res1 = transformations::backbone_simplification(formula, &f);
            assert_eq!(f.caches.backbone_simps.len(), 1);

            let res2 = transformations::backbone_simplification(formula, &f);
            assert_eq!(f.caches.backbone_simps.len(), 1);
            assert_eq!(res1, res2);
        }

        #[test]
        fn disable_backbone_simps() {
            let mut f = FormulaFactory::new();
            f.config.caches.backbone_simps = false;

            let formula = "a => b".to_formula(&f);

            let res1 = transformations::backbone_simplification(formula, &f);
            assert_eq!(f.caches.backbone_simps.len(), 0);

            let res2 = transformations::backbone_simplification(formula, &f);
            assert_eq!(f.caches.backbone_simps.len(), 0);
            assert_eq!(res1, res2);
        }
    }
}
