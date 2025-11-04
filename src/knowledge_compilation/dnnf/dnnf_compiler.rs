use std::collections::{BTreeMap, BTreeSet};
use std::iter::repeat_n;
use std::sync::Arc;

use bitvec::bitvec;
use bitvec::vec::BitVec;
use itertools::Itertools;

use crate::formulas::{EncodedFormula, FormulaFactory, FormulaType, Literal, Variable};
use crate::knowledge_compilation::dnnf::DnnfSatSolver;
use crate::knowledge_compilation::dnnf::dtree::{DTree, DTreeFactory, DTreeIndex, min_fill_dtree_generation};
use crate::operations::predicates::is_sat;
use crate::operations::transformations::{backbone_simplification, cnf_subsumption};
use crate::solver::minisat::sat::{MiniSat2Solver, MsVar, Tristate, var};

/// Represents a formula in DNNF.
///
/// A formula in NNF is in _decomposable negation normal form_ (DNNF) if the
/// decompositional property holds, that is, the operands of a conjunction do
/// not share variables.
#[derive(Clone, Hash, Eq, PartialEq, Debug)]
pub struct DnnfFormula {
    /// Formula stored in the [`FormulaFactory`].
    pub formula: EncodedFormula,
    /// All variables contained in the original formula.
    pub original_variables: Arc<BTreeSet<Variable>>,
}

/// Compiles the given formula to a DNNF instance.
pub fn compile_dnnf(formula: EncodedFormula, f: &FormulaFactory) -> DnnfFormula {
    let original_variables = formula.variables(f);
    let cnf = f.cnf_of(formula);
    let simplified = backbone_simplification(cnf, f);
    let subsumption = cnf_subsumption(simplified, f);
    DnnfFormula { formula: DnnfCompiler::new(subsumption, f).compile(), original_variables }
}

struct DnnfCompiler<'a> {
    cnf: EncodedFormula,
    unit_clauses: EncodedFormula,
    non_unit_clauses: EncodedFormula,
    solver: DnnfSatSolver,
    number_of_variables: usize,
    cache: BTreeMap<BitVec, EncodedFormula>,
    f: &'a FormulaFactory,
    df: DTreeFactory,
}

impl<'a> DnnfCompiler<'a> {
    fn new(cnf: EncodedFormula, f: &'a FormulaFactory) -> Self {
        let (unit_clauses, non_unit_clauses) = initialize_clauses(cnf, f);
        let number_of_variables = cnf.variables(f).len();
        let mut solver = DnnfSatSolver::new(MiniSat2Solver::new(), number_of_variables);
        solver.add(cnf, f);
        DnnfCompiler {
            cnf,
            unit_clauses,
            non_unit_clauses,
            solver,
            number_of_variables,
            cache: BTreeMap::new(),
            f,
            df: DTreeFactory::new(),
        }
    }

    fn compile(&mut self) -> EncodedFormula {
        if self.non_unit_clauses.is_atomic() {
            self.cnf
        } else if !is_sat(self.cnf, self.f) || !self.solver.start() {
            self.f.falsum()
        } else {
            let tree = min_fill_dtree_generation(self.cnf, self.f, &mut self.df);
            self.df.finish(tree, &self.solver);
            self.compile_tree(tree)
        }
    }

    fn compile_tree(&mut self, tree: DTree) -> EncodedFormula {
        let result = self.cnf2ddnnf(tree);
        self.f.and([self.unit_clauses, result])
    }

    fn cnf2ddnnf(&mut self, tree: DTree) -> EncodedFormula {
        let implied = self.newly_implied_literals(&self.df.static_var_set(tree));
        let separator = self.df.dynamic_separator(tree, &self.solver);

        if separator.not_any() {
            match tree {
                DTree::Leaf(n) => {
                    let leaf_formula = self.leaf2ddnnf(n);
                    self.f.and([implied, leaf_formula])
                }
                DTree::Node(n) => self.conjoin(implied, self.df.children(n)),
            }
        } else {
            let sep = separator;
            let var = self.choose_shannon_variable(tree, &sep);

            // Positive branch
            let positive_dnnf = if self.solver.decide(var, true) { self.cnf2ddnnf(tree) } else { self.f.falsum() };
            self.solver.undo_decide(var);
            if positive_dnnf.is_falsum() {
                return if self.solver.at_assertion_level() && self.solver.assert_cd_literal() {
                    self.cnf2ddnnf(tree)
                } else {
                    self.f.falsum()
                };
            }

            // Negative branch
            let negative_dnnf = if self.solver.decide(var, false) { self.cnf2ddnnf(tree) } else { self.f.falsum() };
            self.solver.undo_decide(var);
            if negative_dnnf.is_falsum() {
                return if self.solver.at_assertion_level() && self.solver.assert_cd_literal() {
                    self.cnf2ddnnf(tree)
                } else {
                    self.f.falsum()
                };
            }

            let lit = EncodedFormula::from(self.solver.var_for_idx(var).pos_lit());
            let neg_lit = self.f.negate(lit);
            let positive_branch = self.f.and([lit, positive_dnnf]);
            let negative_branch = self.f.and([neg_lit, negative_dnnf]);
            let shannon = self.f.or([positive_branch, negative_branch]);
            self.f.and([implied, shannon])
        }
    }

    fn newly_implied_literals(&mut self, known_variables: &Arc<BitVec>) -> EncodedFormula {
        self.solver.newly_implied(known_variables, self.f)
    }

    fn leaf2ddnnf(&self, leaf_index: DTreeIndex) -> EncodedFormula {
        let leaf = &self.df.leaf_literals[leaf_index as usize];
        let mut leaf_result_operands = Vec::with_capacity(leaf.len());
        let mut leaf_current_literals = Vec::with_capacity(leaf.len());
        for lit in leaf {
            match self.solver.value_of(*lit) {
                Tristate::True => return self.f.verum(),
                Tristate::Undef => {
                    let literal = EncodedFormula::from(Literal::new(self.solver.var_for_idx(var(*lit)), DnnfSatSolver::phase(*lit)));
                    leaf_current_literals.push(literal);
                    leaf_result_operands.push(self.f.and(&leaf_current_literals));
                    let last_index = leaf_current_literals.len() - 1;
                    leaf_current_literals[last_index] = self.f.negate(literal);
                }
                Tristate::False => {}
            }
        }
        self.f.or(&leaf_result_operands)
    }

    fn conjoin(&mut self, implied: EncodedFormula, node: (DTree, DTree)) -> EncodedFormula {
        if implied.is_falsum() {
            return implied;
        }
        let left = self.cnf_aux(node.0);
        if left.is_falsum() {
            return left;
        }
        let right = self.cnf_aux(node.1);
        if right.is_falsum() {
            return right;
        }
        self.f.and([implied, left, right])
    }

    fn cnf_aux(&mut self, tree: DTree) -> EncodedFormula {
        match tree {
            DTree::Leaf(n) => self.leaf2ddnnf(n),
            DTree::Node(_) => {
                let key = self.compute_cache_key(tree);
                if let Some(&cache) = self.cache.get(&key) {
                    cache
                } else {
                    let dnnf = self.cnf2ddnnf(tree);
                    if !dnnf.is_falsum() {
                        self.cache.insert(key, dnnf);
                    }
                    dnnf
                }
            }
        }
    }

    fn compute_cache_key(&self, tree: DTree) -> BitVec {
        // cached allocation as in Java was significantly slower here, so we rather create a new bitvec on every call
        let mut result = bitvec![0; self.df.tree_size() + self.number_of_variables];
        self.df.cache_key(tree, &self.solver, &mut result, self.number_of_variables);
        result
    }

    #[allow(clippy::cast_possible_wrap)]
    fn choose_shannon_variable(&self, tree: DTree, separator: &BitVec) -> MsVar {
        // cached allocation as in Java was significantly slower here, so we rather create a new vector on every call
        let mut occurrences: Vec<isize> = repeat_n(-1, self.number_of_variables).collect();
        separator.iter_ones().for_each(|n| occurrences[n] = 0);

        self.df.count_unsubsumed_occurrences(tree, &mut occurrences, &self.solver);

        MsVar(occurrences.iter().position_max().unwrap())
    }
}

fn initialize_clauses(cnf: EncodedFormula, f: &FormulaFactory) -> (EncodedFormula, EncodedFormula) {
    match cnf.formula_type() {
        FormulaType::And => {
            let (l, r): (Vec<EncodedFormula>, Vec<EncodedFormula>) = cnf.operands(f).iter().partition(|&&o| o.is_atomic());
            (f.and(l), f.and(r))
        }
        FormulaType::Or => (f.verum(), cnf),
        _ => (cnf, f.verum()),
    }
}

#[cfg(test)]
mod tests {
    use crate::formulas::{EncodedFormula, FormulaFactory, FormulaType, ToFormula};
    use crate::io::read_cnf;
    use crate::knowledge_compilation::bdd::orderings::force_ordering;
    use crate::knowledge_compilation::bdd::{Bdd, BddKernel};
    use crate::knowledge_compilation::dnnf::dnnf_compiler::compile_dnnf;
    use crate::knowledge_compilation::dnnf::dnnf_model_counting::count;
    use crate::operations::predicates::is_tautology;
    use num_bigint::{BigUint, ToBigUint};
    use std::fs::File;
    use std::io::{BufRead, BufReader};

    #[test]
    fn test_trivial_formulas() {
        let f = &FormulaFactory::new();
        test_formula("$true".to_formula(f), f, true);
        test_formula("$false".to_formula(f), f, true);
        test_formula("a".to_formula(f), f, true);
        test_formula("~a".to_formula(f), f, true);
        test_formula("a & b".to_formula(f), f, true);
        test_formula("a | b".to_formula(f), f, true);
        test_formula("a => b".to_formula(f), f, true);
        test_formula("a <=> b".to_formula(f), f, true);
        test_formula("a | b | c".to_formula(f), f, true);
        test_formula("a & b & c".to_formula(f), f, true);
        test_formula("f & ((~b | c) <=> ~a & ~c)".to_formula(f), f, true);
        test_formula("a | ((b & ~c) | (c & (~d | ~a & b)) & e)".to_formula(f), f, true);
        test_formula("a + b + c + d <= 1".to_formula(f), f, true);
        test_formula("a + b + c + d <= 3".to_formula(f), f, true);
        test_formula("2*a + 3*b + -2*c + d < 5".to_formula(f), f, true);
        test_formula("2*a + 3*b + -2*c + d >= 5".to_formula(f), f, true);
        test_formula("~a & (~a | b | c | d)".to_formula(f), f, true);
    }

    #[test]
    #[cfg_attr(not(feature = "long_running_tests"), ignore)]
    fn test_large_formulas() {
        let f = &FormulaFactory::new();
        let cnf1 = read_cnf("resources/dnnf/both_bdd_dnnf_1.cnf", f).unwrap();
        let cnf2 = read_cnf("resources/dnnf/both_bdd_dnnf_2.cnf", f).unwrap();
        let cnf3 = read_cnf("resources/dnnf/both_bdd_dnnf_3.cnf", f).unwrap();
        let cnf4 = read_cnf("resources/dnnf/both_bdd_dnnf_4.cnf", f).unwrap();
        let cnf5 = read_cnf("resources/dnnf/both_bdd_dnnf_5.cnf", f).unwrap();
        test_formula(f.and(cnf1), f, true);
        test_formula(f.and(cnf2), f, true);
        test_formula(f.and(cnf3), f, true);
        test_formula(f.and(cnf4), f, true);
        test_formula(f.and(cnf5), f, true);
    }

    #[test]
    #[cfg_attr(not(feature = "long_running_tests"), ignore)]
    fn test_all_small_formulas() {
        let f = &FormulaFactory::new();
        BufReader::new(File::open("resources/formulas/small_formulas.txt").unwrap())
            .lines()
            .for_each(|line| test_formula(line.unwrap().to_formula(f), f, false));
    }

    fn test_formula(formula: EncodedFormula, f: &FormulaFactory, with_equivalence: bool) {
        let dnnf = compile_dnnf(formula, f);

        let dnnf_count = count(&dnnf, f);
        let bdd_count = count_with_bdd(formula, f);
        assert_eq!(bdd_count, dnnf_count);
        if with_equivalence {
            let equivalence = f.equivalence(formula, dnnf.formula);
            assert!(is_tautology(equivalence, f));
        }
    }

    fn count_with_bdd(formula: EncodedFormula, f: &FormulaFactory) -> BigUint {
        match formula.formula_type() {
            FormulaType::True => 1.to_biguint().unwrap(),
            FormulaType::False => 0.to_biguint().unwrap(),
            _ => {
                let kernel = &mut BddKernel::new_with_var_ordering(&force_ordering(formula, f), 10000, 10000);
                Bdd::from_formula(formula, f, kernel).model_count(kernel)
            }
        }
    }
}
