use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use itertools::Itertools;

use crate::datastructures::UbTree;
use crate::formulas::{EncodedFormula, FormulaFactory, Literal, LIT_PRECEDENCE};

/// This transformation performs subsumption on a given CNF and returns a new
/// CNF. I.e. performs as many subsumptions as possible.
///
/// A subsumption in a CNF means, that e.g. a clause `A | B | C` is subsumed by
/// another clause `A | B` and can therefore be deleted for an equivalent CNF.
pub fn cnf_subsumption(formula: EncodedFormula, f: &FormulaFactory) -> EncodedFormula {
    assert!(formula.is_cnf(f), "CNF subsumption can only be applied to formulas in CNF");
    if formula.precedence() >= LIT_PRECEDENCE || formula.is_or() {
        formula
    } else {
        assert!(formula.is_and());
        let ub_tree = generate_subsumed_ubtree(formula, f);
        let mut clauses = Vec::new();
        for literals in ub_tree.all_sets() {
            clauses.push(f.clause(&literals.iter().copied().collect_vec()));
        }
        f.and(&clauses)
    }
}

/// This transformation performs subsumption on a given DNF and returns a new
/// DNF. I.e. performs as many subsumptions as possible.
///
/// A subsumption in a DNF means, that e.g. a minterm {@code A & B & C} is
/// subsumed by another minterm {@code A & B} and can therefore be deleted for
/// an equivalent DNF.
pub fn dnf_subsumption(formula: EncodedFormula, f: &FormulaFactory) -> EncodedFormula {
    assert!(formula.is_dnf(f), "DNF subsumption can only be applied to formulas in DNF");
    if formula.precedence() >= LIT_PRECEDENCE || formula.is_and() {
        formula
    } else {
        assert!(formula.is_or());
        let ub_tree = generate_subsumed_ubtree(formula, f);
        let mut minterms = Vec::new();
        for literals in ub_tree.all_sets() {
            minterms.push(f.and(&literals.iter().map(|&l| EncodedFormula::from(l)).collect::<Box<[_]>>()));
        }
        f.or(&minterms)
    }
}

fn generate_subsumed_ubtree(formula: EncodedFormula, f: &FormulaFactory) -> UbTree<Literal> {
    let mut mapping: BTreeMap<usize, Vec<Arc<BTreeSet<Literal>>>> = BTreeMap::new();
    for &term in &*formula.operands(f) {
        let literals = term.literals(f);
        mapping.entry(literals.len()).or_default().push(literals);
    }
    let mut ub_tree = UbTree::new();
    for (_, value) in mapping {
        for set in value {
            if ub_tree.first_subset(set.as_ref()).is_none() {
                ub_tree.add_set((*set).clone());
            }
        }
    }
    ub_tree
}
