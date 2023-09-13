use std::cmp::Ordering;

use crate::formulas::{EncodedFormula, FormulaFactory, Variable};
use crate::operations::functions::variable_profile;

use super::dfs_ordering::dfs_ordering;

/// A BDD variable ordering sorting the variables from minimal to maximal occurrence
/// in the input formula.  If two variables have the same number of occurrences, their
/// ordering according to their DFS ordering will be considered.
pub fn min_to_max_ordering(formula: EncodedFormula, f: &FormulaFactory) -> Vec<Variable> {
    sort_ordering(formula, f, false)
}

/// A BDD variable ordering sorting the variables from maximal to minimal occurrence
/// in the input formula.  If two variables have the same number of occurrences, their
/// ordering according to their DFS ordering will be considered.
pub fn max_to_min_ordering(formula: EncodedFormula, f: &FormulaFactory) -> Vec<Variable> {
    sort_ordering(formula, f, true)
}

fn sort_ordering(formula: EncodedFormula, f: &FormulaFactory, reverse: bool) -> Vec<Variable> {
    let profile = variable_profile(formula, f);
    let dfs_ordering = dfs_ordering(formula, f);
    let mut list: Vec<(&Variable, &usize)> = profile.iter().collect();
    list.sort_by(|o1, o2| {
        let occ_comp = o1.1.cmp(o2.1);
        if occ_comp != Ordering::Equal {
            return if reverse { occ_comp.reverse() } else { occ_comp };
        }
        let index1 = dfs_ordering.iter().position(|x| x == o1.0).unwrap();
        let index2 = dfs_ordering.iter().position(|x| x == o2.0).unwrap();
        index1.cmp(&index2)
    });
    list.iter().map(|p| *p.0).collect()
}

#[cfg(test)]
mod tests {
    use crate::formulas::FormulaFactory;
    use crate::knowledge_compilation::bdd::orderings::occurrence_ordering::max_to_min_ordering;

    use super::min_to_max_ordering;

    #[test]
    fn test_simple_formulas() {
        let f = FormulaFactory::new();

        let va = f.var("A");
        let vb = f.var("B");
        let vc = f.var("C");

        assert!(min_to_max_ordering(f.parse("$true").unwrap(), &f).is_empty());
        assert!(min_to_max_ordering(f.parse("$false").unwrap(), &f).is_empty());
        assert_eq!(min_to_max_ordering(f.parse("A").unwrap(), &f), vec![va]);
        assert_eq!(min_to_max_ordering(f.parse("~A").unwrap(), &f), vec![va]);
        assert_eq!(min_to_max_ordering(f.parse("A => ~B").unwrap(), &f), vec![va, vb]);
        assert_eq!(min_to_max_ordering(f.parse("A <=> ~B").unwrap(), &f), vec![va, vb]);
        assert_eq!(min_to_max_ordering(f.parse("~(A <=> ~B)").unwrap(), &f), vec![va, vb]);
        assert_eq!(min_to_max_ordering(f.parse("A | ~C | B").unwrap(), &f), vec![va, vc, vb]);
        assert_eq!(min_to_max_ordering(f.parse("A & ~B & C").unwrap(), &f), vec![va, vb, vc]);
        assert_eq!(min_to_max_ordering(f.parse("A + C + B < 2").unwrap(), &f), vec![va, vc, vb]);
        assert_eq!(min_to_max_ordering(f.parse("3*C + B + 4*A < 7").unwrap(), &f), vec![vc, vb, va]);

        assert!(max_to_min_ordering(f.parse("$true").unwrap(), &f).is_empty());
        assert!(max_to_min_ordering(f.parse("$false").unwrap(), &f).is_empty());
        assert_eq!(max_to_min_ordering(f.parse("A").unwrap(), &f), vec![va]);
        assert_eq!(max_to_min_ordering(f.parse("~A").unwrap(), &f), vec![va]);
        assert_eq!(max_to_min_ordering(f.parse("A => ~B").unwrap(), &f), vec![va, vb]);
        assert_eq!(max_to_min_ordering(f.parse("A <=> ~B").unwrap(), &f), vec![va, vb]);
        assert_eq!(max_to_min_ordering(f.parse("~(A <=> ~B)").unwrap(), &f), vec![va, vb]);
        assert_eq!(max_to_min_ordering(f.parse("A | ~C | B").unwrap(), &f), vec![va, vc, vb]);
        assert_eq!(max_to_min_ordering(f.parse("A & ~B & C").unwrap(), &f), vec![va, vb, vc]);
        assert_eq!(max_to_min_ordering(f.parse("A + C + B < 2").unwrap(), &f), vec![va, vc, vb]);
        assert_eq!(max_to_min_ordering(f.parse("3*C + B + 4*A < 7").unwrap(), &f), vec![vc, vb, va]);
    }

    #[test]
    fn test_complex_formula() {
        let f = FormulaFactory::new();
        let formula = f.parse("(A => ~B) & ((A & C) | (D & ~C)) & (A | Y | X) & (Y <=> (X | (W + A + F < 1)))").unwrap();
        let ordering = vec![f.var("B"), f.var("D"), f.var("W"), f.var("F"), f.var("C"), f.var("Y"), f.var("X"), f.var("A")];
        let rev_ordering = vec![f.var("A"), f.var("C"), f.var("Y"), f.var("X"), f.var("B"), f.var("D"), f.var("W"), f.var("F")];

        assert_eq!(min_to_max_ordering(formula, &f), ordering);
        assert_eq!(max_to_min_ordering(formula, &f), rev_ordering);
    }
}
