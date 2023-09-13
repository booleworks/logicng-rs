use std::collections::{HashSet, VecDeque};

use crate::formulas::{EncodedFormula, Formula, FormulaFactory, Variable};

/// A breadth-first-search BDD variable ordering.  Traverses the formula in a BFS manner
/// and gathers all variables in the occurrence.
pub fn bfs_ordering(formula: EncodedFormula, f: &FormulaFactory) -> Vec<Variable> {
    let mut queue = VecDeque::new();
    queue.push_back(formula);
    let mut added = HashSet::new();
    let mut variables = Vec::new();

    let mut add = |var| {
        if !added.contains(&var) {
            variables.push(var);
            added.insert(var);
        }
    };

    while !queue.is_empty() {
        let current = queue.pop_front().unwrap();
        match current.unpack(f) {
            Formula::Lit(lit) => {
                if lit.phase() {
                    add(lit.variable());
                } else {
                    queue.push_back(lit.variable().into());
                }
            }
            Formula::Not(op) => queue.push_back(op),
            Formula::Impl((left, right)) | Formula::Equiv((left, right)) => {
                queue.push_back(left);
                queue.push_back(right);
            }
            Formula::And(ops) | Formula::Or(ops) => {
                ops.for_each(|op| queue.push_back(op));
            }
            Formula::Cc(cc) => {
                cc.variables.iter().for_each(|var| add(*var));
            }
            Formula::Pbc(pbc) => {
                pbc.literals.iter().for_each(|lit| add(lit.variable()));
            }
            _ => {}
        }
    }
    variables
}

#[cfg(test)]
mod tests {
    use crate::formulas::FormulaFactory;

    use super::bfs_ordering;

    #[test]
    fn test_simple_formulas() {
        let f = FormulaFactory::new();

        let va = f.var("A");
        let vb = f.var("B");
        let vc = f.var("C");

        assert!(bfs_ordering(f.parse("$true").unwrap(), &f).is_empty());
        assert!(bfs_ordering(f.parse("$false").unwrap(), &f).is_empty());
        assert_eq!(bfs_ordering(f.parse("A").unwrap(), &f), vec![va]);
        assert_eq!(bfs_ordering(f.parse("~A").unwrap(), &f), vec![va]);
        assert_eq!(bfs_ordering(f.parse("A => ~B").unwrap(), &f), vec![va, vb]);
        assert_eq!(bfs_ordering(f.parse("A <=> ~B").unwrap(), &f), vec![va, vb]);
        assert_eq!(bfs_ordering(f.parse("~(A <=> ~B)").unwrap(), &f), vec![va, vb]);
        assert_eq!(bfs_ordering(f.parse("A | ~C | B").unwrap(), &f), vec![va, vb, vc]);
        assert_eq!(bfs_ordering(f.parse("A & ~B & C").unwrap(), &f), vec![va, vc, vb]);
        assert_eq!(bfs_ordering(f.parse("A + C + B < 2").unwrap(), &f), vec![va, vc, vb]);
        assert_eq!(bfs_ordering(f.parse("3*C + B + 4*A < 7").unwrap(), &f), vec![vc, vb, va]);
    }

    #[test]
    fn test_complex_formula() {
        let f = FormulaFactory::new();
        let formula = f.parse("(A => ~B) & ((A & C) | (D & ~C)) & (A | Y | X) & (Y <=> (X | (W + A + F < 1)))").unwrap();
        let ordering = vec![f.var("A"), f.var("Y"), f.var("X"), f.var("B"), f.var("C"), f.var("D"), f.var("W"), f.var("F")];

        assert_eq!(bfs_ordering(formula, &f), ordering);
    }
}
