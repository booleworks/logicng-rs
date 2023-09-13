use std::collections::HashSet;

use crate::formulas::{EncodedFormula, Formula, FormulaFactory, Variable};

/// A depth-first-search BDD variable ordering.  Traverses the formula in a DFS manner
/// and gathers all variables in the occurrence.
pub fn dfs_ordering(formula: EncodedFormula, f: &FormulaFactory) -> Vec<Variable> {
    let mut variables = Vec::new();
    let mut added = HashSet::new();
    dfs_rec(formula, f, &mut variables, &mut added);
    variables
}

fn dfs_rec(formula: EncodedFormula, f: &FormulaFactory, variables: &mut Vec<Variable>, added: &mut HashSet<Variable>) {
    let mut add = |var| {
        if !added.contains(&var) {
            variables.push(var);
            added.insert(var);
        }
    };

    match formula.unpack(f) {
        Formula::Lit(lit) => add(lit.variable()),
        Formula::Not(op) => dfs_rec(op, f, variables, added),
        Formula::Impl((left, right)) | Formula::Equiv((left, right)) => {
            dfs_rec(left, f, variables, added);
            dfs_rec(right, f, variables, added);
        }
        Formula::And(ops) | Formula::Or(ops) => {
            ops.for_each(|op| dfs_rec(op, f, variables, added));
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

#[cfg(test)]
mod tests {
    use crate::formulas::FormulaFactory;

    use super::dfs_ordering;

    #[test]
    fn test_simple_formulas() {
        let f = FormulaFactory::new();

        let va = f.var("A");
        let vb = f.var("B");
        let vc = f.var("C");

        assert!(dfs_ordering(f.parse("$true").unwrap(), &f).is_empty());
        assert!(dfs_ordering(f.parse("$false").unwrap(), &f).is_empty());
        assert_eq!(dfs_ordering(f.parse("A").unwrap(), &f), vec![va]);
        assert_eq!(dfs_ordering(f.parse("~A").unwrap(), &f), vec![va]);
        assert_eq!(dfs_ordering(f.parse("A => ~B").unwrap(), &f), vec![va, vb]);
        assert_eq!(dfs_ordering(f.parse("A <=> ~B").unwrap(), &f), vec![va, vb]);
        assert_eq!(dfs_ordering(f.parse("~(A <=> ~B)").unwrap(), &f), vec![va, vb]);
        assert_eq!(dfs_ordering(f.parse("A | ~C | B").unwrap(), &f), vec![va, vc, vb]);
        assert_eq!(dfs_ordering(f.parse("A & ~B & C").unwrap(), &f), vec![va, vb, vc]);
        assert_eq!(dfs_ordering(f.parse("A + C + B < 2").unwrap(), &f), vec![va, vc, vb]);
        assert_eq!(dfs_ordering(f.parse("3*C + B + 4*A < 7").unwrap(), &f), vec![vc, vb, va]);
    }

    #[test]
    fn test_complex_formula() {
        let f = FormulaFactory::new();
        let formula = f.parse("(A => ~B) & ((A & C) | (D & ~C)) & (A | Y | X) & (Y <=> (X | (W + A + F < 1)))").unwrap();
        let ordering = vec![f.var("A"), f.var("B"), f.var("C"), f.var("D"), f.var("Y"), f.var("X"), f.var("W"), f.var("F")];

        assert_eq!(dfs_ordering(formula, &f), ordering);
    }
}
