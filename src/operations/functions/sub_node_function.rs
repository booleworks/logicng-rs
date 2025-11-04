use std::collections::HashSet;
use std::sync::Arc;

use crate::formulas::operation_cache::OperationCache;
use crate::formulas::{EncodedFormula, Formula, FormulaFactory};

/// A function that computes a vector of al sub-formulas of a given formula. For
/// example, applied on the function `A & B | C` the sub-formulas are
///
/// - `A`
/// - `B`
/// - `C`
/// - `A & B`
/// - `A & B | C`
///
/// Each sub-formula is added exactly once to the vector. The sub-formula
/// function is implemented in such a way, that the order of the sub-formulas in
/// the result is bottom-up, i.e. a sub-formula only appears in the result when
/// all of its sub-formulas are already listed. The formula itself is always the
/// last element in the result.
///
/// # Example
///
/// Basic usage:
///
/// ```
/// # use logicng::formulas::{FormulaFactory, ToFormula};
/// # use logicng::operations::functions::sub_nodes;
/// # let f = FormulaFactory::new();
///
/// let formula = "a & ~b => a | b | c".to_formula(&f);
///
/// let result = sub_nodes(formula, &f);
///
/// assert_eq!(result[0].to_string(&f), "a");
/// assert_eq!(result[1].to_string(&f), "~b");
/// assert_eq!(result[2].to_string(&f), "a & ~b");
/// assert_eq!(result[3].to_string(&f), "b");
/// assert_eq!(result[4].to_string(&f), "c");
/// assert_eq!(result[5].to_string(&f), "a | b | c");
/// assert_eq!(result[6].to_string(&f), "a & ~b => a | b | c");
/// ```
pub fn sub_nodes(formula: EncodedFormula, f: &FormulaFactory) -> Arc<[EncodedFormula]> {
    if f.config.caches.sub_nodes {
        sub_nodes_cached(formula, f, &mut None)
    } else {
        sub_nodes_cached(formula, f, &mut Some(OperationCache::new()))
    }
}

fn sub_nodes_cached(
    formula: EncodedFormula,
    f: &FormulaFactory,
    local_cache: &mut Option<OperationCache<Arc<[EncodedFormula]>>>,
) -> Arc<[EncodedFormula]> {
    if let Some(lc) = local_cache
        && let Some(v) = lc.get(formula)
    {
        return v;
    }

    if let Some(v) = f.caches.sub_nodes.get(formula) {
        return v;
    }

    let mut result = Vec::new();
    let mut result_set = HashSet::new();
    for &op in &*formula.operands(f) {
        if !result_set.contains(&formula) {
            for &sub in &*sub_nodes_cached(op, f, local_cache) {
                if !result_set.contains(&sub) {
                    result.push(sub);
                    result_set.insert(sub);
                }
            }
        }
    }
    result.push(formula);
    let rc: Arc<[_]> = Arc::from(result);
    if f.config.caches.sub_nodes {
        f.caches.sub_nodes.insert(formula, Arc::clone(&rc));
    } else {
        local_cache.as_mut().unwrap().insert(formula, Arc::clone(&rc));
    }
    rc
}

/// Returns the number of atomic formulas of this formula. An atomic formula is a predicate (constants and literals)
/// or a cardinal/pseudo-boolean constraint.
///
/// # Example
///
/// Basic usage:
/// ```
/// # use logicng::formulas::FormulaFactory;
/// # use logicng::formulas::ToFormula;
/// # use logicng::operations::functions::number_of_atoms;
/// let f = FormulaFactory::new();
///
/// let formula1 = "$true".to_formula(&f);
/// let formula2 = "a => b".to_formula(&f);
/// let formula3 = "a & b & c".to_formula(&f);
/// let formula4 = "a + b = 1".to_formula(&f);
///
/// assert_eq!(number_of_atoms(formula1, &f), 1);
/// assert_eq!(number_of_atoms(formula2, &f), 2);
/// assert_eq!(number_of_atoms(formula3, &f), 3);
/// assert_eq!(number_of_atoms(formula4, &f), 1);
/// ```
pub fn number_of_atoms(formula: EncodedFormula, f: &FormulaFactory) -> u64 {
    if formula.is_atomic() {
        1
    } else if let Some(result) = f.caches.number_of_atoms.get(formula) {
        result
    } else {
        let result = formula.operands(f).iter().map(|op| number_of_atoms(*op, f)).sum();
        if f.config.caches.number_of_atoms {
            f.caches.number_of_atoms.insert(formula, result);
        }
        result
    }
}

/// Returns the number of internal nodes of this formula. A internal node is
/// a node as it exists in the `FormulaFactory`. So each atom is exactly one
/// node.
///
/// There is a similar function [`number_of_nodes`], which returns a
/// more intuitive result, by counting the literals/variables within a atom.
/// For example, the constraint `a + b = 1` is one internal node, but
/// [`number_of_nodes`] counts two additional nodes for `a` and `b`.
///
/// [`number_of_nodes`]: EncodedFormula::number_of_nodes
///
/// # Example
///
/// Basic usage:
/// ```
/// # use logicng::formulas::FormulaFactory;
/// # use logicng::formulas::ToFormula;
/// # use logicng::operations::functions::number_of_internal_nodes;
/// let f = FormulaFactory::new();
///
/// let formula1 = "$true".to_formula(&f);
/// let formula2 = "a => (b & (c + d = 1))".to_formula(&f);
/// let formula3 = "a & b & c".to_formula(&f);
/// let formula4 = "a + b = 1".to_formula(&f);
///
/// assert_eq!(number_of_internal_nodes(formula1, &f), 1);
/// assert_eq!(number_of_internal_nodes(formula2, &f), 5);
/// assert_eq!(number_of_internal_nodes(formula3, &f), 4);
/// assert_eq!(number_of_internal_nodes(formula4, &f), 1);
/// ```
pub fn number_of_internal_nodes(formula: EncodedFormula, f: &FormulaFactory) -> u64 {
    sub_nodes(formula, f).len() as u64
}

/// Returns the number of nodes of this formula.
///
/// Unlike [`number_of_internal_nodes`], which returns the real number of
/// nodes as they exist in the `FormulaFactory`, `number_of_nodes` also
/// counts the literals/variables within a atom. For example, the constraint
/// `a + b = 1` is one internal node, but `number_of_nodes` counts two
/// additional nodes for `a` and `b`.
///
/// [`number_of_internal_nodes`]: EncodedFormula::number_of_internal_nodes
///
/// # Example
///
/// Basic usage:
/// ```
/// # use logicng::formulas::FormulaFactory;
/// # use logicng::formulas::ToFormula;
/// # use logicng::operations::functions::number_of_nodes;
/// let f = FormulaFactory::new();
///
/// let formula1 = "$true".to_formula(&f);
/// let formula2 = "a => (b & (c + d = 1))".to_formula(&f);
/// let formula3 = "a & b & c".to_formula(&f);
/// let formula4 = "a + b = 1".to_formula(&f);
///
/// assert_eq!(number_of_nodes(formula1, &f), 1);
/// assert_eq!(number_of_nodes(formula2, &f), 7);
/// assert_eq!(number_of_nodes(formula3, &f), 4);
/// assert_eq!(number_of_nodes(formula4, &f), 3);
/// ```
pub fn number_of_nodes(formula: EncodedFormula, f: &FormulaFactory) -> u64 {
    1 + if formula.is_constant() || formula.is_literal() {
        0
    } else if let Some(result) = f.caches.number_of_nodes.get(formula) {
        result
    } else {
        let result = if formula.is_cc() {
            formula.as_cc(f).unwrap().variables.len() as u64
        } else if formula.is_pbc() {
            formula.as_pbc(f).unwrap().literals.len() as u64
        } else {
            formula.operands(f).iter().map(|op| number_of_nodes(*op, f)).sum()
        };
        if f.config.caches.number_of_nodes {
            f.caches.number_of_nodes.insert(formula, result);
        }
        result
    }
}

/// Returns the number of operands of this formula.
///
/// | type | number |
/// | --- | --- |
/// | not | 1 |
/// | binary op.| 2 |
/// | nary op. | # of ops. |
/// | literal | 0 |
/// | constant | 0 |
/// | constraints | 0 |
///
/// # Example
///
/// Basic usage:
/// ```
/// # use logicng::formulas::FormulaFactory;
/// # use logicng::formulas::ToFormula;
/// # use logicng::operations::functions::number_of_operands;
/// let f = FormulaFactory::new();
///
/// let formula1 = "$true".to_formula(&f);
/// let formula2 = "a => b".to_formula(&f);
/// let formula3 = "a & b & c".to_formula(&f);
/// let formula4 = "a + b = 1".to_formula(&f);
///
/// assert_eq!(number_of_operands(formula1, &f), 0);
/// assert_eq!(number_of_operands(formula2, &f), 2);
/// assert_eq!(number_of_operands(formula3, &f), 3);
/// assert_eq!(number_of_operands(formula4, &f), 0);
/// ```
pub fn number_of_operands(formula: EncodedFormula, f: &FormulaFactory) -> usize {
    use Formula::{And, Equiv, Impl, Not, Or};
    match formula.unpack(f) {
        Equiv(_) | Impl(_) => 2,
        Not(_) => 1,
        Or(ops) | And(ops) => ops.len(),
        _ => 0,
    }
}

#[cfg(test)]
mod tests {
    use crate::formulas::{EncodedFormula, FormulaFactory, ToFormula};
    use crate::operations::functions::sub_node_function::sub_nodes;

    #[test]
    fn test() {
        let f = &FormulaFactory::new();
        let f1 = "((a & ~b & c) | (d & (~e | c))) & (a => (~x | y) & (x | ~z))".to_formula(f);
        let expected = [
            "a".to_formula(f),
            "~b".to_formula(f),
            "c".to_formula(f),
            "a & ~b & c".to_formula(f),
            "d".to_formula(f),
            "~e".to_formula(f),
            "~e | c".to_formula(f),
            "d & (~e | c)".to_formula(f),
            "(a & ~b & c) | (d & (~e | c))".to_formula(f),
            "~x".to_formula(f),
            "y".to_formula(f),
            "~x | y".to_formula(f),
            "x".to_formula(f),
            "~z".to_formula(f),
            "x | ~z".to_formula(f),
            "(~x | y) & (x | ~z)".to_formula(f),
            "a => (~x | y) & (x | ~z)".to_formula(f),
            "((a & ~b & c) | (d & (~e | c))) & (a => (~x | y) & (x | ~z))".to_formula(f),
        ]
        .into_iter()
        .collect::<Vec<EncodedFormula>>();
        assert_eq!(*sub_nodes(f1, f), expected);
    }
}
