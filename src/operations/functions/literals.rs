use std::borrow::Cow;
use std::collections::{BTreeSet, HashSet};
use std::sync::Arc;

use crate::formulas::{EncodedFormula, Formula, FormulaFactory, Literal, StringLiteral, Variable};
use crate::util::exceptions::panic_unexpected_formula_type;

/// Returns a set with all names of the variables in this formula.
///
/// # Example
///
/// Basic usage:
/// ```
/// # use logicng::formulas::FormulaFactory;
/// # use logicng::formulas::ToFormula;
/// # use logicng::formulas::StringLiteral;
/// # use logicng::operations::functions::string_literals;
/// # use std::collections::BTreeSet;
/// # use std::borrow::Cow;
/// let f = FormulaFactory::new();
///
/// let formula = "(a => b) & ~c".to_formula(&f);
///
/// let expected = BTreeSet::from_iter(vec![
///     StringLiteral::new("a", true),
///     StringLiteral::new("b", true),
///     StringLiteral::new("c", false),
/// ].into_iter());
/// assert_eq!(string_literals(formula, &f), expected)
/// ```
pub fn string_literals(formula: EncodedFormula, f: &FormulaFactory) -> BTreeSet<StringLiteral> {
    formula.literals(f).iter().map(|lit| lit.to_string_lit(f)).collect()
}

/// Assuming this formula is a clause or term, it returns all literals in
/// this formula.
///
/// # Panic
///
/// This function panics, if the passed formula is not a clause or a term. A
/// formula is a clause/term if all operands of the `n-ary` operators are
/// literals or the formula is a literal or a constant. Otherwise it will
/// panic!
///
/// # Example
///
/// Basic usage:
/// ```
/// # use logicng::formulas::FormulaFactory;
/// # use logicng::formulas::ToFormula;
/// # use logicng::operations::functions::literals_for_clause_or_term;
/// let f = FormulaFactory::new();
///
/// let a = f.lit("a", false);
/// let b = f.lit("b", true);
/// let c = f.lit("c", true);
///
/// let formula1 = "$true".to_formula(&f);
/// let formula2 = "~a".to_formula(&f);
/// let formula3 = "~a & b & c".to_formula(&f);
/// let formula4 = "~a | b | c".to_formula(&f);
///
/// assert_eq!(literals_for_clause_or_term(formula1, &f), vec![]);
/// assert_eq!(literals_for_clause_or_term(formula2, &f), vec![a]);
/// assert_eq!(literals_for_clause_or_term(formula3, &f), vec![a, b, c]);
/// assert_eq!(literals_for_clause_or_term(formula4, &f), vec![a, b, c]);
/// ```
///
/// Panic behavior:
///
/// The `literals_for_clause_or_term` panics if the passed formula isn't a
/// clause/term.
/// ```
/// # use logicng::formulas::FormulaFactory;
/// # use logicng::formulas::ToFormula;
/// let f = FormulaFactory::new();
///
/// let formula1 = "a => b".to_formula(&f);
/// let formula2 = "a & b & (c => d)".to_formula(&f);
///
/// //literals_for_clause_or_term(formula1, &f); //PANIC!
/// //literals_for_clause_or_term(formula2, &f); //PANIC!
/// ```
pub fn literals_for_clause_or_term(formula: EncodedFormula, f: &FormulaFactory) -> Vec<Literal> {
    use Formula::{And, False, Lit, Or, True};
    match formula.unpack(f) {
        Or(ops) | And(ops) => ops
            .map(|l| l.as_literal().map_or_else(|| panic!("Expected {} to be a clause or a term", formula.to_string(f)), |lit| lit))
            .collect(),
        Lit(l) => vec![l],
        True | False => vec![],
        _ => panic_unexpected_formula_type(formula, Some(f)),
    }
}

/// Returns a set with all variables in this formula.
///
/// # Example
///
/// Basic usage:
///
/// ```
/// # use logicng::formulas::FormulaFactory;
/// # use logicng::formulas::ToFormula;
/// # use logicng::operations::functions::variables;
/// # use std::collections::BTreeSet;
/// let f = FormulaFactory::new();
///
/// let a = f.var("a");
/// let b = f.var("b");
/// let c = f.var("c");
/// let formula = "(a => b) & c".to_formula(&f);
///
/// let expected = BTreeSet::from_iter(vec![a, b, c].into_iter());
/// assert_eq!(variables(formula, &f).as_ref(), &expected);
pub fn variables(formula: EncodedFormula, f: &FormulaFactory) -> Arc<BTreeSet<Variable>> {
    use Formula::{Cc, False, Lit, Pbc, True};
    f.caches.variables.get(formula).unwrap_or_else(|| {
        let mut result = BTreeSet::new();
        match formula.unpack(f) {
            True | False => (),
            Lit(lit) => {
                result.insert(lit.variable());
            }
            Cc(cc) => result.extend(cc.variables.iter()),
            Pbc(pbc) => result.extend(pbc.literals.iter().map(Literal::variable)),
            _ => {
                for op in &*formula.operands(f) {
                    result.extend(op.variables(f).iter());
                }
            }
        }
        let rc = Arc::new(result);
        if f.config.caches.variables {
            f.caches.variables.insert(formula, rc.clone());
        }
        rc
    })
}

pub fn variables2(formula: EncodedFormula, f: &FormulaFactory) -> Arc<BTreeSet<Variable>> {
    let mut result = BTreeSet::new();
    let mut subresult = Vec::new();
    let mut stack = Vec::new();
    let mut visited = HashSet::new();
    stack.push(formula);

    while let Some(current) = stack.pop() {
        if let Some(cached) = f.caches.variables.get(current) {
            subresult.push(cached);
        } else {
            match current.unpack(f) {
                Formula::Lit(l) => {
                    result.insert(l.variable());
                }
                Formula::And(ops) | Formula::Or(ops) => {
                    let vars = ops.map(|op| variables(op, f)).fold(BTreeSet::new(), |mut akk, vs| {
                        akk.extend((*vs).clone());
                        akk
                    });

                    let rc = Arc::new(vars);
                    if f.config.caches.variables {
                        f.caches.variables.insert(current, Arc::clone(&rc));
                    }
                    subresult.push(rc);
                }
                Formula::Equiv((left, right)) | Formula::Impl((left, right)) => {
                    if visited.insert(left) {
                        stack.push(left);
                    }
                    if visited.insert(right) {
                        stack.push(right);
                    }
                }
                Formula::Not(op) => {
                    if visited.insert(op) {
                        stack.push(op);
                    }
                }
                Formula::Cc(cc) => {
                    for &v in &*cc.variables {
                        result.insert(v);
                    }
                }
                Formula::Pbc(pbc) => {
                    for &l in &*pbc.literals {
                        result.insert(l.variable());
                    }
                }
                _ => {}
            }
        }
    }

    let rc = if result.is_empty() {
        Arc::clone(&subresult[0])
    } else {
        for sub in subresult {
            result.extend((*sub).clone());
        }
        Arc::new(result)
    };

    if f.config.caches.variables {
        f.caches.variables.insert(formula, Arc::clone(&rc));
    }
    rc
}

/// Returns a set with all names of the variables in this formula.
///
/// # Example
///
/// Basic usage:
/// ```
/// # use logicng::formulas::FormulaFactory;
/// # use logicng::formulas::ToFormula;
/// # use logicng::operations::functions::string_variables;
/// # use std::collections::BTreeSet;
/// # use std::borrow::Cow;
/// let f = FormulaFactory::new();
///
/// let formula = "(a => b) & c".to_formula(&f);
///
/// let expected = BTreeSet::from_iter(vec![
///     Cow::from("a"),
///     Cow::from("b"),
///     Cow::from("c")
/// ].into_iter());
/// assert_eq!(string_variables(formula, &f), expected)
/// ```
pub fn string_variables(formula: EncodedFormula, f: &FormulaFactory) -> BTreeSet<Cow<'_, str>> {
    formula.variables(f).iter().map(|var| var.name(f)).collect()
}

/// Returns a set with all literals in this set.
///
/// # Example
///
/// Basic usage:
///
/// ```
/// # use logicng::formulas::FormulaFactory;
/// # use logicng::formulas::ToFormula;
/// # use logicng::operations::functions::literals;
/// # use std::collections::BTreeSet;
/// let f = FormulaFactory::new();
///
/// let a = f.lit("a", true);
/// let b = f.lit("b", true);
/// let c = f.lit("c", false);
/// let formula = "(a => b) & ~c".to_formula(&f);
///
/// let expected = BTreeSet::from_iter(vec![a, b, c].into_iter());
/// assert_eq!(literals(formula, &f).as_ref(), &expected);
/// ```
pub fn literals(formula: EncodedFormula, f: &FormulaFactory) -> Arc<BTreeSet<Literal>> {
    use Formula::{And, Cc, Equiv, Impl, Lit, Not, Or, Pbc};
    f.caches.literals.get(formula).unwrap_or_else(|| {
        let mut result = BTreeSet::new();
        match formula.unpack(f) {
            Lit(l) => {
                result.insert(l);
            }
            Equiv(_) | Impl(_) | Or(_) | And(_) | Not(_) => {
                formula.operands(f).iter().for_each(|&op| result.append(&mut (*literals(op, f)).clone()));
            }
            Cc(cc) => cc.variables.iter().for_each(|v| {
                result.insert(v.pos_lit());
            }),
            Pbc(pbc) => pbc.literals.iter().for_each(|&l| {
                result.insert(l);
            }),
            _ => (),
        }
        let rc = Arc::new(result);
        if f.config.caches.literals {
            f.caches.literals.insert(formula, rc.clone());
        }
        rc
    })
}

pub fn literals_reduced_caching(formula: EncodedFormula, f: &FormulaFactory) -> Arc<BTreeSet<Literal>> {
    if let Some(cached) = f.caches.literals.get(formula) {
        return cached;
    }

    let mut result = BTreeSet::new();
    let mut stack = Vec::new();
    let mut visited = HashSet::new();
    stack.push(formula);

    while let Some(current) = stack.pop() {
        if let Some(cached) = f.caches.literals.get(current) {
            result.extend((*cached).clone());
        } else {
            match current.unpack(f) {
                Formula::Lit(l) => {
                    result.insert(l);
                }
                Formula::And(ops) | Formula::Or(ops) => {
                    for op in ops {
                        if visited.insert(op) {
                            stack.push(op);
                        }
                    }
                }
                Formula::Equiv((left, right)) | Formula::Impl((left, right)) => {
                    if visited.insert(left) {
                        stack.push(left);
                    }
                    if visited.insert(right) {
                        stack.push(right);
                    }
                }
                Formula::Not(op) => {
                    if visited.insert(op) {
                        stack.push(op);
                    }
                }
                Formula::Cc(cc) => {
                    for &v in &*cc.variables {
                        result.insert(v.pos_lit());
                    }
                }
                Formula::Pbc(pbc) => {
                    for &l in &*pbc.literals {
                        result.insert(l);
                    }
                }
                _ => {}
            }
        }
    }
    let rc = Arc::new(result);
    if f.config.caches.literals {
        f.caches.literals.insert(formula, rc.clone());
    }
    rc
}
