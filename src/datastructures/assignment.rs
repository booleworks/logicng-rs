use std::collections::hash_map::DefaultHasher;
use std::collections::{BTreeSet, HashSet};
use std::hash::{Hash, Hasher};
use std::num::Wrapping;

use itertools::Itertools;

use crate::formulas::{EncodedFormula, FormulaFactory, Literal, StringLiteral, Variable};

use super::model::Model;

/// An `Assignment` stores a set of positive and negative [`Variable`]s.
///
/// `Assignment` stores all variables in [`HashSet`]s, this allows for a fast
/// evaluation of formulas. This might introduce additional costs when creating
/// an assignment. An opposite approach has the [`Model`] data-structure. It also
/// stores an assignment, but uses vectors instead of sets. Making it easier to
/// create, but slower to use.
///
/// # Conversion to `Model` and vice-versa
///
/// Depending of your use case it might be better to have a [`Model`] or an
/// `Assignment`. Both data-structures implement the `From` trait, such that you
/// can easily swap between both.
///
/// Convert from [`Model`] to `Assignment`:
/// ```
/// # use crate::logicng::formulas::FormulaFactory;
/// # use crate::logicng::datastructures::{Model, Assignment};
/// let f = FormulaFactory::new();
///
/// let a = f.var("a");
/// let b = f.var("b");
/// let model = Model::new(vec![a], vec![b]);
/// let assignment = Assignment::from(model);
/// ```
///
/// /// Convert from `Assignment` to [`Model`]:
/// ```
/// # use crate::logicng::formulas::FormulaFactory;
/// # use crate::logicng::datastructures::{Model, Assignment};
/// let f = FormulaFactory::new();
///
/// let a = f.var("a");
/// let b = f.var("b");
/// let assignment = Assignment::from_variables(&[a], &[b]);
/// let model = Model::from(assignment);
/// ```
#[derive(Debug, Clone)]
pub struct Assignment {
    /// Set of all positive variables of this assignment.
    pub pos: HashSet<Variable>,
    /// Set of all negative variables of this assignment.
    pub neg: HashSet<Variable>,
}

impl Assignment {
    /// Creates a new assignment.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::datastructures::Assignment;
    /// # use logicng::formulas::FormulaFactory;
    /// # use std::collections::HashSet;
    /// let f = FormulaFactory::new();
    ///
    /// let a = f.var("a");
    /// let b = f.var("b");
    ///
    /// let pos = HashSet::from([a]);
    /// let neg = HashSet::from([b]);
    ///
    /// let assignment = Assignment::new(pos, neg);
    /// ```
    pub const fn new(pos: HashSet<Variable>, neg: HashSet<Variable>) -> Self {
        Self { pos, neg }
    }

    /// Creates a new assignment from slices.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::datastructures::Assignment;
    /// # use logicng::formulas::FormulaFactory;
    /// let f = FormulaFactory::new();
    ///
    /// let a = f.var("a");
    /// let b = f.var("b");
    ///
    /// let assignment = Assignment::from_variables(&[a], &[b]);
    /// ```
    pub fn from_variables(pos: &[Variable], neg: &[Variable]) -> Self {
        Self { pos: pos.iter().copied().collect::<HashSet<Variable>>(), neg: neg.iter().copied().collect::<HashSet<Variable>>() }
    }

    /// Converts a literal into an assignment.
    ///
    /// A positive literal is added to the positive variables, and a negative
    /// literal to the negative variables.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::datastructures::Assignment;
    /// # use logicng::formulas::FormulaFactory;
    /// let f = FormulaFactory::new();
    ///
    /// let a = f.lit("a", true);
    /// let b = f.lit("b", false);
    ///
    /// let assignment1 = Assignment::from_lit(a);
    /// let assignment2 = Assignment::from_lit(b);
    ///
    /// assert!(assignment1.contains_pos(a.variable()));
    /// assert!(assignment2.contains_neg(b.variable()));
    /// ```
    pub fn from_lit(lit: Literal) -> Self {
        if lit.phase() {
            Self { pos: vec![lit.variable()].into_iter().collect(), neg: HashSet::new() }
        } else {
            Self { pos: HashSet::new(), neg: vec![lit.variable()].into_iter().collect() }
        }
    }

    /// Creates an assignment from a single vector of literals.
    ///
    /// All positive literals are added to the positive variables, and all
    /// negative literals to the negative variables.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::datastructures::Assignment;
    /// # use logicng::formulas::FormulaFactory;
    /// let f = FormulaFactory::new();
    ///
    /// let a = f.lit("a", true);
    /// let b = f.lit("b", false);
    ///
    /// let assignment = Assignment::from_literals(&[a, b]);
    ///
    /// assert!(assignment.contains_pos(a.variable()));
    /// assert!(assignment.contains_neg(b.variable()));
    /// ```
    pub fn from_literals(literals: &[Literal]) -> Self {
        let mut pos = HashSet::with_capacity(literals.len());
        let mut neg = HashSet::with_capacity(literals.len());
        for lit in literals {
            if lit.phase() {
                pos.insert(lit.variable());
            } else {
                neg.insert(lit.variable());
            }
        }
        Self { pos, neg }
    }

    /// Creates an assignment from a single set of literals.
    ///
    /// All positive literals are added to the positive variables, and all
    /// negative literals to the negative variables.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::datastructures::Assignment;
    /// # use logicng::formulas::FormulaFactory;
    /// # use std::collections::BTreeSet;
    /// let f = FormulaFactory::new();
    ///
    /// let a = f.lit("a", true);
    /// let b = f.lit("b", false);
    ///
    /// let set = BTreeSet::from([a, b]);
    /// let assignment = Assignment::from_set(set);
    ///
    /// assert!(assignment.contains_pos(a.variable()));
    /// assert!(assignment.contains_neg(b.variable()));
    /// ```
    pub fn from_set(set: BTreeSet<Literal>) -> Self {
        let mut pos = HashSet::new();
        let mut neg = HashSet::new();
        for lit in set {
            if lit.phase() {
                pos.insert(lit.variable());
            } else {
                neg.insert(lit.variable());
            }
        }
        Self { pos, neg }
    }

    /// Creates a new assignment from slices of names.
    ///
    /// Uses names of already existing variables and adds those variables to the
    /// assignment. If a name has no existing variable in the formula factory, the
    /// function will return an error.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::datastructures::Assignment;
    /// # use logicng::formulas::FormulaFactory;
    /// # fn main() -> Result<(), String> {
    /// let f = FormulaFactory::new();
    ///
    /// let a = f.var("a");
    /// let b = f.var("b");
    ///
    /// let assignment = Assignment::from_names(&["a"], &["b"], &f)?;
    ///
    /// assert!(assignment.contains_pos(a));
    /// assert!(assignment.contains_neg(b));
    /// # Ok(())
    /// # }
    /// ```
    pub fn from_names(pos: &[&str], neg: &[&str], f: &FormulaFactory) -> Result<Self, String> {
        let pos = names_to_indices(pos, f)?;
        let neg = names_to_indices(neg, f)?;
        Ok(Self { pos, neg })
    }

    /// Adds a single literal to this assignment.
    ///
    /// Returns true iff the literal previously was not contained in the
    /// assignment.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::datastructures::Assignment;
    /// # use logicng::formulas::FormulaFactory;
    /// let f = FormulaFactory::new();
    /// let mut assignment = Assignment::from_lit(f.lit("a", true));
    ///
    /// assignment.add_literal(f.lit("b", false));
    /// assert!(assignment.contains(f.lit("a", true)));
    /// assert!(assignment.contains(f.lit("b", false)));
    /// ```
    ///
    /// Returns true if a new values is added:
    /// ```
    /// # use logicng::datastructures::Assignment;
    /// # use logicng::formulas::FormulaFactory;
    /// let f = FormulaFactory::new();
    /// let mut assignment = Assignment::from_lit(f.lit("a", true));
    ///
    /// assert_eq!(assignment.add_literal(f.lit("a", true)), false);
    /// assert_eq!(assignment.add_literal(f.lit("b", true)), true);
    /// ```
    pub fn add_literal(&mut self, lit: Literal) -> bool {
        match lit {
            Literal::Pos(var) => self.pos.insert(var),
            Literal::Neg(var) => self.neg.insert(var),
        }
    }

    /// Returns all positive variables of this assignment.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::datastructures::Assignment;
    /// # use logicng::formulas::FormulaFactory;
    /// # use std::collections::HashSet;
    /// let f = FormulaFactory::new();
    ///
    /// let a = f.var("a");
    /// let b = f.var("b");
    ///
    /// let pos = HashSet::from([a]);
    /// let neg = HashSet::from([b]);
    ///
    /// let assignment = Assignment::new(pos.clone(), neg);
    ///
    /// assert_eq!(assignment.pos(), &pos);
    /// ```
    pub const fn pos(&self) -> &HashSet<Variable> {
        &self.pos
    }

    /// Returns all negative variables of this assignment.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::datastructures::Assignment;
    /// # use logicng::formulas::FormulaFactory;
    /// # use std::collections::HashSet;
    /// let f = FormulaFactory::new();
    ///
    /// let a = f.var("a");
    /// let b = f.var("b");
    ///
    /// let pos = HashSet::from([a]);
    /// let neg = HashSet::from([b]);
    ///
    /// let assignment = Assignment::new(pos, neg.clone());
    ///
    /// assert_eq!(assignment.neg(), &neg);
    /// ```
    pub const fn neg(&self) -> &HashSet<Variable> {
        &self.neg
    }

    /// Returns the overall number of positive and negative variables.
    ///
    /// A variable added as positive and negative is counted twice.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::datastructures::Assignment;
    /// # use logicng::formulas::FormulaFactory;
    /// let f = FormulaFactory::new();
    ///
    /// let a = f.var("a");
    /// let b = f.var("b");
    ///
    /// let assignment = Assignment::from_variables(&[a], &[b]);
    ///
    /// assert_eq!(assignment.len(), 2);
    /// ```
    pub fn len(&self) -> usize {
        self.pos.len() + self.neg.len()
    }

    /// Returns `true` if there is no variable in this assignment.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::datastructures::Assignment;
    /// # use logicng::formulas::FormulaFactory;
    /// let f = FormulaFactory::new();
    ///
    /// let a = f.var("a");
    /// let b = f.var("b");
    ///
    /// let assignment1 = Assignment::from_variables(&[a], &[b]);
    /// let assignment2 = Assignment::from_variables(&[], &[]);
    ///
    /// assert_eq!(assignment1.is_empty(), false);
    /// assert_eq!(assignment2.is_empty(), true);
    /// ```
    pub fn is_empty(&self) -> bool {
        self.pos.is_empty() && self.neg.is_empty()
    }

    /// Returns `true` if the given variable is a positive variable in this
    /// assignment.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::datastructures::Assignment;
    /// # use logicng::formulas::FormulaFactory;
    /// let f = FormulaFactory::new();
    ///
    /// let a = f.var("a");
    /// let b = f.var("b");
    /// let c = f.var("c");
    ///
    /// let assignment = Assignment::from_variables(&[a], &[b]);
    ///
    /// assert_eq!(assignment.contains_pos(a), true);
    /// assert_eq!(assignment.contains_pos(b), false);
    /// assert_eq!(assignment.contains_pos(c), false);
    /// ```
    pub fn contains_pos(&self, var: Variable) -> bool {
        self.pos.contains(&var)
    }

    /// Returns `true` if the given variable is a negative variable in this
    /// assignment.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::datastructures::Assignment;
    /// # use logicng::formulas::FormulaFactory;
    /// let f = FormulaFactory::new();
    ///
    /// let a = f.var("a");
    /// let b = f.var("b");
    /// let c = f.var("c");
    ///
    /// let assignment = Assignment::from_variables(&[a], &[b]);
    ///
    /// assert_eq!(assignment.contains_neg(a), false);
    /// assert_eq!(assignment.contains_neg(b), true);
    /// assert_eq!(assignment.contains_neg(c), false);
    /// ```
    pub fn contains_neg(&self, var: Variable) -> bool {
        self.neg.contains(&var)
    }

    /// Returns `true` if the variable of the given literal is a variable with
    /// the same phase in this assignment.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::datastructures::Assignment;
    /// # use logicng::formulas::FormulaFactory;
    /// let f = FormulaFactory::new();
    ///
    /// let a = f.var("a");
    /// let b = f.var("b");
    /// let c = f.var("c");
    ///
    /// let lit1 = f.lit("a", true);
    /// let lit2 = f.lit("b", true);
    /// let lit3 = f.lit("c", false);
    ///
    /// let assignment = Assignment::from_variables(&[a], &[b]);
    ///
    /// assert_eq!(assignment.contains(lit1), true);
    /// assert_eq!(assignment.contains(lit2), false);
    /// assert_eq!(assignment.contains(lit3), false);
    /// ```
    pub fn contains(&self, lit: Literal) -> bool {
        if lit.phase() { self.pos.contains(&lit.variable()) } else { self.neg.contains(&lit.variable()) }
    }

    /// Evaluates the given literals on this assignment.
    ///
    /// It will return `true`, if the literal is positive and it's variable is
    /// added as positive, or the literal is negative and it's variable is added
    /// as negative or not contained in this assignment.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::datastructures::Assignment;
    /// # use logicng::formulas::FormulaFactory;
    /// let f = FormulaFactory::new();
    ///
    /// let a = f.var("a");
    /// let b = f.var("b");
    /// let c = f.var("c");
    ///
    /// let lit1 = f.lit("a", true);
    /// let lit2 = f.lit("b", true);
    /// let lit3 = f.lit("c", false);
    ///
    /// let assignment = Assignment::from_variables(&[a], &[b]);
    ///
    /// assert_eq!(assignment.evaluate_lit(lit1), true);
    /// assert_eq!(assignment.evaluate_lit(lit2), false);
    /// assert_eq!(assignment.evaluate_lit(lit3), true);
    /// ```
    pub fn evaluate_lit(&self, lit: Literal) -> bool {
        let var = &lit.variable();
        if lit.phase() { self.pos.contains(var) } else { self.neg.contains(var) || !self.pos.contains(var) }
    }

    /// Restricts the given literal in this assignment.
    ///
    /// It will return a [`EncodedFormula`], which is either a constant, if the
    /// variable is contained in the assignment, or it is the passed literal as
    /// a formula, if the variable is not in the assignment.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::datastructures::Assignment;
    /// # use logicng::formulas::{FormulaFactory, EncodedFormula};
    /// let f = FormulaFactory::new();
    ///
    /// let a = f.var("a");
    /// let b = f.var("b");
    /// let c = f.var("c");
    ///
    /// let lit1 = f.lit("a", true);
    /// let lit2 = f.lit("b", true);
    /// let lit3 = f.lit("c", false);
    ///
    /// let assignment = Assignment::from_variables(&[a], &[b]);
    ///
    /// assert_eq!(assignment.restrict_lit(lit1), EncodedFormula::constant(true));
    /// assert_eq!(assignment.restrict_lit(lit2), EncodedFormula::constant(false));
    /// assert_eq!(assignment.restrict_lit(lit3), EncodedFormula::from(lit3));
    /// ```
    pub fn restrict_lit(&self, lit: Literal) -> EncodedFormula {
        let var = lit.variable();
        let phase = lit.phase();
        if self.pos.contains(&var) {
            if phase { EncodedFormula::constant(true) } else { EncodedFormula::constant(false) }
        } else if self.neg.contains(&var) {
            if phase { EncodedFormula::constant(false) } else { EncodedFormula::constant(true) }
        } else {
            lit.into()
        }
    }

    /// Creates the blocking clause for this assignment.
    #[allow(clippy::option_if_let_else)] // proposed change does not improve readability
    pub fn blocking_clause(&self, f: &FormulaFactory, variables: Option<&[Variable]>) -> EncodedFormula {
        let ops = if let Some(variables) = variables {
            variables
                .iter()
                .filter_map(|v| {
                    if self.pos.contains(v) {
                        Some(EncodedFormula::from(v.neg_lit()))
                    } else if self.neg.contains(v) {
                        Some(EncodedFormula::from(v.pos_lit()))
                    } else {
                        None
                    }
                })
                .collect()
        } else {
            let mut ops: Vec<EncodedFormula> = self.pos.iter().map(|v| EncodedFormula::from(v.neg_lit())).collect();
            ops.extend(self.neg.iter().map(|v| EncodedFormula::from(v.pos_lit())));
            ops
        };
        f.or(ops)
    }

    /// Returns a vector of [`Literal`] representing this assignment.
    ///
    /// All positive variables are returned as positive literals and all
    /// negative variables are returned as negative literals. The vector first
    /// consists of all positive literals and then of all negative literals.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::datastructures::Assignment;
    /// # use logicng::formulas::FormulaFactory;
    /// let f = FormulaFactory::new();
    ///
    /// let a = f.var("a");
    /// let b = f.var("b");
    ///
    /// let lit1 = f.lit("a", true);
    /// let lit2 = f.lit("b", false);
    ///
    /// let assignment = Assignment::from_variables(&[a], &[b]);
    ///
    /// assert_eq!(assignment.literals(), vec![lit1, lit2]);
    /// ```
    pub fn literals(&self) -> Vec<Literal> {
        let mut result = Vec::with_capacity(self.len());
        self.pos.iter().for_each(|var| result.push(Literal::Pos(*var)));
        self.neg.iter().for_each(|var| result.push(Literal::Neg(*var)));
        result
    }

    /// Returns a vector of [`StringLiteral`] representing this assignment.
    ///
    /// All positive variables are returned as positive literals and all
    /// negative variables are returned as negative literals. The vector first
    /// consists of all positive literals and then of all negative literals.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::datastructures::Assignment;
    /// # use logicng::formulas::FormulaFactory;
    /// let f = FormulaFactory::new();
    ///
    /// let a = f.var("a");
    /// let b = f.var("b");
    ///
    /// let lit1 = f.lit("a", true);
    /// let lit2 = f.lit("b", false);
    ///
    /// let assignment = Assignment::from_variables(&[a], &[b]);
    ///
    /// assert_eq!(assignment.string_literals(&f), vec![lit1.to_string_lit(&f), lit2.to_string_lit(&f)]);
    /// ```
    pub fn string_literals<'a>(&self, f: &'a FormulaFactory) -> Vec<StringLiteral<'a>> {
        let mut result = Vec::with_capacity(self.len());
        self.pos.iter().for_each(|var| result.push(Literal::Pos(*var).to_string_lit(f)));
        self.neg.iter().for_each(|var| result.push(Literal::Neg(*var).to_string_lit(f)));
        result
    }

    /// Creates a string representation of this assignment.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::datastructures::Assignment;
    /// # use logicng::formulas::FormulaFactory;
    /// let f = FormulaFactory::new();
    ///
    /// let a = f.var("a");
    /// let b = f.var("b");
    ///
    /// let assignment = Assignment::from_variables(&[a], &[b]);
    ///
    /// assert_eq!(assignment.to_string(&f), "Assignment{pos=[a], neg=[b]}");
    /// ```
    pub fn to_string(&self, f: &FormulaFactory) -> String {
        let pos = self.pos.iter().map(|v| v.name(f)).join(", ");
        let neg = self.neg.iter().map(|v| v.name(f)).join(", ");
        format!("Assignment{{pos=[{pos}], neg=[{neg}]}}")
    }
}

impl Hash for Assignment {
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write_u64(self.pos.iter().map(|&v| var_hash(v)).sum::<Wrapping<u64>>().0);
        state.write_u64(self.neg.iter().map(|&v| var_hash(v)).sum::<Wrapping<u64>>().0);
    }
}

impl PartialEq for Assignment {
    fn eq(&self, other: &Self) -> bool {
        self.pos == other.pos && self.neg == other.neg
    }
}

impl Eq for Assignment {}

impl<A: AsRef<Assignment>> From<A> for Model {
    fn from(assignment: A) -> Self {
        Self::new(assignment.as_ref().pos.iter().copied().collect::<Vec<_>>(), assignment.as_ref().neg.iter().copied().collect::<Vec<_>>())
    }
}

impl From<Assignment> for Model {
    fn from(assignment: Assignment) -> Self {
        Self::new(assignment.pos.into_iter().collect::<Vec<_>>(), assignment.neg.into_iter().collect::<Vec<_>>())
    }
}

fn var_hash(var: Variable) -> Wrapping<u64> {
    let hasher = &mut DefaultHasher::new();
    var.hash(hasher);
    Wrapping(hasher.finish())
}

fn names_to_indices(names: &[&str], f: &FormulaFactory) -> Result<HashSet<Variable>, String> {
    let mut result = HashSet::with_capacity(names.len());
    for name in names {
        let index = match f.variables.lookup(name) {
            Some(i) => Variable::FF(i),
            None => {
                return Err(format!("Variable {} is not known in the given FormulaFactory", *name));
            }
        };
        result.insert(index);
    }
    Ok(result)
}

#[cfg(test)]
mod tests {
    use crate::datastructures::Assignment;
    use crate::formulas::{FormulaFactory, ToFormula};
    use crate::util::test_util::{lits, vars_list};

    #[test]
    fn test_constructor1() {
        let f = &FormulaFactory::new();
        let vars1 = vars_list("a b c", f);
        let vars2 = vars_list("x y", f);
        let a1 = Assignment::new(vars1.iter().copied().collect(), vars2.iter().copied().collect());
        assert!(a1.contains_pos(f.var("a")));
        assert!(a1.contains_pos(f.var("b")));
        assert!(a1.contains_pos(f.var("c")));
        assert!(!a1.contains_pos(f.var("d")));
        assert!(!a1.contains_pos(f.var("x")));
        assert!(!a1.contains_pos(f.var("y")));
        assert!(!a1.contains_neg(f.var("a")));
        assert!(!a1.contains_neg(f.var("b")));
        assert!(!a1.contains_neg(f.var("c")));
        assert!(!a1.contains_neg(f.var("d")));
        assert!(a1.contains_neg(f.var("x")));
        assert!(a1.contains_neg(f.var("y")));
        assert_eq!(5, a1.len());
    }

    #[test]
    fn test_constructor2() {
        let f = &FormulaFactory::new();
        let vars1 = vars_list("a b c", f);
        let vars2 = vars_list("x y", f);
        let a1 = Assignment::from_variables(&vars1, &vars2);
        assert!(a1.contains_pos(f.var("a")));
        assert!(a1.contains_pos(f.var("b")));
        assert!(a1.contains_pos(f.var("c")));
        assert!(!a1.contains_pos(f.var("d")));
        assert!(!a1.contains_pos(f.var("x")));
        assert!(!a1.contains_pos(f.var("y")));
        assert!(!a1.contains_neg(f.var("a")));
        assert!(!a1.contains_neg(f.var("b")));
        assert!(!a1.contains_neg(f.var("c")));
        assert!(!a1.contains_neg(f.var("d")));
        assert!(a1.contains_neg(f.var("x")));
        assert!(a1.contains_neg(f.var("y")));
        assert_eq!(5, a1.len());
    }

    #[test]
    fn test_constructor3() {
        let f = &FormulaFactory::new();
        let lits = lits("a b c ~x ~y", f);
        let a1 = Assignment::from_set(lits);
        assert!(a1.contains_pos(f.var("a")));
        assert!(a1.contains_pos(f.var("b")));
        assert!(a1.contains_pos(f.var("c")));
        assert!(!a1.contains_pos(f.var("d")));
        assert!(!a1.contains_pos(f.var("x")));
        assert!(!a1.contains_pos(f.var("y")));
        assert!(!a1.contains_neg(f.var("a")));
        assert!(!a1.contains_neg(f.var("b")));
        assert!(!a1.contains_neg(f.var("c")));
        assert!(!a1.contains_neg(f.var("d")));
        assert!(a1.contains_neg(f.var("x")));
        assert!(a1.contains_neg(f.var("y")));
        assert_eq!(5, a1.len());
    }

    #[test]
    fn test_constructor4() {
        let f = &FormulaFactory::new();
        let a1 = Assignment::from_lit(f.lit("a", true));
        assert!(a1.contains_pos(f.var("a")));
        assert!(!a1.contains_pos(f.var("b")));
        assert!(!a1.contains_neg(f.var("a")));
        assert!(!a1.contains_neg(f.var("b")));
        assert_eq!(1, a1.len());

        let a2 = Assignment::from_lit(f.lit("a", false));
        assert!(!a2.contains_pos(f.var("a")));
        assert!(!a2.contains_pos(f.var("b")));
        assert!(a2.contains_neg(f.var("a")));
        assert!(!a2.contains_neg(f.var("b")));
        assert_eq!(1, a2.len());
    }

    #[test]
    fn test_is_empty() {
        let f = &FormulaFactory::new();
        let vars1 = vars_list("a b", f);
        let vars2 = vars_list("x y", f);
        let a1 = Assignment::from_variables(&[], &[]);
        let a2 = Assignment::from_variables(&vars1, &[]);
        let a3 = Assignment::from_variables(&[], &vars2);
        let a4 = Assignment::from_variables(&vars1, &vars2);
        assert!(a1.is_empty());
        assert!(!a2.is_empty());
        assert!(!a3.is_empty());
        assert!(!a4.is_empty());
    }

    #[test]
    fn test_contains() {
        let f = &FormulaFactory::new();
        let lits = lits("a b c ~x ~y", f);
        let a1 = Assignment::from_set(lits);
        assert!(a1.contains(f.lit("a", true)));
        assert!(a1.contains(f.lit("b", true)));
        assert!(a1.contains(f.lit("c", true)));
        assert!(a1.contains(f.lit("x", false)));
        assert!(a1.contains(f.lit("y", false)));
        assert!(!a1.contains(f.lit("a", false)));
        assert!(!a1.contains(f.lit("b", false)));
        assert!(!a1.contains(f.lit("c", false)));
        assert!(!a1.contains(f.lit("x", true)));
        assert!(!a1.contains(f.lit("y", true)));
        assert!(!a1.contains(f.lit("d", true)));
        assert!(!a1.contains(f.lit("d", false)));
    }

    #[test]
    fn test_evaluate_lit() {
        let f = &FormulaFactory::new();
        let vars1 = vars_list("a b", f);
        let vars2 = vars_list("x", f);
        let a1 = Assignment::from_variables(&vars1, &vars2);
        assert!(a1.evaluate_lit(f.lit("a", true)));
        assert!(!a1.evaluate_lit(f.lit("a", false)));
        assert!(a1.evaluate_lit(f.lit("b", true)));
        assert!(!a1.evaluate_lit(f.lit("b", false)));
        assert!(!a1.evaluate_lit(f.lit("x", true)));
        assert!(a1.evaluate_lit(f.lit("x", false)));
        assert!(!a1.evaluate_lit(f.lit("d", true)));
        assert!(a1.evaluate_lit(f.lit("d", false)));
    }

    #[test]
    fn test_restrict_lit() {
        let f = &FormulaFactory::new();
        let vars1 = vars_list("a b", f);
        let vars2 = vars_list("x", f);
        let a1 = Assignment::from_variables(&vars1, &vars2);
        assert_eq!(f.verum(), a1.restrict_lit(f.lit("a", true)));
        assert_eq!(f.falsum(), a1.restrict_lit(f.lit("a", false)));
        assert_eq!(f.verum(), a1.restrict_lit(f.lit("b", true)));
        assert_eq!(f.falsum(), a1.restrict_lit(f.lit("b", false)));
        assert_eq!(f.falsum(), a1.restrict_lit(f.lit("x", true)));
        assert_eq!(f.verum(), a1.restrict_lit(f.lit("x", false)));
        assert_eq!(f.literal("d", true), a1.restrict_lit(f.lit("d", true)));
        assert_eq!(f.literal("d", false), a1.restrict_lit(f.lit("d", false)));
    }

    #[test]
    fn test_blocking_clause() {
        let f = &FormulaFactory::new();
        let vars1 = vars_list("a b", f);
        let vars2 = vars_list("x y", f);
        let a1 = Assignment::from_variables(&vars1, &vars2);
        assert_eq!("~a | ~b | x | y".to_formula(f), a1.blocking_clause(f, None));
        let bc_vars = vars_list("a x c", f);
        assert_eq!("~a | x".to_formula(f), a1.blocking_clause(f, Some(&bc_vars)));
    }

    #[test]
    fn test_to_string() {
        let f = &FormulaFactory::new();
        let vars1 = vars_list("a b", f);
        let vars2 = vars_list("x y", f);
        let a1 = Assignment::from_variables(&[], &[]);
        let a2 = Assignment::from_variables(&vars1, &[]);
        let a3 = Assignment::from_variables(&[], &vars2);
        let a4 = Assignment::from_variables(&vars1, &vars2);
        assert_eq!("Assignment{pos=[], neg=[]}", a1.to_string(f));
        assert!(a2.to_string(f) == "Assignment{pos=[a, b], neg=[]}" || a2.to_string(f) == "Assignment{pos=[b, a], neg=[]}");
        assert!(a3.to_string(f) == "Assignment{pos=[], neg=[x, y]}" || a3.to_string(f) == "Assignment{pos=[], neg=[y, x]}");
        assert!(
            a4.to_string(f) == "Assignment{pos=[a, b], neg=[x, y]}"
                || a4.to_string(f) == "Assignment{pos=[b, a], neg=[x, y]}"
                || a4.to_string(f) == "Assignment{pos=[a, b], neg=[y, x]}"
                || a4.to_string(f) == "Assignment{pos=[b, a], neg=[y, x]}"
        );
    }
}
