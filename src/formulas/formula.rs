use std::borrow::Cow;
use std::collections::BTreeSet;
use std::sync::Arc;

use crate::formulas::{CardinalityConstraint, FormulaFactory, Literal, PbConstraint, StringLiteral, Variable};
use crate::operations::{functions, predicates};

use super::formula_cache::formula_encoding::{Encoding, FormulaEncoding};
use super::formula_cache::nary_formula_cache::NaryIterator;
use super::LitType;

/// Specifies all types a [`EncodedFormula`] can have.
///
/// You can get the type of an `EncodedFormula` by calling [`EncodedFormula::formula_type()`].
#[derive(Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd, Debug)]
pub enum FormulaType {
    /// Pseudo-boolean constraint
    Pbc,
    /// Cardinality constraint
    Cc,
    /// Equivalence
    Equiv,
    /// Implication
    Impl,
    /// Disjunction
    Or,
    /// Conjunction
    And,
    /// Negation
    Not,
    /// Literal and type of the literal
    Lit(LitType),
    /// Constant true
    True,
    /// Constant false
    False,
}

/// A unpacked representation of an [`EncodedFormula`]. Allows access to the
/// operands of the formula.
///
/// You can obtain a `Formula` from a `EncodedFormula` by calling [`EncodedFormula::unpack()`].
#[derive(Clone, Hash, Eq, PartialEq, Debug)]
pub enum Formula<'a> {
    /// Reference to a pseudo-boolean constraint
    Pbc(&'a PbConstraint),
    /// Reference to a cardinality constraint
    Cc(&'a CardinalityConstraint),
    /// Operands of an equivalence
    Equiv((EncodedFormula, EncodedFormula)),
    /// Operands of an implication
    Impl((EncodedFormula, EncodedFormula)),
    /// Iterator over all operands of a disjunction
    Or(NaryIterator<'a>),
    /// Iterator over all operands of a conjunction
    And(NaryIterator<'a>),
    /// Operand of a negation
    Not(EncodedFormula),
    /// Literal
    Lit(Literal),
    /// Constant true
    True,
    /// Constant false
    False,
}

/// `EncodedFormula` represents a logical formula.
///
/// In _LogicNG_ an `EncodedFormula` instance does not contain much information. It is
/// instead a reference into a `FormulaFactory` which stores the information
/// about that formula. This means that **an `EncodedFormula` is only useful in the
/// context of the `FormulaFactory` it was created in.**
///
/// Since a `EncodedFormula` is technically only a fancy pointer, it also implements
/// the [`Copy`] trait.
#[derive(Eq, Hash, PartialEq, Copy, Clone, Debug)]
pub struct EncodedFormula {
    pub(super) encoding: FormulaEncoding,
}

impl EncodedFormula {
    /// Creates a new constant `true` or `false` based on `value`.
    ///
    /// Note that, a constant is the only type of a formula, that does not need
    /// a [`FormulaFactory`].
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::formulas::{EncodedFormula, FormulaType};
    ///
    /// let verum = EncodedFormula::constant(true);
    /// let falsum = EncodedFormula::constant(false);
    ///
    /// assert_eq!(verum.formula_type(), FormulaType::True);
    /// assert_eq!(falsum.formula_type(), FormulaType::False);
    /// ```
    pub fn constant(value: bool) -> Self {
        let ty = if value { FormulaType::True } else { FormulaType::False };
        Self::from(FormulaEncoding::encode_type(ty))
    }

    /// Returns the type of the formula as a `FormulaType` enum.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::formulas::{FormulaFactory, FormulaType, ToFormula};
    /// let f = FormulaFactory::new();
    ///
    /// let formula1 = "$true".to_formula(&f);
    /// let formula2 = "a & b".to_formula(&f);
    /// let formula3 = "a + b + c = 1".to_formula(&f);
    ///
    /// assert_eq!(formula1.formula_type(), FormulaType::True);
    /// assert_eq!(formula2.formula_type(), FormulaType::And);
    /// assert_eq!(formula3.formula_type(), FormulaType::Cc)
    /// ```
    pub fn formula_type(self) -> FormulaType {
        self.encoding.formula_type()
    }

    /// Unpacks a `EncodedFormula` in a [`Formula`] enum, providing access to
    /// the structure of the formula.
    ///
    /// - If the formula is `True`, `False` it returns the respective constants.
    /// - If the formula is a Literal it returns a copy of the literal.
    /// - If the formula is a `Not`, `Equiv`, `Impl` it returns the respective
    ///   operands as `EncodedFormula`s.
    /// - If the formula is a `Pbc` or `Cc` it returns a shared reference to the
    ///   objects stored in the `FormulaFactory`.
    /// - If the formula is a n-ary operator (`And` and `Or`) it returns a
    ///   `NaryIterator`, which holds a reference to the operands in the
    ///   `FormulaFactory`. The `NaryIterator` can be used to iterate over those
    ///   operands. If you want to dissolve the reference to the `FormulaFactory`
    ///   you can use [`NaryIterator::into_owned`] or [`NaryIterator::into_vec`] to
    ///   clone the operands.
    ///
    /// You should drop the obtained `Formula` as soon as possible, because it
    /// can have a shared reference to objects in the `FormulaFactory`. The
    /// current design of `LogicNG Rust`, however, requires for most functions
    /// an exclusive reference of the `FormulaFactory`. So the borrow
    /// checker will not allow to call such functions as long as a `Formula`
    /// exists.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::formulas::{FormulaFactory, Formula, ToFormula};
    /// # let f = FormulaFactory::new();
    ///
    /// # let formula = "$true".to_formula(&f);
    ///
    /// match formula.unpack(&f) {
    ///     Formula::True => {},
    ///     Formula::False => {},
    ///     Formula::Lit(literal) => {},
    ///     Formula::Not(operand) => {},
    ///     Formula::Equiv((left, right)) => {},
    ///     Formula::Impl((left, right)) => {},
    ///     Formula::Pbc(pbc) => {},
    ///     Formula::Cc(cc) => {},
    ///     Formula::Or(operands_iterator) => {},
    ///     Formula::And(operands_iterator) => {},
    /// }
    /// ```
    pub fn unpack(self, f: &FormulaFactory) -> Formula {
        match self.formula_type() {
            FormulaType::Pbc => Formula::Pbc(&f.pbcs[self.encoding]),
            FormulaType::Cc => Formula::Cc(&f.ccs[self.encoding]),
            FormulaType::Equiv => Formula::Equiv(f.equivs.get(self.encoding)),
            FormulaType::Impl => Formula::Impl(f.impls.get(self.encoding)),
            FormulaType::Or => Formula::Or(f.ors.get_iter(self.encoding)),
            FormulaType::And => Formula::And(f.ands.get_iter(self.encoding)),
            FormulaType::Not => Formula::Not(f.nots.get(self.encoding)),
            FormulaType::Lit(LitType::Pos(_)) => Formula::Lit(Literal::Pos(Variable::try_from(self).unwrap())),
            FormulaType::Lit(LitType::Neg(_)) => Formula::Lit(Literal::Neg(Variable::try_from(self).unwrap())),
            FormulaType::True => Formula::True,
            FormulaType::False => Formula::False,
        }
    }

    /// Compares this formula with another formula and returns `true` if both
    /// are the same formula type. So only the type is considered and not the
    /// actual formula.
    ///
    /// When comparing literals, this function will not consider the phase or
    /// variable type. So two literals always have the same type.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::formulas::FormulaFactory;
    /// # use logicng::formulas::ToFormula;
    /// let f = FormulaFactory::new();
    ///
    /// let formula1 = "a <=> b".to_formula(&f);
    /// let formula2 = "a => b".to_formula(&f);
    ///
    /// assert!(!formula1.same_type(formula2));
    ///
    /// let formula1 = f.not(formula1); //~(a <=> b)
    /// let formula2 = f.not(formula2); //~(a => b)
    ///
    /// assert!(formula1.same_type(formula2));
    /// ```
    pub fn same_type(self, other: Self) -> bool {
        self.is_type(other.formula_type())
    }

    /// Returns `true` if and only if this formula is of type `other_ty`.
    ///
    /// When comparing literals, this function will not consider the phase or
    /// variable type.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::formulas::FormulaFactory;
    /// # use logicng::formulas::FormulaType;
    /// # use logicng::formulas::ToFormula;
    /// let f = FormulaFactory::new();
    ///
    /// let formula1 = "a <=> b".to_formula(&f);
    /// let formula2 = "a => b".to_formula(&f);
    /// let formula3 = f.not(formula1); //~(a <=> b)
    /// let formula4 = f.not(formula2); //~(a => b)
    ///
    /// assert!(formula1.is_type(FormulaType::Equiv));
    /// assert!(formula2.is_type(FormulaType::Impl));
    /// assert!(formula3.is_type(FormulaType::Not));
    /// assert!(formula4.is_type(FormulaType::Not));
    /// ```
    pub fn is_type(self, other_ty: FormulaType) -> bool {
        let ty = self.formula_type();
        match ty {
            FormulaType::Lit(_) => matches!(other_ty, FormulaType::Lit(_)),
            _ => ty == other_ty,
        }
    }

    /// Returns `true` if this formula is the constant `False`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::formulas::EncodedFormula;
    ///
    /// let formula1 = EncodedFormula::constant(false);
    /// let formula2 = EncodedFormula::constant(true);
    ///
    /// assert!(formula1.is_falsum());
    /// assert!(!formula2.is_falsum());
    /// ```
    pub fn is_falsum(self) -> bool {
        matches!(self.formula_type(), FormulaType::False)
    }

    /// Returns `true` if this formula is the constant `True`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::formulas::EncodedFormula;
    ///
    /// let formula1 = EncodedFormula::constant(true);
    /// let formula2 = EncodedFormula::constant(false);
    ///
    /// assert!(formula1.is_verum());
    /// assert!(!formula2.is_verum());
    /// ```
    pub fn is_verum(self) -> bool {
        matches!(self.formula_type(), FormulaType::True)
    }

    /// Returns `true` if this formula is a constant (`True` or `False`).
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::formulas::EncodedFormula;
    ///
    /// let formula1 = EncodedFormula::constant(true);
    /// let formula2 = EncodedFormula::constant(false);
    ///
    /// assert!(formula1.is_constant());
    /// assert!(formula2.is_constant());
    /// ```
    pub fn is_constant(self) -> bool {
        self.is_falsum() || self.is_verum()
    }

    /// Returns `true` if this formula is variable/positive literal.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::formulas::FormulaFactory;
    /// let f = FormulaFactory::new();
    ///
    /// let formula1 = f.variable("a");
    /// let formula2 = f.literal("b", true);
    /// let formula3 = f.literal("c", false);
    ///
    /// assert!(formula1.is_variable());
    /// assert!(formula2.is_variable());
    /// assert!(!formula3.is_variable());
    /// ```
    pub fn is_variable(self) -> bool {
        matches!(self.formula_type(), FormulaType::Lit(LitType::Pos(_)))
    }

    /// Returns `true` if this formula is negative literal.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::formulas::FormulaFactory;
    /// let f = FormulaFactory::new();
    ///
    /// let formula1 = f.variable("a");
    /// let formula2 = f.literal("b", true);
    /// let formula3 = f.literal("c", false);
    ///
    /// assert!(!formula1.is_negative_literal());
    /// assert!(!formula2.is_negative_literal());
    /// assert!(formula3.is_negative_literal());
    /// ```
    pub fn is_negative_literal(self) -> bool {
        matches!(self.formula_type(), FormulaType::Lit(LitType::Neg(_)))
    }

    /// Returns `true` if this formula is literal.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::formulas::FormulaFactory;
    /// let f = FormulaFactory::new();
    ///
    /// let formula1 = f.variable("a");
    /// let formula2 = f.literal("b", true);
    /// let formula3 = f.literal("c", false);
    ///
    /// assert!(formula1.is_literal());
    /// assert!(formula2.is_literal());
    /// assert!(formula3.is_literal());
    /// ```
    pub fn is_literal(self) -> bool {
        self.is_variable() || self.is_negative_literal()
    }

    /// Returns `true` if this formula is a cardinality constraint.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::formulas::FormulaFactory;
    /// # use logicng::formulas::ToFormula;
    /// let f = FormulaFactory::new();
    ///
    /// let formula = "a + b = 1".to_formula(&f);
    ///
    /// assert!(formula.is_cc());
    /// ```
    pub fn is_cc(self) -> bool {
        matches!(self.formula_type(), FormulaType::Cc)
    }

    /// Returns `true` if this formula is a pseudo-boolean constraint, but not
    /// an cardinality constraint.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::formulas::FormulaFactory;
    /// # use logicng::formulas::ToFormula;
    /// let f = FormulaFactory::new();
    ///
    /// let formula = "2*a + 3*b >= 2".to_formula(&f);
    ///
    /// assert!(formula.is_pbc());
    /// ```
    pub fn is_pbc(self) -> bool {
        matches!(self.formula_type(), FormulaType::Pbc)
    }

    /// Returns `true` if this formula is atomic. A atomic formula is a constant,
    /// literal, cardinality constraint, or pseudo boolean constraint.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::formulas::FormulaFactory;
    /// # use logicng::formulas::EncodedFormula;
    /// # use logicng::formulas::ToFormula;
    /// let f = FormulaFactory::new();
    ///
    /// let formula1 = EncodedFormula::constant(true);
    /// let formula2 = EncodedFormula::constant(false);
    /// let formula3 = f.variable("a");
    /// let formula4 = f.literal("b", true);
    /// let formula5 = f.literal("c", false);
    /// let formula6 = "a + b = 1".to_formula(&f);
    /// let formula7 = "2*a + 3*b >= 2".to_formula(&f);
    ///
    /// assert!(formula1.is_atomic());
    /// assert!(formula2.is_atomic());
    /// assert!(formula3.is_atomic());
    /// assert!(formula4.is_atomic());
    /// assert!(formula5.is_atomic());
    /// assert!(formula6.is_atomic());
    /// assert!(formula7.is_atomic());
    /// ```
    pub fn is_atomic(self) -> bool {
        self.is_literal() || self.is_constant() || self.is_cc() || self.is_pbc()
    }

    /// Returns `true` if this formula is a conjunction.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::formulas::FormulaFactory;
    /// # use logicng::formulas::ToFormula;
    /// let f = FormulaFactory::new();
    ///
    /// let formula1 = "a & b".to_formula(&f);
    /// let formula2 = "a | b".to_formula(&f);
    ///
    /// assert!(formula1.is_and());
    /// assert!(!formula2.is_and());
    /// ```
    pub fn is_and(self) -> bool {
        matches!(self.formula_type(), FormulaType::And)
    }

    /// Returns `true` if this formula is a disjunction.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::formulas::FormulaFactory;
    /// # use logicng::formulas::ToFormula;
    /// let f = FormulaFactory::new();
    ///
    /// let formula1 = "a | b".to_formula(&f);
    /// let formula2 = "a & b".to_formula(&f);
    ///
    /// assert!(formula1.is_or());
    /// assert!(!formula2.is_or());
    /// ```
    pub fn is_or(self) -> bool {
        matches!(self.formula_type(), FormulaType::Or)
    }

    /// Returns `true` if this formula is a _n-ary_ operator (disjunction or conjunction).
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::formulas::FormulaFactory;
    /// # use logicng::formulas::ToFormula;
    /// let f = FormulaFactory::new();
    ///
    /// let formula1 = "a & b".to_formula(&f);
    /// let formula2 = "a | b".to_formula(&f);
    ///
    /// assert!(formula1.is_nary_operator());
    /// assert!(formula2.is_nary_operator());
    /// ```
    pub fn is_nary_operator(self) -> bool {
        self.is_and() || self.is_or()
    }

    /// Returns `true` if this formula is an implication.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::formulas::FormulaFactory;
    /// # use logicng::formulas::ToFormula;
    /// let f = FormulaFactory::new();
    ///
    /// let formula1 = "a => b".to_formula(&f);
    /// let formula2 = "a <=> b".to_formula(&f);
    ///
    /// assert!(formula1.is_impl());
    /// assert!(!formula2.is_impl());
    /// ```
    pub fn is_impl(self) -> bool {
        matches!(self.formula_type(), FormulaType::Impl)
    }

    /// Returns `true` if this formula is an equivalence.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::formulas::FormulaFactory;
    /// # use logicng::formulas::ToFormula;
    /// let f = FormulaFactory::new();
    ///
    /// let formula1 = "a <=> b".to_formula(&f);
    /// let formula2 = "a => b".to_formula(&f);
    ///
    /// assert!(formula1.is_equiv());
    /// assert!(!formula2.is_equiv());
    /// ```
    pub fn is_equiv(self) -> bool {
        matches!(self.formula_type(), FormulaType::Equiv)
    }

    /// Returns `true` if this formula is a binary operator (implication or equivalence).
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::formulas::FormulaFactory;
    /// # use logicng::formulas::ToFormula;
    /// let f = FormulaFactory::new();
    ///
    /// let formula1 = "a <=> b".to_formula(&f);
    /// let formula2 = "a => b".to_formula(&f);
    ///
    /// assert!(formula1.is_binary_operator());
    /// assert!(formula2.is_binary_operator());
    /// ```
    pub fn is_binary_operator(self) -> bool {
        self.is_impl() || self.is_equiv()
    }

    /// Returns `true` if this formula is a negation. This does not include negative
    /// literals.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::formulas::FormulaFactory;
    /// # use logicng::formulas::ToFormula;
    /// let f = FormulaFactory::new();
    ///
    /// let formula1 = "~(a <=> b)".to_formula(&f);
    /// let formula2 = "~a".to_formula(&f);
    ///
    /// assert!(formula1.is_not());
    /// assert!(!formula2.is_not());
    /// ```
    pub fn is_not(self) -> bool {
        matches!(self.formula_type(), FormulaType::Not)
    }

    /// Returns `true` if this formula is in NNF.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::formulas::FormulaFactory;
    /// # use logicng::formulas::ToFormula;
    /// let f = FormulaFactory::new();
    ///
    /// let formula1 = "a => b".to_formula(&f);
    /// let formula2 = "~a | b".to_formula(&f);
    ///
    /// assert!(!formula1.is_nnf(&f));
    /// assert!(formula2.is_nnf(&f));
    /// ```
    pub fn is_nnf(self, f: &FormulaFactory) -> bool {
        predicates::is_nnf(self, f)
    }

    /// Returns `true` if this formula is in CNF.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::formulas::FormulaFactory;
    /// # use logicng::formulas::ToFormula;
    /// let f = FormulaFactory::new();
    ///
    /// let formula1 = "(a & b) | c".to_formula(&f);
    /// let formula2 = "(a | c) & (b | c)".to_formula(&f);
    ///
    /// assert!(!formula1.is_cnf(&f));
    /// assert!(formula2.is_cnf(&f));
    /// ```
    pub fn is_cnf(self, f: &FormulaFactory) -> bool {
        predicates::is_cnf(self, f)
    }

    /// Returns `true` if this formula is in DNF.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::formulas::FormulaFactory;
    /// # use logicng::formulas::ToFormula;
    /// let f = FormulaFactory::new();
    ///
    /// let formula1 = "(a | b) & c".to_formula(&f);
    /// let formula2 = "(a & c) | (b & c)".to_formula(&f);
    ///
    /// assert!(!formula1.is_dnf(&f));
    /// assert!(formula2.is_dnf(&f));
    /// ```
    pub fn is_dnf(self, f: &FormulaFactory) -> bool {
        predicates::is_dnf(self, f)
    }

    /// Returns a vector of all operands of this formula.
    ///
    /// _n-ary_ operators return all their operands, _binary_ operators return
    /// their `left` and `right` operands, `Not` returns a vector with only its
    /// inner formula, and all other formulas return an empty vector.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::formulas::FormulaFactory;
    /// # use logicng::formulas::ToFormula;
    /// let f = FormulaFactory::new();
    ///
    /// let a = f.variable("a");
    /// let b = f.variable("b");
    /// let c = f.variable("c");
    ///
    /// let formula1 = "a & b & c".to_formula(&f);
    /// let formula2 = "a => b".to_formula(&f);
    /// let formula3 = f.not(formula2);
    ///
    /// assert_eq!(a.operands(&f), vec![]);
    /// assert_eq!(formula1.operands(&f), vec![a, b, c]);
    /// assert_eq!(formula2.operands(&f), vec![a, b]);
    /// assert_eq!(formula3.operands(&f), vec![formula2]);
    /// ```
    pub fn operands(self, f: &FormulaFactory) -> Vec<Self> {
        functions::operands(self, f)
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
    /// # use std::collections::BTreeSet;
    /// let f = FormulaFactory::new();
    ///
    /// let a = f.var("a");
    /// let b = f.var("b");
    /// let c = f.var("c");
    /// let formula = "(a => b) & c".to_formula(&f);
    ///
    /// let expected = BTreeSet::from_iter(vec![a, b, c].into_iter());
    /// assert_eq!(formula.variables(&f).as_ref(), &expected);
    pub fn variables(self, f: &FormulaFactory) -> Arc<BTreeSet<Variable>> {
        functions::variables(self, f)
    }

    /// Returns a set with all names of the variables in this formula.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::formulas::FormulaFactory;
    /// # use logicng::formulas::ToFormula;
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
    /// assert_eq!(formula.string_variables(&f), expected)
    /// ```
    pub fn string_variables(self, f: &FormulaFactory) -> BTreeSet<Cow<str>> {
        functions::string_variables(self, f)
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
    /// # use std::collections::BTreeSet;
    /// let f = FormulaFactory::new();
    ///
    /// let a = f.lit("a", true);
    /// let b = f.lit("b", true);
    /// let c = f.lit("c", false);
    /// let formula = "(a => b) & ~c".to_formula(&f);
    ///
    /// let expected = BTreeSet::from_iter(vec![a, b, c].into_iter());
    /// assert_eq!(formula.literals(&f).as_ref(), &expected);
    /// ```
    pub fn literals(self, f: &FormulaFactory) -> Arc<BTreeSet<Literal>> {
        functions::literals(self, f)
    }

    /// Returns a set with all names of the variables in this formula.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::formulas::FormulaFactory;
    /// # use logicng::formulas::ToFormula;
    /// # use logicng::formulas::StringLiteral;
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
    /// assert_eq!(formula.string_literals(&f), expected)
    /// ```
    pub fn string_literals(self, f: &FormulaFactory) -> BTreeSet<StringLiteral> {
        functions::string_literals(self, f)
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
    /// assert_eq!(formula1.literals_for_clause_or_term(&f), vec![]);
    /// assert_eq!(formula2.literals_for_clause_or_term(&f), vec![a]);
    /// assert_eq!(formula3.literals_for_clause_or_term(&f), vec![a, b, c]);
    /// assert_eq!(formula4.literals_for_clause_or_term(&f), vec![a, b, c]);
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
    /// //formula1.literals_for_clause_or_term(&f); //PANIC!
    /// //formula2.literals_for_clause_or_term(&f); //PANIC!
    /// ```
    pub fn literals_for_clause_or_term(self, f: &FormulaFactory) -> Vec<Literal> {
        functions::literals_for_clause_or_term(self, f)
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
    /// let f = FormulaFactory::new();
    ///
    /// let formula1 = "$true".to_formula(&f);
    /// let formula2 = "a => b".to_formula(&f);
    /// let formula3 = "a & b & c".to_formula(&f);
    /// let formula4 = "a + b = 1".to_formula(&f);
    ///
    /// assert_eq!(formula1.number_of_atoms(&f), 1);
    /// assert_eq!(formula2.number_of_atoms(&f), 2);
    /// assert_eq!(formula3.number_of_atoms(&f), 3);
    /// assert_eq!(formula4.number_of_atoms(&f), 1);
    /// ```
    pub fn number_of_atoms(self, f: &FormulaFactory) -> u64 {
        functions::number_of_atoms(self, f)
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
    /// let f = FormulaFactory::new();
    ///
    /// let formula1 = "$true".to_formula(&f);
    /// let formula2 = "a => (b & (c + d = 1))".to_formula(&f);
    /// let formula3 = "a & b & c".to_formula(&f);
    /// let formula4 = "a + b = 1".to_formula(&f);
    ///
    /// assert_eq!(formula1.number_of_internal_nodes(&f), 1);
    /// assert_eq!(formula2.number_of_internal_nodes(&f), 5);
    /// assert_eq!(formula3.number_of_internal_nodes(&f), 4);
    /// assert_eq!(formula4.number_of_internal_nodes(&f), 1);
    /// ```
    pub fn number_of_internal_nodes(self, f: &FormulaFactory) -> u64 {
        functions::number_of_internal_nodes(self, f)
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
    /// let f = FormulaFactory::new();
    ///
    /// let formula1 = "$true".to_formula(&f);
    /// let formula2 = "a => (b & (c + d = 1))".to_formula(&f);
    /// let formula3 = "a & b & c".to_formula(&f);
    /// let formula4 = "a + b = 1".to_formula(&f);
    ///
    /// assert_eq!(formula1.number_of_nodes(&f), 1);
    /// assert_eq!(formula2.number_of_nodes(&f), 7);
    /// assert_eq!(formula3.number_of_nodes(&f), 4);
    /// assert_eq!(formula4.number_of_nodes(&f), 3);
    /// ```
    pub fn number_of_nodes(self, f: &FormulaFactory) -> u64 {
        functions::number_of_nodes(self, f)
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
    /// let f = FormulaFactory::new();
    ///
    /// let formula1 = "$true".to_formula(&f);
    /// let formula2 = "a => b".to_formula(&f);
    /// let formula3 = "a & b & c".to_formula(&f);
    /// let formula4 = "a + b = 1".to_formula(&f);
    ///
    /// assert_eq!(formula1.number_of_operands(&f), 0);
    /// assert_eq!(formula2.number_of_operands(&f), 2);
    /// assert_eq!(formula3.number_of_operands(&f), 3);
    /// assert_eq!(formula4.number_of_operands(&f), 0);
    /// ```
    pub fn number_of_operands(self, f: &FormulaFactory) -> usize {
        functions::number_of_operands(self, f)
    }

    /// Returns `true` if a given variable name is found in this formula, `false` otherwise.
    ///
    /// If you have a `Variable` instance you are searching for, you can instead use [`contains_variable`].
    ///
    /// [`contains_variable`]: EncodedFormula::contains_variable
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::formulas::FormulaFactory;
    /// # use logicng::formulas::ToFormula;
    /// let f = FormulaFactory::new();
    ///
    /// let formula = "a => (b & c)".to_formula(&f);
    ///
    /// assert!(formula.contains_var_name("b", &f));
    /// assert!(!formula.contains_var_name("d", &f));
    /// ```
    pub fn contains_var_name(self, variable: &str, f: &FormulaFactory) -> bool {
        predicates::contains_var_name(self, variable, f)
    }

    /// Returns `true` if a given variable name is found in this formula, `false` otherwise.
    ///
    /// If you have only the name of a variable, you can instead use [`contains_var_name`].
    ///
    /// [`contains_var_name`]: EncodedFormula::contains_var_name
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::formulas::FormulaFactory;
    /// # use logicng::formulas::ToFormula;
    /// let f = FormulaFactory::new();
    ///
    /// let formula = "a => (b & c)".to_formula(&f);
    ///
    /// let b = f.var("b");
    /// let d = f.var("d");
    ///
    /// assert!(formula.contains_variable(b, &f));
    /// assert!(!formula.contains_variable(d, &f));
    /// ```
    pub fn contains_variable(self, variable: Variable, f: &FormulaFactory) -> bool {
        predicates::contains_node(self, variable.into(), f)
    }

    /// Returns `true` if this formula contains `formula`, `false` otherwise.
    ///
    /// This is very similar to asking wether `formula` is a sub-formula of this
    /// formula. But not quite the same, because a `FormulaFactory` stores some
    /// formulas differently: For example a literal `~a` does not contain the
    /// literal/variable `a`. Or `a & b` does contain `b & a`.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::formulas::FormulaFactory;
    /// # use logicng::formulas::ToFormula;
    /// let f = FormulaFactory::new();
    ///
    /// let formula = "a => (b & c)".to_formula(&f);
    ///
    /// let sub1 = "b & c".to_formula(&f);
    /// let sub2 = "a => b".to_formula(&f);
    ///
    /// assert!(formula.contains_node(sub1, &f));
    /// assert!(!formula.contains_node(sub2, &f));
    /// ```
    pub fn contains_node(self, formula: Self, f: &FormulaFactory) -> bool {
        predicates::contains_node(self, formula, f)
    }

    /// Returns this formula as the explicit literal type. If the formula isn't
    /// a literal, it will return `None`.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::formulas::FormulaFactory;
    /// let f = FormulaFactory::new();
    ///
    /// let formula1 = f.literal("a", true);
    /// let formula2 = f.verum();
    ///
    /// let lit1 = f.lit("a", true);
    ///
    /// assert_eq!(formula1.as_literal(), Some(lit1));
    /// assert_eq!(formula2.as_literal(), None);
    /// ```
    pub fn as_literal(self) -> Option<Literal> {
        match self.formula_type() {
            FormulaType::Lit(LitType::Pos(_)) => Some(Literal::Pos(Variable::try_from(self).unwrap())),
            FormulaType::Lit(LitType::Neg(_)) => Some(Literal::Neg(Variable::try_from(self).unwrap())),
            _ => None,
        }
    }

    /// Returns this formula as the explicit variable type. If the formula isn't
    /// a variable/positive literal, it will return `None`.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::formulas::FormulaFactory;
    /// let f = FormulaFactory::new();
    ///
    /// let formula1 = f.variable("a");
    /// let formula2 = f.verum();
    ///
    /// let var1 = f.var("a");
    ///
    /// assert_eq!(formula1.as_variable(), Some(var1));
    /// assert_eq!(formula2.as_variable(), None);
    /// ```
    pub fn as_variable(self) -> Option<Variable> {
        match self.formula_type() {
            FormulaType::Lit(LitType::Pos(_)) => Some(Variable::try_from(self).unwrap()),
            _ => None,
        }
    }

    /// Returns this formula as the explicit cardinality constraints type. If
    /// the formula isn't a cardinality constraint, it will return `None`.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::formulas::FormulaFactory;
    /// # use logicng::formulas::ToFormula;
    /// # use logicng::formulas::{CType, CardinalityConstraint};
    /// let f = FormulaFactory::new();
    ///
    /// let formula = "a + b = 1".to_formula(&f);
    ///
    /// let cc: CardinalityConstraint = formula.as_cc(&f).unwrap();
    /// ```
    pub fn as_cc(self, f: &FormulaFactory) -> Option<CardinalityConstraint> {
        match self.unpack(f) {
            Formula::Cc(cc) => Some(cc.clone()),
            _ => None,
        }
    }

    /// Returns this formula as the explicit pseudo-boolean constraints type. If
    /// the formula isn't a pseudo-boolean constraint, it will return `None`.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::formulas::{CType, PbConstraint, ToFormula, FormulaFactory};
    /// let f = FormulaFactory::new();
    ///
    /// let formula = "2 * a + b = 1".to_formula(&f);
    ///
    /// let pbc: PbConstraint = formula.as_pbc(&f).unwrap();
    /// ```
    pub fn as_pbc(self, f: &FormulaFactory) -> Option<PbConstraint> {
        match self.unpack(f) {
            Formula::Pbc(pbc) => Some(pbc.clone()),
            _ => None,
        }
    }

    /// Returns the left operand of a binary operator. If the formula isn't a
    /// binary operator, it will return `None`.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::formulas::FormulaFactory;
    /// # use logicng::formulas::ToFormula;
    /// let f = FormulaFactory::new();
    ///
    /// let formula = "a => b".to_formula(&f);
    ///
    /// let a = f.variable("a");
    ///
    /// assert_eq!(formula.left(&f), Some(a));
    /// ```
    pub fn left(self, f: &FormulaFactory) -> Option<Self> {
        match self.formula_type() {
            FormulaType::Equiv => Some(f.equivs.get(self.encoding).0),
            FormulaType::Impl => Some(f.impls.get(self.encoding).0),
            _ => None,
        }
    }

    /// Returns the right operand of a binary operator. If the formula isn't a
    /// binary operator constraint, it will return `None`.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::formulas::FormulaFactory;
    /// # use logicng::formulas::ToFormula;
    /// let f = FormulaFactory::new();
    ///
    /// let formula = "a => b".to_formula(&f);
    ///
    /// let b = f.variable("b");
    ///
    /// assert_eq!(formula.right(&f), Some(b));
    /// ```
    pub fn right(self, f: &FormulaFactory) -> Option<Self> {
        match self.formula_type() {
            FormulaType::Equiv => Some(f.equivs.get(self.encoding).1),
            FormulaType::Impl => Some(f.impls.get(self.encoding).1),
            _ => None,
        }
    }

    /// Return the operand of a `Not`-node. If the formula isn't a `Not`-node,
    /// it will return `None`.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::formulas::FormulaFactory;
    /// # use logicng::formulas::ToFormula;
    /// let f = FormulaFactory::new();
    ///
    /// let formula = "~ (a => b)".to_formula(&f);
    ///
    /// let expected = "a => b".to_formula(&f);
    ///
    /// assert_eq!(formula.not_operand(&f), Some(expected));
    /// ```
    pub fn not_operand(self, f: &FormulaFactory) -> Option<Self> {
        match self.unpack(f) {
            Formula::Not(op) => Some(op),
            _ => None,
        }
    }

    /// Converts this formula into a string representation.
    ///
    /// Strings obtained by this function, can also be parsed back again.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::formulas::FormulaFactory;
    /// # use logicng::formulas::ToFormula;
    /// let f = FormulaFactory::new();
    ///
    /// let str1 = "$true";
    /// let str2 = "a & b & c";
    /// let str3 = "~(a => b)";
    ///
    /// let formula1 = str1.to_formula(&f);
    /// let formula2 = str2.to_formula(&f);
    /// let formula3 = str3.to_formula(&f);
    ///
    /// assert_eq!(formula1.to_string(&f), str1);
    /// assert_eq!(formula2.to_string(&f), str2);
    /// assert_eq!(formula3.to_string(&f), str3);
    /// ```
    pub fn to_string(self, f: &FormulaFactory) -> String {
        match self.unpack(f) {
            Formula::True => "$true".to_string(),
            Formula::False => "$false".to_string(),
            Formula::Lit(lit) => lit.to_string(f),
            Formula::And(_) => self.nary_to_string(" & ", f),
            Formula::Or(_) => self.nary_to_string(" | ", f),
            Formula::Not(op) => {
                format!("~({})", op.to_string(f))
            }
            Formula::Impl(_) => self.nary_to_string(" => ", f),
            Formula::Equiv(_) => self.nary_to_string(" <=> ", f),
            Formula::Cc(cc) => cc.to_string(f),
            Formula::Pbc(pbc) => pbc.to_string(f),
        }
    }

    pub(crate) fn precedence(self) -> u8 {
        use FormulaType::{And, Cc, Equiv, False, Impl, Lit, Not, Or, Pbc, True};
        match self.formula_type() {
            Pbc => 0_u8,
            Cc => 1_u8,
            Equiv => 2_u8,
            Impl => 3_u8,
            Or => 4_u8,
            And => 5_u8,
            Not => 6_u8,
            Lit(_) => LIT_PRECEDENCE,
            True => 8_u8,
            False => 9_u8,
        }
    }

    fn nary_to_string(self, op_char: &str, f: &FormulaFactory) -> String {
        let mut result = String::new();
        for (i, op) in self.operands(f).iter().enumerate() {
            if i > 0 {
                result.push_str(op_char);
            }
            if self.precedence() > op.precedence() {
                result.push_str(&format!("({})", &op.to_string(f)));
            } else {
                result.push_str(&op.to_string(f));
            }
        }
        result
    }
}

impl From<FormulaEncoding> for EncodedFormula {
    fn from(encoding: FormulaEncoding) -> Self {
        Self { encoding }
    }
}

impl TryFrom<EncodedFormula> for Variable {
    type Error = String;

    fn try_from(formula: EncodedFormula) -> Result<Self, Self::Error> {
        Self::try_from(formula.encoding)
    }
}

/// Trait for converting a type into a formula of the given [`FormulaFactory`].
pub trait ToFormula {
    /// Converts `self` into a formula of `f`.
    fn to_formula(&self, f: &FormulaFactory) -> EncodedFormula;
}

impl ToFormula for str {
    /// Parses a string into a `Formula`.
    ///
    /// It only work if the passed string also
    /// is a valid function. So you need to be sure, that the input string is
    /// valid. If you are not sure, whether the input is a valid formula, you should use [`parse`]
    ///
    /// [`parse`]: FormulaFactory::parse
    ///
    /// # Panic
    ///
    /// This function panics if input string is not a valid formula.
    fn to_formula(&self, f: &FormulaFactory) -> EncodedFormula {
        f.parse(self).unwrap()
    }
}

#[allow(clippy::redundant_pub_crate)] // Seems to be just wrong.
pub(crate) const LIT_PRECEDENCE: u8 = 7_u8;

#[cfg(test)]
mod tests {
    use crate::formulas::VarType;

    use super::*;

    #[test]
    fn test_formula_creation() {
        fn ff_lit(n: u64, phase: bool) -> EncodedFormula {
            if phase {
                EncodedFormula::from(FormulaEncoding::encode(n, FormulaType::Lit(LitType::Pos(VarType::FF)), true))
            } else {
                EncodedFormula::from(FormulaEncoding::encode(n, FormulaType::Lit(LitType::Neg(VarType::FF)), true))
            }
        }

        fn df(n: u64, ty: FormulaType, large_cache: bool) -> EncodedFormula {
            EncodedFormula::from(FormulaEncoding::encode(n, ty, large_cache))
        }

        let factory = FormulaFactory::new();
        let va = factory.variable("a");
        let vb = factory.variable("b");
        let vc = factory.variable("c");
        let vd = factory.variable("d");
        let ve = factory.variable("e");
        let vg = factory.variable("g");
        let na = factory.literal("a", false);
        let nh = factory.literal("nh", false);
        let ab = factory.and([va, vb]);
        let ab_c_d = factory.or([ab, vc, vd]);
        let ab_c_d2 = factory.or([ab, vc, vd]);
        let nab = factory.not(ab);
        let ab_z_ab_c_d = factory.implication(ab, ab_c_d);
        let d_e = factory.or([vd, ve]);
        let ab_eq_d_e = factory.equivalence(ab, d_e);
        let ab_eq_d_e2 = factory.equivalence(ab, d_e);
        let de = factory.and([vd, ab_eq_d_e]);
        let de2 = factory.and([vd, ab_eq_d_e]);

        assert_eq!(factory.verum().unpack(&factory), Formula::True);
        assert_eq!(factory.falsum().unpack(&factory), Formula::False);
        assert_eq!(va, ff_lit(0, true));
        assert_eq!(vb, ff_lit(1, true));
        assert_eq!(vc, ff_lit(2, true));
        assert_eq!(vd, ff_lit(3, true));
        assert_eq!(ve, ff_lit(4, true));
        assert_eq!(vg, ff_lit(5, true));
        assert_eq!(na, ff_lit(0, false));
        assert_eq!(nh, ff_lit(6, false));
        assert_eq!(ab, df(0, FormulaType::And, false));
        assert_eq!(ab_c_d, df(0, FormulaType::Or, false));
        assert_eq!(ab_c_d2, df(0, FormulaType::Or, false));
        assert_eq!(nab, df(0, FormulaType::Not, false));
        assert_eq!(ab_z_ab_c_d, df(0, FormulaType::Impl, false));
        assert_eq!(d_e, df(1, FormulaType::Or, false));
        assert_eq!(ab_eq_d_e, df(0, FormulaType::Equiv, false));
        assert_eq!(ab_eq_d_e2, df(0, FormulaType::Equiv, false));
        assert_eq!(de, df(1, FormulaType::And, false));
        assert_eq!(de2, df(1, FormulaType::And, false));
    }

    #[test]
    #[allow(clippy::many_single_char_names)]
    fn test_to_string() {
        let f = FormulaFactory::new();
        let a = f.variable("a");
        let b = f.variable("b");
        let c = f.variable("c");
        let d = f.variable("d");
        let e = f.variable("e");
        let _g = f.variable("g");
        let na = f.literal("a", false);
        let _nh = f.literal("nh", false);
        let ab = f.and([a, b]);
        let ab_c_d = f.or([ab, c, d]);
        let _ab_c_d2 = f.or([ab, c, d]);
        let _nab = f.not(ab);
        let _ab_z_ab_c_d = f.implication(ab, ab_c_d);
        let d_e = f.or([d, e]);
        let ab_eq_d_e = f.equivalence(ab, d_e);
        let _ab_eq_d_e2 = f.equivalence(ab, d_e);
        let de = f.and([d, ab_eq_d_e]);
        let _de2 = f.and([d, ab_eq_d_e]);
        assert_eq!(na.to_string(&f), "~a");
        assert_eq!(de.to_string(&f), "d & (a & b <=> d | e)");
    }

    #[test]
    fn test_from_string() {
        let f = FormulaFactory::new();
        let formula1 = String::from("a & b => ~c").to_formula(&f);
        let formula2 = "a & b => ~c".to_formula(&f);

        assert_eq!(formula1, f.parse("a & b => ~c").unwrap());
        assert_eq!(formula2, f.parse("a & b => ~c").unwrap());
    }
}
