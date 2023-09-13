use std::borrow::Cow;
use std::fmt::{Display, Formatter};

use crate::formulas::{EncodedFormula, FormulaFactory, Variable};

use super::formula::ToFormula;
use super::formula_cache::formula_encoding::{Encoding, FormulaEncoding};
use super::{FormulaType, VarType};

/// Specifies all types of literals.
#[derive(Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd, Debug)]
pub enum LitType {
    /// Positive literal
    Pos(VarType),
    /// Negative literal
    Neg(VarType),
}

/// Boolean literal.
///
/// Literals are besides the constants `True` and `False` and
/// cardinality/pseudo-boolean constraints the atomic formulas in _LogicNG_.
///
/// A literal consists of a [`Variable`] and its phase (also sign or polarity in
/// the literature).
///
/// `Literal` is the explicit type for literals. A literal can also be in the
/// form of an [`EncodedFormula`], and a [`Variable`] is in many contexts used as a
/// positive literal. When deciding for a type, you want to use the most
/// specific type. For example, if you only need literals, you should use the
/// explicit type `Literal`, but if you allow a mix of multiple formula types,
/// it is easier to use `EncodedFormula`.
///
/// There are multiple ways to create a new `Literal`:
/// - If you new a new literal from scratch, you can use the [`FormulaFactory`]
///   function [`lit()`] to get a new instance of the explicit type, [`literal()`]
///   to get it directly as a `EncodedFormula`.
/// - If you already have a `Variable` that you want to use as a literal, you
///   can use the constructor [`new()`] of `Literal`.
/// - If you already have a literal as a `EncodedFormula`, you can use the
///   [`as_literal()`] function to convert it.
///
/// Note that, the bool `phase` describes the value of the literal. So `true`
/// will yield a positive literal, and `false` a negated literal.
///
/// `Literal` can only be used in the context of a `FormulaFactory`, since the
/// name is stored there.
///
/// [`lit()`]: FormulaFactory::lit
/// [`literal()`]: FormulaFactory::literal
/// [`new()`]: Literal::new
/// [`as_literal()`]: EncodedFormula::as_literal
/// [`FormulaFactory`]: super::FormulaFactory
#[derive(Hash, Eq, PartialEq, Copy, Clone, Debug, Ord, PartialOrd)]
pub enum Literal {
    /// Positive literal
    Pos(Variable),
    /// Negative literal
    Neg(Variable),
}

impl Literal {
    /// Creates a new `Literal` from a [`Variable`] and a `phase`. `phase`
    /// describes the value of the literal. So `true` will yield a positive
    /// literal, and `false` a negated literal.
    ///
    /// If you want to create a literal without an existing `Variable`, you can
    /// use the function [`lit()`] in [`FormulaFactory`].
    ///
    /// Note that, such a `Literal` should only be used in the context of the
    /// `FormulaFactory`, which was used to create it or the passed variable.
    ///
    /// [`lit()`]: FormulaFactory::lit
    /// [`FormulaFactory`]: super::FormulaFactory
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::formulas::FormulaFactory;
    /// # use logicng::formulas::Literal;
    /// let f = FormulaFactory::new();
    ///
    /// let var = f.var("a");
    /// let literal1 = Literal::new(var, true); // "a"
    /// let literal2 = Literal::new(var, false); // "~a"
    /// ```
    pub const fn new(variable: Variable, phase: bool) -> Self {
        if phase {
            Self::Pos(variable)
        } else {
            Self::Neg(variable)
        }
    }

    /// Returns the inherit variable of this literal.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::formulas::FormulaFactory;
    /// # use logicng::formulas::Literal;
    /// let f = FormulaFactory::new();
    ///
    /// let var = f.var("a");
    /// let literal = Literal::new(var, true);
    ///
    /// assert_eq!(literal.variable(), var);
    /// ```
    pub const fn variable(&self) -> Variable {
        match self {
            Self::Pos(v) | Self::Neg(v) => *v,
        }
    }

    /// Returns the phase of this literal.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::formulas::FormulaFactory;
    /// # use logicng::formulas::Literal;
    /// let f = FormulaFactory::new();
    ///
    /// let var = f.var("a");
    /// let literal1 = Literal::new(var, true);
    /// let literal2 = Literal::new(var, false);
    ///
    /// assert_eq!(literal1.phase(), true);
    /// assert_eq!(literal2.phase(), false);
    /// ```
    pub const fn phase(&self) -> bool {
        match self {
            Self::Pos(_) => true,
            Self::Neg(_) => false,
        }
    }

    /// Returns the name of the variable of this literal.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::formulas::FormulaFactory;
    /// # use logicng::formulas::Literal;
    /// # use std::borrow::Cow;
    /// let f = FormulaFactory::new();
    ///
    /// let var = f.var("a");
    /// let literal = Literal::new(var, true);
    ///
    /// assert_eq!(literal.name(&f), Cow::from("a"));
    /// ```
    pub fn name<'a>(&self, f: &'a FormulaFactory) -> Cow<'a, str> {
        self.variable().name(f)
    }

    /// Returns the name of the variable of this literal, if the variable is a
    /// auxiliary variable. Otherwise, it will return `None`.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::formulas::FormulaFactory;
    /// let f = FormulaFactory::new();
    ///
    /// let aux_name = format!("@RESERVED_{}_CNF_0", f.id());
    /// let aux_lit = f.parsed_variable(&aux_name).as_literal().unwrap();
    /// assert_eq!(aux_lit.aux_name(&f), Some(aux_name));
    /// ```
    pub fn aux_name(&self, f: &FormulaFactory) -> Option<String> {
        self.variable().aux_name(f)
    }

    /// Returns a new literal with the phase inverted.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::formulas::FormulaFactory;
    /// # use logicng::formulas::Literal;
    /// let f = FormulaFactory::new();
    ///
    /// let var = f.var("a");
    /// let literal1 = Literal::new(var, true);
    /// let literal2 = Literal::new(var, false);
    ///
    /// assert_eq!(literal1.negate(), literal2);
    /// assert_eq!(literal1, literal2.negate());
    /// ```
    #[must_use]
    pub const fn negate(&self) -> Self {
        Self::new(self.variable(), !self.phase())
    }

    /// Returns this literal as a `StringLiteral`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::formulas::FormulaFactory;
    /// # use logicng::formulas::Literal;
    /// # use logicng::formulas::StringLiteral;
    /// let f = FormulaFactory::new();
    ///
    /// let var = f.var("a");
    /// let literal = Literal::new(var, true);
    ///
    /// assert_eq!(literal.to_string_lit(&f), StringLiteral::new("a", true));
    /// ```
    pub fn to_string_lit<'a>(&self, f: &'a FormulaFactory) -> StringLiteral<'a> {
        StringLiteral { name: self.name(f), phase: self.phase() }
    }

    /// Converts this literal into a string representation.
    ///
    /// Strings obtained by this function, can also be parsed back again.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::formulas::FormulaFactory;
    /// # use logicng::formulas::Literal;
    /// let f = FormulaFactory::new();
    ///
    /// let var = f.var("a");
    /// let literal1 = Literal::new(var, true);
    /// let literal2 = Literal::new(var, false);
    ///
    /// assert_eq!(literal1.to_string(&f), "a");
    /// assert_eq!(literal2.to_string(&f), "~a");
    /// ```
    pub fn to_string(&self, f: &FormulaFactory) -> String {
        let sign = if self.phase() { "" } else { "~" };
        format!("{sign}{}", self.name(f))
    }
}

impl From<Literal> for EncodedFormula {
    fn from(lit: Literal) -> Self {
        let (index, ty) = match lit {
            Literal::Pos(var) => (var.index(), LitType::Pos(var.var_type())),
            Literal::Neg(var) => (var.index(), LitType::Neg(var.var_type())),
        };
        Self::from(FormulaEncoding::encode(index, FormulaType::Lit(ty), true))
    }
}

impl ToFormula for Literal {
    fn to_formula(&self, _: &FormulaFactory) -> EncodedFormula {
        (*self).into()
    }
}

/// Representation of a literals for external use.
///
/// [`Literal`] and [`Variable`] instances are bound to a [`FormulaFactory`], which
/// makes them unsuited for external use cases. `StringLiteral` allows you to
/// have literals and variables that are not bound to a `FormulaFactory`.
/// _LogicNG_ provides some functions to easily convert between those types.
#[derive(PartialOrd, PartialEq, Ord, Eq, Debug, Clone)]
pub struct StringLiteral<'a> {
    /// name of the literal
    pub name: Cow<'a, str>,
    /// phase of the literal
    pub phase: bool,
}

impl<'a> StringLiteral<'a> {
    /// Creates a new `StringLiteral` with the name passed as a `&str`.
    ///
    /// `phase` describes the value of the literal. So `true` will yield a
    /// positive literal, and `false` a negated literal.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::formulas::StringLiteral;
    ///
    /// let literal = StringLiteral::new("a", true);
    /// ```
    pub fn new(name: &'a str, phase: bool) -> Self {
        StringLiteral { name: Cow::from(name), phase }
    }

    /// Creates a new `StringLiteral` with a owned string for the name.
    ///
    /// `phase` describes the value of the literal. So `true` will yield a
    /// positive literal, and `false` a negated literal.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::formulas::StringLiteral;
    ///
    /// let name = String::from("a");
    /// let literal = StringLiteral::new_owned(name, true);
    /// ```
    pub fn new_owned(name: String, phase: bool) -> Self {
        StringLiteral { name: Cow::from(name), phase }
    }

    /// Creates a new `StringLiteral` representing a variable with the name as
    /// `&str`.
    ///
    /// This function is equivalent to `StringLiteral::new(name, true)`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::formulas::StringLiteral;
    ///
    /// let literal = StringLiteral::new_variable("a");
    /// ```
    pub fn new_variable(name: &'a str) -> Self {
        StringLiteral::new(name, true)
    }

    /// Creates a new `StringLiteral` representing a variable with a owned
    /// string for the name.
    ///
    /// This function is equivalent to `StringLiteral::new_owned(name, true)`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::formulas::StringLiteral;
    ///
    /// let name = String::from("a");
    /// let literal = StringLiteral::new_variable_owned(name);
    /// ```
    pub fn new_variable_owned(name: String) -> Self {
        StringLiteral::new_owned(name, true)
    }

    /// Converts this `StringLiteral` to a [`Literal`] in the given
    /// [`FormulaFactory`].
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::formulas::FormulaFactory;
    /// # use logicng::formulas::Literal;
    /// # use logicng::formulas::StringLiteral;
    /// let f = FormulaFactory::new();
    ///
    /// let str_lit = StringLiteral::new("a", true);
    ///
    /// assert_eq!(str_lit.to_literal(&f), f.lit("a", true));
    /// ```
    pub fn to_literal(&self, f: &FormulaFactory) -> Literal {
        f.lit(&self.name, self.phase)
    }
}

/// Converts a type into a `StringLiteral`.
pub trait ToStringLiteral {
    /// Converts `self` into a `StringLiteral`.
    fn to_string_literal(self) -> StringLiteral<'static>;
}

impl ToStringLiteral for String {
    fn to_string_literal(self) -> StringLiteral<'static> {
        let trimmed = self.trim();
        if trimmed.starts_with('~') || trimmed.starts_with('-') {
            StringLiteral::new_owned(trimmed[1..].into(), false)
        } else {
            StringLiteral::new_owned(trimmed.into(), true)
        }
    }
}

impl<'a> ToFormula for StringLiteral<'a> {
    fn to_formula(&self, f: &FormulaFactory) -> EncodedFormula {
        f.literal(&self.name, self.phase)
    }
}

impl<'a> Display for StringLiteral<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}{}", if self.phase { "" } else { "~" }, self.name)
    }
}
