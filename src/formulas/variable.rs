use crate::formulas::formula_cache::formula_encoding::Encoding;
use crate::formulas::{EncodedFormula, FormulaFactory, FormulaType, LitType, Literal, StringLiteral};

use super::formula::ToFormula;
use super::formula_cache::formula_encoding::FormulaEncoding;

pub const AUX_CNF: &str = "CNF";
pub const AUX_CC: &str = "CC";
pub const AUX_PBC: &str = "PB";

/// Boolean variables.
#[derive(Hash, Eq, PartialEq, Copy, Clone, Debug, Ord, PartialOrd)]
pub struct Variable(FormulaEncoding);

impl Variable {
    /// Constructs a variable based on a index in a [`FormulaFactory`].
    ///
    /// Note that this variable will not be registered in any `FormulaFactory`.
    /// So if you pass a invalid index and use the yield variable, it will end
    /// in undefined behavior.
    ///
    /// In any normal use case of this library, it should not be necessary to
    /// use this constructor.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::formulas::{FormulaFactory, Variable};
    /// let f = FormulaFactory::new();
    ///
    /// let var1 = f.var("A");
    /// let var2 = Variable::from_index(0);
    ///
    /// assert_eq!(var1, var2);
    /// ```
    pub fn from_index(index: u64) -> Self {
        let enc = FormulaEncoding::encode(index, FormulaType::Lit(LitType::Pos), true);
        Self(enc)
    }

    /// Returns the name of the variable. If it is a auxiliary variable, it will
    /// be formatted with its corresponding prefix.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::formulas::FormulaFactory;
    /// let f = FormulaFactory::new();
    ///
    /// let var = f.var("A");
    ///
    /// assert_eq!(var.name(&f).into_owned(), "A");
    /// ```
    pub fn name<'a>(&self, f: &'a FormulaFactory) -> &'a str {
        f.var_name(self.0)
    }

    /// Returns this variable as a negative literal.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::formulas::{FormulaFactory};
    /// let f = FormulaFactory::new();
    ///
    /// let var = f.var("A");
    /// let lit = f.lit("A", false);
    ///
    /// assert_eq!(var.negate(), lit);
    /// ```
    pub const fn negate(&self) -> Literal {
        Literal::new(*self, false)
    }

    /// Returns this variable as a positive literal.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::formulas::{FormulaFactory};
    /// let f = FormulaFactory::new();
    ///
    /// let var = f.var("A");
    /// let lit = f.lit("A", true);
    ///
    /// assert_eq!(var.pos_lit(), lit);
    /// ```
    pub const fn pos_lit(&self) -> Literal {
        Literal::Pos(*self)
    }

    /// Returns this variable as a negative literal.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::formulas::{FormulaFactory};
    /// let f = FormulaFactory::new();
    ///
    /// let var = f.var("A");
    /// let lit = f.lit("A", false);
    ///
    /// assert_eq!(var.neg_lit(), lit);
    /// ```
    pub const fn neg_lit(&self) -> Literal {
        Literal::Neg(*self)
    }

    /// Returns this variable as a `StringLiteral`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::formulas::FormulaFactory;
    /// # use logicng::formulas::StringLiteral;
    /// let f = FormulaFactory::new();
    ///
    /// let var = f.var("a");
    ///
    /// assert_eq!(var.to_string_lit(&f), StringLiteral::new("a", true));
    /// ```
    pub fn to_string_lit<'a>(&self, f: &'a FormulaFactory) -> StringLiteral<'a> {
        StringLiteral::new(self.name(f), true)
    }

    pub(super) fn index(self) -> u64 {
        self.0.index()
    }
}

impl From<Variable> for EncodedFormula {
    fn from(var: Variable) -> Self {
        Self::from(Literal::new(var, true))
    }
}

impl<'a> From<&'a Variable> for EncodedFormula {
    fn from(value: &'a Variable) -> Self {
        (*value).into()
    }
}

impl<'a> From<&'a Self> for Variable {
    fn from(value: &'a Self) -> Self {
        *value
    }
}

impl ToFormula for Variable {
    fn to_formula(&self, _: &FormulaFactory) -> EncodedFormula {
        (*self).into()
    }
}

impl TryFrom<FormulaEncoding> for Variable {
    type Error = String;

    fn try_from(enc: FormulaEncoding) -> Result<Self, Self::Error> {
        match enc.formula_type() {
            FormulaType::Lit(LitType::Pos | LitType::Neg) => {
                Ok(Self(FormulaEncoding::encode(enc.index(), FormulaType::Lit(LitType::Pos), true)))
            }
            _ => Err(format!("Cannot convert {:?} to an variable!", enc.formula_type())),
        }
    }
}
