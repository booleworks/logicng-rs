use std::borrow::Cow;
use std::borrow::Cow::{Borrowed, Owned};
use std::str::FromStr;

use crate::formulas::formula_cache::formula_encoding::Encoding;
use crate::formulas::formula_factory::AUX_PREFIX;
use crate::formulas::{EncodedFormula, FormulaFactory, FormulaType, LitType, Literal, StringLiteral};

use super::formula::ToFormula;
use super::formula_cache::formula_encoding::FormulaEncoding;

/// Specifies all types of literals.
#[derive(Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd, Debug)]
pub enum VarType {
    /// A normal variable created by the user.
    FF,
    /// An auxiliary variable.
    Aux(AuxVarType),
}

/// Implementation note:
/// We're not using a dedicated `AuxVarType` for CC/PBC vars created on solver, because this yields a problem:
/// We do not want such variables to occur in formulas outside of the solver (otherwise we could just use `CC`),
/// but it's hard to prevent the solver from returning them (especially in the `FormulaOnSolverFunction`).
/// We would need to transform such variables into `CC` variables then, but that could easily be forgotten
/// or we would require `MiniSat2Solver#variable_for_idx` to also take a FF which would be a pain.
#[derive(Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd, Debug)]
pub enum AuxVarType {
    /// auxiliary variable for CNFs
    CNF,
    /// auxiliary variable for cardinality constraint.
    CC,
    /// auxiliary variable for pseudo-boolean constraint.
    PB,
    /// temporary auxiliary variables for algorithms, meant to be used within algorithms, but should never be present in a final result
    TMP,
}

impl AuxVarType {
    fn prefix(self, id: &str) -> String {
        match self {
            Self::CNF => format!("{AUX_PREFIX}{id}_CNF_"),
            Self::CC => format!("{AUX_PREFIX}{id}_CC_"),
            Self::PB => format!("{AUX_PREFIX}{id}_PB_"),
            Self::TMP => format!("{AUX_PREFIX}{id}_TMP_"),
        }
    }
}

impl FromStr for AuxVarType {
    type Err = String;

    fn from_str(input: &str) -> Result<Self, Self::Err> {
        match input {
            "CNF" => Ok(Self::CNF),
            "CC" => Ok(Self::CC),
            "PB" | "TMP" => Ok(Self::PB),
            _ => Err(format!("Unknown AuxVarType: {input}")),
        }
    }
}


/// Boolean variables.
#[derive(Hash, Eq, PartialEq, Copy, Clone, Debug, Ord, PartialOrd)]
pub enum Variable {
    /// A normal variable created by the user.
    FF(FormulaEncoding),
    /// An auxiliary variable.
    Aux(AuxVarType, u64),
}

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
        let enc = FormulaEncoding::encode(index, FormulaType::Lit(LitType::Pos(VarType::FF)), true);
        Self::FF(enc)
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
    pub fn name<'a>(&self, f: &'a FormulaFactory) -> Cow<'a, str> {
        match self {
            Self::FF(i) => Borrowed(f.var_name(*i)),
            Self::Aux(t, i) => Owned(format!("{}{}", t.prefix(&f.id), *i)),
        }
    }

    /// Formats an auxiliary variable as a string.
    ///
    /// Returns `None` if the variable is not an auxiliary variable.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::formulas::FormulaFactory;
    /// let f = FormulaFactory::new();
    ///
    /// let aux_name = format!("@RESERVED_{}_CNF_0", f.id());
    /// let aux_var = f.parsed_variable(&aux_name).as_variable().unwrap();
    /// assert_eq!(aux_var.aux_name(&f), Some(aux_name));
    /// ```
    pub fn aux_name(&self, f: &FormulaFactory) -> Option<String> {
        match self {
            Self::FF(_) => None,
            Self::Aux(t, i) => Some(format!("{}{}", t.prefix(&f.id), *i)),
        }
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
        StringLiteral { name: self.name(f), phase: true }
    }

    /// Returns the type of this variable as a [`VarType`].
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::formulas::{FormulaFactory, VarType};
    /// let f = FormulaFactory::new();
    ///
    /// let var = f.var("a");
    ///
    /// match var.var_type() {
    ///     VarType::FF => {},
    ///     VarType::Aux(ty) => {},
    /// };
    /// ```
    pub const fn var_type(self) -> VarType {
        match self {
            Self::FF(_) => VarType::FF,
            Self::Aux(ty, _) => VarType::Aux(ty),
        }
    }

    pub(super) fn index(self) -> u64 {
        match self {
            Self::FF(i) => i.index(),
            Self::Aux(_, i) => i,
        }
    }
}

impl From<Variable> for EncodedFormula {
    fn from(var: Variable) -> Self {
        Self::from(Literal::new(var, true))
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
            FormulaType::Lit(LitType::Pos(VarType::Aux(aux_type)) | LitType::Neg(VarType::Aux(aux_type))) => {
                Ok(Self::Aux(aux_type, enc.index()))
            }
            FormulaType::Lit(LitType::Pos(VarType::FF) | LitType::Neg(VarType::FF)) => {
                Ok(Self::FF(FormulaEncoding::encode(enc.index(), FormulaType::Lit(LitType::Pos(VarType::FF)), true)))
            }
            _ => Err(format!("Cannot convert {:?} to an variable!", enc.formula_type())),
        }
    }
}
