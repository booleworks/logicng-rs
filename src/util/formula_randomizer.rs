use std::sync::Arc;
use std::usize;

use fastrand::Rng;

use crate::formulas::CType::{EQ, GE, GT, LE, LT};
use crate::formulas::{CType, EncodedFormula, FormulaFactory, Variable};

/// A configuration for randomizing formulas.
///
/// The following things can be configured:
/// - the seed -- use a value `!= 0` to get deterministic results
/// - the variables -- this list of variables will be used. The probabilities of
///   being chosen are the same for all variables.
/// - weights for different formula types, defining how often a formula type is
///   generated compared to other types.
/// - weights for comparator types in pseudo boolean constraints and cardinality
///   constraints.
/// - maximum numbers of operands for conjunctions, disjunctions, PBCs, and CCs.
///
/// Note that the weights can only be applied for inner nodes of the generated
/// formula, since the 'leaves' of a formula in LogicNG are **always** literals
/// or PBCs. So the weight of literals and PBCs will effectively be higher and
/// the weights of all other formula types (especially conjunctions and
/// disjunctions) will be lower. Similarly, the weight of constants will usually
/// be lower, because they are always reduced in LogicNG unless they are a
/// single formula.
#[derive(Clone, PartialEq, Debug)]
pub struct FormulaRandomizerConfig {
    pub(crate) seed: u64,
    pub(crate) variables: Vec<String>,
    pub(crate) weight_constant: f32,
    pub(crate) weight_variable: f32,
    pub(crate) weight_negative_literal: f32,
    pub(crate) weight_or: f32,
    pub(crate) weight_and: f32,
    pub(crate) weight_not: f32,
    pub(crate) weight_impl: f32,
    pub(crate) weight_equiv: f32,
    pub(crate) maximum_operands_and: u32,
    pub(crate) maximum_operands_or: u32,

    pub(crate) weight_pbc: f32,
    pub(crate) weight_pbc_coeff_positive: f32,
    pub(crate) weight_pbc_coeff_negative: f32,
    pub(crate) weight_pbc_type_le: f32,
    pub(crate) weight_pbc_type_lt: f32,
    pub(crate) weight_pbc_type_ge: f32,
    pub(crate) weight_pbc_type_gt: f32,
    pub(crate) weight_pbc_type_eq: f32,
    pub(crate) maximum_operands_pbc: u32,
    pub(crate) maximum_coefficient_pbc: u32,

    pub(crate) weight_cc: f32,
    pub(crate) weight_amo: f32,
    pub(crate) weight_exo: f32,
    pub(crate) maximum_operands_cc: u32,
}

impl FormulaRandomizerConfig {
    /// Builds a basic configuration with the given variables and with default
    /// settings.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::util::formula_randomizer::FormulaRandomizerConfig;
    /// let variables = vec![String::from("A"), String::from("B")];
    /// let config = FormulaRandomizerConfig::default_with_variables(variables);
    /// ```
    pub fn default_with_variables(variables: Vec<String>) -> Self {
        Self {
            seed: 42_u64,
            variables,
            weight_constant: 0.1,
            weight_variable: 1.0,
            weight_negative_literal: 1.0,
            weight_or: 30.0,
            weight_and: 30.0,
            weight_not: 1.0,
            weight_impl: 1.0,
            weight_equiv: 1.0,
            maximum_operands_and: 5,
            maximum_operands_or: 5,
            weight_pbc: 0.0,
            weight_pbc_coeff_positive: 1.0,
            weight_pbc_coeff_negative: 0.2,
            weight_pbc_type_le: 0.2,
            weight_pbc_type_lt: 0.2,
            weight_pbc_type_ge: 0.2,
            weight_pbc_type_gt: 0.2,
            weight_pbc_type_eq: 0.2,
            maximum_operands_pbc: 5,
            maximum_coefficient_pbc: 10,
            weight_cc: 0.0,
            weight_amo: 0.0,
            weight_exo: 0.0,
            maximum_operands_cc: 5,
        }
    }

    /// Builds a basic configuration with with default settings. Additionally,
    /// it generates `num_vars` variables and adds them to the configuration.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::util::formula_randomizer::FormulaRandomizerConfig;
    /// let config = FormulaRandomizerConfig::default_with_num_vars(2);
    /// ```
    pub fn default_with_num_vars(num_vars: usize) -> Self {
        match num_vars {
            0..=9 => Self::default_with_variables((0..num_vars).map(|n| format!("v{n:01}")).collect()),
            10..=99 => Self::default_with_variables((0..num_vars).map(|n| format!("v{n:02}")).collect()),
            100..=999 => Self::default_with_variables((0..num_vars).map(|n| format!("v{n:03}")).collect()),
            1000..=9999 => Self::default_with_variables((0..num_vars).map(|n| format!("v{n:04}")).collect()),
            10000..=99999 => Self::default_with_variables((0..num_vars).map(|n| format!("v{n:05}")).collect()),
            100_000..=999_999 => Self::default_with_variables((0..num_vars).map(|n| format!("v{n:06}")).collect()),
            _ => Self::default_with_variables((0..num_vars).map(|n| format!("v{n}")).collect()),
        }
    }

    /// Updates the seed, which will be used to generate pseudo-random values.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::util::formula_randomizer::FormulaRandomizerConfig;
    /// # const NUMBER_OF_VARS: usize = 0;
    /// let config = FormulaRandomizerConfig::default_with_num_vars(NUMBER_OF_VARS)
    ///         // ...
    ///         .seed(24)
    ///         // ...
    ///         ;
    /// ```
    #[must_use]
    pub const fn seed(mut self, seed: u64) -> Self {
        self.seed = seed;
        self
    }

    /// Sets the relative weight of a constant.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::util::formula_randomizer::FormulaRandomizerConfig;
    /// # const NUMBER_OF_VARS: usize = 0;
    /// let config = FormulaRandomizerConfig::default_with_num_vars(NUMBER_OF_VARS)
    ///         // ...
    ///         .weight_constant(0.2)
    ///         // ...
    ///         ;
    /// ```
    #[must_use]
    pub const fn weight_constant(mut self, weight_constant: f32) -> Self {
        self.weight_constant = weight_constant;
        self
    }

    /// Sets the relative weight of a variable/positive literal.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::util::formula_randomizer::FormulaRandomizerConfig;
    /// # const NUMBER_OF_VARS: usize = 0;
    /// let config = FormulaRandomizerConfig::default_with_num_vars(NUMBER_OF_VARS)
    ///         // ...
    ///         .weight_variable(2.0)
    ///         // ...
    ///         ;
    /// ```
    #[must_use]
    pub const fn weight_variable(mut self, weight_variable: f32) -> Self {
        self.weight_variable = weight_variable;
        self
    }

    /// Sets the relative weight of a negative literal.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::util::formula_randomizer::FormulaRandomizerConfig;
    /// # const NUMBER_OF_VARS: usize = 0;
    /// let config = FormulaRandomizerConfig::default_with_num_vars(NUMBER_OF_VARS)
    ///         // ...
    ///         .weight_negative_literal(2.0)
    ///         // ...
    ///         ;
    /// ```
    #[must_use]
    pub const fn weight_negative_literal(mut self, weight_negative_literal: f32) -> Self {
        self.weight_negative_literal = weight_negative_literal;
        self
    }

    /// Sets the relative weight of a disjunction.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::util::formula_randomizer::FormulaRandomizerConfig;
    /// # const NUMBER_OF_VARS: usize = 0;
    /// let config = FormulaRandomizerConfig::default_with_num_vars(NUMBER_OF_VARS)
    ///         // ...
    ///         .weight_or(25.0)
    ///         // ...
    ///         ;
    /// ```
    #[must_use]
    pub const fn weight_or(mut self, weight_or: f32) -> Self {
        self.weight_or = weight_or;
        self
    }

    /// Sets the relative weight of a conjunction.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::util::formula_randomizer::FormulaRandomizerConfig;
    /// # const NUMBER_OF_VARS: usize = 0;
    /// let config = FormulaRandomizerConfig::default_with_num_vars(NUMBER_OF_VARS)
    ///         // ...
    ///         .weight_and(25.0)
    ///         // ...
    ///         ;
    /// ```
    #[must_use]
    pub const fn weight_and(mut self, weight_and: f32) -> Self {
        self.weight_and = weight_and;
        self
    }

    /// Sets the relative weight of a negation.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::util::formula_randomizer::FormulaRandomizerConfig;
    /// # const NUMBER_OF_VARS: usize = 0;
    /// let config = FormulaRandomizerConfig::default_with_num_vars(NUMBER_OF_VARS)
    ///         // ...
    ///         .weight_not(2.0)
    ///         // ...
    ///         ;
    /// ```
    #[must_use]
    pub const fn weight_not(mut self, weight_not: f32) -> Self {
        self.weight_not = weight_not;
        self
    }

    /// Sets the relative weight of an implication.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::util::formula_randomizer::FormulaRandomizerConfig;
    /// # const NUMBER_OF_VARS: usize = 0;
    /// let config = FormulaRandomizerConfig::default_with_num_vars(NUMBER_OF_VARS)
    ///         // ...
    ///         .weight_impl(2.0)
    ///         // ...
    ///         ;
    /// ```
    #[must_use]
    pub const fn weight_impl(mut self, weight_impl: f32) -> Self {
        self.weight_impl = weight_impl;
        self
    }

    /// Sets the relative weight of an equivalence.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::util::formula_randomizer::FormulaRandomizerConfig;
    /// # const NUMBER_OF_VARS: usize = 0;
    /// let config = FormulaRandomizerConfig::default_with_num_vars(NUMBER_OF_VARS)
    ///         // ...
    ///         .weight_equiv(2.0)
    ///         // ...
    ///         ;
    /// ```
    #[must_use]
    pub const fn weight_equiv(mut self, weight_equiv: f32) -> Self {
        self.weight_equiv = weight_equiv;
        self
    }

    /// Sets the maximum number of operands in a conjunction.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::util::formula_randomizer::FormulaRandomizerConfig;
    /// # const NUMBER_OF_VARS: usize = 0;
    /// let config = FormulaRandomizerConfig::default_with_num_vars(NUMBER_OF_VARS)
    ///         // ...
    ///         .maximum_operands_and(7)
    ///         // ...
    ///         ;
    /// ```
    #[must_use]
    pub const fn maximum_operands_and(mut self, maximum_operands_and: u32) -> Self {
        self.maximum_operands_and = maximum_operands_and;
        self
    }

    /// Sets the maximum number of operands in a disjunction.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::util::formula_randomizer::FormulaRandomizerConfig;
    /// # const NUMBER_OF_VARS: usize = 0;
    /// let config = FormulaRandomizerConfig::default_with_num_vars(NUMBER_OF_VARS)
    ///         // ...
    ///         .maximum_operands_or(7)
    ///         // ...
    ///         ;
    /// ```
    #[must_use]
    pub const fn maximum_operands_or(mut self, maximum_operands_or: u32) -> Self {
        self.maximum_operands_or = maximum_operands_or;
        self
    }

    /// Sets the relative weight of a pseudo boolean constraint.
    ///
    /// Note that the constraint may by chance also be a cardinality constraint,
    /// or even a literal or a constant.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::util::formula_randomizer::FormulaRandomizerConfig;
    /// # const NUMBER_OF_VARS: usize = 0;
    /// let config = FormulaRandomizerConfig::default_with_num_vars(NUMBER_OF_VARS)
    ///         // ...
    ///         .weight_pbc(1.0)
    ///         // ...
    ///         ;
    /// ```
    #[must_use]
    pub const fn weight_pbc(mut self, weight_pbc: f32) -> Self {
        self.weight_pbc = weight_pbc;
        self
    }

    /// Sets the relative weight of a positive coefficient.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::util::formula_randomizer::FormulaRandomizerConfig;
    /// # const NUMBER_OF_VARS: usize = 0;
    /// let config = FormulaRandomizerConfig::default_with_num_vars(NUMBER_OF_VARS)
    ///         // ...
    ///         .weight_pbc_coeff_positive(2.0)
    ///         // ...
    ///         ;
    /// ```
    #[must_use]
    pub const fn weight_pbc_coeff_positive(mut self, weight_pbc_coeff_positive: f32) -> Self {
        self.weight_pbc_coeff_positive = weight_pbc_coeff_positive;
        self
    }

    /// Sets the relative weight of a negative coefficient.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::util::formula_randomizer::FormulaRandomizerConfig;
    /// # const NUMBER_OF_VARS: usize = 0;
    /// let config = FormulaRandomizerConfig::default_with_num_vars(NUMBER_OF_VARS)
    ///         // ...
    ///         .weight_pbc_coeff_negative(2.0)
    ///         // ...
    ///         ;
    /// ```
    #[must_use]
    pub const fn weight_pbc_coeff_negative(mut self, weight_pbc_coeff_negative: f32) -> Self {
        self.weight_pbc_coeff_negative = weight_pbc_coeff_negative;
        self
    }

    /// Sets the relative weight of a [`CType::LE`](`crate::formulas::CType`) constraint.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::util::formula_randomizer::FormulaRandomizerConfig;
    /// # const NUMBER_OF_VARS: usize = 0;
    /// let config = FormulaRandomizerConfig::default_with_num_vars(NUMBER_OF_VARS)
    ///         // ...
    ///         .weight_pbc_type_le(0.5)
    ///         // ...
    ///         ;
    /// ```
    #[must_use]
    pub const fn weight_pbc_type_le(mut self, weight_pbc_type_le: f32) -> Self {
        self.weight_pbc_type_le = weight_pbc_type_le;
        self
    }

    /// Sets the relative weight of a [`CType::LT`](`crate::formulas::CType`) constraint.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::util::formula_randomizer::FormulaRandomizerConfig;
    /// # const NUMBER_OF_VARS: usize = 0;
    /// let config = FormulaRandomizerConfig::default_with_num_vars(NUMBER_OF_VARS)
    ///         // ...
    ///         .weight_pbc_type_lt(0.5)
    ///         // ...
    ///         ;
    /// ```
    #[must_use]
    pub const fn weight_pbc_type_lt(mut self, weight_pbc_type_lt: f32) -> Self {
        self.weight_pbc_type_lt = weight_pbc_type_lt;
        self
    }

    /// Sets the relative weight of a [`CType::GE`](`crate::formulas::CType`) constraint.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::util::formula_randomizer::FormulaRandomizerConfig;
    /// # const NUMBER_OF_VARS: usize = 0;
    /// let config = FormulaRandomizerConfig::default_with_num_vars(NUMBER_OF_VARS)
    ///         // ...
    ///         .weight_pbc_type_ge(0.5)
    ///         // ...
    ///         ;
    /// ```
    #[must_use]
    pub const fn weight_pbc_type_ge(mut self, weight_pbc_type_ge: f32) -> Self {
        self.weight_pbc_type_ge = weight_pbc_type_ge;
        self
    }

    /// Sets the relative weight of a [`CType::GT`](`crate::formulas::CType`) constraint.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::util::formula_randomizer::FormulaRandomizerConfig;
    /// # const NUMBER_OF_VARS: usize = 0;
    /// let config = FormulaRandomizerConfig::default_with_num_vars(NUMBER_OF_VARS)
    ///         // ...
    ///         .weight_pbc_type_gt(0.5)
    ///         // ...
    ///         ;
    /// ```
    #[must_use]
    pub const fn weight_pbc_type_gt(mut self, weight_pbc_type_gt: f32) -> Self {
        self.weight_pbc_type_gt = weight_pbc_type_gt;
        self
    }

    /// Sets the relative weight of a [`CType::EQ`](`crate::formulas::CType`) constraint.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::util::formula_randomizer::FormulaRandomizerConfig;
    /// # const NUMBER_OF_VARS: usize = 0;
    /// let config = FormulaRandomizerConfig::default_with_num_vars(NUMBER_OF_VARS)
    ///         // ...
    ///         .weight_pbc_type_eq(0.5)
    ///         // ...
    ///         ;
    /// ```
    #[must_use]
    pub const fn weight_pbc_type_eq(mut self, weight_pbc_type_eq: f32) -> Self {
        self.weight_pbc_type_eq = weight_pbc_type_eq;
        self
    }

    /// Sets the maximum number of operands in a pseudo boolean constraint.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::util::formula_randomizer::FormulaRandomizerConfig;
    /// # const NUMBER_OF_VARS: usize = 0;
    /// let config = FormulaRandomizerConfig::default_with_num_vars(NUMBER_OF_VARS)
    ///         // ...
    ///         .maximum_operands_pbc(7)
    ///         // ...
    ///         ;
    /// ```
    #[must_use]
    pub const fn maximum_operands_pbc(mut self, maximum_operands_pbc: u32) -> Self {
        self.maximum_operands_pbc = maximum_operands_pbc;
        self
    }

    /// Sets the maximum absolute value of a coefficient in a pseudo boolean
    /// constraint.
    ///
    /// Whether the coefficient is positive or negative is depends on
    /// `self.weight_pbc_coeff_positive` and `weight_pbc_coeff_negative`.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::util::formula_randomizer::FormulaRandomizerConfig;
    /// # const NUMBER_OF_VARS: usize = 0;
    /// let config = FormulaRandomizerConfig::default_with_num_vars(NUMBER_OF_VARS)
    ///         // ...
    ///         .maximum_coefficient_pbc(15)
    ///         // ...
    ///         ;
    /// ```
    #[must_use]
    pub const fn maximum_coefficient_pbc(mut self, maximum_coefficient_pbc: u32) -> Self {
        self.maximum_coefficient_pbc = maximum_coefficient_pbc;
        self
    }

    /// Sets the relative weight of a cardinality constraint.
    ///
    /// Note that the cardinality constraint may by chance also be an AMO or EXO
    /// constraint, or even a literal or a constant.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::util::formula_randomizer::FormulaRandomizerConfig;
    /// # const NUMBER_OF_VARS: usize = 0;
    /// let config = FormulaRandomizerConfig::default_with_num_vars(NUMBER_OF_VARS)
    ///         // ...
    ///         .weight_cc(0.1)
    ///         // ...
    ///         ;
    /// ```
    #[must_use]
    pub const fn weight_cc(mut self, weight_cc: f32) -> Self {
        self.weight_cc = weight_cc;
        self
    }

    /// Sets the relative weight of an at-most-one constraint.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::util::formula_randomizer::FormulaRandomizerConfig;
    /// # const NUMBER_OF_VARS: usize = 0;
    /// let config = FormulaRandomizerConfig::default_with_num_vars(NUMBER_OF_VARS)
    ///         // ...
    ///         .weight_amo(0.1)
    ///         // ...
    ///         ;
    /// ```
    #[must_use]
    pub const fn weight_amo(mut self, weight_amo: f32) -> Self {
        self.weight_amo = weight_amo;
        self
    }

    /// Sets the relative weight of an exactly-one constraint.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::util::formula_randomizer::FormulaRandomizerConfig;
    /// # const NUMBER_OF_VARS: usize = 0;
    /// let config = FormulaRandomizerConfig::default_with_num_vars(NUMBER_OF_VARS)
    ///         // ...
    ///         .weight_exo(0.1)
    ///         // ...
    ///         ;
    /// ```
    #[must_use]
    pub const fn weight_exo(mut self, weight_exo: f32) -> Self {
        self.weight_exo = weight_exo;
        self
    }

    /// Sets the maximum number of operands in a cardinality, AMO, or EXO
    /// constraint.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::util::formula_randomizer::FormulaRandomizerConfig;
    /// # const NUMBER_OF_VARS: usize = 0;
    /// let config = FormulaRandomizerConfig::default_with_num_vars(NUMBER_OF_VARS)
    ///         // ...
    ///         .maximum_operands_cc(7)
    ///         // ...
    ///         ;
    /// ```
    #[must_use]
    pub const fn maximum_operands_cc(mut self, maximum_operands_cc: u32) -> Self {
        self.maximum_operands_cc = maximum_operands_cc;
        self
    }

    fn compute_formula_type_probabilities(&self) -> FormulaTypeProbabilities {
        let total = self.weight_constant
            + self.weight_variable
            + self.weight_negative_literal
            + self.weight_or
            + self.weight_and
            + self.weight_not
            + self.weight_impl
            + self.weight_equiv
            + self.weight_pbc
            + self.weight_cc
            + self.weight_amo
            + self.weight_exo;
        let constant = self.weight_constant / total;
        let literal = constant + (self.weight_variable + self.weight_negative_literal) / total;
        let pbc = literal + self.weight_pbc / total;
        let cc = pbc + self.weight_cc / total;
        let amo = cc + self.weight_amo / total;
        let exo = amo + self.weight_exo / total;
        let or = exo + self.weight_or / total;
        let and = or + self.weight_and / total;
        let not = and + self.weight_not / total;
        let implication = not + self.weight_impl / total;
        let equivalence = implication + self.weight_equiv / total;
        let phase = self.weight_variable / (self.weight_variable + self.weight_negative_literal);
        FormulaTypeProbabilities { constant, literal, pbc, cc, amo, exo, or, and, not, implication, _equivalence: equivalence, phase }
    }

    fn compute_c_type_probabilities(&self) -> CTypeProbabilities {
        let total =
            self.weight_pbc_type_le + self.weight_pbc_type_lt + self.weight_pbc_type_ge + self.weight_pbc_type_gt + self.weight_pbc_type_eq;
        let le = self.weight_pbc_type_le / total;
        let lt = le + self.weight_pbc_type_lt / total;
        let ge = lt + self.weight_pbc_type_ge / total;
        let gt = ge + self.weight_pbc_type_gt / total;
        let eq = gt + self.weight_pbc_type_eq / total;
        CTypeProbabilities { le, lt, ge, gt, _eq: eq }
    }
}

struct FormulaTypeProbabilities {
    constant: f32,
    literal: f32,
    pbc: f32,
    cc: f32,
    amo: f32,
    exo: f32,
    or: f32,
    and: f32,
    not: f32,
    implication: f32,
    _equivalence: f32,
    phase: f32,
}

struct CTypeProbabilities {
    le: f32,
    lt: f32,
    ge: f32,
    gt: f32,
    _eq: f32,
}

/// A generator for random formulas.
///
/// The formula types included in the generated formulas can be configured with
/// a [`FormulaRandomizerConfig`].
pub struct FormulaRandomizer {
    config: FormulaRandomizerConfig,
    random: Rng,
    formula_probs: FormulaTypeProbabilities,
    c_type_probs: CTypeProbabilities,
    coefficient_negative_probability: f32,
}

impl FormulaRandomizer {
    /// Builds a new `FormulaRandomizer` from a [`FormulaRandomizerConfig`].
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::util::formula_randomizer::{FormulaRandomizerConfig, FormulaRandomizer};
    /// let config = FormulaRandomizerConfig::default_with_num_vars(5);
    /// let mut randomizer = FormulaRandomizer::new(config);
    /// ```
    pub fn new(config: FormulaRandomizerConfig) -> Self {
        let seed = config.seed;
        let formula_probs = config.compute_formula_type_probabilities();
        let c_type_probs = config.compute_c_type_probabilities();
        let coefficient_negative_probability =
            config.weight_pbc_coeff_negative / (config.weight_pbc_coeff_positive + config.weight_pbc_coeff_negative);
        Self { config, random: Rng::with_seed(seed), formula_probs, c_type_probs, coefficient_negative_probability }
    }

    /// Returns a random constant.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::util::formula_randomizer::{FormulaRandomizerConfig, FormulaRandomizer};
    /// # use logicng::formulas::FormulaFactory;
    /// # let f = FormulaFactory::new();
    /// # let config = FormulaRandomizerConfig::default_with_num_vars(0);
    /// # let mut randomizer = FormulaRandomizer::new(config);
    /// let constant = randomizer.constant(&f);
    /// ```
    pub fn constant(&mut self, f: &FormulaFactory) -> EncodedFormula {
        f.constant(self.random.bool())
    }

    /// Returns a random name of a variable as a string.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::util::formula_randomizer::{FormulaRandomizerConfig, FormulaRandomizer};
    /// let config = FormulaRandomizerConfig::default_with_variables(vec![String::from("A"), String::from("B")]);
    /// let mut randomizer = FormulaRandomizer::new(config);
    ///
    /// let variable = randomizer.var_string(); // "A" or "B"
    /// ```
    pub fn var_string(&mut self) -> &str {
        &self.config.variables[self.random.usize(0..self.config.variables.len())]
    }

    /// Returns a random variable.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::util::formula_randomizer::{FormulaRandomizerConfig, FormulaRandomizer};
    /// # use logicng::formulas::FormulaFactory;
    /// let f = FormulaFactory::new();
    /// let config = FormulaRandomizerConfig::default_with_variables(vec![String::from("A"), String::from("B")]);
    /// let mut randomizer = FormulaRandomizer::new(config);
    ///
    /// let variable = randomizer.variable(&f); // A or B
    /// ```
    pub fn variable(&mut self, f: &FormulaFactory) -> EncodedFormula {
        f.variable(self.var_string())
    }

    /// Returns a random literal.
    ///
    /// The probability of whether it is positive or negative depends on the
    /// configuration.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::util::formula_randomizer::{FormulaRandomizerConfig, FormulaRandomizer};
    /// # use logicng::formulas::FormulaFactory;
    /// let f = FormulaFactory::new();
    /// let config = FormulaRandomizerConfig::default_with_variables(vec![String::from("A"), String::from("B")]);
    /// let mut randomizer = FormulaRandomizer::new(config);
    ///
    /// let variable = randomizer.literal(&f); // "A", "B", "~A", or "~B"
    /// ```
    pub fn literal(&mut self, f: &FormulaFactory) -> EncodedFormula {
        let phase = self.random.f32() < self.formula_probs.phase;
        let variable = self.var_string();
        f.literal(variable, phase)
    }

    /// Returns a random atom.
    ///
    /// This includes constants, literals, pseudo boolean constraints, and
    /// cardinality constraints (including amo and exo).
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::util::formula_randomizer::{FormulaRandomizerConfig, FormulaRandomizer};
    /// # use logicng::formulas::FormulaFactory;
    /// # let f = FormulaFactory::new();
    /// # let config = FormulaRandomizerConfig::default_with_num_vars(1);
    /// # let mut randomizer = FormulaRandomizer::new(config);
    /// let atom = randomizer.atom(&f);
    /// ```
    pub fn atom(&mut self, f: &FormulaFactory) -> EncodedFormula {
        let n = self.random.f32() * self.formula_probs.exo;
        if n < self.formula_probs.constant {
            self.constant(f)
        } else if n < self.formula_probs.literal {
            self.literal(f)
        } else if n < self.formula_probs.pbc {
            self.pbc(f)
        } else if n < self.formula_probs.cc {
            self.cc(f)
        } else if n < self.formula_probs.amo {
            self.amo(f)
        } else {
            self.exo(f)
        }
    }

    /// Returns a random negation with a given maximal depth.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::util::formula_randomizer::{FormulaRandomizerConfig, FormulaRandomizer};
    /// # use logicng::formulas::FormulaFactory;
    /// # let f = FormulaFactory::new();
    /// # let config = FormulaRandomizerConfig::default_with_num_vars(10);
    /// # let mut randomizer = FormulaRandomizer::new(config);
    /// let negation = randomizer.not(&f, 2);
    /// ```
    pub fn not(&mut self, f: &FormulaFactory, max_depth: u32) -> EncodedFormula {
        if max_depth == 0 {
            self.atom(f)
        } else {
            let inner = self.formula(f, max_depth - 1);
            let result = f.not(inner);
            if max_depth >= 2 && !result.is_not() {
                self.not(f, max_depth)
            } else {
                result
            }
        }
    }

    /// Returns a random implication with a given maximal depth.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::util::formula_randomizer::{FormulaRandomizerConfig, FormulaRandomizer};
    /// # use logicng::formulas::FormulaFactory;
    /// # let f = FormulaFactory::new();
    /// # let config = FormulaRandomizerConfig::default_with_num_vars(10);
    /// # let mut randomizer = FormulaRandomizer::new(config);
    /// let implication = randomizer.implication(&f, 2);
    /// ```
    pub fn implication(&mut self, f: &FormulaFactory, max_depth: u32) -> EncodedFormula {
        if max_depth == 0 {
            self.atom(f)
        } else {
            let left = self.formula(f, max_depth - 1);
            let right = self.formula(f, max_depth - 1);
            let result = f.implication(left, right);
            if result.is_impl() {
                result
            } else {
                self.implication(f, max_depth)
            }
        }
    }

    /// Returns a random equivalence with a given maximal depth.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::util::formula_randomizer::{FormulaRandomizerConfig, FormulaRandomizer};
    /// # use logicng::formulas::FormulaFactory;
    /// # let f = FormulaFactory::new();
    /// # let config = FormulaRandomizerConfig::default_with_num_vars(10);
    /// # let mut randomizer = FormulaRandomizer::new(config);
    /// let equivalence = randomizer.equivalence(&f, 2);
    /// ```
    pub fn equivalence(&mut self, f: &FormulaFactory, max_depth: u32) -> EncodedFormula {
        if max_depth == 0 {
            self.atom(f)
        } else {
            let left = self.formula(f, max_depth - 1);
            let right = self.formula(f, max_depth - 1);
            let result = f.equivalence(left, right);
            if result.is_equiv() {
                result
            } else {
                self.equivalence(f, max_depth)
            }
        }
    }

    /// Returns a random conjunction with a given maximal depth.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::util::formula_randomizer::{FormulaRandomizerConfig, FormulaRandomizer};
    /// # use logicng::formulas::FormulaFactory;
    /// # let f = FormulaFactory::new();
    /// # let config = FormulaRandomizerConfig::default_with_num_vars(10);
    /// # let mut randomizer = FormulaRandomizer::new(config);
    /// let conjunction = randomizer.and(&f, 2);
    /// ```
    pub fn and(&mut self, f: &FormulaFactory, max_depth: u32) -> EncodedFormula {
        if max_depth == 0 {
            self.atom(f)
        } else {
            let num_operands = self.random.u32(2..self.config.maximum_operands_and);
            let operands = (0..num_operands).map(|_| self.formula(f, max_depth - 1));
            let result = f.and(operands);
            if result.is_and() {
                result
            } else {
                self.and(f, max_depth)
            }
        }
    }

    /// Returns a random disjunction with a given maximal depth.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::util::formula_randomizer::{FormulaRandomizerConfig, FormulaRandomizer};
    /// # use logicng::formulas::FormulaFactory;
    /// # let f = FormulaFactory::new();
    /// # let config = FormulaRandomizerConfig::default_with_num_vars(10);
    /// # let mut randomizer = FormulaRandomizer::new(config);
    /// let disjunction = randomizer.or(&f, 2);
    /// ```
    pub fn or(&mut self, f: &FormulaFactory, max_depth: u32) -> EncodedFormula {
        if max_depth == 0 {
            self.atom(f)
        } else {
            let num_operands = self.random.u32(2..self.config.maximum_operands_or);
            let operands = (0..num_operands).map(|_| self.formula(f, max_depth - 1));
            let result = f.or(operands);
            if result.is_or() {
                result
            } else {
                self.or(f, max_depth)
            }
        }
    }

    /// Returns a random cardinality constraint.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::util::formula_randomizer::{FormulaRandomizerConfig, FormulaRandomizer};
    /// # use logicng::formulas::FormulaFactory;
    /// # let f = FormulaFactory::new();
    /// # let config = FormulaRandomizerConfig::default_with_num_vars(1);
    /// # let mut randomizer = FormulaRandomizer::new(config);
    /// let cc = randomizer.cc(&f);
    /// ```
    pub fn cc(&mut self, f: &FormulaFactory) -> EncodedFormula {
        let variables = self.cc_variables(f);
        let c_type = self.c_type();
        let rhs_bound = if c_type == GT || c_type == LT { variables.len() + 1 } else { variables.len() }
            .try_into()
            .expect("too many variables for a cardinality constraint");
        let rhs_offset = u32::from(c_type == LT);
        let rhs = rhs_offset + self.random.u32(0..rhs_bound);
        let cc = f.cc(c_type, rhs, variables);
        if cc.is_constant() {
            self.cc(f)
        } else {
            cc
        }
    }

    /// Returns a random at-most-one constraint.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::util::formula_randomizer::{FormulaRandomizerConfig, FormulaRandomizer};
    /// # use logicng::formulas::FormulaFactory;
    /// # let f = FormulaFactory::new();
    /// # let config = FormulaRandomizerConfig::default_with_num_vars(1);
    /// # let mut randomizer = FormulaRandomizer::new(config);
    /// let amo = randomizer.amo(&f);
    /// ```
    pub fn amo(&mut self, f: &FormulaFactory) -> EncodedFormula {
        let vars = self.cc_variables(f);
        f.amo(vars)
    }

    /// Returns a random exactly-one constraint.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::util::formula_randomizer::{FormulaRandomizerConfig, FormulaRandomizer};
    /// # use logicng::formulas::FormulaFactory;
    /// # let f = FormulaFactory::new();
    /// # let config = FormulaRandomizerConfig::default_with_num_vars(1);
    /// # let mut randomizer = FormulaRandomizer::new(config);
    /// let exo = randomizer.exo(&f);
    /// ```
    pub fn exo(&mut self, f: &FormulaFactory) -> EncodedFormula {
        let vars = self.cc_variables(f);
        f.exo(vars)
    }

    /// Returns a random pseudo boolean constraint.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::util::formula_randomizer::{FormulaRandomizerConfig, FormulaRandomizer};
    /// # use logicng::formulas::FormulaFactory;
    /// # let f = FormulaFactory::new();
    /// # let config = FormulaRandomizerConfig::default_with_num_vars(1);
    /// # let mut randomizer = FormulaRandomizer::new(config);
    /// let pbc = randomizer.pbc(&f);
    /// ```
    pub fn pbc(&mut self, f: &FormulaFactory) -> EncodedFormula {
        let num_ops = self.random.u32(0..self.config.maximum_operands_pbc) as usize;
        let mut literals = Vec::with_capacity(num_ops);
        let mut coefficients = Vec::with_capacity(num_ops);
        let mut min_sum = 0;
        let mut max_sum = 0;
        for i in 0..num_ops {
            literals.push(self.literal(f).as_literal().unwrap());
            #[allow(clippy::cast_possible_wrap)]
            coefficients.push((self.random.u64(0..u64::from(self.config.maximum_coefficient_pbc)) + 1) as i64);
            if self.random.f32() < self.coefficient_negative_probability {
                min_sum += coefficients[i];
                coefficients[i] = -coefficients[i];
            } else {
                max_sum += coefficients[i];
            }
        }
        let c_type = self.c_type();
        let rhs = self.random.i64(0..=(max_sum + min_sum)) - min_sum;
        let pbc = f.pbc(c_type, rhs, literals, coefficients);
        if pbc.is_constant() {
            self.pbc(f)
        } else {
            pbc
        }
    }

    /// Returns a random formula with a given maximal depth.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::util::formula_randomizer::{FormulaRandomizerConfig, FormulaRandomizer};
    /// # use logicng::formulas::FormulaFactory;
    /// # let f = FormulaFactory::new();
    /// # let config = FormulaRandomizerConfig::default_with_num_vars(10);
    /// # let mut randomizer = FormulaRandomizer::new(config);
    /// let formula = randomizer.formula(&f, 2);
    /// ```
    pub fn formula(&mut self, f: &FormulaFactory, max_depth: u32) -> EncodedFormula {
        if max_depth == 0 {
            self.atom(f)
        } else {
            let n = self.random.f32();
            if n < self.formula_probs.constant {
                self.constant(f)
            } else if n < self.formula_probs.literal {
                self.literal(f)
            } else if n < self.formula_probs.pbc {
                self.pbc(f)
            } else if n < self.formula_probs.cc {
                self.cc(f)
            } else if n < self.formula_probs.amo {
                self.amo(f)
            } else if n < self.formula_probs.exo {
                self.exo(f)
            } else if n < self.formula_probs.or {
                self.or(f, max_depth)
            } else if n < self.formula_probs.and {
                self.and(f, max_depth)
            } else if n < self.formula_probs.not {
                self.not(f, max_depth)
            } else if n < self.formula_probs.implication {
                self.implication(f, max_depth)
            } else {
                self.equivalence(f, max_depth)
            }
        }
    }

    /// Returns a list of `num_constraints` random formula with a given
    /// maximal depth.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::util::formula_randomizer::{FormulaRandomizerConfig, FormulaRandomizer};
    /// # use logicng::formulas::FormulaFactory;
    /// # let f = FormulaFactory::new();
    /// # let config = FormulaRandomizerConfig::default_with_num_vars(10);
    /// # let mut randomizer = FormulaRandomizer::new(config);
    /// let formulas = randomizer.constraint_set(&f, 5, 2);
    /// ```
    pub fn constraint_set(&mut self, f: &FormulaFactory, num_constraints: u32, max_depth: u32) -> Arc<[EncodedFormula]> {
        (0..num_constraints).map(|_| self.formula(f, max_depth)).collect()
    }

    fn cc_variables(&mut self, f: &FormulaFactory) -> Box<[Variable]> {
        (0..self.random.u32(1..self.config.maximum_operands_cc)).map(|_| self.variable(f).as_variable().unwrap()).collect()
    }

    fn c_type(&mut self) -> CType {
        let n = self.random.f32();
        if n < self.c_type_probs.le {
            LE
        } else if n < self.c_type_probs.lt {
            LT
        } else if n < self.c_type_probs.ge {
            GE
        } else if n < self.c_type_probs.gt {
            GT
        } else {
            EQ
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeSet, HashMap};

    use CType::{GE, GT, LT};

    use crate::formulas::CType::{EQ, LE};
    use crate::formulas::{CType, EncodedFormula, FormulaFactory, FormulaType, LitType, Literal, Variable};
    use crate::operations::functions::formula_depth;
    use crate::util::formula_randomizer::{FormulaRandomizer, FormulaRandomizerConfig};

    fn config() -> FormulaRandomizerConfig {
        FormulaRandomizerConfig::default_with_num_vars(25).seed(2812)
    }

    #[test]
    fn test_determinism() {
        let f = &FormulaFactory::new();
        let expected = FormulaRandomizer::new(config()).formula(f, 3);
        assert_eq!(expected, FormulaRandomizer::new(config()).formula(f, 3));
        assert_ne!(expected, FormulaRandomizer::new(config().seed(43)).formula(f, 3));
        assert_ne!(expected, FormulaRandomizer::new(FormulaRandomizerConfig::default_with_num_vars(25)).formula(f, 3));
        let expected = random_formulas(f);
        for _ in 0..10 {
            assert_eq!(expected, random_formulas(f));
        }
    }

    #[test]
    fn test_constant() {
        let f = &FormulaFactory::new();
        let mut random = FormulaRandomizer::new(config());
        let mut num_true = 0;
        for _ in 0..100 {
            let constant = random.constant(f);
            assert!(constant.is_constant());
            if constant.is_verum() {
                num_true += 1;
            }
        }
        assert!(40 < num_true && num_true < 60);
    }

    #[test]
    fn test_variable() {
        let f = &FormulaFactory::new();
        let vars: Vec<String> = ["A", "B", "C"].iter().map(|&s| s.into()).collect();
        let mut random = FormulaRandomizer::new(FormulaRandomizerConfig::default_with_variables(vars.clone()));
        let (mut num_a, mut num_b, mut num_c) = (0, 0, 0);
        for _ in 0..100 {
            let var = random.variable(f).as_variable().unwrap().name(f).to_string();
            assert!(vars.contains(&var.to_string()));
            match var.as_str() {
                "A" => num_a += 1,
                "B" => num_b += 1,
                "C" => num_c += 1,
                _ => panic!("Unexpected variable: {var}"),
            }
        }
        assert!(20 < num_a && num_a < 40);
        assert!(20 < num_b && num_b < 40);
        assert!(20 < num_c && num_c < 40);
        let vars2: Vec<String> = (0..20).map(|i| format!("TEST_VAR_{i}")).collect();
        let mut random = FormulaRandomizer::new(
            FormulaRandomizerConfig::default_with_variables(vars2.clone()).weight_pbc(1.0).weight_cc(1.0).weight_amo(1.0).weight_exo(1.0),
        );
        let vars2set: BTreeSet<Variable> = vars2.iter().map(|v| f.var(v)).collect();
        for _ in 0..100 {
            assert!(random.formula(f, 4).variables(f).is_subset(&vars2set));
        }
    }

    #[test]
    fn test_literal() {
        let f = &FormulaFactory::new();
        let mut random =
            FormulaRandomizer::new(FormulaRandomizerConfig::default_with_num_vars(25).weight_variable(40.0).weight_negative_literal(60.0));
        let num_pos = (0..100).map(|_| random.literal(f).as_literal().unwrap()).filter(Literal::phase).count();
        assert!(30 < num_pos && num_pos < 50);
    }

    #[test]
    fn test_atom() {
        let f = &FormulaFactory::new();
        let mut random = FormulaRandomizer::new(
            FormulaRandomizerConfig::default_with_num_vars(25)
                .weight_constant(1.0)
                .weight_variable(2.0)
                .weight_negative_literal(3.0)
                .weight_pbc(4.0)
                .weight_cc(5.0)
                .weight_amo(6.0)
                .weight_exo(7.0),
        );
        let (mut num_const, mut num_pos, mut num_neg, mut num_pbc, mut num_cc, mut num_amo, mut num_exo) =
            (0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0);
        for _ in 0..10000 {
            let formula = random.atom(f);
            assert!(formula.is_atomic());
            if formula.is_constant() {
                num_const += 1.0;
            } else if formula.is_variable() {
                num_pos += 1.0;
            } else if formula.is_negative_literal() {
                num_neg += 1.0;
            } else if !formula.is_cc() {
                num_pbc += 1.0;
            } else {
                let cc = formula.as_cc(f).unwrap();
                if cc.rhs == 1 && cc.comparator == LE {
                    num_amo += 1.0;
                } else if cc.rhs == 1 && cc.comparator == EQ {
                    num_exo += 1.0;
                } else {
                    num_cc += 1.0;
                }
            }
        }

        assert!(0.8 * 7.0 / 6.0 * num_amo < num_exo && num_exo < 1.2 * 7.0 / 6.0 * num_amo);
        assert!(0.8 * 6.0 / 5.0 * num_cc < num_amo && num_amo < 1.2 * 6.0 / 5.0 * num_cc);
        assert!(0.8 * 5.0 / 4.0 * num_pbc < num_cc && num_cc < 1.2 * 5.0 / 4.0 * num_pbc);
        assert!(0.8 * 4.0 / 3.0 * num_neg < num_pbc && num_pbc < 1.2 * 4.0 / 3.0 * num_neg);
        assert!(0.8 * 3.0 / 2.0 * num_pos < num_neg && num_neg < 1.2 * 3.0 / 2.0 * num_pos);
        assert!(0.8 * 2.0 / 1.0 * num_const < num_pos && num_pos < 1.2 * 2.0 / 1.0 * num_const);

        let mut random_only_literals = FormulaRandomizer::new(
            FormulaRandomizerConfig::default_with_num_vars(25).weight_constant(0.0).weight_variable(3.0).weight_negative_literal(6.0),
        );
        (0..100).for_each(|_| assert!(random_only_literals.atom(f).is_literal()));
    }

    #[test]
    fn test_and() {
        let f = &FormulaFactory::new();
        let mut random = FormulaRandomizer::new(config());
        (0..100).for_each(|_| assert!(random.and(f, 0).is_atomic()));
        for depth in 1..7 {
            for _ in 0..10 {
                let formula = random.and(f, depth);
                assert!(formula.is_and());
                assert!(formula_depth(formula, f) <= u64::from(depth));
            }
        }
    }

    #[test]
    fn test_or() {
        let f = &FormulaFactory::new();
        let mut random = FormulaRandomizer::new(config());
        (0..100).for_each(|_| assert!(random.or(f, 0).is_atomic()));
        for depth in 1..7 {
            for _ in 0..10 {
                let formula = random.or(f, depth);
                assert!(formula.is_or());
                assert!(formula_depth(formula, f) <= u64::from(depth));
            }
        }
    }

    #[test]
    fn test_not() {
        let f = &FormulaFactory::new();
        let mut random = FormulaRandomizer::new(config());
        (0..100).for_each(|_| {
            assert!(random.not(f, 0).is_atomic());
            assert!(random.not(f, 1).is_atomic());
        });
        for depth in 2..7 {
            for _ in 0..10 {
                let formula = random.not(f, depth);
                assert!(formula.is_not());
                assert!(formula_depth(formula, f) <= u64::from(depth));
            }
        }
    }

    #[test]
    fn test_impl() {
        let f = &FormulaFactory::new();
        let mut random = FormulaRandomizer::new(config());
        (0..100).for_each(|_| assert!(random.implication(f, 0).is_atomic()));
        for depth in 1..7 {
            for _ in 0..10 {
                let formula = random.implication(f, depth);
                assert!(formula.is_impl());
                assert!(formula_depth(formula, f) <= u64::from(depth));
            }
        }
    }

    #[test]
    fn test_equiv() {
        let f = &FormulaFactory::new();
        let mut random = FormulaRandomizer::new(config());
        (0..100).for_each(|_| assert!(random.equivalence(f, 0).is_atomic()));
        for depth in 1..7 {
            for _ in 0..10 {
                let formula = random.equivalence(f, depth);
                assert!(formula.is_equiv());
                assert!(formula_depth(formula, f) <= u64::from(depth));
            }
        }
    }

    #[test]
    //#[allow(clippy::cast_lossless)]
    fn test_pbc() {
        let f = &FormulaFactory::new();
        let mut random = FormulaRandomizer::new(
            FormulaRandomizerConfig::default_with_num_vars(25)
                .weight_pbc_coeff_positive(3.0)
                .weight_pbc_coeff_negative(1.0)
                .weight_variable(3.0)
                .weight_negative_literal(1.0)
                .weight_pbc_type_le(5.0)
                .weight_pbc_type_lt(4.0)
                .weight_pbc_type_ge(3.0)
                .weight_pbc_type_gt(2.0)
                .weight_pbc_type_eq(1.0)
                .maximum_coefficient_pbc(10),
        );
        let (mut pos_coeff, mut neg_coeff, mut pos_lit, mut neg_lit, mut le, mut lt, mut ge, mut gt, mut eq) =
            (0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0);
        for _ in 0..5000 {
            let formula = random.pbc(f);
            assert!(formula.is_pbc() || formula.is_cc());
            let (coeffs, lits, rhs, comparator) = if formula.is_pbc() {
                let pbc = formula.as_pbc(f).unwrap();
                (pbc.coefficients, pbc.literals, pbc.rhs, pbc.comparator)
            } else {
                let cc = formula.as_cc(f).unwrap();
                (Box::from(vec![1; cc.variables.len()]), cc.variables.iter().map(Variable::pos_lit).collect(), cc.rhs.into(), cc.comparator)
            };
            let (mut pos_sum, mut neg_sum) = (0, 0);
            assert!(coeffs.len() <= 10);
            for &coeff in &*coeffs {
                if coeff > 0 {
                    pos_coeff += 1.0;
                    pos_sum += coeff;
                } else {
                    neg_coeff += 1.0;
                    neg_sum += coeff;
                }
            }
            assert!(neg_sum - 1 < rhs && rhs < pos_sum + 1);
            for lit in &*lits {
                if lit.phase() {
                    pos_lit += 1.0;
                } else {
                    neg_lit += 1.0;
                }
            }
            match comparator {
                LE => le += 1.0,
                LT => lt += 1.0,
                GE => ge += 1.0,
                GT => gt += 1.0,
                EQ => eq += 1.0,
            }
        }
        assert!(0.8 * 3.0 * neg_coeff < pos_coeff && pos_coeff < 1.2 * 3.0 * neg_coeff);
        assert!(0.8 * 3.0 * neg_lit < pos_lit && pos_lit < 1.2 * 3.0 * neg_lit);
        assert!(0.7 * 5.0 / 4.0 * lt < le && le < 1.3 * 5.0 / 4.0 * lt);
        assert!(0.7 * 4.0 / 3.0 * ge < lt && lt < 1.3 * 4.0 / 3.0 * ge);
        assert!(0.7 * 3.0 / 2.0 * gt < ge && ge < 1.3 * 3.0 / 2.0 * gt);
        assert!(0.7 * 2.0 / 1.0 * eq < gt && gt < 1.3 * 2.0 / 1.0 * eq);
    }

    #[test]
    fn test_cc() {
        let f = &FormulaFactory::new();
        let mut random = FormulaRandomizer::new(
            FormulaRandomizerConfig::default_with_num_vars(25)
                .seed(43_547_143)
                .weight_pbc_type_le(5.0)
                .weight_pbc_type_lt(4.0)
                .weight_pbc_type_ge(3.0)
                .weight_pbc_type_gt(2.0)
                .weight_pbc_type_eq(1.0)
                .maximum_coefficient_pbc(10),
        );
        let (mut le, mut lt, mut ge, mut gt, mut eq) = (0.0, 0.0, 0.0, 0.0, 0.0);
        for _ in 0..10000 {
            let formula = random.cc(f);
            assert!(formula.is_cc());
            let cc = formula.as_cc(f).unwrap();
            assert!(cc.variables.len() <= 10);
            assert!(cc.rhs <= 10);
            match cc.comparator {
                LE => le += 1.0,
                LT => lt += 1.0,
                GE => ge += 1.0,
                GT => gt += 1.0,
                EQ => eq += 1.0,
            }
        }
        assert!(0.7 * 5.0 / 4.0 * lt < le && le < 1.3 * 5.0 / 4.0 * lt);
        assert!(0.7 * 4.0 / 3.0 * ge < lt && lt < 1.3 * 4.0 / 3.0 * ge);
        assert!(0.7 * 3.0 / 2.0 * gt < ge && ge < 1.3 * 3.0 / 2.0 * gt);
        assert!(0.7 * 2.0 / 1.0 * eq < gt && gt < 1.3 * 2.0 / 1.0 * eq);
    }

    #[test]
    fn test_amo() {
        let f = &FormulaFactory::new();
        let mut random = FormulaRandomizer::new(FormulaRandomizerConfig::default_with_num_vars(25).maximum_coefficient_pbc(10));
        for _ in 0..1000 {
            let formula = random.amo(f);
            assert!(formula.is_cc());
            let amo = formula.as_cc(f).unwrap();
            assert_eq!(1, amo.rhs);
            assert_eq!(LE, amo.comparator);
            assert!(amo.variables.len() < 10);
        }
    }

    #[test]
    fn test_exo() {
        let f = &FormulaFactory::new();
        let mut random = FormulaRandomizer::new(FormulaRandomizerConfig::default_with_num_vars(25).maximum_coefficient_pbc(10));
        for _ in 0..1000 {
            let formula = random.exo(f);
            assert!(formula.is_cc());
            let exo = formula.as_cc(f).unwrap();
            assert_eq!(1, exo.rhs);
            assert_eq!(EQ, exo.comparator);
            assert!(exo.variables.len() < 10);
        }
    }

    #[test]
    fn test_formula() {
        let f = &FormulaFactory::new();
        let mut random = FormulaRandomizer::new(
            FormulaRandomizerConfig::default_with_num_vars(25)
                .weight_constant(1.0)
                .weight_variable(2.0)
                .weight_negative_literal(3.0)
                .weight_and(4.0)
                .weight_or(5.0)
                .weight_not(6.0)
                .weight_impl(7.0)
                .weight_equiv(8.0),
        );
        let mut occurrences = HashMap::new();
        for _ in 0..10000 {
            let formula = random.formula(f, 3);
            count_occurrences(&mut occurrences, formula, f);
            assert!(formula_depth(formula, f) <= 3);
        }
        let total_occurrences = occurrences["and"] + occurrences["or"] + occurrences["impl"] + occurrences["equiv"];
        // Considering constants does not make sense (they are always removed)
        // Considering literals does not make sense (they must be at the leafs, so their effective weight will be considerably higher)
        // Not is also a special case (it will be reduced to a literal if it's operand is itself a literal)
        assert!(4 * total_occurrences / 30 / 2 < occurrences["and"] && occurrences["and"] < 4 * total_occurrences / 30 * 2);
        assert!(5 * total_occurrences / 30 / 2 < occurrences["or"] && occurrences["or"] < 5 * total_occurrences / 30 * 2);
        assert!(7 * total_occurrences / 30 / 2 < occurrences["impl"] && occurrences["impl"] < 7 * total_occurrences / 30 * 2);
        assert!(8 * total_occurrences / 30 / 2 < occurrences["equiv"] && occurrences["equiv"] < 8 * total_occurrences / 30 * 2);
        assert!(occurrences.get("pbc").is_none());
        assert!(occurrences.get("cc").is_none());
        assert!(occurrences.get("amo").is_none());
        assert!(occurrences.get("exo").is_none());
    }

    #[test]
    #[allow(clippy::cast_precision_loss)]
    fn test_formula_with_pbc() {
        let f = &FormulaFactory::new();
        let mut random = FormulaRandomizer::new(
            FormulaRandomizerConfig::default_with_num_vars(25)
                .weight_constant(0.0)
                .weight_variable(1.0)
                .weight_negative_literal(1.0)
                .weight_pbc(1.0)
                .weight_cc(1.0)
                .weight_amo(1.0)
                .weight_exo(1.0)
                .weight_and(3.0)
                .weight_or(3.0)
                .weight_not(0.0)
                .weight_impl(0.0)
                .weight_equiv(0.0),
        );
        let mut occurrences = HashMap::new();
        for _ in 0..10000 {
            let formula = random.formula(f, 3);
            count_occurrences(&mut occurrences, formula, f);
            assert!(formula_depth(formula, f) <= 3);
        }
        assert!(
            0.8 * (occurrences["pos_lit"] as f32) < occurrences["neg_lit"] as f32
                && (occurrences["neg_lit"] as f32) < 1.2 * occurrences["pos_lit"] as f32
        );
        assert!(
            0.8 * (occurrences["pos_lit"] as f32) < occurrences["pbc"] as f32
                && (occurrences["pbc"] as f32) < 1.2 * occurrences["pos_lit"] as f32
        );
        assert!(
            0.8 * (occurrences["pos_lit"] as f32) < occurrences["cc"] as f32
                && (occurrences["cc"] as f32) < 1.2 * occurrences["pos_lit"] as f32
        );
        assert!(
            0.8 * (occurrences["pos_lit"] as f32) < occurrences["exo"] as f32
                && (occurrences["exo"] as f32) < 1.2 * occurrences["pos_lit"] as f32
        );
        assert!(
            0.8 * (occurrences["pos_lit"] as f32) < occurrences["amo"] as f32
                && (occurrences["amo"] as f32) < 1.2 * occurrences["pos_lit"] as f32
        );
    }

    fn random_formulas(f: &FormulaFactory) -> [EncodedFormula; 15] {
        let mut random = FormulaRandomizer::new(config());
        let constraint_set = random.constraint_set(f, 5, 3);
        [
            random.constant(f),
            random.variable(f),
            random.literal(f),
            random.atom(f),
            random.and(f, 3),
            random.or(f, 3),
            random.not(f, 3),
            random.implication(f, 3),
            random.equivalence(f, 3),
            random.formula(f, 3),
            f.and(constraint_set.iter()),
            random.cc(f),
            random.pbc(f),
            random.amo(f),
            random.exo(f),
        ]
    }

    fn count_occurrences(occurrences: &mut HashMap<&str, i32>, formula: EncodedFormula, f: &FormulaFactory) {
        use FormulaType::{And, Cc, Equiv, False, Impl, Lit, Not, Or, Pbc, True};
        match formula.formula_type() {
            True | False => *occurrences.entry("constant").or_insert(0) += 1,
            Lit(LitType::Pos(_)) => *occurrences.entry("pos_lit").or_insert(0) += 1,
            Lit(LitType::Neg(_)) => *occurrences.entry("neg_lit").or_insert(0) += 1,
            And => *occurrences.entry("and").or_insert(0) += 1,
            Or => *occurrences.entry("or").or_insert(0) += 1,
            Not => *occurrences.entry("not").or_insert(0) += 1,
            Impl => *occurrences.entry("impl").or_insert(0) += 1,
            Equiv => *occurrences.entry("equiv").or_insert(0) += 1,
            Cc => {
                let cc = formula.as_cc(f).unwrap();
                if cc.rhs == 1 && cc.comparator == LE {
                    *occurrences.entry("amo").or_insert(0) += 1;
                } else if cc.rhs == 1 && cc.comparator == EQ {
                    *occurrences.entry("exo").or_insert(0) += 1;
                } else {
                    *occurrences.entry("cc").or_insert(0) += 1;
                }
            }
            Pbc => *occurrences.entry("pbc").or_insert(0) += 1,
        };
        formula.operands(f).iter().for_each(|&op| count_occurrences(occurrences, op, f));
    }
}
