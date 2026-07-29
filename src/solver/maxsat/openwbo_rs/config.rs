/// Algorithms supported by the Rust OpenWBO backend.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Algorithm {
    /// Weighted Boolean Optimization
    Wbo,
    /// OLL
    Oll,
    /// Linear Sat-Unsat
    LinearSu,
    /// Core-guided MSU3 algorithm.
    Msu3,
}

impl Algorithm {
    /// Returns whether this algorithm supports weighted MaxSAT with the given
    /// configuration.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::solver::maxsat::*;
    /// let config = OpenWboConfig::default();
    ///
    /// assert!(Algorithm::Wbo.weighted(&config));
    /// assert!(!Algorithm::Msu3.weighted(&config));
    /// ```
    pub fn weighted(&self, config: &OpenWboConfig) -> bool {
        match self {
            Self::Wbo | Self::Oll => true,
            Self::LinearSu => config.pb_encoding != PbEncoding::Adder,
            Self::Msu3 => false,
        }
    }
}

/// The pseudo-boolean encoding.
#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub enum PbEncoding {
    /// SWC encoding.
    Swc,
    /// GTE encoding.
    Gte,
    /// Adder encoding.
    Adder,
}

/// The incremental strategy for cardinality and pseudo-Boolean encodings.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub enum IncrementalStrategy {
    /// No incremental encoding.
    None,
    /// Blocking incremental encoding.
    Blocking,
    /// Weakening incremental encoding.
    Weakening,
    /// Iterative incremental encoding.
    Iterative,
}

/// The cardinality encoding.
#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub enum CardinalEncoding {
    /// Cardinality Networks encoding.
    CNetworks,
    /// Totalizer encoding.
    Totalizer,
    /// Modulo totalizer encoding.
    MTotalizer,
}

/// The weight strategy.
#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub enum WeightStrategy {
    /// No strategy.
    None,
    /// Normal strategy.
    Normal,
    /// Diversify strategy.
    Diversify,
}

/// The verbosity of the solver.
#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub enum Verbosity {
    /// No verbosity.
    None,
    /// Print intermediate results and stats.
    Some,
}

/// Symmetry of the solver.
#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub enum Symmetry {
    /// No symmetry.
    None,
    /// Use symmetry.
    Sym(i32),
}

/// Configuration for the Rust OpenWBO backend.
///
/// # Usage
///
/// This configuration follows the builder pattern:
/// ```
/// # use logicng::solver::maxsat::*;
///
/// let default_config = OpenWboConfig::default();
/// let custom_config = OpenWboConfig::default()
///                 .cardinal(CardinalEncoding::MTotalizer)
///                 .pb(PbEncoding::Gte);
/// ```
///
/// Not every option applies to every algorithm. Algorithms ignore settings
/// which are not relevant to them. Use [`Algorithm::weighted`] to determine
/// whether a selected algorithm and encoding support weighted clauses. The
/// default configuration is valid for every algorithm.
#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub struct OpenWboConfig {
    /// The MaxSAT algorithm.
    pub algorithm: Algorithm,
    /// Pseudo-Boolean encoding.
    pub pb_encoding: PbEncoding,
    /// Cardinality encoding.
    pub cardinal_encoding: CardinalEncoding,
    /// Incremental encoding strategy.
    pub incremental_strategy: IncrementalStrategy,
    /// Weight strategy used by WBO.
    pub weight_strategy: WeightStrategy,
    /// Symmetry-breaking configuration used by WBO.
    pub symmetry: Symmetry,
    /// Whether LinearSU may use bounded multilevel optimization.
    pub bmo: bool,
}

impl Default for OpenWboConfig {
    fn default() -> Self {
        Self {
            algorithm: Algorithm::Oll,
            pb_encoding: PbEncoding::Swc,
            cardinal_encoding: CardinalEncoding::Totalizer,
            incremental_strategy: IncrementalStrategy::None,
            weight_strategy: WeightStrategy::None,
            symmetry: Symmetry::Sym(i32::MAX),
            bmo: true,
        }
    }
}

impl OpenWboConfig {
    /// Selects the MaxSAT algorithm.
    ///
    /// The chosen algorithm determines which other configuration options and
    /// weighted-problem variants are supported.
    ///
    /// # Example
    ///
    /// ```
    /// # use logicng::solver::maxsat::*;
    /// let config = OpenWboConfig::default().algorithm(Algorithm::Msu3);
    ///
    /// assert_eq!(config.algorithm, Algorithm::Msu3);
    /// ```
    #[must_use]
    pub const fn algorithm(mut self, algorithm: Algorithm) -> Self {
        self.algorithm = algorithm;
        self
    }

    /// Selects the pseudo-Boolean encoding.
    ///
    /// Possible values:
    /// - `Swc` (default)
    /// - `Gte`
    /// - `Adder`
    ///
    /// `PbEncoding` is used by
    /// [`Algorithm::LinearSu`](crate::solver::maxsat::Algorithm).
    /// `LinearSu` in combination with the `Adder` encoding does not support
    /// weighted MaxSAT problems.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::solver::maxsat::*;
    /// let config = OpenWboConfig::default()
    ///         // ...
    ///         .pb(PbEncoding::Adder)
    ///         // ...
    ///         ;
    /// ```
    #[must_use]
    pub const fn pb(mut self, pb_encoding: PbEncoding) -> Self {
        self.pb_encoding = pb_encoding;
        self
    }

    /// Selects the cardinality encoding.
    ///
    /// Possible values:
    /// - `CNetworks`
    /// - `Totalizer` (default)
    /// - `MTotalizer`
    ///
    /// `CardinalEncoding` is used by
    /// [`Algorithm::LinearSu`](crate::solver::maxsat::Algorithm).
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::solver::maxsat::*;
    /// let config = OpenWboConfig::default()
    ///         // ...
    ///         .cardinal(CardinalEncoding::CNetworks)
    ///         // ...
    ///         ;
    /// ```
    #[must_use]
    pub const fn cardinal(mut self, card_encoding: CardinalEncoding) -> Self {
        self.cardinal_encoding = card_encoding;
        self
    }

    /// Selects WBO's weight strategy.
    ///
    /// Possible values:
    /// - `None` (default)
    /// - `Normal`
    /// - `Diversify`
    ///
    /// `WeightStrategy` is used by
    /// [`Algorithm::Wbo`](crate::solver::maxsat::Algorithm).
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::solver::maxsat::*;
    /// let config = OpenWboConfig::default()
    ///         // ...
    ///         .weight(WeightStrategy::Diversify)
    ///         // ...
    ///         ;
    /// ```
    #[must_use]
    pub const fn weight(mut self, weight_strategy: WeightStrategy) -> Self {
        self.weight_strategy = weight_strategy;
        self
    }

    /// Selects WBO's symmetry-breaking configuration.
    ///
    /// Possible values:
    /// - `None`
    /// - `Sym(limit: i32)` (default with i32::MAX)
    ///
    /// `Symmetry` is used by
    /// [`Algorithm::Wbo`](crate::solver::maxsat::Algorithm).
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::solver::maxsat::*;
    /// let config = OpenWboConfig::default()
    ///         // ...
    ///         .symmetry(Symmetry::Sym(1000))
    ///         // ...
    ///         ;
    /// ```
    #[must_use]
    pub const fn symmetry(mut self, symmetry: Symmetry) -> Self {
        self.symmetry = symmetry;
        self
    }

    /// Updates the `bmo` setting. By default, `bmo` is active.
    ///
    /// `bmo` is used by
    /// [`Algorithm::LinearSu`](crate::solver::maxsat::Algorithm).
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::solver::maxsat::*;
    /// let config = OpenWboConfig::default()
    ///         // ...
    ///         .bmo(false)
    ///         // ...
    ///         ;
    /// ```
    #[must_use]
    pub const fn bmo(mut self, bmo: bool) -> Self {
        self.bmo = bmo;
        self
    }
}
