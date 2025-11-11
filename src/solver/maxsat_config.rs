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
    /// Print intermediated results and stats.
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

/// Merge strategy of the solver.
#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub enum MergeStrategy {
    /// Sequential strategy.
    Sequential,
    /// Sequential sorted strategy.
    SequentialSorted,
    /// Binary strategy.
    Binary,
}

/// Graph type used the solver.
#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub enum GraphType {
    /// Vig.
    Vig,
    /// CVig.
    CVig,
    /// Res.
    Res,
}

/// Configuration for
/// [`MaxSatSolver`](crate::solver::maxsat::MaxSatSolver).
///
/// # Usage
///
/// This configuration follows the builder pattern:
/// ```
/// # use logicng::solver::maxsat::*;
///
/// let default_config = MaxSatConfig::default();
/// let custom_config = MaxSatConfig::default()
///                 .cardinal(CardinalEncoding::MTotalizer)
///                 .pb(PbEncoding::Gte);
/// ```
///
/// Warning: Not all configurations allowed by `MaxSatConfig` are valid
/// configurations. Some algorithms do only work under certain combinations of
/// settings and the algorithms will ignore settings which are not relevant for
/// it. The default configuration works for all algorithms.
#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub struct MaxSatConfig {
    /// Pseudo-boolean encoding
    pub pb_encoding: PbEncoding,
    /// Cardinality encoding
    pub cardinal_encoding: CardinalEncoding,
    /// Weight strategy
    pub weight_strategy: WeightStrategy,
    /// Merge strategy
    pub merge_strategy: MergeStrategy,
    /// Graph type
    pub graph_type: GraphType,
    /// Print verbosity
    pub verbosity: Verbosity,
    /// Symmetry
    pub symmetry: Symmetry,
    /// bmo
    pub bmo: bool,
}

impl Default for MaxSatConfig {
    fn default() -> Self {
        Self {
            pb_encoding: PbEncoding::Swc,
            cardinal_encoding: CardinalEncoding::Totalizer,
            weight_strategy: WeightStrategy::None,
            merge_strategy: MergeStrategy::Binary,
            graph_type: GraphType::Res,
            symmetry: Symmetry::Sym(i32::MAX),
            verbosity: Verbosity::None,
            bmo: true,
        }
    }
}

impl MaxSatConfig {
    /// Updates [`PbEncoding`].
    ///
    /// Possible values:
    /// - `Swc` (default)
    /// - `Gte`
    /// - `Adder`
    ///
    /// `PbEncoding` is used by
    /// [`Algorithm::LinearSu`](crate::solver::maxsat::Algorithm).
    /// `LinearSu` in combination with the `Adder` encoding does not support
    /// weighted ``MaxSat`` problems.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::solver::maxsat::*;
    /// let config = MaxSatConfig::default()
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

    /// Updates [`CardinalEncoding`].
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
    /// let config = MaxSatConfig::default()
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

    /// Updates [`WeightStrategy`].
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
    /// let config = MaxSatConfig::default()
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

    /// Updates [`MergeStrategy`].
    ///
    /// Possible values:
    /// - `Sequential`
    /// - `SequentialSorted`
    /// - `Binary` (default)
    ///
    /// `MergeStrategy` is used by
    /// [`Algorithm::PartMsu3`](crate::solver::maxsat::Algorithm).
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::solver::maxsat::*;
    /// let config = MaxSatConfig::default()
    ///         // ...
    ///         .merge(MergeStrategy::Sequential)
    ///         // ...
    ///         ;
    /// ```
    #[must_use]
    pub const fn merge(mut self, merge_strategy: MergeStrategy) -> Self {
        self.merge_strategy = merge_strategy;
        self
    }

    /// Updates [`GraphType`].
    ///
    /// Possible values:
    /// - `Vig`
    /// - `CVig`
    /// - `Res` (default)
    ///
    /// `GraphType` is used by
    /// [`Algorithm::PartMsu3`](crate::solver::maxsat::Algorithm).
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::solver::maxsat::*;
    /// let config = MaxSatConfig::default()
    ///         // ...
    ///         .graph(GraphType::Vig)
    ///         // ...
    ///         ;
    /// ```
    #[must_use]
    pub const fn graph(mut self, graph_type: GraphType) -> Self {
        self.graph_type = graph_type;
        self
    }

    /// Updates [`Symmetry`].
    ///
    /// Possible values:
    /// - `None` (default)
    /// - `Sym(limit: i32)`
    ///
    /// `Symmetry` is used by
    /// [`Algorithm::Wbo`](crate::solver::maxsat::Algorithm).
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::solver::maxsat::*;
    /// let config = MaxSatConfig::default()
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

    /// Updates [`Verbosity`]. When activated the algorithms may output their
    /// progress and intermediated results.
    ///
    /// Possible values:
    /// - `None` (default)
    /// - `Some`
    ///
    /// `Verbosity` is used by all algorithms.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::solver::maxsat::*;
    /// let config = MaxSatConfig::default()
    ///         // ...
    ///         .verbosity(Verbosity::Some)
    ///         // ...
    ///         ;
    /// ```
    #[must_use]
    pub const fn verbosity(mut self, verb: Verbosity) -> Self {
        self.verbosity = verb;
        self
    }

    /// Updates the `bmo` setting. By default `bmo` is active.
    ///
    /// `bmo` is used by
    /// [`Algorithm::LinearSu`](crate::solver::maxsat::Algorithm).
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::solver::maxsat::*;
    /// let config = MaxSatConfig::default()
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
