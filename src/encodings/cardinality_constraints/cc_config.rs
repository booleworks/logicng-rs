/// The encoder for at-most-one and exactly-one constraints.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum AmoEncoder {
    /// Pure encoding.
    Pure,
    /// Ladder encoding.
    Ladder,
    /// Product encoding.
    Product {
        /// Recursive bound for encoding.
        recursive_bound: usize,
    },
    /// Nested encoding.
    Nested {
        /// Group size for encoding.
        group_size: usize,
    },
    /// Commander encoding.
    Commander {
        /// Group size for encoding.
        group_size: usize,
    },
    /// Binary encoding.
    Binary,
    /// Bimander encoding.
    Bimander {
        /// Group size for encoding.
        group_size: BimanderGroupSize,
    },
    /// Best encoding algorithm.
    Best,
}

/// The encoder for at-most-k constraints.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum AmkEncoder {
    /// Totalizer encoding.
    Totalizer,
    /// Modular totalizer encoding.
    ModularTotalizer,
    /// Cardinality network.
    CardinalityNetwork,
    /// Best encoding.
    Best,
}

/// The encoder for at-least-k constraints.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum AlkEncoder {
    /// Totalizer encoding.
    Totalizer,
    /// Modular totalizer encoding.
    ModularTotalizer,
    /// Cardinality network.
    CardinalityNetwork,
    /// Best encoding.
    Best,
}

/// The encoder for exactly-k constraints.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum ExkEncoder {
    /// Totalizer encoding.
    Totalizer,
    /// Cardinality network.
    CardinalityNetwork,
    /// Best encoding.
    Best,
}

/// The group size for the Bimander encoding.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum BimanderGroupSize {
    /// Half.
    Half,
    /// Square root.
    Sqrt,
    /// Fixed size.
    Fixed(usize),
}

/// Configuration for the [`CcEncoder`](`crate::cardinality_constraints::CcEncoder`).
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct CcConfig {
    /// Encoder for at-most-one constraints.
    pub amo_encoder: AmoEncoder,
    /// Encoder for at-most-k constraints.
    pub amk_encoder: AmkEncoder,
    /// Encoder for at-least-k constraints.
    pub alk_encoder: AlkEncoder,
    /// Encoder for exactly-k constraints.
    pub exk_encoder: ExkEncoder,
}

impl Default for CcConfig {
    fn default() -> Self {
        Self::new()
    }
}

impl CcConfig {
    /// Default size for `Bimander` encoding.
    pub const DEFAULT_BIMANDER_GROUP_SIZE: usize = 3;
    /// Default size for `Nested` encoding.
    pub const DEFAULT_NESTING_GROUP_SIZE: usize = 4;
    /// Default recursive bound for `Product` encoding.
    pub const DEFAULT_PRODUCT_RECURSIVE_BOUND: usize = 20;
    /// Default size for `Commander` encoding.
    pub const DEFAULT_COMMANDER_GROUP_SIZE: usize = 3;

    /// Creates a new configuration.
    pub const fn new() -> Self {
        Self { amo_encoder: AmoEncoder::Best, amk_encoder: AmkEncoder::Best, alk_encoder: AlkEncoder::Best, exk_encoder: ExkEncoder::Best }
    }

    /// Sets the encoder for at-most-one constraints.
    #[must_use]
    pub const fn amo_encoder(mut self, amo_encoder: AmoEncoder) -> Self {
        self.amo_encoder = amo_encoder;
        self
    }

    /// Sets the encoder for at-most-k constraints.
    #[must_use]
    pub const fn amk_encoder(mut self, amk_encoder: AmkEncoder) -> Self {
        self.amk_encoder = amk_encoder;
        self
    }

    /// Sets the encoder for at-least-k constraints.
    #[must_use]
    pub const fn alk_encoder(mut self, alk_encoder: AlkEncoder) -> Self {
        self.alk_encoder = alk_encoder;
        self
    }

    /// Sets the encoder for exactly-k constraints.
    #[must_use]
    pub const fn exk_encoder(mut self, exk_encoder: ExkEncoder) -> Self {
        self.exk_encoder = exk_encoder;
        self
    }
}
