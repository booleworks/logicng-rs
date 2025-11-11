/// Pseudo-boolean constraint encoding algorithms.
#[derive(Copy, Clone, Eq, PartialEq, Debug, Hash)]
pub enum PbAlgorithm {
    /// SWC algorithm.
    Swc,
    /// Binary merge algorithm.
    BinaryMerge,
    /// Adder networks.
    AdderNetworks,
    /// Best algorithm.
    Best,
}

/// Configuration for [`PbEncoder`](`crate::pseudo_booleans::PbEncoder`).
#[derive(Clone, Eq, PartialEq, Debug, Hash)]
pub struct PbConfig {
    /// Algorithm used to encoded pseudo-boolean constraint.
    pub pb_algorithm: PbAlgorithm,
    /// Setting for general arc consistency in binary merge encoding.
    pub binary_merge_use_gac: bool,
    /// Setting for support for single bits in the binary merge encoding.
    pub binary_merge_no_support_for_single_bit: bool,
    /// Setting for watchdog encoding in the binary merge
    pub binary_merge_use_watch_dog: bool,
}

impl Default for PbConfig {
    fn default() -> Self {
        Self::new()
    }
}

impl PbConfig {
    /// Constructs a new configuration with default values.
    pub const fn new() -> Self {
        Self {
            pb_algorithm: PbAlgorithm::Best,
            binary_merge_use_gac: true,
            binary_merge_no_support_for_single_bit: false,
            binary_merge_use_watch_dog: true,
        }
    }

    /// Updates the algorithm for pseudo-boolean constraints. The default
    /// algorithm is [`PbAlgorithm::Best`](`PbAlgorithm`).
    #[must_use]
    pub const fn pb_encoder(mut self, pb_encoder: PbAlgorithm) -> Self {
        self.pb_algorithm = pb_encoder;
        self
    }

    /// Sets whether general arc consistency should be used in the binary merge
    /// encoding. The default value is `true`.
    #[must_use]
    pub const fn binary_merge_use_gac(mut self, binary_merge_use_gac: bool) -> Self {
        self.binary_merge_use_gac = binary_merge_use_gac;
        self
    }

    /// Sets the support for single bits in the binary merge encoding. The
    /// default value is `false`.
    #[must_use]
    pub const fn binary_merge_no_support_for_single_bit(mut self, binary_merge_no_support_for_single_bit: bool) -> Self {
        self.binary_merge_no_support_for_single_bit = binary_merge_no_support_for_single_bit;
        self
    }

    /// Sets whether the watchdog encoding should be used in the binary merge
    /// encoding. The default value is `true`.
    #[must_use]
    pub const fn binary_merge_use_watch_dog(mut self, binary_merge_use_watch_dog: bool) -> Self {
        self.binary_merge_use_watch_dog = binary_merge_use_watch_dog;
        self
    }
}
