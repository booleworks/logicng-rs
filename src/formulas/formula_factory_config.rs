use crate::encodings::{CcConfig, PbConfig};
use crate::operations::transformations::{AdvancedFactorizationConfig, CnfAlgorithm};

use super::CacheConfig;

/// `FormulaFactoryConfig` is a configuration for a [`FormulaFactory`].
///
/// It consists of four sub-configuration, which defines the behavior in certain
/// situation. The respective documentation of those configurations gives you
/// more information about themself.
///
/// [`FormulaFactory`]: super::FormulaFactory
#[derive(Clone)]
pub struct FormulaFactoryConfig {
    /// Specifies the exact handling of cardinality constraints. In particular,
    /// the encoding algorithms.
    pub cc_config: CcConfig,
    /// Specifies the exact handling of pseudo-boolean constraints. In
    /// particular, the encoding algorithms.
    pub pb_config: PbConfig,
    /// Specifies the algorithm that is used to calculate the _CNF_-form of a
    /// formula.
    pub cnf_config: CnfAlgorithm,
    /// A `FormulaFactory` is able to cache results and intermediate results of
    /// operations. The `CacheConfig` allows you to enable or disable the cache
    /// for specific operations.
    pub caches: CacheConfig,
}

impl FormulaFactoryConfig {
    /// Creates a new `FormulaFactoryConfig` with a default configuration.
    ///
    /// Be aware that the default _CNF_ algorithm for the CNF transformation may
    /// result in a _CNF_ containing additional auxiliary variables. Also, the
    /// result may not be a semantically equivalent CNF but an equisatisfiable
    /// _CNF_. If the introduction of auxiliary variables is unwanted, you can
    /// choose one of the algorithms [`CnfAlgorithm::Factorization`] and
    /// [`CnfAlgorithm::Bdd`]. Both algorithms provide CNF conversions without
    /// the introduction of auxiliary variables and the result is a semantically
    /// equivalent CNF.
    ///
    /// The default configuration of [`CcConfig`] and [`PbConfig`] is also used
    /// in this configuration.
    pub fn new() -> Self {
        Self {
            cc_config: CcConfig::new(),
            pb_config: PbConfig::new(),
            cnf_config: CnfAlgorithm::Advanced(AdvancedFactorizationConfig::default()),
            caches: CacheConfig::default(),
        }
    }
}

impl Default for FormulaFactoryConfig {
    fn default() -> Self {
        Self::new()
    }
}
