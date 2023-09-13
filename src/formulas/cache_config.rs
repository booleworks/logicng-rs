#[allow(clippy::struct_excessive_bools)]
#[derive(Clone, Debug, Eq, PartialEq, Hash)]

/// Specifies which type of operations are allowed to cache their results.
///
/// A `FormulaFactory` can make use of caches to store already calculated
/// results of operations. Whether to use caches for a operations, depends on
/// the application and is a trade-off between write/read operations and
/// recalculating already known results. With larger and more complex formulas,
/// it becomes more likely that a cache improves the performance.
pub struct CacheConfig {
    /// Used by [`functions::number_of_atoms`](crate::operations::functions::number_of_atoms).
    pub number_of_atoms: bool,
    /// Used by [`functions::number_of_nodes`](crate::operations::functions::number_of_nodes).
    pub number_of_nodes: bool,
    /// Used by [`functions::formula_depth`](crate::operations::functions::formula_depth).
    pub formula_depth: bool,
    /// Used by [`functions::variables`](crate::operations::functions::variables).
    pub variables: bool,
    /// Used by [`functions::literals`](crate::operations::functions::literals).
    pub literals: bool,
    /// Used by [`functions::sub_nodes`](crate::operations::functions::sub_nodes).
    pub sub_nodes: bool,
    /// Used by [`CardinalityConstraint`](crate::formulas::CardinalityConstraint) for its encoding.
    pub cc_encoding: bool,
    /// Used by [`PbConstraint`](crate::formulas::PbConstraint) for its encoding.
    pub pbc_encoding: bool,
    /// Used by [`transformations::nnf`](crate::operations::transformations::nnf).
    pub nnf: bool,
    /// Used by [`transformations::factorization_dnf`](crate::operations::transformations::factorization_dnf).
    pub dnf: bool,
    /// Used by [`predicates::is_sat`](crate::operations::predicates::is_sat).
    pub sat: bool,
    /// Used by [`CnfAlgorithm::Factorization`](crate::operations::transformations::CnfAlgorithm).
    pub factorization_cnf: bool,
    /// Used by [`predicates::is_nnf`](crate::operations::predicates::is_nnf) and
    /// [`transformations::nnf`](crate::operations::transformations::nnf).
    pub is_nnf: bool,
    /// Used by [`predicates::is_cnf`](crate::operations::predicates::is_cnf) and
    /// [`CnfAlgorithm::Factorization`](crate::operations::transformations::CnfAlgorithm).
    pub is_cnf: bool,
    /// Used by [`predicates::is_dnf`](crate::operations::predicates::is_dnf) and
    /// [`transformations::factorization_dnf`](crate::operations::transformations::factorization_dnf).
    pub is_dnf: bool,
    /// Used by [`predicates::contains_pbc`](crate::operations::predicates::contains_pbc).//
    pub contains_pbc: bool,
    /// Used by
    /// [`transformations::backbone_simplification`](crate::operations::transformations::backbone_simplification).
    pub backbone_simps: bool,
}

impl CacheConfig {
    /// Creates a configuration with all caches disabled.
    ///
    /// # Example
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::formulas::CacheConfig;
    ///
    /// let config = CacheConfig::all_disabled();
    /// ```
    pub const fn all_disabled() -> Self {
        Self {
            number_of_atoms: false,
            number_of_nodes: false,
            formula_depth: false,
            variables: false,
            literals: false,
            sub_nodes: false,
            cc_encoding: false,
            pbc_encoding: false,
            nnf: false,
            dnf: false,
            sat: false,
            is_nnf: false,
            is_cnf: false,
            is_dnf: false,
            contains_pbc: false,
            factorization_cnf: false,
            backbone_simps: false,
        }
    }
}

impl Default for CacheConfig {
    fn default() -> Self {
        Self {
            number_of_atoms: true,
            number_of_nodes: true,
            formula_depth: true,
            variables: true,
            literals: true,
            sub_nodes: true,
            cc_encoding: true,
            pbc_encoding: true,
            nnf: true,
            dnf: true,
            sat: false,
            is_nnf: true,
            is_cnf: true,
            is_dnf: true,
            contains_pbc: true,
            factorization_cnf: true,
            backbone_simps: true,
        }
    }
}
