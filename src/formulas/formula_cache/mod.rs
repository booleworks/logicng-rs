pub mod equivalence_cache;
pub mod implication_cache;
pub mod nary_formula_cache;
pub mod not_cache;
pub mod simple_cache;

pub mod formula_encoding;
pub mod formula_factory_caches;
pub mod hashable_formula_set;

const CACHE_INITIAL_CAPACITY: usize = 10;
