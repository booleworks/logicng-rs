use dashmap::DashMap;

use crate::formulas::EncodedFormula;

use super::formula_cache::formula_encoding::FormulaEncoding;

pub type FormulaCache<V> = DashMap<FormulaEncoding, V>;

pub struct OperationCache<V> {
    cache: DashMap<FormulaEncoding, V>,
}

impl<V> OperationCache<V> {
    pub fn new() -> Self {
        Self { cache: DashMap::new() }
    }

    pub fn insert(&self, formula: EncodedFormula, value: V) {
        self.cache.entry(formula.encoding).or_insert(value);
    }

    #[cfg(test)]
    pub(crate) fn len(&self) -> usize {
        self.cache.len()
    }
}

impl<V: Clone> OperationCache<V> {
    pub fn get(&self, formula: EncodedFormula) -> Option<V> {
        self.cache.get(&formula.encoding).map(|v| v.clone())
    }

    #[allow(dead_code)]
    pub fn get_or_insert<F: FnOnce() -> V>(&mut self, formula: EncodedFormula, computation: F) -> V {
        self.cache.entry(formula.encoding).or_insert_with(computation).clone()
    }
}
