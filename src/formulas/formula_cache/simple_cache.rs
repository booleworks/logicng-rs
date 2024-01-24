use std::fmt::Debug;
use std::hash::Hash;

use dashmap::DashMap;

use crate::collections::AppendOnlyVec;
use crate::formulas::formula_cache::formula_encoding::Encoding;
use crate::formulas::formula_cache::CACHE_INITIAL_CAPACITY;
use crate::formulas::FormulaType;

use super::formula_encoding::FormulaEncoding;

pub struct SimpleCache<T: Hash + Eq + Clone + Debug> {
    vec: AppendOnlyVec<T>,
    reverse_map: DashMap<T, FormulaEncoding>,
}

impl<T: Hash + Eq + Clone + Debug> SimpleCache<T> {
    pub fn new() -> Self {
        Self { vec: AppendOnlyVec::new(), reverse_map: DashMap::with_capacity(CACHE_INITIAL_CAPACITY) }
    }

    #[allow(clippy::cast_possible_truncation)]
    pub fn get(&self, index: FormulaEncoding) -> &T {
        assert!(index.is_large_cache(), "SimpleCache does not optimize for small formulas!");
        &self.vec[index.index() as usize]
    }

    pub fn get_or_insert(&self, element: T, ty: FormulaType) -> FormulaEncoding {
        // first a fast check whether the element is already there.
        if let Some(v) = self.reverse_map.get(&element) {
            return *v;
        }

        // If we need to add the element, we have to check again if the element
        // is there, but in a more expensive thread-safe way.
        *self.reverse_map.entry(element.clone()).or_insert_with(|| {
            let index = self.vec.push(element);
            FormulaEncoding::encode(index as u64, ty, true)
        })
    }

    pub fn lookup(&self, element: &T) -> Option<FormulaEncoding> {
        self.reverse_map.get(element).map(|v| *v)
    }

    pub fn shrink_to_fit(&self) {
        self.reverse_map.shrink_to_fit();
    }

    pub fn len(&self) -> usize {
        debug_assert_eq!(self.vec.len(), self.reverse_map.len());
        self.vec.len()
    }
}

impl<T: Hash + Eq + Clone + Debug> std::ops::Index<FormulaEncoding> for SimpleCache<T> {
    type Output = T;

    fn index(&self, index: FormulaEncoding) -> &Self::Output {
        self.get(index)
    }
}
