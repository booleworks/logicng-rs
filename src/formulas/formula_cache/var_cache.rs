use std::borrow::Cow;

use dashmap::DashMap;

use crate::collections::AppendOnlyVec;
use crate::formulas::formula_cache::formula_encoding::Encoding;
use crate::formulas::formula_cache::CACHE_INITIAL_CAPACITY;
use crate::formulas::{FormulaType, LitType};

use super::formula_encoding::FormulaEncoding;

pub struct VariableCache {
    vec: AppendOnlyVec<String>,
    reverse_map: DashMap<String, FormulaEncoding>,
}

impl VariableCache {
    pub fn new() -> Self {
        Self { vec: AppendOnlyVec::new(), reverse_map: DashMap::with_capacity(CACHE_INITIAL_CAPACITY) }
    }

    #[allow(clippy::cast_possible_truncation)]
    pub fn get(&self, index: FormulaEncoding) -> &str {
        assert!(index.is_large_cache(), "VariableCache does not optimize for small formulas!");
        &self.vec[index.index() as usize]
    }

    pub fn get_or_insert(&self, element: Cow<'_, str>) -> FormulaEncoding {
        // first a fast check whether the element is already there.
        if let Some(v) = self.reverse_map.get(element.as_ref()) {
            return *v;
        }

        // If we need to add the element, we have to check again if the element
        // is there, but in a more expensive thread-safe way.
        let name = element.into_owned();
        *self.reverse_map.entry(name.clone()).or_insert_with(|| {
            let index = self.vec.push(name);
            FormulaEncoding::encode(index as u64, FormulaType::Lit(LitType::Pos), true)
        })
    }

    pub fn lookup(&self, element: &str) -> Option<FormulaEncoding> {
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

impl std::ops::Index<FormulaEncoding> for VariableCache {
    type Output = str;

    fn index(&self, index: FormulaEncoding) -> &Self::Output {
        self.get(index)
    }
}
