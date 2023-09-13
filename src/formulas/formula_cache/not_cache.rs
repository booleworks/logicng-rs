use dashmap::DashMap;

use crate::collections::AppendOnlyVec;
use crate::formulas::formula_cache::CACHE_INITIAL_CAPACITY;
use crate::formulas::{EncodedFormula, FormulaType};

use super::formula_encoding::{Encoding, FormulaEncoding, SmallFormulaEncoding};

pub struct NotCache {
    vec32: AppendOnlyVec<SmallFormulaEncoding>,
    vec64: AppendOnlyVec<FormulaEncoding>,
    reverse_map32: DashMap<SmallFormulaEncoding, FormulaEncoding>,
    reverse_map64: DashMap<FormulaEncoding, FormulaEncoding>,
}

impl NotCache {
    pub fn new() -> Self {
        Self {
            vec32: AppendOnlyVec::new(),
            vec64: AppendOnlyVec::new(),
            reverse_map32: DashMap::with_capacity(CACHE_INITIAL_CAPACITY),
            reverse_map64: DashMap::default(),
        }
    }

    #[allow(clippy::cast_possible_truncation)]
    pub fn get(&self, index: FormulaEncoding) -> EncodedFormula {
        if index.is_large_cache() {
            let element = self.vec64[index.index() as usize];
            element.to_formula()
        } else {
            let element = self.vec32[index.index() as usize];
            element.to_formula()
        }
    }

    pub fn get_or_insert(&self, element: EncodedFormula) -> FormulaEncoding {
        if element.encoding.is_large() {
            let encoded = element.encoding;
            *self.reverse_map64.entry(encoded).or_insert_with(|| {
                let index = self.vec64.push(encoded);
                FormulaEncoding::encode(index as u64, FormulaType::Not, true)
            })
        } else {
            let encoded = element.encoding.as_32();
            *self.reverse_map32.entry(encoded).or_insert_with(|| {
                let index = self.vec32.push(encoded);
                FormulaEncoding::encode(index as u64, FormulaType::Not, false)
            })
        }
    }

    pub fn lookup(&self, element: EncodedFormula) -> Option<FormulaEncoding> {
        if element.encoding.is_large() {
            self.reverse_map64.get(&element.encoding).map(|v| *v)
        } else {
            self.reverse_map32.get(&element.encoding.as_32()).map(|v| *v)
        }
    }

    pub fn shrink_to_fit(&self) {
        self.reverse_map32.shrink_to_fit();
        self.reverse_map64.shrink_to_fit();
    }

    pub fn len(&self) -> usize {
        self.vec32.len() + self.vec64.len()
    }
}
