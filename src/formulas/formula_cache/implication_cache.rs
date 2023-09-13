use dashmap::DashMap;

use crate::collections::AppendOnlyVec;
use crate::formulas::formula_cache::CACHE_INITIAL_CAPACITY;
use crate::formulas::{EncodedFormula, FormulaType};

use super::formula_encoding::{Encoding, FormulaEncoding, SmallFormulaEncoding};

pub struct ImplicationCache {
    vec32: AppendOnlyVec<(SmallFormulaEncoding, SmallFormulaEncoding)>,
    vec64: AppendOnlyVec<(FormulaEncoding, FormulaEncoding)>,
    reverse_map32: DashMap<(SmallFormulaEncoding, SmallFormulaEncoding), FormulaEncoding>,
    reverse_map64: DashMap<(FormulaEncoding, FormulaEncoding), FormulaEncoding>,
}

impl ImplicationCache {
    pub fn new() -> Self {
        Self {
            vec32: AppendOnlyVec::new(),
            vec64: AppendOnlyVec::new(),
            reverse_map32: DashMap::with_capacity(CACHE_INITIAL_CAPACITY),
            reverse_map64: DashMap::default(),
        }
    }

    #[allow(clippy::cast_possible_truncation)]
    pub fn get(&self, index: FormulaEncoding) -> (EncodedFormula, EncodedFormula) {
        if index.is_large_cache() {
            let (left, right) = self.vec64[index.index() as usize];
            (left.to_formula(), right.to_formula())
        } else {
            let (left, right) = self.vec32[index.index() as usize];
            (left.to_formula(), right.to_formula())
        }
    }

    pub fn get_or_insert(&self, (left, right): (EncodedFormula, EncodedFormula)) -> FormulaEncoding {
        if left.encoding.is_large() || right.encoding.is_large() {
            let encoded = (left.encoding, right.encoding);
            *self.reverse_map64.entry(encoded).or_insert_with(|| {
                let index = self.vec64.push(encoded);
                FormulaEncoding::encode(index as u64, FormulaType::Impl, true)
            })
        } else {
            let encoded = (left.encoding.as_32(), right.encoding.as_32());
            *self.reverse_map32.entry(encoded).or_insert_with(|| {
                let index = self.vec32.push(encoded);
                FormulaEncoding::encode(index as u64, FormulaType::Impl, false)
            })
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
