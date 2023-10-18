use std::collections::HashSet;
use std::fmt::Debug;
use std::hash::{BuildHasherDefault, Hash};
use std::vec::IntoIter;

use dashmap::DashMap;
use itertools::Itertools;

use crate::collections::AppendOnlyVec;
use crate::formulas::formula_cache::hashable_formula_set::{HashableFormulaSet, SimpleHashAdder};
use crate::formulas::formula_cache::CACHE_INITIAL_CAPACITY;
use crate::formulas::{EncodedFormula, FormulaType};

use super::formula_encoding::{extend_32, Encoding, FormulaEncoding, SmallFormulaEncoding};

pub struct NaryFormulaCache {
    vec32: AppendOnlyVec<Box<[SmallFormulaEncoding]>>,
    vec64: AppendOnlyVec<Box<[FormulaEncoding]>>,
    reverse_map32: DashMap<HashableFormulaSet<SmallFormulaEncoding>, FormulaEncoding, BuildHasherDefault<SimpleHashAdder>>,
    reverse_map64: DashMap<HashableFormulaSet<FormulaEncoding>, FormulaEncoding, BuildHasherDefault<SimpleHashAdder>>,
    representing_type: FormulaType,
}

impl NaryFormulaCache {
    pub fn new(ty: FormulaType) -> Self {
        Self {
            vec32: AppendOnlyVec::new(),
            vec64: AppendOnlyVec::new(),
            reverse_map32: DashMap::with_capacity_and_hasher(CACHE_INITIAL_CAPACITY, BuildHasherDefault::default()),
            reverse_map64: DashMap::default(),
            representing_type: ty,
        }
    }

    #[allow(dead_code, clippy::cast_possible_truncation)]
    pub fn get(&self, index: FormulaEncoding) -> Vec<EncodedFormula> {
        if index.is_large_cache() {
            self.vec64[index.index() as usize].iter().map(|&encoding| encoding.to_formula()).collect()
        } else {
            self.vec32[index.index() as usize].iter().map(|&encoding| encoding.to_formula()).collect()
        }
    }

    #[allow(clippy::cast_possible_truncation)]
    pub fn get_iter(&self, index: FormulaEncoding) -> NaryIterator {
        let container = if index.is_large_cache() {
            let vec = &self.vec64[index.index() as usize];
            NaryCacheContainer::Encoding64(vec)
        } else {
            let vec = &self.vec32[index.index() as usize];
            NaryCacheContainer::Encoding32(vec)
        };
        NaryIterator::new(container)
    }

    pub fn get_or_insert(
        &self,
        elements32: Vec<SmallFormulaEncoding>,
        element_set32: HashSet<SmallFormulaEncoding>,
        mut elements64: Vec<FormulaEncoding>,
        mut element_set64: HashSet<FormulaEncoding>,
    ) -> FormulaEncoding {
        if elements64.is_empty() {
            let set = HashableFormulaSet::new(element_set32);
            *self.reverse_map32.entry(set).or_insert_with(|| {
                let index = self.vec32.push(elements32.into());
                FormulaEncoding::encode(index as u64, self.representing_type, false)
            })
        } else {
            elements64.extend(elements32.iter().map(|e| e.as_64()));
            elements64.rotate_right(elements32.len());
            element_set64.extend(elements32.iter().map(|e| e.as_64()));
            let set = HashableFormulaSet::new(element_set64);
            *self.reverse_map64.entry(set).or_insert_with(|| {
                let index = self.vec64.push(elements64.into());
                FormulaEncoding::encode(index as u64, self.representing_type, true)
            })
        }
    }

    pub fn shrink_to_fit(&self) {
        self.reverse_map32.shrink_to_fit();
        self.reverse_map64.shrink_to_fit();
    }

    pub fn len(&self) -> usize {
        debug_assert_eq!(self.vec32.len(), self.reverse_map32.len());
        debug_assert_eq!(self.vec64.len(), self.reverse_map64.len());

        self.vec32.len() + self.vec64.len()
    }
}

#[derive(Clone, Hash, Eq, PartialEq, Debug)]
enum NaryCacheContainer<'a> {
    Encoding32(&'a [SmallFormulaEncoding]),
    Encoding64(&'a [FormulaEncoding]),
}

/// An iterator returning operands of a nary-operator.
///
/// This iterator keeps a reference to the data structure in the
/// [`FormulaFactory`](`crate::formulas::FormulaFactory`) storing the encoded operands of a nary-operator. This
/// allows to decoded all operands lazily when they are need.
///
/// You can resolve the reference by cloning the iterator with [`Self::into_owned()`].
/// This clones and decodes all values into a owned iterator. In some cases this
/// is necessary to deal with the borrow checker.
#[derive(Clone, Hash, Eq, PartialEq, Debug)]
pub struct NaryIterator<'a> {
    container: NaryCacheContainer<'a>,
    len: usize,
    current_index: usize,
}

impl<'a> NaryIterator<'a> {
    const fn new(container: NaryCacheContainer<'a>) -> Self {
        let len = match container {
            NaryCacheContainer::Encoding32(v) => v.len(),
            NaryCacheContainer::Encoding64(v) => v.len(),
        };
        NaryIterator { container, len, current_index: 0 }
    }

    /// Returns the length of the iterator.
    pub const fn len(&self) -> usize {
        self.len
    }

    /// Returns `true` if and only if the iterator has no elements.
    pub const fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Returns a owned version of this iterator. It clones and decodes all
    /// operands, such that it no longer needs the reference into the
    /// [`FormulaFactory`](`crate::formulas::FormulaFactory`).
    pub fn into_owned(self) -> IntoIter<EncodedFormula> {
        self.collect_vec().into_iter()
    }

    /// Returns a vector with all operands of this iterator, by cloning and
    /// decoding all operands.
    pub fn into_vec(self) -> Vec<EncodedFormula> {
        self.collect_vec()
    }
}

impl<'a> Iterator for NaryIterator<'a> {
    type Item = EncodedFormula;

    fn next(&mut self) -> Option<Self::Item> {
        if self.current_index == self.len {
            None
        } else {
            let res = match self.container {
                NaryCacheContainer::Encoding32(vec) => EncodedFormula::from(extend_32(vec[self.current_index])),
                NaryCacheContainer::Encoding64(vec) => EncodedFormula::from(vec[self.current_index]),
            };
            self.current_index += 1;
            Some(res)
        }
    }
}
