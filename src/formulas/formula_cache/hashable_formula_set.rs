use std::collections::hash_map::DefaultHasher;
use std::collections::HashSet;
use std::fmt::Debug;
use std::hash::{Hash, Hasher};

use super::formula_encoding::Encoding;

pub struct HashableFormulaSet<E: Encoding> {
    base: HashSet<E>,
}

impl<E: Encoding> HashableFormulaSet<E> {
    pub const fn new(base: HashSet<E>) -> Self {
        Self { base }
    }
}

impl<E> Hash for HashableFormulaSet<E>
where E: Encoding + Clone + Copy + Debug + PartialEq + Eq + Hash
{
    fn hash<H: Hasher>(&self, state: &mut H) {
        for op in &self.base {
            let mut op_hasher = DefaultHasher::new();
            op.hash(&mut op_hasher);
            op_hasher.finish().hash(state);
        }
    }
}

impl<E> PartialEq for HashableFormulaSet<E>
where E: Encoding + Clone + Copy + Debug + PartialEq + Eq + Hash
{
    fn eq(&self, other: &Self) -> bool {
        self.base.eq(&other.base)
    }
}

impl<E> Eq for HashableFormulaSet<E> where E: Encoding + Clone + Copy + Debug + PartialEq + Eq + Hash {}

#[derive(Default)]
pub struct SimpleHashAdder {
    result: u64,
}

impl Hasher for SimpleHashAdder {
    fn finish(&self) -> u64 {
        self.result
    }

    fn write(&mut self, _bytes: &[u8]) {
        panic!("Should not be called.")
    }

    fn write_u64(&mut self, i: u64) {
        self.result = self.result.wrapping_add(i);
    }
}
