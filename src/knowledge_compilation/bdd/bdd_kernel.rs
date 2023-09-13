use std::collections::BTreeMap;
use std::num::Wrapping;

use crate::formulas::Variable;

use super::bdd_cache::BddCache;
use super::bdd_handler::{BddError, BddHandler};
use super::bdd_prime::{prime_gte, prime_lte};

pub(super) const BDD_TRUE: usize = 1;
pub(super) const BDD_FALSE: usize = 0;

pub(super) const MAXVAR: usize = 0x1F_FFFF;
pub(super) const MAXREF: usize = 0x3FF;
pub(super) const MARKON: usize = 0x20_0000;
pub(super) const MARKOFF: usize = 0x1F_FFFF;

pub(super) const OPCODE_AND: usize = 0;
pub(super) const OPCODE_OR: usize = 2;
pub(super) const OPCODE_IMP: usize = 5;
pub(super) const OPCODE_EQUIV: usize = 6;
pub(super) const OPCODE_NOT: usize = 10;

#[derive(Debug)]
struct Node {
    refcou: usize,
    level: usize,
    low: Option<usize>,
    high: usize,
    hash: usize,
    next: usize,
}

/// A operation, which can be applied on a BDD.
#[derive(Debug)]
pub(super) struct Operand {
    op_code: usize,
    truth_table: [usize; 4],
}

/// Statistics for a BDD kernel.
#[derive(Debug)]
pub struct BddStatistics {
    /// Number of new nodes ever produced.
    pub produced: usize,
    /// Number of allocated nodes.
    pub nodesize: usize,
    /// Number of free nodes.
    pub freenum: usize,
    /// Number of defined BDD variables.
    pub varnum: usize,
    /// Size of the operator caches.
    pub cachesize: usize,
    /// Number of garbage collections.
    pub gbcollectnum: usize,
}

impl Operand {
    pub const fn and() -> Self {
        Self { op_code: OPCODE_AND, truth_table: [0, 0, 0, 1] }
    }

    pub const fn or() -> Self {
        Self { op_code: OPCODE_OR, truth_table: [0, 1, 1, 1] }
    }

    pub const fn imp() -> Self {
        Self { op_code: OPCODE_IMP, truth_table: [1, 1, 0, 1] }
    }

    pub const fn equiv() -> Self {
        Self { op_code: OPCODE_EQUIV, truth_table: [1, 0, 0, 1] }
    }
}

/// The BUDDY kernel.
#[rustfmt::skip]
pub struct BddKernel {
    pub(crate) var2idx: BTreeMap<Variable, usize>,
    pub(crate) idx2var: BTreeMap<usize, Variable>,
    // BDDReordering reordering;
    nodes: Vec<Node>,                 // All the BDD nodes
    pub(crate) vars: Vec<usize>,      // Set of defined BDD variables
    minfreenodes: usize,              // Minimal % of nodes that has to be left after a garbage collection
    gbcollectnum: usize,              // Number of garbage collections
    cachesize: usize,                 // Size of the operator caches
    pub(crate) nodesize: usize,       // Number of allocated nodes
    maxnodeincrease: usize,           // Max. # of nodes used to inc. table
    freepos: usize,                   // First free node
    freenum: usize,                   // Number of free nodes
    produced: usize,                  // Number of new nodes ever produced
    pub(crate) varnum: usize,         // Number of defined BDD variables
    refstack: Vec<usize>,             // Internal node reference stack
    refstacktop: usize,               // Internal node reference stack top
    pub(crate) level2var: Vec<usize>, // Level -> variable table
    var2level: Vec<usize>,            // Variable -> level table
    pub(crate) quantvarset: Vec<i32>, // Current variable set for quant.
    pub(crate) quantvarset_id: u32,   // Current id used in quantvarset
    pub(crate) quantlast: usize,      // Current last variable to be quant.
    pub(crate) applycache: BddCache,  // Cache for apply results
    itecache: BddCache,               // Cache for ITE results
    pub(crate) quantcache: BddCache,  // Cache for exist/forall results
    appexcache: BddCache,             // Cache for appex/appall results
    replacecache: BddCache,           // Cache for replace results
    pub(crate) misccache: BddCache,   // Cache for other results
}

impl BddKernel {
    /// Constructs a new BDD kernel with a given number of variables
    pub fn new_with_num_vars(num_vars: usize, node_size: usize, cache_size: usize) -> Self {
        assert!(num_vars <= MAXVAR, "Invalid variable number {num_vars}");
        let computed_node_size = prime_gte(usize::max(node_size, 3));
        let computed_cache_size = usize::max(cache_size, 3);
        let mut kernel = Self {
            var2idx: BTreeMap::new(),
            idx2var: BTreeMap::new(),
            nodesize: computed_node_size,
            nodes: Vec::with_capacity(computed_node_size),
            minfreenodes: 20,
            freepos: 2,
            freenum: computed_node_size - 2,
            varnum: 0,
            gbcollectnum: 0,
            cachesize: cache_size,
            maxnodeincrease: 50000,
            applycache: BddCache::new(computed_cache_size),
            itecache: BddCache::new(computed_cache_size),
            quantcache: BddCache::new(computed_cache_size),
            appexcache: BddCache::new(computed_cache_size),
            replacecache: BddCache::new(computed_cache_size),
            misccache: BddCache::new(computed_cache_size),
            quantvarset_id: 0,
            quantvarset: vec![0; num_vars],
            quantlast: 0,
            produced: 0,
            vars: vec![0; num_vars * 2],
            level2var: vec![0; num_vars + 1],
            var2level: vec![0; num_vars + 1],
            refstack: vec![0; num_vars * 2 + 4],
            refstacktop: 0,
        };

        for n in 0..computed_node_size {
            kernel.nodes.push(Node { refcou: 0, level: 0, low: None, high: 0, hash: 0, next: n + 1 });
        }

        kernel.set_next(kernel.nodesize - 1, 0);
        kernel.set_refcou(0, MAXREF);
        kernel.set_refcou(1, MAXREF);
        kernel.set_low(0, Some(0));
        kernel.set_high(0, 0);
        kernel.set_low(1, Some(1));
        kernel.set_high(1, 1);

        while kernel.varnum < num_vars {
            let push_node = kernel.make_node(kernel.varnum, 0, 1);
            kernel.vars[kernel.varnum * 2] = kernel.push_ref(push_node);
            kernel.vars[kernel.varnum * 2 + 1] = kernel.make_node(kernel.varnum, 1, 0);
            kernel.pop_ref(1);
            kernel.set_refcou(kernel.vars[kernel.varnum * 2], MAXREF);
            kernel.set_refcou(kernel.vars[kernel.varnum * 2 + 1], MAXREF);
            kernel.level2var[kernel.varnum] = kernel.varnum;
            kernel.var2level[kernel.varnum] = kernel.varnum;
            kernel.varnum += 1;
        }
        kernel.set_level(0, num_vars);
        kernel.set_level(1, num_vars);
        kernel.level2var[num_vars] = num_vars;
        kernel.var2level[num_vars] = num_vars;
        kernel
    }

    /// Constructs a new BDD kernel with the given variable ordering
    pub fn new_with_var_ordering(ordering: Vec<Variable>, node_size: usize, cache_size: usize) -> Self {
        let mut kernel = Self::new_with_num_vars(ordering.len(), node_size, cache_size);
        for var in ordering {
            kernel.get_or_add_var_index(var);
        }
        kernel
    }

    pub(super) fn get_or_add_var_index(&mut self, variable: Variable) -> usize {
        if self.var2idx.contains_key(&variable) {
            return self.var2idx[&variable];
        }
        assert!(self.var2idx.len() < self.varnum, "No free variables left! You did not set the number of variables high enough.");
        let index = self.var2idx.len();
        self.var2idx.insert(variable, index);
        self.idx2var.insert(index, variable);
        index
    }

    pub(super) fn get_variable_for_index(&self, idx: usize) -> Option<Variable> {
        self.idx2var.get(&idx).map(ToOwned::to_owned)
    }

    pub(super) fn apply(&mut self, l: usize, r: usize, op: &Operand) -> usize {
        self.init_ref();
        self.apply_rec(l, r, op)
    }

    pub(super) fn add_ref(&mut self, root: usize, handler: &mut dyn BddHandler) -> Result<usize, BddError> {
        if let Some(error) = handler.new_ref_added() {
            return Err(error);
        }
        if root < 2 {
            return Ok(root);
        }
        assert!(root < self.nodesize, "Not a valid BDD root node: {root}");
        assert!(self.low(root).is_some(), "Not a valid BDD root node: {root}");
        self.inc_ref(root);
        Ok(root)
    }

    pub(super) fn del_ref(&mut self, root: usize) {
        if root < 2 {
            return;
        }
        assert!(root < self.nodesize, "Cannot dereference a variable > varnum");
        assert!(self.low(root).is_some(), "Cannot dereference variable -1");
        assert!(self.has_ref(root), "Cannot dereference a variable which has no reference");
        self.dec_ref(root);
    }

    pub(super) fn unmark(&mut self, i: usize) {
        if i < 2 {
            return;
        }
        if !self.marked(i) || self.low(i).is_none() {
            return;
        }
        self.unmark_node(i);
        self.unmark(self.low(i).unwrap());
        self.unmark(self.high(i));
    }

    pub(super) fn mark(&mut self, i: usize) {
        if i < 2 {
            return;
        }
        if (self.level(i) & MARKON) != 0 || self.low(i).is_none() {
            return;
        }
        self.set_level(i, self.level(i) | MARKON);
        self.mark(self.low(i).unwrap());
        self.mark(self.high(i));
    }

    pub(super) fn mark_count(&mut self, i: usize) -> usize {
        if i < 2 {
            return 0;
        }
        if self.marked(i) || self.low(i).is_none() {
            return 0;
        }
        self.set_mark(i);
        1 + self.mark_count(self.low(i).unwrap()) + self.mark_count(self.high(i))
    }

    /// Returns statistics of this kernel.
    pub const fn statistics(&self) -> BddStatistics {
        BddStatistics {
            produced: self.produced,
            nodesize: self.nodesize,
            freenum: self.freenum,
            varnum: self.varnum,
            cachesize: self.cachesize,
            gbcollectnum: self.gbcollectnum,
        }
    }

    pub(super) fn apply_rec(&mut self, l: usize, r: usize, op: &Operand) -> usize {
        match op.op_code {
            OPCODE_AND => {
                if l == r {
                    return l;
                }
                if is_zero(l) || is_zero(r) {
                    return 0;
                }
                if is_one(l) {
                    return r;
                }
                if is_one(r) {
                    return l;
                }
            }
            OPCODE_OR => {
                if l == r {
                    return l;
                }
                if is_one(l) || is_one(r) {
                    return 1;
                }
                if is_zero(l) {
                    return r;
                }
                if is_zero(r) {
                    return l;
                }
            }
            OPCODE_IMP => {
                if is_zero(l) {
                    return 1;
                }
                if is_one(l) {
                    return r;
                }
                if is_one(r) {
                    return 1;
                }
            }
            _ => {}
        }
        if is_const(l) && is_const(r) {
            return op.truth_table[l << 1 | r];
        }
        let search_hash = triple(l, r, op.op_code);
        let cache_abc = self.applycache.lookup(search_hash);
        if cache_abc.0 == Some(l) && cache_abc.1 == r && cache_abc.2 == op.op_code {
            return self.applycache.lookup_res(search_hash);
        }
        let l_level = self.level(l);
        let res = match l_level {
            _ if l_level == self.level(r) => {
                let ref1 = self.apply_rec(self.low(l).unwrap(), self.low(r).unwrap(), op);
                self.push_ref(ref1);
                let ref2 = self.apply_rec(self.high(l), self.high(r), op);
                self.push_ref(ref2);
                self.make_node(self.level(l), self.read_ref(2), self.read_ref(1))
            }
            _ if l_level < self.level(r) => {
                let ref1 = self.apply_rec(self.low(l).unwrap(), r, op);
                self.push_ref(ref1);
                let ref2 = self.apply_rec(self.high(l), r, op);
                self.push_ref(ref2);
                self.make_node(self.level(l), self.read_ref(2), self.read_ref(1))
            }
            _ => {
                let ref1 = self.apply_rec(l, self.low(r).unwrap(), op);
                self.push_ref(ref1);
                let ref2 = self.apply_rec(l, self.high(r), op);
                self.push_ref(ref2);
                self.make_node(self.level(r), self.read_ref(2), self.read_ref(1))
            }
        };
        self.pop_ref(2);
        self.applycache.set_with_res(search_hash, (l, r, op.op_code), res);
        res
    }

    fn refcou(&self, node: usize) -> usize {
        self.nodes[node].refcou
    }

    pub(super) fn level(&self, node: usize) -> usize {
        self.nodes[node].level
    }

    pub(super) fn low(&self, node: usize) -> Option<usize> {
        self.nodes[node].low
    }

    pub(super) fn high(&self, node: usize) -> usize {
        self.nodes[node].high
    }

    fn hash(&self, node: usize) -> usize {
        self.nodes[node].hash
    }

    fn next(&self, node: usize) -> usize {
        self.nodes[node].next
    }

    fn set_refcou(&mut self, node: usize, refcou: usize) {
        self.nodes[node].refcou = refcou;
    }

    pub(super) fn set_level(&mut self, node: usize, level: usize) {
        self.nodes[node].level = level;
    }

    fn set_low(&mut self, node: usize, low: Option<usize>) {
        self.nodes[node].low = low;
    }

    fn set_high(&mut self, node: usize, high: usize) {
        self.nodes[node].high = high;
    }

    fn set_hash(&mut self, node: usize, hash: usize) {
        self.nodes[node].hash = hash;
    }

    fn set_next(&mut self, node: usize, next: usize) {
        self.nodes[node].next = next;
    }

    pub(super) fn push_ref(&mut self, n: usize) -> usize {
        self.refstack[self.refstacktop] = n;
        self.refstacktop += 1;
        n
    }

    pub(super) fn pop_ref(&mut self, n: usize) {
        self.refstacktop -= n;
    }

    pub(super) fn read_ref(&self, n: usize) -> usize {
        self.refstack[self.refstacktop - n]
    }

    fn dec_ref(&mut self, n: usize) {
        if self.refcou(n) != MAXREF && self.refcou(n) > 0 {
            self.set_refcou(n, self.refcou(n) - 1);
        }
    }
    fn inc_ref(&mut self, n: usize) {
        if self.refcou(n) < MAXREF {
            self.set_refcou(n, self.refcou(n) + 1);
        }
    }

    fn has_ref(&self, n: usize) -> bool {
        self.refcou(n) > 0
    }

    pub(super) fn make_node(&mut self, level: usize, low: usize, high: usize) -> usize {
        if low == high {
            return low;
        }
        let mut hash = self.nodehash(level, low, high);
        let mut res = self.hash(hash);
        while res != 0 {
            if self.level(res) == level && self.low(res) == Some(low) && self.high(res) == high {
                return res;
            }
            res = self.next(res);
        }
        if self.freepos == 0 {
            self.gbc();
            if (self.freenum * 100) / self.nodesize <= self.minfreenodes {
                self.node_resize(true);
                hash = self.nodehash(level, low, high);
            }
            assert_ne!(self.freepos, 0, "Cannot allocate more space for more nodes.");
        }
        res = self.freepos;
        self.freepos = self.next(self.freepos);
        self.freenum -= 1;
        self.produced += 1;
        self.set_level(res, level);
        self.set_low(res, Some(low));
        self.set_high(res, high);
        self.set_next(res, self.hash(hash));
        self.set_hash(hash, res);
        res
    }

    fn nodehash(&self, lvl: usize, l: usize, h: usize) -> usize {
        triple(lvl, l, h) % self.nodesize
    }

    fn gbc(&mut self) {
        for r in 0..self.refstacktop {
            self.mark(self.refstack[r]);
        }
        for n in 0..self.nodesize {
            if self.refcou(n) > 0 {
                self.mark(n);
            }
            self.set_hash(n, 0);
        }
        self.freepos = 0;
        self.freenum = 0;

        for n in (2..self.nodesize).rev() {
            if (self.level(n) & MARKON) != 0 && self.low(n).is_some() {
                self.set_level(n, self.level(n) & MARKOFF);
                let hash = self.nodehash(self.level(n), self.low(n).unwrap(), self.high(n));
                self.set_next(n, self.hash(hash));
                self.set_hash(hash, n);
            } else {
                self.set_low(n, None);
                self.set_next(n, self.freepos);
                self.freepos = n;
                self.freenum += 1;
            }
        }
        self.reset_caches();
        self.gbcollectnum += 1;
    }

    fn reset_caches(&mut self) {
        self.applycache.reset();
        self.itecache.reset();
        self.quantcache.reset();
        self.appexcache.reset();
        self.replacecache.reset();
        self.misccache.reset();
    }

    fn marked(&self, n: usize) -> bool {
        (self.level(n) & MARKON) != 0
    }

    fn set_mark(&mut self, n: usize) {
        self.set_level(n, self.level(n) | MARKON);
    }

    fn unmark_node(&mut self, n: usize) {
        self.set_level(n, self.level(n) & MARKOFF);
    }

    fn node_resize(&mut self, do_rehash: bool) {
        let oldsize = self.nodesize;
        self.nodesize <<= 1;
        if self.nodesize > oldsize + self.maxnodeincrease {
            self.nodesize = oldsize + self.maxnodeincrease;
        }
        self.nodesize = prime_lte(self.nodesize);
        if do_rehash {
            for n in 0..oldsize {
                self.set_hash(n, 0);
            }
        }
        for n in oldsize..self.nodesize {
            self.nodes.push(Node { refcou: 0, level: 0, low: None, high: 0, hash: 0, next: n + 1 });
        }
        self.set_next(self.nodesize - 1, self.freepos);
        self.freepos = oldsize;
        self.freenum += self.nodesize - oldsize;
        if do_rehash {
            self.gbc_rehash();
        }
    }

    fn gbc_rehash(&mut self) {
        self.freepos = 0;
        self.freenum = 0;
        for n in (2..self.nodesize).rev() {
            if self.low(n).is_none() {
                self.set_next(n, self.freepos);
                self.freepos = n;
                self.freenum += 1;
            } else {
                let hash = self.nodehash(self.level(n), self.low(n).unwrap(), self.high(n));
                self.set_next(n, self.hash(hash));
                self.set_hash(hash, n);
            }
        }
    }

    pub(super) fn init_ref(&mut self) {
        self.refstacktop = 0;
    }

    #[allow(clippy::cast_abs_to_unsigned)]
    pub(super) fn insvarset(&self, a: usize) -> bool {
        self.quantvarset[a].abs() as u32 == self.quantvarset_id
    }

    #[allow(clippy::cast_possible_wrap)]
    pub(super) fn invarset(&self, a: usize) -> bool {
        self.quantvarset[a] == self.quantvarset_id as i32
    }
}

pub(super) const fn is_const(n: usize) -> bool {
    n < 2
}

pub(super) const fn is_one(n: usize) -> bool {
    n == 1
}

pub(super) const fn is_zero(n: usize) -> bool {
    n == 0
}

pub(super) fn pair(a: usize, b: usize) -> usize {
    ((Wrapping(a) + Wrapping(b)) * (Wrapping(a) + Wrapping(b) + Wrapping(1)) / Wrapping(2) + Wrapping(a)).0
}

pub(super) fn triple(a: usize, b: usize, c: usize) -> usize {
    pair(c, pair(a, b))
}

#[cfg(test)]
mod tests {
    use super::BddKernel;

    #[test]
    fn create_kernel() {
        let kernel = BddKernel::new_with_num_vars(5, 50, 500);
        let statistics = kernel.statistics();
        assert_eq!(statistics.produced, 10);
        assert_eq!(statistics.nodesize, 53);
        assert_eq!(statistics.freenum, 41);
        assert_eq!(statistics.varnum, 5);
        assert_eq!(statistics.cachesize, 500);
        assert_eq!(statistics.gbcollectnum, 0);
    }
}
