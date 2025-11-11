use num_bigint::{BigUint, ToBigUint};

use super::bdd_prime::prime_gte;

#[derive(Debug)]
struct BddCacheEntry {
    a: Option<usize>,
    b: usize,
    c: usize,
    bdres: BigUint,
    res: usize,
}

impl BddCacheEntry {
    fn reset(&mut self) {
        self.a = None;
        self.b = 0;
        self.c = 0;
        self.res = 0;
    }
}

#[derive(Debug)]
pub struct BddCache {
    table: Vec<BddCacheEntry>,
}

impl BddCache {
    pub fn new(cs: usize) -> Self {
        let size = prime_gte(cs);
        let mut table = Vec::new();
        (0..size).for_each(|_x| table.push(BddCacheEntry { a: None, b: 0, c: 0, bdres: 0.to_biguint().unwrap(), res: 0 }));
        Self { table }
    }

    pub fn reset(&mut self) {
        for entry in &mut self.table {
            entry.reset();
        }
    }

    pub fn lookup_bdres(&self, hash: usize) -> BigUint {
        self.table[hash % self.table.len()].bdres.clone()
    }

    pub fn lookup_res(&self, hash: usize) -> usize {
        self.table[hash % self.table.len()].res
    }

    pub fn lookup(&self, hash: usize) -> (Option<usize>, usize, usize) {
        let entry = &self.table[hash % self.table.len()];
        (entry.a, entry.b, entry.c)
    }

    pub fn set_with_res(&mut self, hash: usize, tuple: (usize, usize, usize), res: usize) {
        let len = self.table.len();
        let entry = self.table.get_mut(hash % len).unwrap();
        entry.a = Some(tuple.0);
        entry.b = tuple.1;
        entry.c = tuple.2;
        entry.res = res;
    }

    pub fn set_with_bdres(&mut self, hash: usize, tuple: (usize, usize, usize), bdres: BigUint) {
        let len = self.table.len();
        let entry = self.table.get_mut(hash % len).unwrap();
        entry.a = Some(tuple.0);
        entry.b = tuple.1;
        entry.c = tuple.2;
        entry.bdres = bdres;
    }
}

#[cfg(test)]
mod tests {
    use num_bigint::{BigUint, ToBigUint};

    use super::BddCache;

    #[test]
    fn test_cache() {
        let mut cache = BddCache::new(10);
        let entry = cache.lookup(7);
        assert_eq!(entry, (None, 0, 0));
        assert_eq!(lookup_a(&cache, 7), None);
        assert_eq!(lookup_b(&cache, 7), 0);
        assert_eq!(lookup_c(&cache, 7), 0);
        assert_eq!(cache.lookup_bdres(7), 0.to_biguint().unwrap());
        assert_eq!(cache.lookup_res(7), 0);

        set_a(&mut cache, 5, 41);
        set_b(&mut cache, 5, 42);
        set_c(&mut cache, 5, 43);
        set_bdres(&mut cache, 5, 44.to_biguint().unwrap());
        set_res(&mut cache, 5, 45);

        assert_eq!(lookup_a(&cache, 5), Some(41));
        assert_eq!(lookup_b(&cache, 5), 42);
        assert_eq!(lookup_c(&cache, 5), 43);
        assert_eq!(cache.lookup_bdres(5), 44.to_biguint().unwrap());
        assert_eq!(cache.lookup_res(5), 45);

        set(&mut cache, 3, (1, 2, 3));
        assert_eq!(lookup_a(&cache, 3), Some(1));
        assert_eq!(lookup_b(&cache, 3), 2);
        assert_eq!(lookup_c(&cache, 3), 3);

        cache.reset();
        assert_eq!(lookup_a(&cache, 7), None);
        assert_eq!(lookup_b(&cache, 7), 0);
        assert_eq!(lookup_c(&cache, 7), 0);
        assert_eq!(cache.lookup_bdres(7), 0.to_biguint().unwrap());
        assert_eq!(cache.lookup_res(7), 0);
    }

    fn lookup_a(cache: &BddCache, hash: usize) -> Option<usize> {
        cache.table[hash % cache.table.len()].a
    }

    fn lookup_b(cache: &BddCache, hash: usize) -> usize {
        cache.table[hash % cache.table.len()].b
    }

    fn lookup_c(cache: &BddCache, hash: usize) -> usize {
        cache.table[hash % cache.table.len()].c
    }

    fn set_a(cache: &mut BddCache, hash: usize, a: usize) {
        let len = cache.table.len();
        cache.table.get_mut(hash % len).unwrap().a = Some(a);
    }

    fn set_b(cache: &mut BddCache, hash: usize, b: usize) {
        let len = cache.table.len();
        cache.table.get_mut(hash % len).unwrap().b = b;
    }

    fn set_c(cache: &mut BddCache, hash: usize, c: usize) {
        let len = cache.table.len();
        cache.table.get_mut(hash % len).unwrap().c = c;
    }

    fn set_bdres(cache: &mut BddCache, hash: usize, bdres: BigUint) {
        let len = cache.table.len();
        cache.table.get_mut(hash % len).unwrap().bdres = bdres;
    }

    fn set_res(cache: &mut BddCache, hash: usize, res: usize) {
        let len = cache.table.len();
        cache.table.get_mut(hash % len).unwrap().res = res;
    }

    fn set(cache: &mut BddCache, hash: usize, tuple: (usize, usize, usize)) {
        let len = cache.table.len();
        let entry = cache.table.get_mut(hash % len).unwrap();
        entry.a = Some(tuple.0);
        entry.b = tuple.1;
        entry.c = tuple.2;
    }
}
