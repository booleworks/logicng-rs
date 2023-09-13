use crate::collections::grow_to;
use crate::solver::minisat::sat::MsVar;

/// A heap for the SAT solver's variable ordering.
#[derive(Debug)]
pub struct LngHeap {
    pub heap: Vec<MsVar>,
    pub indices: Vec<usize>,
}

impl LngHeap {
    pub fn new() -> Self {
        Self { heap: Vec::with_capacity(1000), indices: Vec::with_capacity(1000) }
    }

    pub fn empty(&self) -> bool {
        self.heap.is_empty()
    }

    pub fn in_heap(&self, n: MsVar) -> bool {
        n.0 < self.indices.len() && self.indices[n.0] < (MsVar::MAX).0
    }

    pub fn decrease(&mut self, n: MsVar, activities: &[f64]) {
        debug_assert!(self.in_heap(n));
        self.percolate_up(self.indices[n.0], activities);
    }

    pub fn insert(&mut self, n: MsVar, activities: &[f64]) {
        grow_to(&mut self.indices, n.0 + 1, MsVar::MAX.0);
        debug_assert!(!self.in_heap(n));
        self.indices[n.0] = self.heap.len();
        self.heap.push(n);
        self.percolate_up(self.indices[n.0], activities);
    }

    pub fn remove_min(&mut self, activities: &[f64]) -> MsVar {
        let x = self.heap[0];
        self.heap[0] = self.heap[self.heap.len() - 1];
        self.indices[self.heap[0].0] = 0;
        self.indices[x.0] = MsVar::MAX.0;
        self.heap.pop();
        if self.heap.len() > 1 {
            self.percolate_down(0, activities);
        }
        x
    }

    pub fn remove(&mut self, n: MsVar, activities: &[f64]) {
        debug_assert!(self.in_heap(n));
        let k_pos = self.indices[n.0];
        self.indices[n.0] = MsVar::MAX.0;
        if k_pos < self.heap.len() - 1 {
            self.heap[k_pos] = self.heap[self.heap.len() - 1];
            self.indices[self.heap[k_pos].0] = k_pos;
            self.heap.pop();
            self.percolate_down(k_pos, activities);
        } else {
            self.heap.pop();
        };
    }

    pub fn build(&mut self, ns: &[MsVar], activities: &[f64]) {
        for i in 0..self.heap.len() {
            self.indices[self.heap[i].0] = MsVar::MAX.0;
        }
        self.heap.clear();
        for (i, n) in ns.iter().enumerate() {
            self.indices[n.0] = i;
            self.heap.push(*n);
        }
        for i in (0..(self.heap.len() / 2)).rev() {
            self.percolate_down(i, activities);
        }
    }

    fn percolate_up(&mut self, pos: usize, activities: &[f64]) {
        let x = self.heap[pos];
        let mut p = if pos == 0 { 0 } else { Self::parent(pos) }; // p == 0 => j == 0 => loop will finish and value is irrelevant
        let mut j = pos;
        while j != 0 && activities[x.0] > activities[self.heap[p].0] {
            let heap_p = self.heap[p];
            self.heap[j] = heap_p;
            self.indices[heap_p.0] = j;
            j = p;
            p = if p == 0 { 0 } else { Self::parent(p) };
        }
        self.heap[j] = x;
        self.indices[x.0] = j;
    }

    fn percolate_down(&mut self, pos: usize, activities: &[f64]) {
        let mut p = pos;
        let y = self.heap[p];
        while Self::left(p) < self.heap.len() {
            let p_right = Self::right(p);
            let p_left = Self::left(p);
            let child = if p_right < self.heap.len() && activities[self.heap[p_right].0] > activities[self.heap[p_left].0] {
                p_right
            } else {
                p_left
            };
            if activities[self.heap[child].0] <= activities[y.0] {
                break;
            }
            self.heap[p] = self.heap[child];
            self.indices[self.heap[p].0] = p;
            p = child;
        }
        self.heap[p] = y;
        self.indices[y.0] = p;
    }

    const fn left(pos: usize) -> usize {
        pos * 2 + 1
    }

    const fn right(pos: usize) -> usize {
        (pos + 1) * 2
    }

    const fn parent(pos: usize) -> usize {
        (pos - 1) >> 1
    }
}
