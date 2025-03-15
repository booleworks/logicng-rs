use std::{
    fmt::Debug,
    ops::{Index, IndexMut},
};

use crate::collections::grow_to;

use super::solver_datastructures::{LngVar, LngVariable};

/// A heap for the SAT solver's variable ordering.
pub struct LngHeap {
    heap: Vec<LngVar>,
    indices: Vec<usize>,
}

impl LngHeap {
    pub fn new() -> Self {
        Self { heap: Vec::with_capacity(1000), indices: Vec::with_capacity(1000) }
    }

    pub fn empty(&self) -> bool {
        self.heap.is_empty()
    }

    pub fn len(&self) -> usize {
        self.heap.len()
    }

    pub fn in_heap(&self, n: LngVar) -> bool {
        n.0 < self.indices.len() && self.indices[n.0] < (LngVar::UNDEF).0
    }

    pub fn decrease(&mut self, n: LngVar, solver_variables: &[LngVariable]) {
        debug_assert!(self.in_heap(n));
        self.percolate_up(self.indices[n.0], solver_variables);
    }

    pub fn insert(&mut self, n: LngVar, solver_variables: &[LngVariable]) {
        grow_to(&mut self.indices, n.0 + 1, LngVar::UNDEF.0);
        debug_assert!(!self.in_heap(n));
        self.indices[n.0] = self.heap.len();
        self.heap.push(n);
        self.percolate_up(self.indices[n.0], solver_variables);
    }

    pub fn remove_min(&mut self, solver_variables: &[LngVariable]) -> LngVar {
        let x = self.heap[0];
        self.heap[0] = self.heap[self.heap.len() - 1];
        self.indices[self.heap[0].0] = 0;
        self.indices[x.0] = LngVar::UNDEF.0;
        self.heap.pop();
        if self.heap.len() > 1 {
            self.percolate_down(0, solver_variables);
        }
        x
    }

    pub fn remove(&mut self, n: LngVar, solver_variables: &[LngVariable]) {
        debug_assert!(self.in_heap(n));
        let k_pos = self.indices[n.0];
        self.indices[n.0] = LngVar::UNDEF.0;
        if k_pos < self.heap.len() - 1 {
            self.heap[k_pos] = self.heap[self.heap.len() - 1];
            self.indices[self.heap[k_pos].0] = k_pos;
            self.heap.pop();
            self.percolate_down(k_pos, solver_variables);
        } else {
            self.heap.pop();
        };
    }

    pub fn build(&mut self, ns: &[LngVar], solver_variables: &[LngVariable]) {
        for i in 0..self.heap.len() {
            self.indices[self.heap[i].0] = LngVar::UNDEF.0;
        }
        self.heap.clear();
        for (i, n) in ns.iter().enumerate() {
            self.indices[n.0] = i;
            self.heap.push(*n);
        }
        for i in (0..(self.heap.len() / 2)).rev() {
            self.percolate_down(i, solver_variables);
        }
    }

    pub fn clear(&mut self) {
        for i in 0..self.heap.len() {
            self.indices[self.heap[i].0] = LngVar::UNDEF.0;
        }
        self.heap.clear();
    }

    fn percolate_up(&mut self, pos: usize, solver_variables: &[LngVariable]) {
        let x = self.heap[pos];
        let mut p = if pos == 0 { 0 } else { Self::parent(pos) }; // p == 0 => j == 0 => loop will finish and value is irrelevant
        let mut j = pos;
        while j != 0 && solver_variables[x.0].activity > solver_variables[self.heap[p].0].activity {
            let heap_p = self.heap[p];
            self.heap[j] = heap_p;
            self.indices[heap_p.0] = j;
            j = p;
            p = if p == 0 { 0 } else { Self::parent(p) };
        }
        self.heap[j] = x;
        self.indices[x.0] = j;
    }

    fn percolate_down(&mut self, pos: usize, solver_variables: &[LngVariable]) {
        let mut p = pos;
        let y = self.heap[p];
        while Self::left(p) < self.heap.len() {
            let p_right = Self::right(p);
            let p_left = Self::left(p);
            let child = if p_right < self.heap.len()
                && solver_variables[self.heap[p_right].0].activity > solver_variables[self.heap[p_left].0].activity
            {
                p_right
            } else {
                p_left
            };
            if solver_variables[self.heap[child].0].activity <= solver_variables[y.0].activity {
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

impl Index<usize> for LngHeap {
    type Output = LngVar;

    fn index(&self, index: usize) -> &Self::Output {
        &self.heap[index]
    }
}

impl IndexMut<usize> for LngHeap {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.heap[index]
    }
}

impl Debug for LngHeap {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "LngHeap{{")?;
        f.debug_list().entries(self.heap.iter().enumerate().map(|(i, hv)| (hv.0, self.indices[i]))).finish()?;
        write!(f, "}}")
    }
}

#[cfg(test)]
mod tests {
    use crate::solver::lng_core_solver::{LngCoreSolver, LngVar};

    use super::LngHeap;

    #[test]
    pub fn test() {
        let mut solver = LngCoreSolver::<()>::new();
        solver.new_var(true, true);
        solver.new_var(true, true);
        solver.new_var(true, true);
        let mut heap = LngHeap::new();
        assert!(heap.empty());
        heap.insert(LngVar(1), &solver.vars);
        heap.insert(LngVar(2), &solver.vars);
        heap.insert(LngVar(0), &solver.vars);
        assert_eq!(heap[0], LngVar(1));
        assert_eq!(&format!("{heap:?}"), "LngHeap{[(1, 2), (2, 0), (0, 1)]}");
        assert_eq!(heap.len(), 3);
        heap.clear();
        assert!(heap.empty());
    }
}
