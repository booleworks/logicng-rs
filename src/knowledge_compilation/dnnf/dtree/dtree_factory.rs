#![allow(clippy::cast_possible_truncation, clippy::cast_sign_loss, clippy::cast_possible_wrap)]

use std::collections::HashSet;
use std::iter::repeat_n;
use std::ops::{BitAndAssign, BitOr};
use std::sync::Arc;

use bitvec::bitvec;
use bitvec::prelude::*;
use bitvec::vec::BitVec;

use crate::formulas::{Literal, Variable};
use crate::knowledge_compilation::dnnf::dnnf_sat_solver::DnnfSatSolver;
use crate::knowledge_compilation::dnnf::dtree::dtree_datastructure::DTree::{Leaf, Node};
use crate::knowledge_compilation::dnnf::dtree::dtree_datastructure::{DTree, DTreeEncoding, DTreeIndex};
use crate::solver::minisat::sat::Tristate::{True, Undef};
use crate::solver::minisat::sat::{MsLit, mk_lit, var};

pub struct DTreeFactory {
    pub(crate) _id: String,
    pub(crate) leafs: Vec<Vec<Literal>>,
    pub(crate) nodes: Vec<DTreeEncoding>,

    pub(crate) leafs_static_variable_set: Vec<HashSet<Variable>>,
    pub(crate) nodes_static_variable_set: Vec<HashSet<Variable>>,
    pub(crate) node_2_leaf_indices: Vec<Vec<DTreeIndex>>,

    pub(crate) leaf_literals: Vec<Vec<MsLit>>,
    max_var: MsLit,

    finished: bool,

    // content of all clauses, e.g. clause {1,3} with id 0, {2,6,8} with id 1, {4,6} with id 6 --> [1,3,-1,2,6,-2,4,6,-7]
    clause_contents: Vec<isize>,
    // for each encoded leaf or node: Indices into clause_contents, where its clause(s) start and end
    clause_content_ranges: Vec<(usize, usize)>,

    static_var_sets: Vec<Arc<BitVec>>,
}

impl DTreeFactory {
    pub const fn new() -> Self {
        Self {
            _id: String::new(),
            leafs: vec![],
            nodes: vec![],
            leafs_static_variable_set: vec![],
            nodes_static_variable_set: vec![],
            node_2_leaf_indices: vec![],
            leaf_literals: vec![],
            max_var: MsLit(0),
            finished: false,
            clause_contents: vec![],
            clause_content_ranges: vec![],
            static_var_sets: vec![],
        }
    }

    pub fn leaf(&mut self, literals: Vec<Literal>) -> DTree {
        assert!(!self.finished, "DTree is already finished.");
        self.leafs_static_variable_set.push(literals.iter().map(Literal::variable).collect::<HashSet<_>>());
        self.leafs.push(literals);
        Leaf(self.leafs.len() as DTreeIndex - 1)
    }

    pub fn node(&mut self, left: DTree, right: DTree) -> DTree {
        assert!(!self.finished, "DTree is already finished.");
        let left_encoding = Self::encode(left);
        let right_encoding = Self::encode(right);
        let mut var_set: HashSet<Variable> = left.static_variable_set(self).iter().copied().collect();
        var_set.extend(right.static_variable_set(self));
        self.nodes_static_variable_set.push(var_set);
        self.nodes.push((left_encoding, right_encoding));
        let mut leaf_indices = left.leaf_indices(self);
        leaf_indices.extend(right.leaf_indices(self));
        self.node_2_leaf_indices.push(leaf_indices);
        Node(self.nodes.len() as DTreeIndex - 1)
    }

    pub fn children(&self, node_index: DTreeIndex) -> (DTree, DTree) {
        let encoding = self.nodes[node_index as usize];
        (Self::decode(encoding.0), Self::decode(encoding.1))
    }

    pub fn tree_size(&self) -> usize {
        self.leafs.len() * 2 - 1
    }

    pub(crate) fn finish(&mut self, root: DTree, solver: &DnnfSatSolver) {
        self.leaf_literals = self.generate_leaf_literals(solver);
        self.max_var = *self.leaf_literals.iter().map(|leaf| leaf.iter().max().unwrap()).max().unwrap();
        let (clause_contents, clause_content_ranges) = self.generate_clause_contents(root);
        self.clause_contents = clause_contents;
        self.clause_content_ranges = clause_content_ranges;
        self.static_var_sets = repeat_n(Arc::new(bitvec![]), 2 * self.leafs.len()).collect();
        self.compute_static_var_sets(root);
        self.finished = true;
    }

    pub(crate) fn dynamic_separator(&mut self, tree: DTree, solver: &DnnfSatSolver) -> BitVec {
        match tree {
            Leaf(_) => bitvec!(),
            Node(n) => {
                let (left, right) = self.nodes[n as usize];
                let mut local_left_var_set = bitvec!(0; self.max_var.0);
                let mut local_right_var_set = bitvec!(0; self.max_var.0);
                self.var_set(left, solver, &mut local_left_var_set);
                self.var_set(right, solver, &mut local_right_var_set);
                local_left_var_set.bitand_assign(local_right_var_set);
                local_left_var_set
            }
        }
    }

    pub(crate) fn static_var_set(&self, tree: DTree) -> Arc<BitVec> {
        self.static_var_sets[Self::encode(tree) as usize].clone()
    }

    pub(crate) fn cache_key(&self, tree: DTree, solver: &DnnfSatSolver, key: &mut BitVec, number_of_variables: usize) {
        let (from, to) = self.clause_content_ranges[Self::encode(tree) as usize];
        let mut i = from;
        while i < to {
            let mut j = i;
            let mut subsumed = false;
            while self.clause_contents[j] >= 0 {
                if !subsumed && solver.value_of(MsLit(self.clause_contents[j] as usize)) == True {
                    subsumed = true;
                }
                j += 1;
            }
            if !subsumed {
                let clause_id = -self.clause_contents[j] - 1;
                key.set(clause_id as usize + 1 + number_of_variables, true);
                for k in i..j {
                    if solver.value_of(MsLit(self.clause_contents[k] as usize)) == Undef {
                        key.set(var(MsLit(self.clause_contents[k] as usize)).0, true);
                    }
                }
            }
            i = j + 1;
        }
    }

    pub(crate) fn count_unsubsumed_occurrences(&self, node: DTree, occurrences: &mut [isize], solver: &DnnfSatSolver) {
        for leaf_index in node.leaf_indices(self) {
            let literals = &self.leaf_literals[leaf_index as usize];
            let is_subsumed = literals.iter().any(|lit| solver.value_of(*lit) == True);
            if !is_subsumed {
                for lit in literals {
                    let var = var(*lit);
                    let occ = occurrences[var.0];
                    if occ >= 0 {
                        occurrences[var.0] = occ + 1;
                    }
                }
            }
        }
    }

    fn generate_leaf_literals(&self, solver: &DnnfSatSolver) -> Vec<Vec<MsLit>> {
        self.leafs.iter().map(|leaf| leaf.iter().map(|&lit| mk_lit(solver.variable_index(lit), !lit.phase())).collect()).collect()
    }

    fn generate_clause_contents(&mut self, root: DTree) -> (Vec<isize>, Vec<(usize, usize)>) {
        let mut clause_contents: Vec<isize> = vec![];
        let mut clause_content_ranges = repeat_n((0, 0), 2 * self.leafs.len()).collect();
        self.generate_clause_contents_rec(root, &mut clause_contents, &mut clause_content_ranges);
        (clause_contents, clause_content_ranges)
    }

    fn generate_clause_contents_rec(&self, tree: DTree, clause_contents: &mut Vec<isize>, clause_content_ranges: &mut Vec<(usize, usize)>) {
        let range_start = clause_contents.len();
        match tree {
            Leaf(n) => {
                clause_contents.extend(self.leaf_literals[n as usize].iter().map(|&i| i.0 as isize));
                clause_contents.push(-(n as isize) - 1);
            }
            Node(n) => {
                let (left, right) = self.children(n);
                self.generate_clause_contents_rec(left, clause_contents, clause_content_ranges);
                self.generate_clause_contents_rec(right, clause_contents, clause_content_ranges);
            }
        }
        clause_content_ranges[Self::encode(tree) as usize] = (range_start, clause_contents.len());
    }

    fn compute_static_var_sets(&mut self, tree: DTree) {
        let var_set = match tree {
            Leaf(n) => {
                let mut bit_vec = bitvec![0; self.max_var.0];
                self.leaf_literals[n as usize].iter().for_each(|n| bit_vec.set(var(*n).0, true));
                bit_vec
            }
            Node(n) => {
                let (left, right) = self.children(n);
                self.compute_static_var_sets(left);
                self.compute_static_var_sets(right);
                let left_var_set = &self.static_var_sets[Self::encode(left) as usize];
                let right_var_set = &self.static_var_sets[Self::encode(right) as usize];
                (left_var_set.as_ref().clone().bitor(right_var_set.as_ref().clone())).to_bitvec()
            }
        };
        self.static_var_sets[Self::encode(tree) as usize] = Arc::new(var_set);
    }

    fn var_set(&mut self, encoding: DTreeIndex, solver: &DnnfSatSolver, local_var_set: &mut BitVec) {
        let (from, to) = self.clause_content_ranges[encoding as usize];
        let mut i = from;
        while i < to {
            let mut j = i;
            let mut subsumed = false;
            while self.clause_contents[j] >= 0 {
                if !subsumed && solver.value_of(MsLit(self.clause_contents[j] as usize)) == True {
                    subsumed = true;
                }
                j += 1;
            }
            if !subsumed {
                for k in i..j {
                    let lit = MsLit(self.clause_contents[k] as usize);
                    if solver.value_of(lit) == Undef {
                        local_var_set.set(var(lit).0, true);
                    }
                }
            }
            i = j + 1;
        }
    }

    const fn encode(tree: DTree) -> DTreeIndex {
        match tree {
            Leaf(index) => (index << 1) + 1,
            Node(index) => index << 1,
        }
    }

    const fn decode(encoded: u32) -> DTree {
        if encoded & 1 > 0 { Leaf((encoded - 1) >> 1) } else { Node(encoded >> 1) }
    }
}

impl Default for DTreeFactory {
    fn default() -> Self {
        Self::new()
    }
}
