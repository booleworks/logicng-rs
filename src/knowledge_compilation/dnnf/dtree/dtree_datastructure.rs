use std::collections::HashSet;

use crate::formulas::Variable;
use crate::knowledge_compilation::dnnf::dtree::dtree_factory::DTreeFactory;

pub type DTreeIndex = u32;
pub type DTreeEncoding = (u32, u32);

#[derive(Eq, Hash, PartialEq, Copy, Clone, Debug)]
pub enum DTree {
    Leaf(DTreeIndex),
    Node(DTreeIndex),
}

impl<'a> DTree {
    pub fn static_variable_set(self, df: &'a DTreeFactory) -> &'a HashSet<Variable> {
        match self {
            Self::Leaf(n) => &df.leafs_static_variable_set[n as usize],
            Self::Node(n) => &df.nodes_static_variable_set[n as usize],
        }
    }

    pub fn leaf_indices(self, df: &'a DTreeFactory) -> Vec<DTreeIndex> {
        match self {
            Self::Leaf(n) => vec![n],
            Self::Node(n) => df.node_2_leaf_indices[n as usize].clone(),
        }
    }

    #[cfg(test)]
    pub fn to_string(self, df: &DTreeFactory, f: &crate::formulas::FormulaFactory) -> String {
        match self {
            Self::Leaf(n) => {
                let leafs: Vec<String> = df.leafs[n as usize].iter().map(|&lit| lit.to_string(f)).collect();
                format!("Leaf{{{}}}", leafs.join(", "))
            }
            Self::Node(n) => {
                let (left, right) = df.children(n);
                format!("Node[{}, {}]", left.to_string(df, f), right.to_string(df, f))
            }
        }
    }
}
