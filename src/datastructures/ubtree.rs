use std::collections::{BTreeMap, BTreeSet, HashSet};

type NodeIndex = usize;
type ChildrenIndex = usize;

struct UbNode<T: Ord> {
    children: ChildrenIndex,
    set: Option<BTreeSet<T>>,
}

impl<T: Ord> UbNode<T> {
    const fn new(children: ChildrenIndex) -> Self {
        Self { children, set: None }
    }

    const fn end_of_path(&self) -> Option<&BTreeSet<T>> {
        self.set.as_ref()
    }

    #[cfg(test)]
    const fn is_end_of_path(&self) -> bool {
        self.set.is_some()
    }
}

/// A data structure for storing sets with efficient sub- and superset queries.
///
/// C.f. `A New Method to Index and Query Sets`, Hoffmann and Koehler, 1999.
/// Note that, we've only implemented the parts of an `UbTree` that we actually
/// use.
pub struct UbTree<T: Ord> {
    root_nodes: ChildrenIndex,
    nodes: Vec<UbNode<T>>,
    children_maps: Vec<BTreeMap<T, NodeIndex>>,
}

impl<T: Ord + Copy> UbTree<T> {
    /// Construct an empty `UbTree`.
    pub fn new() -> Self {
        Self { root_nodes: 0, nodes: Vec::new(), children_maps: vec![BTreeMap::new()] }
    }

    /// Adds a set of comparable objects to this `UbTree`.
    pub fn add_set(&mut self, set: BTreeSet<T>) {
        let mut nodes = self.root_nodes;
        let mut node = None;
        for element in &set {
            let n = if self.children_maps[nodes].contains_key(element) {
                *self.children_maps[nodes].get(element).unwrap()
            } else {
                let new_node = self.new_node();
                self.children_maps[nodes].insert(*element, new_node);
                new_node
            };
            nodes = self.nodes[n].children;
            node = Some(n);
        }
        if let Some(n) = node {
            self.nodes[n].set = Some(set);
        }
    }

    /// Returns the first subset of a given set in this `UbTree`.
    pub fn first_subset(&self, set: &BTreeSet<T>) -> Option<&BTreeSet<T>> {
        if self.get_children(self.root_nodes).is_empty() || set.is_empty() {
            None
        } else {
            self.first_subset_from_forest(set, self.root_nodes)
        }
    }

    /// Returns all sets in this `UbTree`.
    pub fn all_sets(&self) -> BTreeSet<&BTreeSet<T>> {
        let mut all_sets = BTreeSet::new();
        let mut stack = Vec::new();
        stack.push(self.root_nodes);
        while let Some(current) = stack.pop() {
            for node_index in self.get_children(current).values() {
                let node = self.get_node(*node_index);
                if let Some(set) = node.end_of_path() {
                    all_sets.insert(set);
                }
                stack.push(node.children);
            }
        }
        all_sets
    }

    #[cfg(test)]
    pub fn root_nodes(&self) -> &BTreeMap<T, NodeIndex> {
        self.get_children(self.root_nodes)
    }

    fn first_subset_from_forest(&self, set: &BTreeSet<T>, forest: ChildrenIndex) -> Option<&BTreeSet<T>> {
        let nodes = self.get_all_nodes_containing_elements(set, forest);
        let mut found_subset = None;
        for node in nodes {
            if found_subset.is_some() {
                return found_subset;
            }
            if let Some(set) = self.get_node(node).end_of_path() {
                return Some(set);
            }
            let mut remaining_set = set.clone();
            if let Some(f) = set.first() {
                remaining_set.remove(f);
            }
            found_subset = self.first_subset_from_forest(&remaining_set, self.nodes[node].children);
        }
        found_subset
    }

    fn get_all_nodes_containing_elements(&self, set: &BTreeSet<T>, forest: ChildrenIndex) -> HashSet<NodeIndex> {
        let mut nodes = HashSet::new();
        for element in set {
            let node_index = self.get_children(forest).get(element);
            if let Some(n) = node_index {
                nodes.insert(*n);
            }
        }
        nodes
    }

    fn new_node(&mut self) -> NodeIndex {
        let node_index = self.nodes.len();
        let children_index = self.new_children_map(BTreeMap::new());
        self.nodes.push(UbNode::new(children_index));
        node_index
    }

    fn new_children_map(&mut self, map: BTreeMap<T, NodeIndex>) -> ChildrenIndex {
        let index = self.children_maps.len();
        self.children_maps.push(map);
        index
    }

    fn get_children(&self, index: ChildrenIndex) -> &BTreeMap<T, NodeIndex> {
        &self.children_maps[index]
    }

    fn get_node(&self, index: NodeIndex) -> &UbNode<T> {
        &self.nodes[index]
    }
}

impl<T: Ord + Copy> Default for UbTree<T> {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use itertools::Itertools;

    use super::UbTree;

    #[test]
    fn test_empty_set() {
        let mut tree = UbTree::<usize>::new();
        tree.add_set(BTreeSet::new());
        assert!(tree.root_nodes().is_empty());
    }

    #[test]
    fn test_single_set() {
        let mut tree = UbTree::<usize>::new();
        tree.add_set(BTreeSet::from_iter([111, 222, 333]));
        assert_eq!(tree.root_nodes().len(), 1);
        assert_eq!(tree.root_nodes().keys().copied().collect_vec(), vec![111]);

        let root_a = tree.get_node(tree.root_nodes()[&111]);
        assert!(!root_a.is_end_of_path());
        assert_eq!(tree.get_children(root_a.children).len(), 1);
        assert!(tree.get_children(root_a.children).contains_key(&222));

        let root_a_b = tree.get_node(tree.get_children(root_a.children)[&222]);
        assert!(!root_a_b.is_end_of_path());
        assert_eq!(tree.get_children(root_a_b.children).len(), 1);
        assert!(tree.get_children(root_a_b.children).contains_key(&333));

        let root_a_b_c = tree.get_node(tree.get_children(root_a_b.children)[&333]);
        assert!(root_a_b_c.is_end_of_path());
        assert!(tree.get_children(root_a_b_c.children).is_empty());
        assert_eq!(root_a_b_c.set, Some(BTreeSet::from_iter([111, 222, 333])));
    }

    #[test]
    fn test_example_from_paper() {
        let mut tree = UbTree::<usize>::new();
        tree.add_set(BTreeSet::from_iter([0, 1, 2, 3]));
        tree.add_set(BTreeSet::from_iter([0, 1, 3]));
        tree.add_set(BTreeSet::from_iter([0, 1, 2]));
        tree.add_set(BTreeSet::from_iter([2, 3]));
        assert_eq!(tree.root_nodes().len(), 2);
        assert!(tree.root_nodes().contains_key(&0));
        assert!(tree.root_nodes().contains_key(&2));

        // root nodes
        let e0 = tree.get_node(tree.root_nodes()[&0]);
        let e2 = tree.get_node(tree.root_nodes()[&2]);
        assert!(!e0.is_end_of_path());
        assert_eq!(tree.get_children(e0.children).keys().copied().collect_vec(), vec![1]);
        assert!(!e2.is_end_of_path());
        assert_eq!(tree.get_children(e2.children).keys().copied().collect_vec(), vec![3]);

        // first level
        let e0e1 = tree.get_node(tree.get_children(e0.children)[&1]);
        let e2e3 = tree.get_node(tree.get_children(e2.children)[&3]);
        assert!(!e0e1.is_end_of_path());
        assert_eq!(tree.get_children(e0e1.children).keys().copied().collect_vec(), vec![2, 3]);
        assert!(e2e3.is_end_of_path());
        assert_eq!(e2e3.set, Some(BTreeSet::from_iter([2, 3])));
        assert!(tree.get_children(e2e3.children).is_empty());

        // second level
        let e0e1e2 = tree.get_node(tree.get_children(e0e1.children)[&2]);
        assert!(e0e1e2.is_end_of_path());
        assert_eq!(e0e1e2.set, Some(BTreeSet::from_iter([0, 1, 2])));
        assert_eq!(tree.get_children(e0e1e2.children).keys().copied().collect_vec(), vec![3]);
        let e0e1e3 = tree.get_node(tree.get_children(e0e1.children)[&3]);
        assert!(e0e1e3.is_end_of_path());
        assert_eq!(e0e1e3.set, Some(BTreeSet::from_iter([0, 1, 3])));
        assert!(tree.get_children(e0e1e3.children).is_empty());

        // third level
        let e0e1e2e3 = tree.get_node(tree.get_children(e0e1e2.children)[&3]);
        assert!(e0e1e2e3.is_end_of_path());
        assert_eq!(e0e1e2e3.set, Some(BTreeSet::from_iter([0, 1, 2, 3])));
        assert!(tree.get_children(e0e1e2e3.children).is_empty());
    }

    #[allow(clippy::cognitive_complexity)]
    #[test]
    fn test_contains_subset() {
        let mut tree = UbTree::<usize>::new();
        let e0123 = BTreeSet::from_iter([0, 1, 2, 3]);
        let e013 = BTreeSet::from_iter([0, 1, 3]);
        let e012 = BTreeSet::from_iter([0, 1, 2]);
        let e23 = BTreeSet::from_iter([2, 3]);
        tree.add_set(e0123.clone());
        tree.add_set(e013.clone());
        tree.add_set(e012.clone());
        tree.add_set(e23.clone());
        assert_eq!(tree.first_subset(&BTreeSet::from_iter([0])), None);
        assert_eq!(tree.first_subset(&BTreeSet::from_iter([1])), None);
        assert_eq!(tree.first_subset(&BTreeSet::from_iter([2])), None);
        assert_eq!(tree.first_subset(&BTreeSet::from_iter([3])), None);
        assert_eq!(tree.first_subset(&BTreeSet::from_iter([0, 1])), None);
        assert_eq!(tree.first_subset(&BTreeSet::from_iter([0, 2])), None);
        assert_eq!(tree.first_subset(&BTreeSet::from_iter([0, 3])), None);
        assert_eq!(tree.first_subset(&BTreeSet::from_iter([1, 2])), None);
        assert_eq!(tree.first_subset(&BTreeSet::from_iter([2, 3])), Some(&e23));
        assert_eq!(tree.first_subset(&BTreeSet::from_iter([0, 1, 2])), Some(&e012));
        assert_eq!(tree.first_subset(&BTreeSet::from_iter([0, 1, 3])), Some(&e013));
        assert_eq!(tree.first_subset(&BTreeSet::from_iter([0, 2, 3])), Some(&e23));
        assert_eq!(tree.first_subset(&BTreeSet::from_iter([1, 2, 3])), Some(&e23));
        let res0123 = tree.first_subset(&BTreeSet::from_iter([0, 1, 2, 3]));
        assert!([Some(&e0123), Some(&e013), Some(&e012), Some(&e23)].contains(&res0123));
        assert_eq!(tree.first_subset(&BTreeSet::from_iter([0, 4])), None);
        assert_eq!(tree.first_subset(&BTreeSet::from_iter([1, 4])), None);
        assert_eq!(tree.first_subset(&BTreeSet::from_iter([2, 4])), None);
        assert_eq!(tree.first_subset(&BTreeSet::from_iter([3, 4])), None);
        assert_eq!(tree.first_subset(&BTreeSet::from_iter([0, 1, 4])), None);
        assert_eq!(tree.first_subset(&BTreeSet::from_iter([0, 2, 4])), None);
        assert_eq!(tree.first_subset(&BTreeSet::from_iter([0, 3, 4])), None);
        assert_eq!(tree.first_subset(&BTreeSet::from_iter([1, 2, 4])), None);
        assert_eq!(tree.first_subset(&BTreeSet::from_iter([1, 2, 4])), None);
        assert_eq!(tree.first_subset(&BTreeSet::from_iter([2, 3, 4])), Some(&e23));
        assert_eq!(tree.first_subset(&BTreeSet::from_iter([0, 1, 2, 4])), Some(&e012));
        assert_eq!(tree.first_subset(&BTreeSet::from_iter([0, 1, 3, 4])), Some(&e013));
        assert_eq!(tree.first_subset(&BTreeSet::from_iter([0, 2, 3, 4])), Some(&e23));
        assert_eq!(tree.first_subset(&BTreeSet::from_iter([1, 2, 3, 4])), Some(&e23));
        let res01234 = tree.first_subset(&BTreeSet::from_iter([0, 1, 2, 3, 4]));
        assert!([Some(&e0123), Some(&e013), Some(&e012), Some(&e23)].contains(&res01234));
    }

    #[test]
    fn test_all_sets() {
        let mut tree = UbTree::<usize>::new();
        let e0123 = BTreeSet::from_iter([0, 1, 2, 3]);
        let e013 = BTreeSet::from_iter([0, 1, 3]);
        let e012 = BTreeSet::from_iter([0, 1, 2]);
        let e23 = BTreeSet::from_iter([2, 3]);
        tree.add_set(e0123.clone());
        assert_eq!(tree.all_sets(), BTreeSet::from_iter([&e0123]));
        tree.add_set(e013.clone());
        assert_eq!(tree.all_sets(), BTreeSet::from_iter([&e0123, &e013]));
        tree.add_set(e012.clone());
        assert_eq!(tree.all_sets(), BTreeSet::from_iter([&e0123, &e013, &e012]));
        tree.add_set(e23.clone());
        assert_eq!(tree.all_sets(), BTreeSet::from_iter([&e0123, &e013, &e012, &e23]));
    }
}
