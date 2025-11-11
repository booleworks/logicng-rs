use std::collections::BTreeMap;

/// Index for nodes of the hypergraph.
pub type NodeIndex = usize;
/// Index for edges of the hypergraph.
pub type EdgeIndex = usize;

/// A simple data structure for a hypergraph with a generic
/// node content type.
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct Hypergraph<T> {
    nodes: BTreeMap<NodeIndex, HypergraphNode<T>>,
    edges: BTreeMap<EdgeIndex, HypergraphEdge>,
}

/// A node in the hypergraph with a content of type `T`.
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct HypergraphNode<T> {
    /// Content of the node.
    pub content: T,
    /// Index of the node.
    pub index: NodeIndex,
    /// Edges which are connected with this node.
    pub edges: Vec<EdgeIndex>,
}

/// An edge in the hypergraph connecting one ore more nodes.
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct HypergraphEdge {
    /// Nodes connected by this edge.
    pub nodes: Vec<NodeIndex>,
    /// Index of the edge.
    pub index: EdgeIndex,
}

impl<T> Hypergraph<T> {
    /// Creates an empty hypergraph.
    pub const fn new() -> Self {
        Self { nodes: BTreeMap::new(), edges: BTreeMap::new() }
    }

    /// Adds a node to the hypergraph and returns the node index.
    pub fn add_node(&mut self, content: T) -> NodeIndex {
        let index = self.nodes.len();
        let node = HypergraphNode { content, index, edges: Vec::new() };
        self.nodes.insert(index, node);
        index
    }

    /// Adds an edge to the hypergraph
    pub fn add_edge(&mut self, nodes: Vec<NodeIndex>) -> EdgeIndex {
        let index = self.edges.len();
        let edge = HypergraphEdge { nodes, index };
        for node_index in &edge.nodes {
            let node = self.nodes.get_mut(node_index);
            assert!(node.is_some(), "Cannot find node with index {node_index}.");
            node.unwrap().edges.push(index);
        }
        self.edges.insert(index, edge);
        index
    }

    /// Returns the node for the given index.
    pub fn get_node(&self, index: NodeIndex) -> Option<&HypergraphNode<T>> {
        self.nodes.get(&index)
    }

    /// Returns the number of nodes of the graph.
    pub fn number_of_nodes(&self) -> usize {
        self.nodes.len()
    }

    /// Returns the edge for the given index.
    pub fn get_edge(&self, index: EdgeIndex) -> Option<&HypergraphEdge> {
        self.edges.get(&index)
    }

    /// Returns the number of edges of the graph.
    pub fn number_of_edges(&self) -> usize {
        self.edges.len()
    }
}

impl<T> Default for Hypergraph<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> HypergraphNode<T> {
    #[allow(clippy::cast_precision_loss)]
    pub(crate) fn compute_tentative_new_location(&self, graph: &Hypergraph<T>, node_ordering: &BTreeMap<NodeIndex, usize>) -> f64 {
        let mut new_location = 0.0;
        for edge_index in &self.edges {
            let edge = &graph.edges[edge_index];
            new_location += edge.center_of_gravity(node_ordering);
        }
        new_location / self.edges.len() as f64
    }
}

impl HypergraphEdge {
    #[allow(clippy::cast_precision_loss)]
    fn center_of_gravity(&self, node_ordering: &BTreeMap<NodeIndex, usize>) -> f64 {
        let mut cog = 0;
        for node in &self.nodes {
            let level = node_ordering.get(node);
            assert!(level.is_some(), "Could not finde the node index {node} in the node ordering.");
            cog += level.unwrap();
        }
        cog as f64 / self.nodes.len() as f64
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use super::Hypergraph;

    #[test]
    fn test_hypergraph() {
        let mut graph = Hypergraph::new();
        let id1 = graph.add_node("a");
        let id2 = graph.add_node("b");
        let id3 = graph.add_node("c");
        let id4 = graph.add_node("d");
        let e1 = graph.add_edge(vec![id1, id2]);
        let e2 = graph.add_edge(vec![id2, id3, id4]);
        let e3 = graph.add_edge(vec![id3, id4]);

        assert!(graph.get_node(27).is_none());
        assert!(graph.get_node(id1).is_some());
        assert_eq!(graph.get_node(id3).unwrap().content, "c");
        assert_eq!(graph.get_node(id3).unwrap().index, 2);
        assert_eq!(graph.get_edge(e1).unwrap().index, 0);
        assert_eq!(graph.get_edge(e2).unwrap().nodes, vec![id2, id3, id4]);
        assert_eq!(graph.get_node(id1).unwrap().edges, vec![e1]);
        assert_eq!(graph.get_node(id2).unwrap().edges, vec![e1, e2]);
        assert_eq!(graph.get_node(id3).unwrap().edges, vec![e2, e3]);
        assert_eq!(graph.get_node(id4).unwrap().edges, vec![e2, e3]);
    }

    #[test]
    #[allow(clippy::float_cmp)]
    fn test_center_of_gravity() {
        let mut graph = Hypergraph::new();
        let id1 = graph.add_node("a");
        let id2 = graph.add_node("b");
        let id3 = graph.add_node("c");
        let id4 = graph.add_node("d");
        let edge = graph.add_edge(vec![id1, id2, id3, id4]);

        let mut node_ordering = BTreeMap::new();
        node_ordering.insert(id1, 1);
        node_ordering.insert(id2, 2);
        node_ordering.insert(id3, 3);
        node_ordering.insert(id4, 4);
        assert_eq!(graph.get_edge(edge).unwrap().center_of_gravity(&node_ordering), 2.5);

        node_ordering.insert(id1, 2);
        node_ordering.insert(id2, 4);
        node_ordering.insert(id3, 6);
        node_ordering.insert(id4, 8);
        assert_eq!(graph.get_edge(edge).unwrap().center_of_gravity(&node_ordering), 5.0);
    }
}
