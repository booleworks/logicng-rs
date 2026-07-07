use std::collections::HashMap;

use crate::errors::LngResult;
use crate::formulas::{EncodedFormula, Formula, FormulaFactory, Variable};
use crate::graphs::GraphError;
use crate::graphs::hypergraph::Hypergraph;

use super::hypergraph::NodeIndex;

/// Builds a hypergraph from a formula in _CNF_.
///
/// # Errors
///
/// Returns an error if the given formula is not a CNF formula.
pub fn hypergraph_from_cnf(cnf: EncodedFormula, f: &FormulaFactory) -> LngResult<Hypergraph<Variable>> {
    let mut hypergraph = Hypergraph::new();
    let mut node_map = HashMap::new();
    match cnf.unpack(f) {
        Formula::Cc(_) | Formula::Pbc(_) | Formula::Impl(_) | Formula::Equiv(_) | Formula::Not(_) => {
            return Err(GraphError::UnexpectedFormulaInCnf { formula: cnf }.into());
        }
        Formula::Lit(_) | Formula::Or(_) => add_clause(cnf, f, &mut hypergraph, &mut node_map)?,
        Formula::And(ops) => {
            for op in ops {
                add_clause(op, f, &mut hypergraph, &mut node_map)?;
            }
        }
        _ => {}
    }
    Ok(hypergraph)
}

fn add_clause(
    clause: EncodedFormula,
    f: &FormulaFactory,
    graph: &mut Hypergraph<Variable>,
    node_map: &mut HashMap<Variable, NodeIndex>,
) -> LngResult<()> {
    let mut edge_nodes = Vec::new();
    if !clause.is_cnf(f) {
        return Err(GraphError::UnexpectedFormulaInCnf { formula: clause }.into());
    }
    for variable in &*clause.variables(f) {
        let found_node = node_map.get(variable);
        if let Some(index) = found_node {
            edge_nodes.push(*index);
        } else {
            let new_node = graph.add_node(*variable);
            node_map.insert(*variable, new_node);
            edge_nodes.push(new_node);
        }
    }
    graph.add_edge(edge_nodes)?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use crate::formulas::FormulaFactory;

    use super::hypergraph_from_cnf;

    #[test]
    fn test_from_constants() {
        let f = FormulaFactory::new();
        assert_eq!(hypergraph_from_cnf(f.parse("$false").unwrap(), &f).unwrap().number_of_nodes(), 0);
        assert_eq!(hypergraph_from_cnf(f.parse("$false").unwrap(), &f).unwrap().number_of_edges(), 0);
        assert_eq!(hypergraph_from_cnf(f.parse("$true").unwrap(), &f).unwrap().number_of_nodes(), 0);
        assert_eq!(hypergraph_from_cnf(f.parse("$true").unwrap(), &f).unwrap().number_of_edges(), 0);
    }

    #[test]
    fn test_from_literals() {
        let f = FormulaFactory::new();
        let hg_a = hypergraph_from_cnf(f.parse("a").unwrap(), &f).unwrap();
        assert_eq!(hg_a.number_of_nodes(), 1);
        assert_eq!(hg_a.number_of_edges(), 1);
        assert_eq!(hg_a.get_node(0).unwrap().content, f.var("a"));
        assert_eq!(hg_a.get_edge(0).unwrap().nodes, vec![0]);

        let hg_na = hypergraph_from_cnf(f.parse("~a").unwrap(), &f).unwrap();
        assert_eq!(hg_na.number_of_nodes(), 1);
        assert_eq!(hg_na.number_of_edges(), 1);
        assert_eq!(hg_na.get_node(0).unwrap().content, f.var("a"));
        assert_eq!(hg_na.get_edge(0).unwrap().nodes, vec![0]);
    }

    #[test]
    fn test_from_clause() {
        let f = FormulaFactory::new();
        let hg = hypergraph_from_cnf(f.parse("a | b | ~c | d").unwrap(), &f).unwrap();
        assert_eq!(hg.number_of_nodes(), 4);
        assert_eq!(hg.number_of_edges(), 1);
        assert_eq!(hg.get_node(0).unwrap().content, f.var("a"));
        assert_eq!(hg.get_node(1).unwrap().content, f.var("b"));
        assert_eq!(hg.get_node(2).unwrap().content, f.var("c"));
        assert_eq!(hg.get_node(3).unwrap().content, f.var("d"));
        assert_eq!(hg.get_edge(0).unwrap().nodes, vec![0, 1, 2, 3]);
    }

    #[test]
    fn test_from_cnf() {
        let f = FormulaFactory::new();
        let hg = hypergraph_from_cnf(f.parse("(a | b | ~c) & (b | ~d) & (c | ~e) & (~b | ~d | e) & x & ~y").unwrap(), &f).unwrap();

        assert_eq!(hg.number_of_nodes(), 7);
        assert_eq!(hg.number_of_edges(), 6);

        assert_eq!(hg.get_node(0).unwrap().content, f.var("a"));
        assert_eq!(hg.get_node(1).unwrap().content, f.var("b"));
        assert_eq!(hg.get_node(2).unwrap().content, f.var("c"));
        assert_eq!(hg.get_node(3).unwrap().content, f.var("d"));
        assert_eq!(hg.get_node(4).unwrap().content, f.var("e"));
        assert_eq!(hg.get_node(5).unwrap().content, f.var("x"));
        assert_eq!(hg.get_node(6).unwrap().content, f.var("y"));

        assert_eq!(hg.get_edge(0).unwrap().nodes, vec![0, 1, 2]);
        assert_eq!(hg.get_edge(1).unwrap().nodes, vec![1, 3]);
        assert_eq!(hg.get_edge(2).unwrap().nodes, vec![2, 4]);
        assert_eq!(hg.get_edge(3).unwrap().nodes, vec![1, 3, 4]);
        assert_eq!(hg.get_edge(4).unwrap().nodes, vec![5]);
        assert_eq!(hg.get_edge(5).unwrap().nodes, vec![6]);
    }
}
