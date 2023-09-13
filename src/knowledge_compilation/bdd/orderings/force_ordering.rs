use itertools::Itertools;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use crate::formulas::{EncodedFormula, FormulaFactory, Variable};
use crate::graphs::{hypergraph_from_cnf, Hypergraph, NodeIndex};

use super::dfs_ordering::dfs_ordering;

/// Simple implementation of the FORCE BDD variable ordering due to Aloul,
/// Markov, and Sakallah.  This ordering only works for CNF formulas.  A formulas
/// has to be converted to CNF before this ordering is called.
pub fn force_ordering(formula: EncodedFormula, f: &FormulaFactory) -> Vec<Variable> {
    let mut original_variables = (*formula.variables(f)).clone();
    let nnf = f.nnf_of(formula);
    original_variables.append(&mut (*nnf.variables(f)).clone());
    let cnf = f.cnf_of(nnf);
    let hypergraph = hypergraph_from_cnf(cnf, f);
    let mut node_map = HashMap::new();
    for i in 0..hypergraph.number_of_nodes() {
        node_map.insert(hypergraph.get_node(i).unwrap().content, i);
    }
    force(cnf, f, &hypergraph, &node_map, &original_variables)
}

fn force(
    formula: EncodedFormula,
    f: &FormulaFactory,
    hypergraph: &Hypergraph<Variable>,
    node_map: &HashMap<Variable, NodeIndex>,
    original_vars: &BTreeSet<Variable>,
) -> Vec<Variable> {
    let initial_ordering = create_initial_ordering(formula, f, node_map);
    let mut last_ordering: BTreeMap<NodeIndex, usize>;
    let mut current_ordering = initial_ordering;

    loop {
        last_ordering = current_ordering;
        let mut new_locations = BTreeMap::new();
        for idx in 0..hypergraph.number_of_nodes() {
            let node = hypergraph.get_node(idx).unwrap();
            let new_location = node.compute_tentative_new_location(hypergraph, &last_ordering);
            new_locations.insert(idx, new_location);
        }
        current_ordering = ordering_from_tentative_new_locations(&new_locations);
        if !should_proceed(&last_ordering, &current_ordering) {
            break;
        }
    }

    let mut ordering: Vec<Variable> = current_ordering
        .iter()
        .sorted_by(|o1, o2| o1.1.cmp(o2.1))
        .map(|(node, _)| hypergraph.get_node(*node).unwrap().content)
        .filter(|v| original_vars.contains(v))
        .collect();

    let ordering_set: HashSet<Variable> = HashSet::from_iter(ordering.clone());
    for var in original_vars {
        if !ordering_set.contains(var) {
            ordering.push(*var);
        }
    }
    ordering
}

fn create_initial_ordering(
    formula: EncodedFormula,
    f: &FormulaFactory,
    node_map: &HashMap<Variable, NodeIndex>,
) -> BTreeMap<NodeIndex, usize> {
    let mut initial_ordering = BTreeMap::new();
    let dfs_order = dfs_ordering(formula, f);
    for (idx, var) in dfs_order.iter().enumerate() {
        initial_ordering.insert(node_map[var], idx);
    }
    initial_ordering
}

fn ordering_from_tentative_new_locations(new_locations: &BTreeMap<NodeIndex, f64>) -> BTreeMap<NodeIndex, usize> {
    let mut ordering = BTreeMap::new();
    let mut list: Vec<(&usize, &f64)> = new_locations.iter().collect();
    list.sort_by(|o1, o2| o1.1.total_cmp(o2.1));
    for (idx, entry) in list.iter().enumerate() {
        ordering.insert(*entry.0, idx);
    }
    ordering
}

fn should_proceed(last_ordering: &BTreeMap<NodeIndex, usize>, current_ordering: &BTreeMap<NodeIndex, usize>) -> bool {
    last_ordering != current_ordering
}

#[cfg(test)]
mod tests {
    use crate::formulas::{FormulaFactory, ToFormula, Variable};
    use crate::knowledge_compilation::bdd::orderings::force_ordering::force_ordering;

    #[test]
    fn test_simple_formulas() {
        let f = &FormulaFactory::with_id("FF42");
        let va = f.var("A");
        let vb = f.var("B");
        let vc = f.var("C");
        assert!(force_ordering("$true".to_formula(f), f).is_empty());
        assert!(force_ordering("$false".to_formula(f), f).is_empty());
        assert_eq!(force_ordering("A".to_formula(f), f), vec![va]);
        assert_eq!(force_ordering("~A".to_formula(f), f), vec![va]);
        assert_eq!(force_ordering("A => ~B".to_formula(f), f), vec![va, vb]);
        assert_eq!(force_ordering("A <=> ~B".to_formula(f), f), vec![va, vb]);
        assert_eq!(force_ordering("~(A <=> ~B)".to_formula(f), f), vec![va, vb]);
        assert_eq!(force_ordering("A | ~C | B".to_formula(f), f), vec![va, vb, vc]);
        assert_eq!(force_ordering("A & ~B & C".to_formula(f), f), vec![va, vb, vc]);
        assert_eq!(force_ordering("A + C + B < 2".to_formula(f), f), vec![va, vc, vb]);
        assert_eq!(
            force_ordering("3*C + B + 4*A < 7".to_formula(f), f),
            [
                "A", "@RESERVED_FF42_PB_0", "@RESERVED_FF42_PB_1", "@RESERVED_FF42_PB_3", "@RESERVED_FF42_PB_2", "B",
                "@RESERVED_FF42_PB_6", "@RESERVED_FF42_PB_7", "@RESERVED_FF42_PB_9", "@RESERVED_FF42_PB_10", "@RESERVED_FF42_PB_4",
                "@RESERVED_FF42_PB_5", "@RESERVED_FF42_PB_15", "@RESERVED_FF42_PB_8", "@RESERVED_FF42_PB_16", "@RESERVED_FF42_PB_12",
                "@RESERVED_FF42_PB_11", "@RESERVED_FF42_PB_13", "C", "@RESERVED_FF42_PB_17", "@RESERVED_FF42_PB_14"
            ]
            .iter()
            .map(|v| v.to_formula(f).as_variable().unwrap())
            .collect::<Vec<Variable>>()
        );
    }

    #[test]
    fn test_complex_formula() {
        let f = &FormulaFactory::new();
        let formula =  "(~A | ~B) & (D | A) & (~C | A) & (D | C) & (A | Y | X) & (~W | ~Y | X) & (~A | ~Y | X) & (~F | ~Y | X) & (~X | Y) & (W | A | F | Y)".to_formula(f);
        let ordering = vec![f.var("B"), f.var("D"), f.var("C"), f.var("A"), f.var("X"), f.var("Y"), f.var("W"), f.var("F")];
        assert_eq!(force_ordering(formula, f), ordering);
    }
}
