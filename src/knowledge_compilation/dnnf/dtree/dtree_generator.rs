use std::cmp::Ordering;
use std::collections::{HashMap, HashSet};
use std::iter::repeat_n;

use itertools::Itertools;

use crate::formulas::{EncodedFormula, FormulaFactory, Variable};
use crate::knowledge_compilation::dnnf::dtree::dtree_datastructure::DTree;
use crate::knowledge_compilation::dnnf::dtree::dtree_factory::DTreeFactory;

pub fn min_fill_dtree_generation(cnf: EncodedFormula, f: &FormulaFactory, df: &mut DTreeFactory) -> DTree {
    let graph = Graph::new_from_cnf(cnf, f);
    let ordering = graph.get_min_fill_ordering();
    generate_with_eliminating_order(cnf, ordering, f, df)
}

fn generate_with_eliminating_order(cnf: EncodedFormula, ordering: Vec<Variable>, f: &FormulaFactory, df: &mut DTreeFactory) -> DTree {
    assert_eq!(cnf.variables(f).len(), ordering.len());

    if !cnf.is_cnf(f) || cnf.is_atomic() {
        panic!("Cannot generate DTree from a non-cnf formula or atomic formula")
    } else if !cnf.is_and() {
        df.leaf((*cnf.literals(f)).iter().copied().collect())
    } else {
        let mut sigma: Vec<DTree> = cnf.operands(f).iter().map(|clause| df.leaf((*clause.literals(f)).iter().copied().collect())).collect();

        for variable in ordering {
            let mut gamma = Vec::new();
            let mut sigma2 = Vec::new();
            for tree in sigma {
                if tree.static_variable_set(df).contains(&variable) {
                    gamma.push(tree);
                } else {
                    sigma2.push(tree);
                }
            }
            sigma = sigma2;
            if !gamma.is_empty() {
                sigma.push(compose(&gamma, df));
            }
        }
        compose(&sigma, df)
    }
}

fn compose(trees: &[DTree], df: &mut DTreeFactory) -> DTree {
    assert!(!trees.is_empty());
    if trees.len() == 1 {
        trees[0]
    } else {
        let (left_split, right_split) = trees.split_at(trees.len() / 2);
        let left_composition = compose(left_split, df);
        let right_composition = compose(right_split, df);
        df.node(left_composition, right_composition)
    }
}

struct Graph {
    number_of_vertices: usize,
    adj_matrix: Vec<Vec<bool>>,
    vertices: Vec<Variable>,
    edge_list: Vec<Vec<usize>>,
}

impl Graph {
    fn new_from_cnf(cnf: EncodedFormula, f: &FormulaFactory) -> Self {
        let cnf_variables: Vec<Variable> = cnf.variables(f).iter().sorted_by_key(|&v| v.name(f)).copied().collect();
        let number_of_vertices = cnf_variables.len();
        let mut vertices = Vec::with_capacity(number_of_vertices);
        let mut var_to_index = HashMap::new();
        for var in cnf_variables {
            var_to_index.insert(var, vertices.len());
            vertices.push(var);
        }

        let mut adj_matrix: Vec<Vec<bool>> = repeat_n(repeat_n(false, number_of_vertices).collect(), number_of_vertices).collect();
        let mut edge_list: Vec<HashSet<usize>> = repeat_n(HashSet::new(), number_of_vertices).collect();

        for clause in &*cnf.operands(f) {
            let variables = clause.variables(f);
            let var_nums: Vec<usize> = variables.iter().map(|v| *var_to_index.get(v).unwrap()).collect();
            for i in 0..var_nums.len() {
                for j in (i + 1)..var_nums.len() {
                    let var_i = var_nums[i];
                    let var_j = var_nums[j];
                    edge_list[var_i].insert(var_j);
                    edge_list[var_j].insert(var_i);
                    adj_matrix[var_i][var_j] = true;
                    adj_matrix[var_j][var_i] = true;
                }
            }
        }
        Self {
            number_of_vertices,
            adj_matrix,
            vertices,
            edge_list: edge_list.into_iter().map(|edges| edges.into_iter().collect::<Vec<usize>>()).collect(),
        }
    }

    pub fn get_min_fill_ordering(self) -> Vec<Variable> {
        let mut fill_adj_matrix = self.adj_matrix;
        let mut fill_edge_list = self.edge_list;
        let mut ordering = Vec::with_capacity(self.number_of_vertices);
        let mut processed: Vec<bool> = repeat_n(false, self.number_of_vertices).collect();
        let mut tree_width = 0;
        for _ in 0..self.number_of_vertices {
            let mut possibly_best_vertices = Vec::new();
            let mut min_edges = usize::MAX;
            for current_vertex in 0..self.number_of_vertices {
                if processed[current_vertex] {
                    continue;
                }
                let mut edges_added = 0;
                let neighbor_list = &fill_edge_list[current_vertex];
                for i in 0..neighbor_list.len() {
                    let first_neighbor = neighbor_list[i];
                    if processed[first_neighbor] {
                        continue;
                    }
                    for second_neighbor in neighbor_list.iter().skip(i + 1) {
                        if !processed[*second_neighbor] && !fill_adj_matrix[first_neighbor][*second_neighbor] {
                            edges_added += 1;
                        }
                    }
                }
                match edges_added.cmp(&min_edges) {
                    Ordering::Less => {
                        min_edges = edges_added;
                        possibly_best_vertices.clear();
                        possibly_best_vertices.push(current_vertex);
                    }
                    Ordering::Equal => {
                        possibly_best_vertices.push(current_vertex);
                    }
                    Ordering::Greater => {}
                }
            }

            let best_vertex = possibly_best_vertices[0];

            let neighbor_list = fill_edge_list[best_vertex].clone();
            for i in 0..neighbor_list.len() {
                let first_neighbor = neighbor_list[i];
                if processed[first_neighbor] {
                    continue;
                }
                for second_neighbor in neighbor_list.iter().skip(i + 1).copied() {
                    if !processed[second_neighbor] && !fill_adj_matrix[first_neighbor][second_neighbor] {
                        fill_adj_matrix[first_neighbor][second_neighbor] = true;
                        fill_adj_matrix[second_neighbor][first_neighbor] = true;
                        fill_edge_list[first_neighbor].push(second_neighbor);
                        fill_edge_list[second_neighbor].push(first_neighbor);
                    }
                }
            }

            let mut current_number_of_edges = 0;
            for (k, p) in processed.iter().enumerate().take(self.number_of_vertices) {
                if fill_adj_matrix[best_vertex][k] && !*p {
                    current_number_of_edges += 1;
                }
            }

            tree_width = tree_width.max(current_number_of_edges);

            processed[best_vertex] = true;
            ordering.push(self.vertices[best_vertex]);
        }
        ordering
    }
}

#[cfg(test)]
mod tests {
    use crate::operations::transformations::{CnfAlgorithm, CnfEncoder};

    #[test]
    #[cfg_attr(not(feature = "long_running_tests"), ignore)]
    fn test_dtree_generation() {
        use std::fs::File;
        use std::io::{BufRead, BufReader};

        use crate::formulas::FormulaFactory;
        use crate::knowledge_compilation::dnnf::dtree::dtree_factory::DTreeFactory;
        use crate::knowledge_compilation::dnnf::dtree::dtree_generator::min_fill_dtree_generation;

        let reader = BufReader::new(File::open("resources/formulas/large_formula.txt").unwrap());
        let f = &FormulaFactory::new();
        let mut df = DTreeFactory::new();
        let formulas = reader.lines().map(|l| f.parse(&l.unwrap()).unwrap());
        let formula = f.and(formulas);
        let cnf = CnfEncoder::new(CnfAlgorithm::Factorization).transform(formula, f);
        let tree = min_fill_dtree_generation(cnf, f, &mut df);
        println!("{}", tree.to_string(&df, f));
    }
}
