use crate::datastructures::Model;
use crate::formulas::Variable;

use super::bdd_kernel::BddKernel;
use super::bdd_operations::all_sat;

pub fn enumerate_all_models(index: usize, variables: Option<&[Variable]>, kernel: &mut BddKernel) -> Vec<Model> {
    let mut res = Vec::new();
    let models = all_sat(index, kernel);
    let mut relevant_indices = Vec::new();
    if let Some(vars) = variables {
        for v in vars {
            relevant_indices.push(kernel.var2idx[v]);
        }
    } else {
        for v in kernel.var2idx.values() {
            relevant_indices.push(*v);
        }
    }
    relevant_indices.sort_unstable();
    for mut model in models {
        let mut all_models = Vec::new();
        generate_all_models(&mut all_models, &mut model, &relevant_indices, 0, kernel);
        res.extend(all_models);
    }
    res
}

fn generate_all_models(models: &mut Vec<Model>, model: &mut Vec<i8>, relevant_indices: &[usize], position: usize, kernel: &mut BddKernel) {
    if position == relevant_indices.len() {
        let mut pos = Vec::new();
        let mut neg = Vec::new();
        for i in relevant_indices {
            if model[*i] == 0 {
                neg.push(kernel.get_variable_for_index(*i).unwrap());
            } else {
                pos.push(kernel.get_variable_for_index(*i).unwrap());
            }
        }
        models.push(Model::new(pos, neg));
    } else if model[relevant_indices[position]] != -1 {
        generate_all_models(models, model, relevant_indices, position + 1, kernel);
    } else {
        model[relevant_indices[position]] = 0;
        generate_all_models(models, model, relevant_indices, position + 1, kernel);
        model[relevant_indices[position]] = 1;
        generate_all_models(models, model, relevant_indices, position + 1, kernel);
        model[relevant_indices[position]] = -1;
    }
}
