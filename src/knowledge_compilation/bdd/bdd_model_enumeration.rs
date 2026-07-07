use crate::datastructures::Model;
use crate::errors::LngResult;
use crate::formulas::Variable;
use crate::knowledge_compilation::bdd::BddError;

use super::bdd_kernel::BddKernel;
use super::bdd_operations::all_sat;

pub fn enumerate_all_models(
    index: usize,
    variables: Option<&[Variable]>,
    kernel: &mut BddKernel,
) -> LngResult<Vec<Model>> {
    let mut res = Vec::new();
    let models = all_sat(index, kernel);
    let mut relevant_indices = Vec::new();
    if let Some(vars) = variables {
        for v in vars {
            let idx = kernel.var2idx.get(v);
            if let Some(i) = idx {
                relevant_indices.push(*i);
            } else {
                return Err(BddError::InvalidVar { var: *v }.into());
            }
        }
    } else {
        for v in kernel.var2idx.values() {
            relevant_indices.push(*v);
        }
    }
    relevant_indices.sort_unstable();
    for mut model in models {
        let mut all_models = Vec::new();
        generate_all_models(&mut all_models, &mut model, &relevant_indices, 0, kernel)?;
        res.extend(all_models);
    }
    Ok(res)
}

fn generate_all_models(
    models: &mut Vec<Model>,
    model: &mut Vec<i8>,
    relevant_indices: &[usize],
    position: usize,
    kernel: &mut BddKernel,
) -> LngResult<()> {
    if position == relevant_indices.len() {
        let mut pos = Vec::new();
        let mut neg = Vec::new();
        for i in relevant_indices {
            let assignment = *model
                .get(*i)
                .ok_or(BddError::InvalidVarNum { var_num: *i })?;
            let variable = kernel
                .get_variable_for_index(*i)
                .ok_or(BddError::InvalidVarNum { var_num: *i })?;
            if assignment == 0 {
                neg.push(variable);
            } else if assignment == 1 {
                pos.push(variable);
            }
        }
        models.push(Model::new(pos, neg));
    } else if *model
        .get(relevant_indices[position])
        .ok_or(BddError::InvalidVarNum {
            var_num: relevant_indices[position],
        })?
        != -1
    {
        generate_all_models(models, model, relevant_indices, position + 1, kernel)?;
    } else {
        model[relevant_indices[position]] = 0;
        generate_all_models(models, model, relevant_indices, position + 1, kernel)?;
        model[relevant_indices[position]] = 1;
        generate_all_models(models, model, relevant_indices, position + 1, kernel)?;
        model[relevant_indices[position]] = -1;
    }
    Ok(())
}
