use crate::cardinality_constraints::cc_config::{AlkEncoder, AmkEncoder};
use crate::cardinality_constraints::cc_incremental_data::CcIncrementalData;
use crate::cardinality_constraints::cc_sorter;
use crate::cardinality_constraints::cc_sorter::ImplicationDirection::{Both, InputToOutput, OutputToInput};
use crate::datastructures::EncodingResult;
use crate::formulas::Variable;

pub(super) fn build_amk(result: &mut dyn EncodingResult, vars: &[Variable], rhs: usize, with_inc: bool) -> Option<CcIncrementalData> {
    if with_inc {
        Some(build_amk_for_incremental(result, vars, rhs))
    } else {
        if rhs > vars.len() / 2 {
            let geq = vars.len() - rhs;
            let input = vars.iter().map(Variable::neg_lit).collect();
            let output = cc_sorter::cc_sort(geq, input, result, OutputToInput);
            for outlit in output.iter().take(geq) {
                result.add_clause(&[*outlit]);
            }
        } else {
            let input = vars.iter().map(Variable::pos_lit).collect();
            let output = cc_sorter::cc_sort(rhs + 1, input, result, InputToOutput);
            result.add_clause(&[output.get(rhs).unwrap().negate()]);
        }
        None
    }
}

pub(super) fn build_alk(result: &mut dyn EncodingResult, vars: &[Variable], rhs: usize, with_inc: bool) -> Option<CcIncrementalData> {
    if with_inc {
        Some(build_alk_for_incremental(result, vars, rhs))
    } else {
        let new_rhs = vars.len() - rhs;
        if new_rhs > vars.len() / 2 {
            let geq = vars.len() - new_rhs;
            let input = vars.iter().map(Variable::pos_lit).collect();
            let output = cc_sorter::cc_sort(geq, input, result, OutputToInput);
            for outlit in output.iter().take(geq) {
                result.add_clause(&[*outlit]);
            }
        } else {
            let input = vars.iter().map(Variable::neg_lit).collect();
            let output = cc_sorter::cc_sort(new_rhs + 1, input, result, InputToOutput);
            result.add_clause(&[output.get(new_rhs).unwrap().negate()]);
        }
        None
    }
}

pub(super) fn build_exk(result: &mut dyn EncodingResult, vars: &[Variable], rhs: usize) {
    let input = vars.iter().map(Variable::pos_lit).collect();
    let output = cc_sorter::cc_sort(rhs + 1, input, result, Both);
    result.add_clause(&[output.get(rhs).unwrap().negate()]);
    result.add_clause(&[*output.get(rhs - 1).unwrap()]);
}

fn build_amk_for_incremental(result: &mut dyn EncodingResult, vars: &[Variable], rhs: usize) -> CcIncrementalData {
    let input = vars.iter().map(Variable::pos_lit).collect();
    let output = cc_sorter::cc_sort(rhs + 1, input, result, InputToOutput);
    result.add_clause(&[output.get(rhs).unwrap().negate()]);
    CcIncrementalData::for_amk(AmkEncoder::CardinalityNetwork, output, rhs)
}

fn build_alk_for_incremental(result: &mut dyn EncodingResult, vars: &[Variable], rhs: usize) -> CcIncrementalData {
    let new_rhs = vars.len() - rhs;
    let input = vars.iter().map(Variable::neg_lit).collect();
    let output = cc_sorter::cc_sort(new_rhs + 1, input, result, InputToOutput);
    result.add_clause(&[output.get(new_rhs).unwrap().negate()]);
    CcIncrementalData::for_alk(AlkEncoder::CardinalityNetwork, output, rhs, vars.len())
}
