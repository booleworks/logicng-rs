#![allow(clippy::cast_possible_truncation)]

use crate::datastructures::{EncodingResult, SolverExportLiteral};
use crate::encodings::cardinality_constraints::cc_sorter::ImplicationDirection::{Both, InputToOutput, OutputToInput};
use crate::formulas::AUX_CC;

#[derive(Eq, PartialEq, Copy, Clone)]
pub enum ImplicationDirection {
    InputToOutput,
    OutputToInput,
    Both,
}

pub fn cc_sort(
    m: usize,
    input: Vec<SolverExportLiteral>,
    result: &mut dyn EncodingResult,
    direction: ImplicationDirection,
) -> Vec<SolverExportLiteral> {
    let n = input.len();
    let m2 = m.min(n);
    if m == 0 || n == 0 {
        Vec::new()
    } else if n == 1 {
        input
    } else if n == 2 {
        let o1 = result.new_auxiliary_variable(AUX_CC);
        if m2 == 2 {
            let o2 = result.new_auxiliary_variable(AUX_CC);
            comparator2(input[0], input[1], o1, o2, result, direction);
            vec![o1, o2]
        } else {
            comparator1(input[0], input[1], o1, result, direction);
            vec![o1]
        }
    } else if direction != InputToOutput {
        recursive_sorter(m2, &input, result, direction)
    } else if counter_sorter_value(m2, n) < direct_sorter_value(n) {
        counter_sorter(m2, &input, result, direction)
    } else {
        direct_sorter(m2, &input, result)
    }
}

pub fn cc_merge(
    m: usize,
    input_a: Vec<SolverExportLiteral>,
    input_b: Vec<SolverExportLiteral>,
    result: &mut dyn EncodingResult,
    direction: ImplicationDirection,
) -> Vec<SolverExportLiteral> {
    if m == 0 {
        Vec::new()
    } else if input_a.is_empty() {
        input_b
    } else if input_b.is_empty() {
        input_a
    } else {
        let n = input_a.len() + input_b.len();
        let m2 = m.min(n);
        if direction == InputToOutput {
            direct_merger(m2, &input_a, &input_b, result)
        } else {
            let output = recursive_merger(m2, &input_a, &input_b, result, direction);
            assert_eq!(output.len(), m2);
            output
        }
    }
}

const fn counter_sorter_value(m: usize, n: usize) -> usize {
    2 * n + (m - 1) * (2 * (n - 1) - 1) - (m - 2) - 2 * ((m - 1) * (m - 2) / 2)
}

const fn direct_sorter_value(n: usize) -> usize {
    if n > 30 {
        usize::MAX
    } else {
        2_usize.pow(n as u32) - 1
    }
}

fn comparator1(
    x1: SolverExportLiteral,
    x2: SolverExportLiteral,
    y: SolverExportLiteral,
    result: &mut dyn EncodingResult,
    direction: ImplicationDirection,
) {
    assert_ne!(x1, x2);
    if direction == InputToOutput || direction == Both {
        result.add_clause(&[x1.negate(), y]);
        result.add_clause(&[x2.negate(), y]);
    }
    if direction == OutputToInput || direction == Both {
        result.add_clause(&[y.negate(), x1, x2]);
    }
}

fn comparator2(
    x1: SolverExportLiteral,
    x2: SolverExportLiteral,
    y1: SolverExportLiteral,
    y2: SolverExportLiteral,
    result: &mut dyn EncodingResult,
    direction: ImplicationDirection,
) {
    assert_ne!(x1, x2);
    assert_ne!(y1, y2);
    if direction == InputToOutput || direction == Both {
        result.add_clause(&[x1.negate(), y1]);
        result.add_clause(&[x2.negate(), y1]);
        result.add_clause(&[x1.negate(), x2.negate(), y2]);
    }
    if direction == OutputToInput || direction == Both {
        result.add_clause(&[y1.negate(), x1, x2]);
        result.add_clause(&[y2.negate(), x1]);
        result.add_clause(&[y2.negate(), x2]);
    }
}

fn recursive_sorter(
    m: usize,
    input: &[SolverExportLiteral],
    result: &mut dyn EncodingResult,
    direction: ImplicationDirection,
) -> Vec<SolverExportLiteral> {
    let n = input.len();
    let l = n / 2;
    assert!(m <= n);
    let mut tmp_lits_a = Vec::with_capacity(l);
    let mut tmp_lits_b = Vec::with_capacity(n - l);

    for lit in input.iter().take(l) {
        tmp_lits_a.push(*lit);
    }
    for lit in input.iter().take(n).skip(l) {
        tmp_lits_b.push(*lit);
    }

    let tmp_lits_o1 = cc_sort(m, tmp_lits_a, result, direction);
    let tmp_lits_o2 = cc_sort(m, tmp_lits_b, result, direction);
    assert_eq!(tmp_lits_o1.len(), m.min(l));
    assert_eq!(tmp_lits_o2.len(), m.min(n - l));
    cc_merge(m, tmp_lits_o1, tmp_lits_o2, result, direction)
}

fn counter_sorter(
    k: usize,
    x: &[SolverExportLiteral],
    result: &mut dyn EncodingResult,
    direction: ImplicationDirection,
) -> Vec<SolverExportLiteral> {
    let n = x.len();
    let mut aux_vars = Vec::with_capacity(n);
    for _ in 0..n {
        aux_vars.push(Vec::with_capacity(k));
    }
    for j in 0..k {
        for aux_var in aux_vars.iter_mut().take(n).skip(j) {
            aux_var.push(result.new_auxiliary_variable(AUX_CC));
        }
    }

    if direction == InputToOutput || direction == Both {
        for i in 0..n {
            result.add_clause(&[x[i].negate(), aux_vars[i][0]]);
            if i > 0 {
                result.add_clause(&[aux_vars[i - 1][0].negate(), aux_vars[i][0]]);
            }
        }
        for j in 1..k {
            for i in j..n {
                result.add_clause(&[x[i].negate(), aux_vars[i - 1][j - 1].negate(), aux_vars[i][j]]);
                if i > j {
                    result.add_clause(&[aux_vars[i - 1][j].negate(), aux_vars[i][j]]);
                }
            }
        }
    }

    assert_eq!(aux_vars[n - 1].len(), k);
    aux_vars[n - 1].clone()
}

fn direct_sorter(m: usize, input: &[SolverExportLiteral], result: &mut dyn EncodingResult) -> Vec<SolverExportLiteral> {
    let n = input.len();
    assert!(n < 20);
    let mut bitmask = 1;
    let mut output = Vec::with_capacity(m);
    for _ in 0..m {
        output.push(result.new_auxiliary_variable(AUX_CC));
    }

    let mut clause = Vec::with_capacity(m);
    while bitmask < 2_u32.pow(n as u32) {
        clause.clear();
        let mut count = 0;
        for (i, lit) in input.iter().enumerate().take(n) {
            if (1 << i) & bitmask != 0 {
                count += 1;
                if count > m {
                    break;
                }
                clause.push(lit.negate());
            }
        }
        assert!(count > 0);
        if count <= m {
            clause.push(output[count - 1]);
            result.add_clause(&clause);
        }
        bitmask += 1;
    }
    output
}

fn recursive_merger(
    c: usize,
    input_a: &[SolverExportLiteral],
    input_b: &[SolverExportLiteral],
    result: &mut dyn EncodingResult,
    direction: ImplicationDirection,
) -> Vec<SolverExportLiteral> {
    let a2 = c.min(input_a.len());
    let b2 = c.min(input_b.len());
    if c == 1 {
        let y = result.new_auxiliary_variable(AUX_CC);
        comparator1(input_a[0], input_b[0], y, result, direction);
        vec![y]
    } else if a2 == 1 && b2 == 1 {
        assert_eq!(c, 2);
        let y1 = result.new_auxiliary_variable(AUX_CC);
        let y2 = result.new_auxiliary_variable(AUX_CC);
        comparator2(input_a[0], input_b[0], y1, y2, result, direction);
        vec![y1, y2]
    } else {
        let mut tmp_lits_odd_a = Vec::with_capacity(input_a.len() / 2 + 1);
        let mut tmp_lits_odd_b = Vec::with_capacity(input_b.len() / 2 + 1);
        let mut tmp_lits_even_a = Vec::with_capacity(input_a.len() / 2 + 1);
        let mut tmp_lits_even_b = Vec::with_capacity(input_b.len() / 2 + 1);

        for i in (0..a2).step_by(2) {
            tmp_lits_odd_a.push(input_a[i]);
        }
        for i in (0..b2).step_by(2) {
            tmp_lits_odd_b.push(input_b[i]);
        }
        for i in (1..a2).step_by(2) {
            tmp_lits_even_a.push(input_a[i]);
        }
        for i in (1..b2).step_by(2) {
            tmp_lits_even_b.push(input_b[i]);
        }

        let odd_merge = cc_merge(c / 2 + 1, tmp_lits_odd_a, tmp_lits_odd_b, result, direction);
        let even_merge = cc_merge(c / 2, tmp_lits_even_a, tmp_lits_even_b, result, direction);

        let mut output = vec![*odd_merge.first().unwrap()];

        let mut i = 1_usize;
        let mut j = 0_usize;
        loop {
            if i < odd_merge.len() && j < even_merge.len() {
                if output.len() + 2 <= c {
                    let z0 = result.new_auxiliary_variable(AUX_CC);
                    let z1 = result.new_auxiliary_variable(AUX_CC);
                    comparator2(odd_merge[i], even_merge[j], z0, z1, result, direction);
                    output.push(z0);
                    output.push(z1);
                    if output.len() == c {
                        return output;
                    }
                } else if output.len() + 1 == c {
                    let z0 = result.new_auxiliary_variable(AUX_CC);
                    comparator1(odd_merge[i], even_merge[j], z0, result, direction);
                    output.push(z0);
                    return output;
                }
            } else if i >= odd_merge.len() && j >= even_merge.len() {
                return output;
            } else if i >= odd_merge.len() {
                output.push(*even_merge.last().unwrap());
            } else {
                output.push(*odd_merge.last().unwrap());
            }
            i += 1;
            j += 1;
        }
    }
}

fn direct_merger(
    m: usize,
    input_a: &[SolverExportLiteral],
    input_b: &[SolverExportLiteral],
    result: &mut dyn EncodingResult,
) -> Vec<SolverExportLiteral> {
    let a = input_a.len();
    let b = input_b.len();
    let output: Vec<SolverExportLiteral> = std::iter::repeat_with(|| result.new_auxiliary_variable(AUX_CC)).take(m).collect();
    for i in 0..m.min(a) {
        result.add_clause(&[input_a[i].negate(), output[i]]);
    }
    for i in 0..m.min(b) {
        result.add_clause(&[input_b[i].negate(), output[i]]);
    }
    for i in 0..a {
        for j in 0..b {
            if i + j + 1 < m {
                result.add_clause(&[input_a[i].negate(), input_b[j].negate(), output[i + j + 1]]);
            }
        }
    }
    output
}
