use crate::formulas::{EncodedFormula, FormulaFactory};

mod assume_tests;
mod inc_dec_tests;
#[cfg(feature = "open_wbo")]
mod maxsat_tests;
mod sat_tests;

pub fn generate_pigeon_hole(n: usize, f: &FormulaFactory) -> EncodedFormula {
    generate_pigeon_hole_with_prefix(n, "v", f)
}

pub fn generate_pigeon_hole_with_prefix(n: usize, prefix: &str, f: &FormulaFactory) -> EncodedFormula {
    let some_hole = place_in_some_hole(n, prefix, f);
    let one_pigeon = only_one_pigeon_in_hole(n, prefix, f);
    f.and([some_hole, one_pigeon])
}

fn place_in_some_hole(n: usize, prefix: &str, f: &FormulaFactory) -> EncodedFormula {
    if n == 1 {
        let v1 = f.variable(&format!("{prefix}1"));
        let v2 = f.variable(&format!("{prefix}2"));
        f.and([v1, v2])
    } else {
        let mut ors = Vec::with_capacity(n + 1);
        for i in 1..=(n + 1) {
            let mut or_ops = Vec::with_capacity(n);
            for j in 1..=n {
                or_ops.push(f.variable(&format!("{prefix}{}", n * (i - 1) + j)));
            }
            ors.push(f.or(&or_ops));
        }
        f.and(&ors)
    }
}

fn only_one_pigeon_in_hole(n: usize, prefix: &str, f: &FormulaFactory) -> EncodedFormula {
    if n == 1 {
        let v1 = f.literal(&format!("{prefix}1"), false);
        let v2 = f.literal(&format!("{prefix}2"), false);
        f.and([v1, v2])
    } else {
        let mut ors = Vec::with_capacity(n + 1);
        for i in 1..=n {
            for j in 1..=n {
                for k in (j + 1)..=(n + 1) {
                    let v1 = f.literal(&format!("{prefix}{}", n * (j - 1) + i), false);
                    let v2 = f.literal(&format!("{prefix}{}", n * (k - 1) + i), false);
                    ors.push(f.or([v1, v2]));
                }
            }
        }
        f.and(&ors)
    }
}
