use std::fs;
use std::iter::zip;
use std::path::{Path, PathBuf};
use std::str::FromStr;

use num_bigint::BigUint;

use crate::formulas::{EncodedFormula, FormulaFactory, ToFormula};

const PATH: &str = "resources/model_count/";

pub fn read_normal(f: &FormulaFactory) -> Vec<(EncodedFormula, BigUint)> {
    read(&PathBuf::from(PATH).join("normal"), f)
}

pub fn read_cnf(f: &FormulaFactory) -> Vec<(EncodedFormula, BigUint)> {
    read(&PathBuf::from(PATH).join("cnfs"), f)
}


fn read(path: &Path, f: &FormulaFactory) -> Vec<(EncodedFormula, BigUint)> {
    let files = fs::read_dir(path).unwrap();
    let mut res = Vec::new();
    for file in files {
        let mut path = file.unwrap().path();
        if path.extension().unwrap().to_str() != Some("count") {
            let formulas = fs::read_to_string(&path).unwrap();
            path.set_extension("count");
            let counts = fs::read_to_string(&path).unwrap();
            res.extend(zip(formulas.lines().map(|form| form.to_formula(f)), counts.lines().map(|c| BigUint::from_str(c).unwrap())));
        }
    }
    res
}
