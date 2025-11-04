use std::fs;

use itertools::Itertools;
use logicng::formulas::FormulaFactory;
use logicng::io::read_formula;
use logicng::operations::functions::{ModelCountAlgorithm, count_models};
use logicng::solver::minisat::MiniSat;

#[cfg(feature = "open_wbo")]
use logicng::solver::maxsat::{Algorithm, MaxSatSolver};

fn main() {
    parse();
    parse();
    sat();
    model_counting();

    #[cfg(feature = "sharp_sat")]
    {
        model_counting_sharpsat();
    }

    #[cfg(feature = "open_wbo")]
    {
        maximize_maxsat();
    }
}

fn sat() {
    let f = FormulaFactory::new();
    let formulas = fs::read_dir("./resources/formula_suite_1/")
        .unwrap()
        .map(|p| read_formula(&String::from(p.unwrap().path().to_str().unwrap()), &f).unwrap())
        .collect_vec();

    let start = std::time::Instant::now();


    for formula in formulas {
        let mut solver = MiniSat::new();
        solver.add(formula, &f);
        let _ = solver.sat();
    }
    println!("Rust SAT: {}s", start.elapsed().as_secs_f32());
}

fn parse() {
    let f = FormulaFactory::new();
    let paths =
        fs::read_dir("./resources/formula_suite_1/").unwrap().map(|p| String::from(p.unwrap().path().to_str().unwrap())).collect_vec();

    let start = std::time::Instant::now();

    for path in paths {
        let _ = read_formula(&path, &f);
    }
    println!("Rust Parser: {}s", start.elapsed().as_secs_f32());
}

fn model_counting() {
    let f = FormulaFactory::new();
    let formulas = fs::read_dir("./resources/formula_suite_1/")
        .unwrap()
        .map(|p| read_formula(&String::from(p.unwrap().path().to_str().unwrap()), &f).unwrap())
        .collect_vec();

    let start = std::time::Instant::now();
    for formula in formulas {
        count_models(formula, ModelCountAlgorithm::Dnnf, &f);
    }
    println!("Rust Model Counting (Dnnf): {}s", start.elapsed().as_secs_f32());
}

#[cfg(feature = "sharp_sat")]
fn model_counting_sharpsat() {
    let f = FormulaFactory::new();
    let formulas = fs::read_dir("./resources/formula_suite_1/")
        .unwrap()
        .map(|p| read_formula(&String::from(p.unwrap().path().to_str().unwrap()), &f).unwrap())
        .collect_vec();

    let start = std::time::Instant::now();
    for formula in formulas {
        count_models(formula, ModelCountAlgorithm::SharpSat, &f);
    }
    println!("Rust Model Counting (SharpSAT): {}s", start.elapsed().as_secs_f32());
}

#[cfg(feature = "open_wbo")]
fn maximize_maxsat() {
    let f = FormulaFactory::new();
    let formulas = fs::read_dir("./resources/formula_suite_1/")
        .unwrap()
        .map(|p| read_formula(&String::from(p.unwrap().path().to_str().unwrap()), &f).unwrap())
        .collect_vec();

    let start = std::time::Instant::now();
    for formula in formulas {
        let variables = formula.variables(&f);
        let mut solver = MaxSatSolver::new(Algorithm::Oll).unwrap();
        solver.add_hard_formula(formula, &f).unwrap();
        for var in &*variables {
            solver.add_soft_formula(1, var.pos_lit().into(), &f).unwrap();
        }
        let _res = solver.solve().unwrap();
    }
    println!("Rust Maximize MaxSAT: {}s", start.elapsed().as_secs_f32());
}
