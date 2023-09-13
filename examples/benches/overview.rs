use std::fs;

use itertools::Itertools;
use logicng::formulas::{EncodedFormula, FormulaFactory};
use logicng::io::read_formula;
use logicng::knowledge_compilation::dnnf::{compile_dnnf, count};
use logicng::operations::transformations::{pure_expansion, AdvancedFactorizationConfig, CnfAlgorithm, CnfEncoder};
use logicng::solver::maxsat::{Algorithm, MaxSatSolver};
use logicng::solver::minisat::MiniSat;

fn main() {
    parse();
    parse();
    sat();
    model_counting();
    maximize_maxsat();
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
        let expanded = pure_expansion(formula, &f);
        let mut cnf_encoder =
            CnfEncoder::new(CnfAlgorithm::Advanced(AdvancedFactorizationConfig::default().fallback_algorithm(CnfAlgorithm::Tseitin)));
        let cnf_formula = cnf_encoder.transform(expanded, &f);
        let dnnf = compile_dnnf(cnf_formula, &f);
        count(&dnnf, &f);
    }
    println!("Rust Model Counting (Dnnf): {}s", start.elapsed().as_secs_f32());
}

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
            solver.add_soft_formula(1, EncodedFormula::from(var.pos_lit()), &f).unwrap();
        }
        let _res = solver.solve().unwrap();
    }
    println!("Rust Maximize MaxSAT: {}s", start.elapsed().as_secs_f32());
}
