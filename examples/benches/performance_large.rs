#![allow(unused_imports, dead_code)]

extern crate logicng;

use std::alloc::System;
use std::fs::File;
use std::io::{BufRead, BufReader};
use std::time::Instant;

use logicng::formulas::{EncodedFormula, FormulaFactory};
use logicng::operations::transformations::{CnfAlgorithm, CnfEncoder};
use logicng::solver::minisat::SolverCnfMethod::FullPgOnSolver;
use logicng::solver::minisat::sat::MiniSat2Solver;
use logicng::solver::minisat::{MiniSat, MiniSatConfig};

use crate::trallocator::Trallocator;

mod trallocator;

#[global_allocator]
static GLOBAL: Trallocator<System> = Trallocator::new(System);

#[allow(dead_code)]
const PRINT_PERFORMANCE: bool = true;
const PRINT_MEMORY: bool = true;

fn main() {
    GLOBAL.reset();
    GLOBAL.print_memory("Initial state");
    for file_name in ["large_formula.txt", "large_formula2.txt", "large_formula2-split.txt"] {
        let f = &FormulaFactory::new();
        GLOBAL.print_memory(&format!("[{file_name}] FF created"));

        GLOBAL.print_memory(&format!("[{file_name}] Parser created"));

        let start = Instant::now();
        let lines = read_file(file_name);
        if PRINT_PERFORMANCE {
            println!("[{}] File read: {:?}", file_name, start.elapsed());
        }
        GLOBAL.print_memory(&format!("[{file_name}] File read"));

        let start = Instant::now();
        let formulas = lines.iter().map(|l| f.parse(l).unwrap());
        if PRINT_PERFORMANCE {
            println!("[{}] Parse: {:?}", file_name, start.elapsed());
        }
        GLOBAL.print_memory(&format!("[{file_name}] Formulas parsed"));

        let start = Instant::now();
        let formula = f.and(formulas);
        if PRINT_PERFORMANCE {
            println!("[{}] Big And: {:?}", file_name, start.elapsed());
        }

        for _ in 0..1 {
            let mut minisat = MiniSat::from_config(MiniSatConfig::default().cnf_method(FullPgOnSolver));
            let start = Instant::now();
            minisat.add(formula, f);
            println!("{:?}", minisat.sat());
            if PRINT_PERFORMANCE {
                println!("[{}] PG on solver: {:?}", file_name, start.elapsed());
            }
            GLOBAL.print_memory(&format!("[{file_name}] CNF on solver created"));
        }
        GLOBAL.print_memory(&format!("[{file_name}] Solver dropped"));

        let start = Instant::now();
        let _cnf = CnfEncoder::new(CnfAlgorithm::Tseitin).transform(formula, f);
        if PRINT_PERFORMANCE {
            println!("[{}] Tseitin CNF: {:?}", file_name, start.elapsed());
        }
        GLOBAL.print_memory(&format!("[{file_name}] Tseitin created"));

        let start = Instant::now();
        let _cnf = CnfEncoder::new(CnfAlgorithm::PlaistedGreenbaum).transform(formula, f);
        if PRINT_PERFORMANCE {
            println!("[{}] PG CNF: {:?}", file_name, start.elapsed());
        }
        GLOBAL.print_memory(&format!("[{file_name}] PG created"));

        f.shrink_to_fit();
        GLOBAL.print_memory(&format!("[{file_name}] After shrink"));

        println!("Internal nodes: {}", _cnf.number_of_internal_nodes(f));
        println!("Formula Factory size: {}", f.number_of_cached_nodes());

        println!("{}", f.print_stats());
    }
    GLOBAL.print_memory("End");
}

fn read_file(file_name: &str) -> Vec<String> {
    let reader = BufReader::new(File::open(format!("resources/formulas/{file_name}")).unwrap());
    let lines: Vec<String> = reader.lines().map(|l| l.unwrap()).collect();
    lines
}
