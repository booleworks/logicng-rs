extern crate logicng;

use std::alloc::System;
use std::error::Error;

use logicng::formulas::FormulaFactory;
use logicng::io::read_formula;
use logicng::solver::functions::{enumerate_models_with_config, BackboneType, ModelEnumerationConfig};
use logicng::solver::minisat::MiniSat;

use crate::trallocator::Trallocator;

mod trallocator;

#[global_allocator]
static GLOBAL: Trallocator<System> = Trallocator::new(System);

#[allow(dead_code)]
const PRINT_PERFORMANCE: bool = true;
const PRINT_MEMORY: bool = false;

fn main() -> Result<(), Box<dyn Error>> {
    GLOBAL.reset();
    let f = FormulaFactory::new();
    let strings = [
        "v697", "v43", "v30", "v183", "v222", "v1", "v202", "v111", "v77", "v690", "v711", "v331", "v311", "v42", "v12", "v173", "v63",
        "v773", "v500", "v401", "v501", "v502", "v503",
    ];
    let vars = strings.map(|v| f.var(v));

    let t1 = std::time::Instant::now();
    let formula = read_formula("resources/formulas/large_formula2.txt", &f)?;
    GLOBAL.print_memory("read");
    let t2 = std::time::Instant::now();
    let mut solver = MiniSat::new();
    solver.add(formula, &f);
    GLOBAL.print_memory("add to solver");
    let t3 = std::time::Instant::now();
    solver.sat();
    GLOBAL.print_memory("solve");
    let t4 = std::time::Instant::now();
    let models = enumerate_models_with_config(&mut solver, &ModelEnumerationConfig::default().variables(vars));
    GLOBAL.print_memory("model enumeration");
    let t5 = std::time::Instant::now();
    let bb =
        solver.underlying_solver.compute_backbone(Vec::from_iter(formula.variables(&f).iter().copied()), BackboneType::PositiveAndNegative);
    GLOBAL.print_memory("backbone");
    let t6 = std::time::Instant::now();
    println!("{}", models.len());
    println!("{:?}", bb.positive_backbone.map(|b| b.len()));
    println!("{}ms", t2.duration_since(t1).as_millis());
    println!("{}ms", t3.duration_since(t2).as_millis());
    println!("{}ms", t4.duration_since(t3).as_millis());
    println!("{}ms", t5.duration_since(t4).as_millis());
    println!("{}ms", t6.duration_since(t5).as_millis());
    Ok(())
}
