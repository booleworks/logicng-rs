use logicng::formulas::{EncodedFormula, FormulaFactory, ToFormula};
use logicng::io::read_formula;
use logicng::solver::minisat::{MiniSat, MiniSatConfig, SolverCnfMethod};

fn main() {
    let f = FormulaFactory::new();
    let formula = read_formula("resources/formulas/large_formula2.txt", &f).unwrap();
    let cnf = f.cnf_of(formula);
    let form = formula.to_string(&f);
    println!("Start");
    onformula(&form);
    pgonsolver(&form);
    //fullpgonsolver(&form);
}

fn onformula(form: &str) {
    let f = FormulaFactory::new();
    let mut solver = MiniSat::from_config(MiniSatConfig::default().cnf_method(SolverCnfMethod::FactoryCnf));

    let cnf = form.to_formula(&f);
    //f.cnf_of(cnf); //add to cache

    let start = std::time::Instant::now();
    solver.add(cnf, &f);
    println!("FF: {}", start.elapsed().as_millis());

    solver = MiniSat::from_config(MiniSatConfig::default().cnf_method(SolverCnfMethod::FactoryCnf));
    let start = std::time::Instant::now();
    solver.add(cnf, &f);
    println!("FF: {}", start.elapsed().as_millis());
}

fn pgonsolver(form: &str) {
    let f = FormulaFactory::new();
    let mut solver = MiniSat::from_config(MiniSatConfig::default().cnf_method(SolverCnfMethod::PgOnSolver));

    let cnf = form.to_formula(&f);

    let start = std::time::Instant::now();
    solver.add(cnf, &f);
    println!("PG on solver: {}", start.elapsed().as_millis());

    let mut solver = MiniSat::from_config(MiniSatConfig::default().cnf_method(SolverCnfMethod::PgOnSolver));
    let start = std::time::Instant::now();
    solver.add(cnf, &f);
    println!("PG on solver: {}", start.elapsed().as_millis());
}

fn fullpgonsolver(form: &str) {
    let f = FormulaFactory::new();
    let mut solver = MiniSat::from_config(MiniSatConfig::default().cnf_method(SolverCnfMethod::FullPgOnSolver));

    let cnf = form.to_formula(&f);

    let start = std::time::Instant::now();
    solver.add(cnf, &f);
    println!("Full PG on solver: {}", start.elapsed().as_millis());
}
