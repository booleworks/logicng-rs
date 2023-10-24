extern crate logicng;

use std::collections::HashMap;
use std::fs::File;
use std::io::{stdout, BufRead, BufReader, Error, Write};
use std::iter::FromIterator;
use std::path::{Path, PathBuf};

use logicng::formulas::Variable;
use logicng::solver::minisat::sat::Tristate::True;
use logicng::solver::minisat::sat::{mk_lit, MiniSat2Solver};

#[test]
#[cfg_attr(not(feature = "long_running_tests"), ignore)]
fn main() {
    let path = format!("{}/{}/{}", env!("CARGO_MANIFEST_DIR"), "resources", "sat");
    let files = read_files(Path::new(&path));

    let result = read_result();

    for file in files.unwrap() {
        let expected_result = result.get(&file.name).unwrap();
        test_file(file, *expected_result);
    }
}

fn read_result() -> HashMap<String, bool> {
    let path = format!("{}/{}/{}/{}", env!("CARGO_MANIFEST_DIR"), "resources", "sat", "results.txt");
    let file = File::open(PathBuf::from(path)).expect("Could not open result file");
    let mut result: HashMap<String, bool> = HashMap::new();
    for line in BufReader::new(file).lines() {
        match line {
            Ok(line) if !line.trim().is_empty() => {
                let split: Vec<&str> = line.split(';').collect();
                result.insert(split[0].into(), split[1].parse().unwrap());
            }
            _ => {}
        }
    }
    result
}

fn test_file(file: DimacsFile, expected: bool) {
    println!("Processing file: {}", file.name);
    stdout().flush().unwrap();
    let mut solver: MiniSat2Solver<()> = MiniSat2Solver::new();
    for v in 1..(file.max_var + 1) {
        let index = solver.new_var(true, true);
        solver.add_variable(Variable::from_index(v as u64), index);
    }
    for clause in file.clauses {
        solver.add_clause(
            clause
                .iter()
                .map(|v| mk_lit(solver.idx_for_variable(Variable::from_index(v.unsigned_abs() as u64)).unwrap(), v.is_negative()))
                .collect(),
            None,
        );
    }
    let result = solver.solve();
    println!("{:?}{}", result, if (result == True) == expected { "" } else { "  <-- ERROR" });
    if expected != (result == True) {
        panic!("unexpected result!");
    }
}

fn read_files(path: &Path) -> Result<Vec<DimacsFile>, Error> {
    let mut files: Vec<DimacsFile> = Vec::new();
    for file in path.read_dir()? {
        let file = file?.path();
        if file.is_file() && file.extension().map(|s| s.to_str().unwrap_or("")).unwrap_or("") == "cnf" {
            files.push(read_single_file(&file)?);
        }
    }
    Ok(files)
}

fn read_single_file(path: &PathBuf) -> Result<DimacsFile, Error> {
    println!("Reading file {}", path.file_name().unwrap().to_str().unwrap());
    let file = File::open(path)?;
    let mut clauses: Vec<Vec<isize>> = Vec::new();
    let mut max_var: usize = 0;
    for line in BufReader::new(file).lines() {
        match line {
            Ok(line) if !line.is_empty() => {
                let split: Vec<&str> = line.split_whitespace().collect();
                match split[0] {
                    "c" => (),
                    "p" => {
                        clauses.reserve(split[3].parse().unwrap());
                        max_var = split[2].parse().unwrap();
                    }
                    _ => clauses.push(Vec::<isize>::from_iter(split[0..split.len() - 1].iter().map(|x| x.parse().unwrap()))),
                }
            }
            _ => (),
        }
    }
    Ok(DimacsFile { name: path.file_name().unwrap().to_str().unwrap().into(), clauses, max_var })
}

struct DimacsFile {
    name: String,
    clauses: Vec<Vec<isize>>,
    max_var: usize,
}
