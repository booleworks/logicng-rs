use crate::formulas::{EncodedFormula, FormulaFactory};
use regex::Regex;
use std::fs::File;
use std::io;
use std::io::{BufRead, BufReader};

/// Reads a DIMACS CNF file with the variable prefix `v`.
///
/// See also [`read_cnf_with_prefix`]
pub fn read_cnf(file_path: &str, f: &FormulaFactory) -> io::Result<Vec<EncodedFormula>> {
    read_cnf_with_prefix(file_path, f, "v")
}

/// A reader for DIMACS CNF files.
///
/// This reader reads all the clauses and variables - independent of the numbers given in the prefix. Also, it assumes
/// that every clause is in its own line and ends with '0'. Comments are only allowed if the lines start with 'c'. No
/// C style comments are supported (yes, we have actually seen these in DIMACS files).
///
/// All variable indices will be prefixed with the given `prefix`. Note that this prefix should not be empty since
/// variable names which consist only of digits may cause problems if you print the formula and then parse it again
/// with the standard parser.
/// If you don't care about the prefix, you can just use [`read_cnf`] which uses `v` as default prefix.
///
/// The result of the method is the list of clauses read from the DIMACS file. If there was a problem reading the file,
/// a respective [`io::Error`] is returned.
///
/// # Example
///
/// Assume there is the following DIMACS CNF file at `path/to/formula.cnf` with the contents:
///
/// ```text
/// c Some description
/// p cnf 5 3
/// -4 1 3 0
/// 2 -1 5 4 0
/// -3 0
/// ```
///
/// ```no_run
/// # use logicng::formulas::{FormulaFactory, ToFormula};
/// # use logicng::io::read_cnf_with_prefix;
/// let f = FormulaFactory::new();
/// let clauses = read_cnf_with_prefix("path/to/formula.cnf", &f, "v").expect("Could not read the file");
/// let expected = vec![
///   "~v4 | v1 | v3".to_formula(&f),
///   "v2 | ~v1 | v5 | v4".to_formula(&f),
///   "~v3".to_formula(&f),
/// ];
/// assert_eq!(clauses, expected);
/// ```
pub fn read_cnf_with_prefix(file_path: &str, f: &FormulaFactory, prefix: &str) -> io::Result<Vec<EncodedFormula>> {
    let mut result = Vec::new();

    let file = File::open(file_path)?;
    let reader = BufReader::new(file);
    for l in reader.lines() {
        let line = l?;
        if !line.starts_with('c') && !line.starts_with('p') && !line.trim().is_empty() {
            let split: Vec<&str> = Regex::new(r"[ \t]+").unwrap().split(&line).collect();
            assert_eq!(*split.last().unwrap(), "0", "Line {line} did not end with 0.");
            let vars = split
                .iter()
                .take(split.len() - 1)
                .map(|&lit| lit.trim())
                .filter(|&lit| !lit.is_empty())
                .map(|lit| {
                    lit.strip_prefix('-')
                        .map_or_else(|| f.variable(&format!("{prefix}{lit}")), |stripped| f.literal(&format!("{prefix}{stripped}"), false))
                })
                .collect::<Box<[_]>>();
            result.push(f.or(&vars));
        }
    }
    Ok(result)
}
