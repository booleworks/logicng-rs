use crate::errors::LngResult;
use crate::formulas::{EncodedFormula, FormulaFactory};
use crate::io::IoError;
use std::fs::File;
use std::io::{BufRead, BufReader};

/// Reads a `Formula` from a file using the given `FormulaFactory`.
///
/// If the file has multiple lines, the result will be the conjunction ([`FormulaFactory::and`])
/// of the formulas in each line.
///
/// # Errors
///
/// Returns an error if the file cannot be opened or read, or if one of its
/// lines cannot be parsed as a formula.
///
/// # Examples
///
/// Assume there is a file `path/to/my-formula.txt` with the contents:
/// ```text
/// (A | B)
/// ~(C => A)
/// E
/// ```
///
/// ```no_run
/// # use logicng::formulas::{FormulaFactory, ToFormula};
/// # use logicng::io::read_formula;
/// let f = FormulaFactory::new();
/// let my_formula = read_formula("path/to/my-formula.txt", &f).expect("Something went wrong");
/// let expected = "(A | B) & ~(C => A) & E".to_formula(&f);
/// assert_eq!(my_formula, expected)
/// ```
pub fn read_formula(file_path: &str, f: &FormulaFactory) -> LngResult<EncodedFormula> {
    let reader = BufReader::new(File::open(file_path).map_err(|err| IoError::OpenFile {
        path: file_path.to_string(),
        reason: err.to_string(),
    })?);
    let mut operands = Vec::new();
    for (line_number, line) in reader.lines().enumerate() {
        let line = line.map_err(|err| IoError::ReadFile {
            path: file_path.to_string(),
            reason: err.to_string(),
        })?;
        let operand = f.parse(&line).map_err(|err| IoError::InvalidFormula {
            path: file_path.to_string(),
            line: line_number + 1,
            reason: err.to_string(),
        })?;
        operands.push(operand);
    }
    Ok(f.and(&operands))
}
