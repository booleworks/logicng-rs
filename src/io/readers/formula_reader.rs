use crate::formulas::{EncodedFormula, FormulaFactory};
use std::fs::File;
use std::io;
use std::io::{BufRead, BufReader};

/// Reads a `Formula` from a file using the given `FormulaFactory`.
///
/// If the file has multiple lines, the result will be the conjunction ([`FormulaFactory::and`])
/// of the formulas in each line.
///
/// If the file cannot be read or contains an invalid formula, a respective [`io::Error`] is returned.
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
pub fn read_formula(file_path: &str, f: &FormulaFactory) -> io::Result<EncodedFormula> {
    let reader = BufReader::new(File::open(file_path)?);
    let mut operands = Vec::new();
    for line in reader.lines() {
        let operand = f.parse(&line?).unwrap();
        operands.push(operand);
    }
    Ok(f.and(&operands))
}
