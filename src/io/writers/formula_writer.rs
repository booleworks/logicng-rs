use std::fs::File;
use std::io;
use std::io::{BufWriter, Write};

use crate::formulas::{EncodedFormula, FormulaFactory};

/// Writes a `Formula` to a file. If the file already exists, its contents will be overridden.
///
/// If the formula is a conjunction, each of its operands will be written in a separate line.
///
/// If any error occurs when creating or writing the file, a respective [`io::Error`] is returned.
///
/// # Examples
///
/// If you run the following code:
///
/// ```no_run
/// # use logicng::formulas::{FormulaFactory, ToFormula};
/// # use logicng::io::write_formula;
/// let f = FormulaFactory::new();
/// let my_formula = "(A | B) & ~(C => A) & E".to_formula(&f);
/// write_formula("path/to/my-formula.txt", my_formula, &f).expect("Something went wrong");
/// ```
///
/// the contents of the file `path/to/my-formula.txt` will be as follows:
///
/// ```text
/// (A | B)
/// ~(C => A)
/// E
/// ```
pub fn write_formula(file_path: &str, formula: EncodedFormula, f: &FormulaFactory) -> io::Result<()> {
    let file = File::create(file_path)?;
    let mut writer = BufWriter::new(file);
    if formula.is_and() {
        for op in &*formula.operands(f) {
            writer.write_all(op.to_string(f).as_bytes())?;
            writer.write_all(b"\n")?;
        }
    } else {
        writer.write_all(formula.to_string(f).as_bytes())?;
    }
    writer.flush()
}
