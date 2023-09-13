use std::io;
use std::path::Path;

use crate::formulas::FormulaFactory;
use crate::io::{read_formula, write_formula};
use crate::operations::transformations::Anonymizer;

/// Anonymizes the formulas in a given file and saves it at `export_path`.
///
/// Anonymization replaces all variables names with `{var_prefix}1`,
/// `{var_prefix}2`, ... By doing so, the original semantics of the variable
/// names gets lost/obscured.
pub fn anonymize_file(path: &Path, export_path: &Path, var_prefix: &str) -> io::Result<()> {
    let f = FormulaFactory::new();
    let formula = read_formula(path.to_str().unwrap(), &f)?;
    let mut anon = Anonymizer::with_prefix(var_prefix, &f);
    let transformed = anon.anonymize(formula);
    write_formula(export_path.to_str().unwrap(), transformed, &f)
}

/// Anonymizes the formulas in a given file and saves it at `export_path`.
///
/// Anonymization replaces all variables names with `{var_prefix}1`,
/// `{var_prefix}2`, ... By doing so, the original semantics of the variable
/// names gets lost/obscured.
///
/// By passing an [`Anonymizer`], one can keep the relation of variables over multiple files.
pub fn anonymize_file_with_anonymizer(path: &Path, export_path: &Path, anonymizer: &mut Anonymizer) -> io::Result<()> {
    let formula = read_formula(path.to_str().unwrap(), anonymizer.factory)?;
    let transformed = anonymizer.anonymize(formula);
    write_formula(export_path.to_str().unwrap(), transformed, anonymizer.factory)
}
