use std::path::Path;

use crate::errors::LngResult;
use crate::formulas::FormulaFactory;
use crate::io::{IoError, read_formula, write_formula};
use crate::operations::transformations::Anonymizer;

/// Anonymizes the formulas in a given file and saves it at `export_path`.
///
/// Anonymization replaces all variables names with `{var_prefix}1`,
/// `{var_prefix}2`, ... By doing so, the original semantics of the variable
/// names gets lost/obscured.
///
/// # Errors
///
/// Returns an error if either path is not valid UTF-8, if the input file cannot
/// be read or parsed, or if the output file cannot be written.
pub fn anonymize_file(path: &Path, export_path: &Path, var_prefix: &str) -> LngResult<()> {
    let f = FormulaFactory::new();
    let formula = read_formula(path_to_str(path)?, &f)?;
    let mut anon = Anonymizer::with_prefix(var_prefix, &f);
    let transformed = anon.anonymize(formula);
    write_formula(path_to_str(export_path)?, transformed, &f)
}

/// Anonymizes the formulas in a given file and saves it at `export_path`.
///
/// Anonymization replaces all variables names with `{var_prefix}1`,
/// `{var_prefix}2`, ... By doing so, the original semantics of the variable
/// names gets lost/obscured.
///
/// By passing an [`Anonymizer`], one can keep the relation of variables over multiple files.
///
/// # Errors
///
/// Returns an error if either path is not valid UTF-8, if the input file cannot
/// be read or parsed, or if the output file cannot be written.
pub fn anonymize_file_with_anonymizer(
    path: &Path,
    export_path: &Path,
    anonymizer: &mut Anonymizer,
) -> LngResult<()> {
    let formula = read_formula(path_to_str(path)?, anonymizer.factory)?;
    let transformed = anonymizer.anonymize(formula);
    write_formula(path_to_str(export_path)?, transformed, anonymizer.factory)
}

fn path_to_str(path: &Path) -> LngResult<&str> {
    path.to_str().ok_or_else(|| IoError::InvalidPath.into())
}
