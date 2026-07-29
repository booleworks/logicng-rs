use crate::errors::LngResult;
use crate::formulas::{EncodedFormula, FormulaFactory};
use crate::io::IoError;
use crate::solver::maxsat::MaxSatSolver;
use std::fs::File;
use std::io::{BufRead, BufReader};

/// A soft clause and the cost incurred when it is not satisfied.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct WeightedClause {
    /// The positive weight of the clause.
    pub weight: u64,
    /// The clause formula.
    pub clause: EncodedFormula,
}

/// The intermediate representation of a MaxSAT instance read from WCNF.
///
/// The representation is independent of a particular MaxSAT backend. Add the
/// formulas in `hard_clauses` as hard formulas and the entries in
/// `soft_clauses` as weighted soft formulas to transfer it to a solver.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Wcnf {
    /// Clauses which must be satisfied.
    pub hard_clauses: Vec<EncodedFormula>,
    /// Clauses whose violation contributes to the objective.
    pub soft_clauses: Vec<WeightedClause>,
}

impl Wcnf {
    /// Adds all hard and soft clauses in this instance to a MaxSAT solver.
    ///
    /// # Errors
    ///
    /// Returns an error if the selected solver configuration rejects a clause,
    /// for example when weighted clauses are added to an unweighted algorithm.
    pub fn add_to_solver(&self, solver: &mut MaxSatSolver, f: &FormulaFactory) -> LngResult<()> {
        for &clause in &self.hard_clauses {
            solver.add_hard_formula(clause, f)?;
        }
        for weighted in &self.soft_clauses {
            solver.add_soft_formula(weighted.weight, weighted.clause, f)?;
        }
        Ok(())
    }
}

/// Reads a MaxSAT instance using `v` as the variable-name prefix.
///
/// This accepts both the current WCNF format (`h` for hard clauses and no
/// problem line) and the pre-2022 DIMACS-derived formats:
///
/// - `p cnf <variables> <clauses>`: every clause is soft with weight one,
/// - `p wcnf <variables> <clauses>`: every line starts with a soft weight,
/// - `p wcnf <variables> <clauses> <top>`: weight `top` denotes a hard clause.
///
/// Comments and empty lines may occur anywhere. Each clause must occupy one
/// line and end in `0`.
///
/// # Errors
///
/// Returns an error for I/O failures, malformed headers or clauses, zero
/// weights, out-of-range variables, and a clause count that disagrees with a
/// legacy problem line.
pub fn read_wcnf(file_path: &str, f: &FormulaFactory) -> LngResult<Wcnf> {
    read_wcnf_with_prefix(file_path, f, "v")
}

/// Reads a MaxSAT instance and prefixes every numeric variable with `prefix`.
///
/// See [`read_wcnf`] for the supported formats.
///
/// # Errors
///
/// Returns an error if the file cannot be read or is not valid WCNF.
pub fn read_wcnf_with_prefix(file_path: &str, f: &FormulaFactory, prefix: &str) -> LngResult<Wcnf> {
    let file = File::open(file_path).map_err(|err| IoError::OpenFile {
        path: file_path.to_string(),
        reason: err.to_string(),
    })?;
    parse_wcnf(BufReader::new(file), file_path, f, prefix)
}

#[derive(Clone, Copy)]
enum Format {
    Modern,
    Cnf,
    Wcnf { top: Option<u64> },
}

fn parse_wcnf<R: BufRead>(
    reader: R,
    path: &str,
    f: &FormulaFactory,
    prefix: &str,
) -> LngResult<Wcnf> {
    let mut result = Wcnf::default();
    let mut format = Format::Modern;
    let mut header: Option<(usize, usize)> = None;
    let mut clause_count = 0;
    let mut clauses_started = false;

    for (index, input) in reader.lines().enumerate() {
        let line_number = index + 1;
        let line = input.map_err(|err| IoError::ReadFile {
            path: path.to_string(),
            reason: err.to_string(),
        })?;
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with('c') {
            continue;
        }

        let tokens: Vec<_> = trimmed.split_whitespace().collect();
        if tokens.first() == Some(&"p") {
            if header.is_some() || clauses_started {
                return invalid(path, line_number, "problem line must precede all clauses");
            }
            let (parsed_format, variables, clauses) = parse_header(&tokens, path, line_number)?;
            format = parsed_format;
            header = Some((variables, clauses));
            continue;
        }

        clauses_started = true;
        clause_count += 1;
        let (hard, weight, literal_tokens) = match format {
            Format::Cnf => (false, 1, tokens.as_slice()),
            Format::Modern if tokens.first() == Some(&"h") => (true, 0, &tokens[1..]),
            Format::Modern => (
                false,
                parse_weight(tokens.first().copied(), path, line_number)?,
                &tokens[1..],
            ),
            Format::Wcnf { top: _ } if tokens.first() == Some(&"h") => (true, 0, &tokens[1..]),
            Format::Wcnf { top } => {
                let weight = parse_weight(tokens.first().copied(), path, line_number)?;
                if let Some(top) = top {
                    if weight > top {
                        return invalid(path, line_number, "clause weight exceeds top weight");
                    }
                    (weight == top, weight, &tokens[1..])
                } else {
                    (false, weight, &tokens[1..])
                }
            }
        };

        let variable_limit = header.map(|(variables, _)| variables);
        let clause = parse_clause(literal_tokens, path, line_number, variable_limit, f, prefix)?;
        if hard {
            result.hard_clauses.push(clause);
        } else {
            result.soft_clauses.push(WeightedClause { weight, clause });
        }
    }

    if let Some((_, expected)) = header {
        if clause_count != expected {
            return invalid(
                path,
                0,
                format!("problem line declares {expected} clauses, but found {clause_count}"),
            );
        }
    }
    Ok(result)
}

fn parse_header(tokens: &[&str], path: &str, line: usize) -> LngResult<(Format, usize, usize)> {
    if tokens.len() < 4 {
        return invalid(path, line, "incomplete problem line");
    }
    let variables = parse_usize(tokens[2], path, line, "variable count")?;
    let clauses = parse_usize(tokens[3], path, line, "clause count")?;
    match tokens[1] {
        "cnf" if tokens.len() == 4 => Ok((Format::Cnf, variables, clauses)),
        "wcnf" if tokens.len() == 4 => Ok((Format::Wcnf { top: None }, variables, clauses)),
        "wcnf" if tokens.len() == 5 => {
            let top = parse_weight(Some(tokens[4]), path, line)?;
            Ok((Format::Wcnf { top: Some(top) }, variables, clauses))
        }
        "cnf" => invalid(path, line, "a CNF problem line has exactly four fields"),
        "wcnf" => invalid(path, line, "a WCNF problem line has four or five fields"),
        kind => invalid(path, line, format!("unsupported problem type {kind:?}")),
    }
}

fn parse_clause(
    tokens: &[&str],
    path: &str,
    line: usize,
    variable_limit: Option<usize>,
    f: &FormulaFactory,
    prefix: &str,
) -> LngResult<EncodedFormula> {
    if tokens.last() != Some(&"0") {
        return invalid(path, line, "clause does not end with 0");
    }
    if tokens[..tokens.len() - 1].contains(&"0") {
        return invalid(path, line, "tokens follow the clause terminator");
    }

    let mut literals = Vec::with_capacity(tokens.len().saturating_sub(1));
    for token in &tokens[..tokens.len() - 1] {
        let literal = token.parse::<i64>().map_err(|_| IoError::InvalidWcnf {
            path: path.to_string(),
            line,
            reason: format!("invalid literal {token:?}"),
        })?;
        if literal == 0 || literal == i64::MIN {
            return invalid(path, line, format!("invalid literal {token:?}"));
        }
        let variable = literal.unsigned_abs();
        if variable_limit.is_some_and(|limit| variable > limit as u64) {
            return invalid(
                path,
                line,
                format!("variable {variable} exceeds the declared variable count"),
            );
        }
        literals.push(f.literal(&format!("{prefix}{variable}"), literal > 0));
    }
    Ok(f.or(literals))
}

fn parse_weight(token: Option<&str>, path: &str, line: usize) -> LngResult<u64> {
    let Some(token) = token else {
        return invalid(path, line, "missing clause weight");
    };
    let weight = token.parse::<u64>().map_err(|_| IoError::InvalidWcnf {
        path: path.to_string(),
        line,
        reason: format!("invalid clause weight {token:?}"),
    })?;
    if weight == 0 {
        return invalid(path, line, "clause weights must be positive");
    }
    Ok(weight)
}

fn parse_usize(token: &str, path: &str, line: usize, name: &str) -> LngResult<usize> {
    token.parse::<usize>().map_err(|_| {
        IoError::InvalidWcnf {
            path: path.to_string(),
            line,
            reason: format!("invalid {name} {token:?}"),
        }
        .into()
    })
}

fn invalid<T>(path: &str, line: usize, reason: impl Into<String>) -> LngResult<T> {
    Err(IoError::InvalidWcnf {
        path: path.to_string(),
        line,
        reason: reason.into(),
    }
    .into())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::formulas::ToFormula;
    use std::io::Cursor;

    fn parse(input: &str, f: &FormulaFactory) -> LngResult<Wcnf> {
        parse_wcnf(Cursor::new(input), "test.wcnf", f, "v")
    }

    #[test]
    fn reads_modern_wcnf() {
        let f = FormulaFactory::new();
        let wcnf = parse("c modern\nh 1 -2 0\n3 -1 0\n", &f).unwrap();
        assert_eq!(wcnf.hard_clauses, vec!["v1 | ~v2".to_formula(&f)]);
        assert_eq!(
            wcnf.soft_clauses,
            vec![WeightedClause {
                weight: 3,
                clause: "~v1".to_formula(&f)
            }]
        );
    }

    #[test]
    fn reads_all_legacy_flavours() {
        let f = FormulaFactory::new();
        let unweighted = parse("p cnf 2 2\n1 0\n-1 2 0\n", &f).unwrap();
        assert!(unweighted.hard_clauses.is_empty());
        assert_eq!(
            unweighted
                .soft_clauses
                .iter()
                .map(|c| c.weight)
                .collect::<Vec<_>>(),
            vec![1, 1]
        );

        let weighted = parse("p wcnf 2 2\n7 1 0\n2 -2 0\n", &f).unwrap();
        assert!(weighted.hard_clauses.is_empty());
        assert_eq!(
            weighted
                .soft_clauses
                .iter()
                .map(|c| c.weight)
                .collect::<Vec<_>>(),
            vec![7, 2]
        );

        let partial = parse("p wcnf 2 2 10\n10 1 0\n4 -1 2 0\n", &f).unwrap();
        assert_eq!(partial.hard_clauses, vec!["v1".to_formula(&f)]);
        assert_eq!(partial.soft_clauses[0].weight, 4);
    }

    #[test]
    fn rejects_malformed_input() {
        let f = FormulaFactory::new();
        assert!(parse("p wcnf 2 1 10\n11 1 0\n", &f).is_err());
        assert!(parse("p cnf 1 2\n1 0\n", &f).is_err());
        assert!(parse("h 1\n", &f).is_err());
        assert!(parse("1 2 0\n", &f).is_ok());
        assert!(parse("1 2 0 3\n", &f).is_err());
        assert!(parse("p cnf 1 1\n2 0\n", &f).is_err());
    }
}
