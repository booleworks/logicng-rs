use crate::formulas::operation_cache::OperationCache;
use crate::formulas::{EncodedFormula, Formula, FormulaFactory, NaryIterator};
use crate::handlers::{FactorizationError, FactorizationHandler, NopFactorizationHandler};

pub fn factorization_cnf(formula: EncodedFormula, f: &FormulaFactory) -> EncodedFormula {
    factorization_cnf_with_handler(formula, f, &mut NopFactorizationHandler {}).expect("Nop Handler never aborts.")
}

pub fn factorization_cnf_with_handler(
    formula: EncodedFormula,
    f: &FormulaFactory,
    handler: &mut dyn FactorizationHandler,
) -> Result<EncodedFormula, FactorizationError> {
    handler.started();
    if f.config.caches.factorization_cnf {
        apply_rec(formula, f, handler, &mut None)
    } else {
        apply_rec(formula, f, handler, &mut Some(OperationCache::new()))
    }
}

fn apply_rec(
    formula: EncodedFormula,
    f: &FormulaFactory,
    handler: &mut dyn FactorizationHandler,
    local_cache: &mut Option<OperationCache<EncodedFormula>>,
) -> Result<EncodedFormula, FactorizationError> {
    use Formula::{And, Cc, Equiv, False, Impl, Lit, Not, Or, Pbc, True};

    if let Some(lc) = local_cache {
        if let Some(cached) = lc.get(formula) {
            return Ok(cached);
        }
    }

    if let Some(cached) = f.caches.factorization_cnf.get(formula) {
        return Ok(cached);
    }

    match formula.unpack(f) {
        Lit(_) | True | False => Ok(formula),
        Pbc(_) | Cc(_) | Equiv(_) | Impl(_) | Not(_) => apply_rec(f.nnf_of(formula), f, handler, local_cache),
        Or(ops) => handle_or(ops, f, handler, local_cache),
        And(ops) => handle_and(ops, f, handler, local_cache),
    }
    .map(|result| {
        if f.config.caches.factorization_cnf {
            f.caches.factorization_cnf.insert(formula, result);
        } else {
            local_cache.as_mut().unwrap().insert(formula, result);
        }
        result
    })
}

fn handle_and(
    operands: NaryIterator,
    f: &FormulaFactory,
    handler: &mut dyn FactorizationHandler,
    local_cache: &mut Option<OperationCache<EncodedFormula>>,
) -> Result<EncodedFormula, FactorizationError> {
    compute_nops(operands, f, handler, local_cache).map(|nops| f.and(nops))
}

fn handle_or(
    operands: NaryIterator,
    f: &FormulaFactory,
    handler: &mut dyn FactorizationHandler,
    local_cache: &mut Option<OperationCache<EncodedFormula>>,
) -> Result<EncodedFormula, FactorizationError> {
    compute_nops(operands, f, handler, local_cache).and_then(|nops| {
        let mut result = *nops.get(0).unwrap();
        for &op in nops.iter().skip(1) {
            result = distribute(result, op, f, handler)?;
        }
        Ok(result)
    })
}

fn compute_nops(
    operands: NaryIterator,
    f: &FormulaFactory,
    handler: &mut dyn FactorizationHandler,
    local_cache: &mut Option<OperationCache<EncodedFormula>>,
) -> Result<Vec<EncodedFormula>, FactorizationError> {
    let mut nops = Vec::with_capacity(operands.len());
    for op in operands {
        nops.push(apply_rec(op, f, handler, local_cache)?);
    }
    Ok(nops)
}

fn distribute(
    f1: EncodedFormula,
    f2: EncodedFormula,
    f: &FormulaFactory,
    handler: &mut dyn FactorizationHandler,
) -> Result<EncodedFormula, FactorizationError> {
    handler.performed_distribution()?;
    if f1.is_and() || f2.is_and() {
        let (and, nand) = if f1.is_and() { (f1, f2) } else { (f2, f1) };
        let mut nops = Vec::new();
        for &op in &*and.operands(f) {
            nops.push(distribute(op, nand, f, handler)?);
        }
        Ok(f.and(&nops))
    } else {
        let result = f.or([f1, f2]);
        handler.created_clause(result).map(|_| result)
    }
}

#[cfg(test)]
mod tests {
    use std::fs::File;
    use std::io::{BufRead, BufReader};
    use std::time::Instant;

    use crate::handlers::ClauseLimitFactorizationHandler;

    use super::*;

    #[test]
    fn test_constants() {
        test_cnf("$true", "$true");
        test_cnf("$false", "$false");
    }

    #[test]
    fn test_literals() {
        test_cnf("a", "a");
        test_cnf("~a", "~a");
    }

    #[test]
    fn test_binary_operators() {
        let f = &FormulaFactory::new();
        test_cnf("a => b", "~a | b");
        test_cnf("~a => ~b", "a | ~b");
        test_cnf("a & b => x | y", "~a | ~b | x | y");
        test_cnf("a <=> b", "(a | ~b) & (~a | b)");
        test_cnf("~a <=> ~b", "(~a | b) & (a | ~b)");
        assert!(factorization_cnf(f.parse("a => b").unwrap(), f).is_cnf(f));
        assert!(factorization_cnf(f.parse("~a => ~b").unwrap(), f).is_cnf(f));
        assert!(factorization_cnf(f.parse("a & b => x | y").unwrap(), f).is_cnf(f));
        assert!(factorization_cnf(f.parse("a <=> b").unwrap(), f).is_cnf(f));
        assert!(factorization_cnf(f.parse("~a <=> b").unwrap(), f).is_cnf(f));
    }

    #[test]
    fn test_nary_operators() {
        let f = &FormulaFactory::new();
        test_cnf("a & b", "a & b");
        test_cnf("x | y", "x | y");
        test_cnf("~(a | b) & c & ~(x & ~y) & (w => z)", "~a & ~b & c & (~x | y) & (~w | z)");
        test_cnf("~(a & b) | c | ~(x | ~y)", "(~a | ~b | c | ~x) & (~a  | ~b | c | y)");
        test_cnf("a | b | (~x & ~y)", "(a | b | ~x) & (a | b | ~y)");
        assert!(factorization_cnf(f.parse("a & b").unwrap(), f).is_cnf(f));
        assert!(factorization_cnf(f.parse("x | y").unwrap(), f).is_cnf(f));
        assert!(factorization_cnf(f.parse("~(a | b) & c & ~(x & ~y) & (w => z)").unwrap(), f).is_cnf(f));
        assert!(factorization_cnf(f.parse("~(a | b) & c & ~(x & ~y) & (w => z)").unwrap(), f).is_cnf(f));
        assert!(factorization_cnf(f.parse("~(a & b) | c | ~(x | ~y)").unwrap(), f).is_cnf(f));
        assert!(factorization_cnf(f.parse("~(a & b) | c | ~(x | ~y)").unwrap(), f).is_cnf(f));
        assert!(factorization_cnf(f.parse("a | b | (~x & ~y)").unwrap(), f).is_cnf(f));
        assert!(factorization_cnf(f.parse("a | b | (~x & ~y)").unwrap(), f).is_cnf(f));
    }

    #[test]
    fn test_not() {
        test_cnf("~a2", "~a2");
        test_cnf("~~a2", "a2");
        test_cnf("~(a2 => b2)", "a2 & ~b2");
        test_cnf("~(~(a2 | b2) => ~(x2 | y2))", "~a2 & ~b2 & (x2 | y2)");
        test_cnf("~(a2 <=> b2)", "(~a2 | ~b2) & (a2 | b2)");
        test_cnf("~(~(a2 | b2) <=> ~(x2 | y2))", "(a2 | b2 | x2 | y2) & (~a2 | ~x2) & (~a2 | ~y2) & (~b2 | ~x2) & (~b2 | ~y2)");
        test_cnf("~(a2 & b2 & ~x2 & ~y2)", "~a2 | ~b2 | x2 | y2");
        test_cnf("~(a2 | b2 | ~x2 | ~y2)", "~a2 & ~b2 & x2 & y2");
        test_cnf("~(a2 | b2 | ~x2 | ~y2)", "~a2 & ~b2 & x2 & y2");
    }

    #[test]
    fn test_with_handler() {
        let f = &FormulaFactory::new();

        let formula = f.parse("(~(~(a | b) => ~(x | y))) & ((a | x) => ~(b | y))").unwrap();
        let mut handler = ClauseLimitFactorizationHandler::new(100, 2);
        let result = factorization_cnf_with_handler(formula, f, &mut handler);
        assert!(result.is_err());
        assert!(handler.aborted);

        let formula = f.parse("~(a | b)").unwrap();
        let result = factorization_cnf_with_handler(formula, f, &mut handler);
        assert!(result.is_ok());
        assert!(!handler.aborted);

        let mut handler = ClauseLimitFactorizationHandler::new(100, 100);
        let formula = f.parse("~(~(a2 | b2) <=> ~(x2 | y2))").unwrap();
        let result = factorization_cnf_with_handler(formula, f, &mut handler);
        assert!(result.is_ok());
        assert!(!handler.aborted);
        assert_eq!(handler.dists, 10);
        assert_eq!(handler.clauses, 7);
    }

    #[test]
    fn test_large_formula() {
        let file_name = "resources/formulas/large_formula.txt";
        let reader = BufReader::new(File::open(file_name).unwrap());
        let f = &FormulaFactory::new();
        let formulas: Vec<EncodedFormula> = reader.lines().map(|l| f.parse(&l.unwrap()).unwrap()).collect();
        let formula = f.and(formulas);
        let start = Instant::now();
        let cnf = factorization_cnf(formula, f);
        println!("{file_name}: {:?}", start.elapsed());
        assert!(cnf.is_cnf(f));
    }

    fn test_cnf(original: &str, expected: &str) {
        let f = &FormulaFactory::new();
        assert_eq!(factorization_cnf(f.parse(original).unwrap(), f), f.parse(expected).unwrap());
    }
}
