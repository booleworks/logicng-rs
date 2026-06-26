use crate::errors::LngResult;
use crate::formulas::operation_cache::OperationCache;
use crate::formulas::{EncodedFormula, Formula, FormulaFactory, NaryIterator};
use crate::handlers::{CancelableResult, ComputationHandler, LngComputation, LngEvent, NopHandler};

/// Constructs the _DNF_ of the given formula by using factorization.
pub fn factorization_dnf(formula: EncodedFormula, f: &FormulaFactory) -> LngResult<EncodedFormula> {
    factorization_dnf_with_handler(formula, f, &mut NopHandler {}).map(|r| r.result().expect("without handler a result is always present"))
}

/// Constructs the _DNF_ of the given formula by using factorization with a
/// custom handler.
pub fn factorization_dnf_with_handler(
    formula: EncodedFormula,
    f: &FormulaFactory,
    handler: &mut dyn ComputationHandler,
) -> LngResult<CancelableResult<EncodedFormula>> {
    if !handler.should_resume(LngEvent::ComputationStarted(LngComputation::Factorization)) {
        return Ok(CancelableResult::Canceled(LngEvent::ComputationStarted(LngComputation::Factorization)));
    }
    if f.config.caches.dnf {
        apply_rec(formula, f, handler, &mut None)
    } else {
        apply_rec(formula, f, handler, &mut Some(OperationCache::new()))
    }
    .into()
}

fn apply_rec(
    formula: EncodedFormula,
    f: &FormulaFactory,
    handler: &mut dyn ComputationHandler,
    local_cache: &mut Option<OperationCache<EncodedFormula>>,
) -> LngResult<CancelableResult<EncodedFormula>> {
    use Formula::{And, Cc, Equiv, False, Impl, Lit, Not, Or, Pbc, True};

    if let Some(lc) = local_cache
        && let Some(cached) = lc.get(formula)
    {
        return Ok(CancelableResult::Ok(cached));
    }

    if let Some(cached) = f.caches.dnf.get(formula) {
        return Ok(CancelableResult::Ok(cached));
    }

    let applied = match formula.unpack(f) {
        Lit(_) | True | False => Ok(CancelableResult::Ok(formula)),
        Pbc(_) | Cc(_) | Equiv(_) | Impl(_) | Not(_) => {
            let nnf = f.nnf_of(formula)?;
            apply_rec(nnf, f, handler, local_cache)
        }
        Or(ops) => handle_or(ops, f, handler, local_cache),
        And(ops) => handle_and(ops, f, handler, local_cache),
    };
    if let Ok(res) = &applied
        && let CancelableResult::Ok(result) = res
    {
        if f.config.caches.dnf {
            f.caches.dnf.insert(formula, *result);
        } else {
            local_cache.as_mut().unwrap().insert(formula, *result);
        }
        if f.config.caches.is_dnf {
            f.caches.is_dnf.insert(*result, true);
        }
    }
    applied
}

fn handle_or(
    operands: NaryIterator,
    f: &FormulaFactory,
    handler: &mut dyn ComputationHandler,
    local_cache: &mut Option<OperationCache<EncodedFormula>>,
) -> LngResult<CancelableResult<EncodedFormula>> {
    let nres = compute_nops(operands, f, handler, local_cache)?;
    match nres {
        CancelableResult::Ok(nops) => Ok(CancelableResult::Ok(f.or(nops))),
        CancelableResult::Canceled(e) | CancelableResult::Partial(_, e) => {
            return Ok(CancelableResult::Canceled(e));
        }
    }
}

fn handle_and(
    operands: NaryIterator,
    f: &FormulaFactory,
    handler: &mut dyn ComputationHandler,
    local_cache: &mut Option<OperationCache<EncodedFormula>>,
) -> LngResult<CancelableResult<EncodedFormula>> {
    let nres = compute_nops(operands, f, handler, local_cache)?;
    match nres {
        CancelableResult::Ok(nops) => {
            let mut result = *nops.first().unwrap();
            for &op in nops.iter().skip(1) {
                match distribute(result, op, f, handler) {
                    Ok(d) => result = d,
                    Err(e) => {
                        return Ok(CancelableResult::Canceled(e));
                    }
                }
            }
            Ok(CancelableResult::Ok(result))
        }
        CancelableResult::Canceled(e) | CancelableResult::Partial(_, e) => {
            return Ok(CancelableResult::Canceled(e));
        }
    }
}

fn compute_nops(
    operands: NaryIterator,
    f: &FormulaFactory,
    handler: &mut dyn ComputationHandler,
    local_cache: &mut Option<OperationCache<EncodedFormula>>,
) -> LngResult<CancelableResult<Vec<EncodedFormula>>> {
    let mut nops = Vec::with_capacity(operands.len());
    for op in operands {
        let applied = apply_rec(op, f, handler, local_cache)?;
        match applied {
            CancelableResult::Ok(a) => nops.push(a),
            CancelableResult::Canceled(e) | CancelableResult::Partial(_, e) => {
                return Ok(CancelableResult::Canceled(e));
            }
        }
    }
    Ok(CancelableResult::Ok(nops))
}

fn distribute(
    f1: EncodedFormula,
    f2: EncodedFormula,
    f: &FormulaFactory,
    handler: &mut dyn ComputationHandler,
) -> Result<EncodedFormula, LngEvent> {
    if !handler.should_resume(LngEvent::DistributionPerformed) {
        return Err(LngEvent::DistributionPerformed);
    }
    if f1.is_or() || f2.is_or() {
        let mut nops = Vec::new();
        let or = if f1.is_or() { f1 } else { f2 };
        let nor = if f1.is_or() { f2 } else { f1 };
        for &op in &*or.operands(f) {
            nops.push(distribute(op, nor, f, handler)?);
        }
        Ok(f.or(&nops))
    } else {
        let result = f.and([f1, f2]);
        if handler.should_resume(LngEvent::FactorizationCreatedClause(result)) {
            Ok(result)
        } else {
            Err(LngEvent::FactorizationCreatedClause(result))
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::operations::transformations::AdvancedFactorizationHandler;

    use super::*;

    #[test]
    fn test_constants() {
        test_dnf("$true", "$true");
        test_dnf("$false", "$false");
    }

    #[test]
    fn test_literals() {
        test_dnf("a", "a");
        test_dnf("~a", "~a");
    }

    #[test]
    fn test_binary_operators() {
        let f = &FormulaFactory::new();
        test_dnf("a => b", "~a | b");
        test_dnf("~a => ~b", "a | ~b");
        test_dnf("a & b => x | y", "~a | ~b | x | y");
        test_dnf("a <=> b", "(a & b) | (~a & ~b)");
        test_dnf("~a <=> ~b", "(a & b) | (~a & ~b)");
        assert!(factorization_dnf(f.parse("a => b").unwrap(), f).unwrap().is_dnf(f));
        assert!(factorization_dnf(f.parse("~a => ~b").unwrap(), f).unwrap().is_dnf(f));
        assert!(factorization_dnf(f.parse("a & b => x | y").unwrap(), f).unwrap().is_dnf(f));
        assert!(factorization_dnf(f.parse("a <=> b").unwrap(), f).unwrap().is_dnf(f));
        assert!(factorization_dnf(f.parse("~a <=> b").unwrap(), f).unwrap().is_dnf(f));
    }

    #[test]
    fn test_nary_operators() {
        let f = &FormulaFactory::new();
        test_dnf("a & b", "a & b");
        test_dnf("x | y", "x | y");
        test_dnf(
            "~(a | b) & c & ~(x & ~y) & (w => z)",
            "~w & ~x & ~a & ~b & c | z & ~x & ~a & ~b & c | ~w & y & ~a & ~b & c | z & y & ~a & ~b & c",
        );
        test_dnf("~(a & b) | c | ~(x | ~y)", "~a | ~b | c | ~x & y ");
        test_dnf("a & b & (~x | ~y)", "~x & a & b | ~y & a & b ");
        assert!(factorization_dnf(f.parse("a & b").unwrap(), f).unwrap().is_dnf(f));
        assert!(factorization_dnf(f.parse("x | y").unwrap(), f).unwrap().is_dnf(f));
        assert!(factorization_dnf(f.parse("~(a | b) & c & ~(x & ~y) & (w => z)").unwrap(), f,).unwrap().is_dnf(f));
        assert!(factorization_dnf(f.parse("~(a | b) & c & ~(x & ~y) & (w => z)").unwrap(), f,).unwrap().is_dnf(f));
        assert!(factorization_dnf(f.parse("~(a & b) | c | ~(x | ~y)").unwrap(), f).unwrap().is_dnf(f));
        assert!(factorization_dnf(f.parse("~(a & b) | c | ~(x | ~y)").unwrap(), f).unwrap().is_dnf(f));
        assert!(factorization_dnf(f.parse("a | b | (~x & ~y)").unwrap(), f).unwrap().is_dnf(f));
        assert!(factorization_dnf(f.parse("a | b | (~x & ~y)").unwrap(), f).unwrap().is_dnf(f));
    }

    #[test]
    fn test_not() {
        test_dnf("~a2", "~a2");
        test_dnf("~~a2", "a2");
        test_dnf("~(a2 => b2)", "a2 & ~b2");
        test_dnf("~(~(a2 | b2) => ~(x2 | y2))", "x2 & ~a2 & ~b2 | y2 & ~a2 & ~b2");
        test_dnf("~(a2 <=> b2)", "(a2 & ~b2) | (~a2 & b2)");
        test_dnf("~(~(a2 | b2) <=> ~(x2 | y2))", "~x2 & ~y2 & a2 | ~x2 & ~y2 & b2 | ~a2 & ~b2 & x2 | ~a2 & ~b2 & y2");
        test_dnf("~(a2 & b2 & ~x2 & ~y2)", "~a2 | ~b2 | x2 | y2");
        test_dnf("~(a2 | b2 | ~x2 | ~y2)", "~a2 & ~b2 & x2 & y2");
        test_dnf("~(a2 | b2 | ~x2 | ~y2)", "~a2 & ~b2 & x2 & y2");
    }

    #[test]
    fn test_with_handler() {
        let f = &FormulaFactory::new();

        let formula = f.parse("(~(~(a | b) => ~(x | y))) & ((a | x) => ~(b | y))").unwrap();
        let mut handler = AdvancedFactorizationHandler::new(Some(100), Some(2));
        let result = factorization_dnf_with_handler(formula, f, &mut handler).unwrap();
        assert!(result.is_canceled());
        assert!(handler.canceled());

        let mut handler = AdvancedFactorizationHandler::new(Some(100), Some(2));
        let formula = f.parse("~(a | b)").unwrap();
        let result = factorization_dnf_with_handler(formula, f, &mut handler).unwrap();
        assert!(result.is_success());
        assert!(!handler.canceled());

        let mut handler = AdvancedFactorizationHandler::new(Some(100), Some(100));
        let formula = f.parse("~(~(a2 | b2) <=> ~(x2 | y2))").unwrap();
        let result = factorization_dnf_with_handler(formula, f, &mut handler).unwrap();
        assert!(result.is_success());
        assert!(!handler.canceled());
        assert_eq!(handler.current_distribution(), 15);
        assert_eq!(handler.current_clause(), 10);
    }

    fn test_dnf(original: &str, expected: &str) {
        let f = &FormulaFactory::new();
        assert_eq!(factorization_dnf(f.parse(original).unwrap(), f).unwrap(), f.parse(expected).unwrap());
    }
}
