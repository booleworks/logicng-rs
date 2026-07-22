use crate::datastructures::Assignment;
use crate::errors::LngResult;
use crate::formulas::{EncodedFormula, FormulaFactory, ToFormula};
use crate::handlers::{CancelableResult, ComputationHandler, NopHandler};
use crate::solver::lng_core_solver::SatSolver;
use crate::solver::lng_core_solver::functions::BackboneType::PositiveAndNegative;

/// This function simplifies a formula by computing its backbone and
/// propagating it through the formula.
///
/// # Errors
///
/// Returns an error if the formula cannot be added to the SAT solver, for
/// example because CNF conversion fails.
///
/// # Example
///
/// Basic usage:
///
/// ```
/// # use logicng::formulas::FormulaFactory;
/// # use logicng::formulas::ToFormula;
/// # use logicng::operations::transformations::backbone_simplification;
/// let f = FormulaFactory::new();
///
/// let formula = "A & B & (A | B | C) & (~B | D)".to_formula(&f);
/// let simplified = backbone_simplification(formula, &f).unwrap();
///
/// assert_eq!(simplified.to_string(&f), "A & B & D");
/// ```
pub fn backbone_simplification(
    formula: EncodedFormula,
    f: &FormulaFactory,
) -> LngResult<EncodedFormula> {
    Ok(
        backbone_simplification_with_handler(formula, f, &mut NopHandler::new())?
            .result()
            .expect("nop handler can never abort"),
    )
}

/// Simplifies a formula by computing and propagating its backbone using a
/// cancelable computation handler.
///
/// # Errors
///
/// Returns an error if the formula cannot be added to the SAT solver, for
/// example because CNF conversion fails.
///
/// # Example
///
/// ```
/// # use logicng::formulas::{FormulaFactory, ToFormula};
/// # use logicng::handlers::NopHandler;
/// # use logicng::operations::transformations::backbone_simplification_with_handler;
/// let f = FormulaFactory::new();
/// let formula = "A & B & (A | B | C) & (~B | D)".to_formula(&f);
/// let simplified = backbone_simplification_with_handler(
///     formula,
///     &f,
///     &mut NopHandler::new(),
/// )
/// .unwrap()
/// .result()
/// .unwrap();
///
/// assert_eq!(simplified.to_string(&f), "A & B & D");
/// ```
pub fn backbone_simplification_with_handler(
    formula: EncodedFormula,
    f: &FormulaFactory,
    handler: &mut dyn ComputationHandler,
) -> LngResult<CancelableResult<EncodedFormula>> {
    match f.caches.backbone_simps.get(formula) {
        Some(c) => Ok(CancelableResult::Ok(c)),
        None => {
            let mut solver = SatSolver::<()>::new();
            solver.add_formula(formula, f)?;
            let variables = formula.variables(f);
            let result = solver
                .backbone_with_handler(variables.iter().copied(), PositiveAndNegative, handler)?
                .map(|backbone| {
                    if !backbone.sat {
                        f.falsum()
                    } else if !backbone.is_empty() {
                        let backbone_formula = backbone.to_formula(f);
                        let assignment = Assignment::from_set(backbone.complete_backbone());
                        let restricted_formula = f.restrict(formula, &assignment);
                        f.and([backbone_formula, restricted_formula])
                    } else {
                        formula
                    }
                });

            if f.config.caches.backbone_simps && result.is_success() {
                f.caches
                    .backbone_simps
                    .insert(formula, *result.result_ref().unwrap());
            }
            Ok(result)
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::formulas::{FormulaFactory, ToFormula};
    use crate::handlers::{ComputationHandler, LngComputation, LngEvent, NopHandler};
    use crate::operations::transformations::simplification::{
        backbone_simplification, backbone_simplification_with_handler,
    };

    struct CancelBackboneStart;

    impl ComputationHandler for CancelBackboneStart {
        fn should_resume(&mut self, event: LngEvent) -> bool {
            !matches!(
                event,
                LngEvent::ComputationStarted(LngComputation::Backbone)
            )
        }
    }

    #[test]
    fn test_trivial_backbones() {
        let f = &FormulaFactory::new();
        assert_eq!(
            "$true".to_formula(f),
            backbone_simplification("$true".to_formula(f), f).unwrap()
        );
        assert_eq!(
            "$false".to_formula(f),
            backbone_simplification("$false".to_formula(f), f).unwrap()
        );
        assert_eq!(
            "$false".to_formula(f),
            backbone_simplification("A & (A => B) & ~B".to_formula(f), f).unwrap()
        );
        assert_eq!(
            "A".to_formula(f),
            backbone_simplification("A".to_formula(f), f).unwrap()
        );
        assert_eq!(
            "A & B".to_formula(f),
            backbone_simplification("A & B".to_formula(f), f).unwrap()
        );
        assert_eq!(
            "A | B | C".to_formula(f),
            backbone_simplification("A | B | C".to_formula(f), f).unwrap()
        );
    }

    #[test]
    fn test_real_backbones() {
        let f = &FormulaFactory::new();
        assert_eq!(
            "A & B".to_formula(f),
            backbone_simplification("A & B & (B | C)".to_formula(f), f).unwrap()
        );
        assert_eq!(
            "A & B & C".to_formula(f),
            backbone_simplification("A & B & (~B | C)".to_formula(f), f).unwrap()
        );
        assert_eq!(
            "A & B & C & F".to_formula(f),
            backbone_simplification("A & B & (~B | C) & (B | D) & (A => F)".to_formula(f), f)
                .unwrap()
        );
        assert_eq!(
            "X & Y & (~B | C) & (B | D) & (A => F)".to_formula(f),
            backbone_simplification("X & Y & (~B | C) & (B | D) & (A => F)".to_formula(f), f)
                .unwrap()
        );
        assert_eq!(
            "~A & ~B & D".to_formula(f),
            backbone_simplification("~A & ~B & (~B | C) & (B | D) & (A => F)".to_formula(f), f)
                .unwrap()
        );
    }

    #[test]
    fn test_with_handler() {
        let f = FormulaFactory::new();
        let formula = "A & B & (~B | C)".to_formula(&f);
        let result =
            backbone_simplification_with_handler(formula, &f, &mut NopHandler::new()).unwrap();
        assert_eq!(result.result(), Some("A & B & C".to_formula(&f)));

        let uncached_f = FormulaFactory::new();
        let uncached_formula = "X & (Y | Z)".to_formula(&uncached_f);
        let canceled = backbone_simplification_with_handler(
            uncached_formula,
            &uncached_f,
            &mut CancelBackboneStart,
        )
        .unwrap();
        assert!(canceled.is_canceled());
        assert_eq!(uncached_f.caches.backbone_simps.len(), 0);

        let completed = backbone_simplification_with_handler(
            uncached_formula,
            &uncached_f,
            &mut NopHandler::new(),
        )
        .unwrap();
        assert!(completed.is_success());
        assert_eq!(uncached_f.caches.backbone_simps.len(), 1);
    }
}
