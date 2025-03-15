use crate::datastructures::Assignment;
use crate::formulas::{EncodedFormula, FormulaFactory, ToFormula};
use crate::handlers::{ComputationHandler, LngResult};
use crate::solver::lng_core_solver::functions::backbone_function::BackboneType;
use crate::solver::lng_core_solver::SatSolver;

/// This class simplifies a formula by computing its backbone and propagating it
/// through the formula.
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
/// let simplified = backbone_simplification(formula, &f);
///
/// assert_eq!(simplified.to_string(&f), "A & B & D");
/// ```
pub fn backbone_simplification(
    formula: EncodedFormula,
    f: &FormulaFactory,
    handler: &mut dyn ComputationHandler,
) -> LngResult<EncodedFormula> {
    if let Some(cached) = f.caches.backbone_simps.get(formula) {
        return LngResult::Ok(cached);
    }
    let mut solver = SatSolver::<()>::new();
    solver.add_formula(formula, f);
    let backbone_result = solver.backbone_with_handler(formula.variables(f).as_ref(), BackboneType::PositiveAndNegative, handler);
    match backbone_result {
        LngResult::Ok(backbone) => {
            let result = if !backbone.sat {
                f.falsum()
            } else if !backbone.is_empty() {
                let backbone_formula = backbone.to_formula(f);
                let assignment = Assignment::from_set(backbone.complete_backbone());
                let restricted_formula = f.restrict(formula, &assignment);
                f.and([backbone_formula, restricted_formula])
            } else {
                formula
            };

            if f.config.caches.backbone_simps {
                f.caches.backbone_simps.insert(formula, result);
            }
            LngResult::Ok(result)
        }
        LngResult::Canceled(lng_event) | LngResult::Partial(_, lng_event) => LngResult::Canceled(lng_event),
    }
}

#[cfg(test)]
mod tests {
    use crate::formulas::{FormulaFactory, ToFormula};
    use crate::handlers::NopHandler;
    use crate::operations::transformations::simplification::backbone_simplification;

    #[test]
    fn test_trivial_backbones() {
        let f = &FormulaFactory::new();
        assert_eq!("$true".to_formula(f), backbone_simplification("$true".to_formula(f), f, &mut NopHandler::new()).result().unwrap());
        assert_eq!("$false".to_formula(f), backbone_simplification("$false".to_formula(f), f, &mut NopHandler::new()).result().unwrap());
        assert_eq!(
            "$false".to_formula(f),
            backbone_simplification("A & (A => B) & ~B".to_formula(f), f, &mut NopHandler::new()).result().unwrap()
        );
        assert_eq!("A".to_formula(f), backbone_simplification("A".to_formula(f), f, &mut NopHandler::new()).result().unwrap());
        assert_eq!("A & B".to_formula(f), backbone_simplification("A & B".to_formula(f), f, &mut NopHandler::new()).result().unwrap());
        assert_eq!(
            "A | B | C".to_formula(f),
            backbone_simplification("A | B | C".to_formula(f), f, &mut NopHandler::new()).result().unwrap()
        );
    }

    #[test]
    fn test_real_backbones() {
        let f = &FormulaFactory::new();
        assert_eq!(
            "A & B".to_formula(f),
            backbone_simplification("A & B & (B | C)".to_formula(f), f, &mut NopHandler::new()).result().unwrap()
        );
        assert_eq!(
            "A & B & C".to_formula(f),
            backbone_simplification("A & B & (~B | C)".to_formula(f), f, &mut NopHandler::new()).result().unwrap()
        );
        assert_eq!(
            "A & B & C & F".to_formula(f),
            backbone_simplification("A & B & (~B | C) & (B | D) & (A => F)".to_formula(f), f, &mut NopHandler::new()).result().unwrap()
        );
        assert_eq!(
            "X & Y & (~B | C) & (B | D) & (A => F)".to_formula(f),
            backbone_simplification("X & Y & (~B | C) & (B | D) & (A => F)".to_formula(f), f, &mut NopHandler::new()).result().unwrap()
        );
        assert_eq!(
            "~A & ~B & D".to_formula(f),
            backbone_simplification("~A & ~B & (~B | C) & (B | D) & (A => F)".to_formula(f), f, &mut NopHandler::new()).result().unwrap()
        );
    }
}
