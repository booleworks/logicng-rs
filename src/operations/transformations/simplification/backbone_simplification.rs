use crate::datastructures::Assignment;
use crate::formulas::{EncodedFormula, FormulaFactory, ToFormula};
use crate::solver::functions::BackboneConfig;
use crate::solver::functions::BackboneType::PositiveAndNegative;
use crate::solver::minisat::MiniSat;

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
pub fn backbone_simplification(formula: EncodedFormula, f: &FormulaFactory) -> EncodedFormula {
    f.caches.backbone_simps.get(formula).unwrap_or_else(|| {
        let mut solver = MiniSat::new();
        solver.add(formula, f);
        let backbone = BackboneConfig::new(formula.variables(f).iter().copied().collect())
            .backbone_type(PositiveAndNegative)
            .compute_backbone(&mut solver);
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
        result
    })
}

#[cfg(test)]
mod tests {
    use crate::formulas::{FormulaFactory, ToFormula};
    use crate::operations::transformations::simplification::backbone_simplification;

    #[test]
    fn test_trivial_backbones() {
        let f = &FormulaFactory::new();
        assert_eq!("$true".to_formula(f), backbone_simplification("$true".to_formula(f), f));
        assert_eq!("$false".to_formula(f), backbone_simplification("$false".to_formula(f), f));
        assert_eq!("$false".to_formula(f), backbone_simplification("A & (A => B) & ~B".to_formula(f), f));
        assert_eq!("A".to_formula(f), backbone_simplification("A".to_formula(f), f));
        assert_eq!("A & B".to_formula(f), backbone_simplification("A & B".to_formula(f), f));
        assert_eq!("A | B | C".to_formula(f), backbone_simplification("A | B | C".to_formula(f), f));
    }

    #[test]
    fn test_real_backbones() {
        let f = &FormulaFactory::new();
        assert_eq!("A & B".to_formula(f), backbone_simplification("A & B & (B | C)".to_formula(f), f));
        assert_eq!("A & B & C".to_formula(f), backbone_simplification("A & B & (~B | C)".to_formula(f), f));
        assert_eq!("A & B & C & F".to_formula(f), backbone_simplification("A & B & (~B | C) & (B | D) & (A => F)".to_formula(f), f));
        assert_eq!(
            "X & Y & (~B | C) & (B | D) & (A => F)".to_formula(f),
            backbone_simplification("X & Y & (~B | C) & (B | D) & (A => F)".to_formula(f), f)
        );
        assert_eq!("~A & ~B & D".to_formula(f), backbone_simplification("~A & ~B & (~B | C) & (B | D) & (A => F)".to_formula(f), f));
    }
}
