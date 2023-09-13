use crate::formulas::{EncodedFormula, FormulaFactory};

pub fn panic_unexpected_formula_type(formula: EncodedFormula, f: Option<&FormulaFactory>) -> ! {
    f.map_or_else(
        || {
            panic!("Unexpected formula type: {formula:?}");
        },
        |f| {
            panic!("Unexpected formula type: {}", formula.to_string(f));
        },
    )
}
