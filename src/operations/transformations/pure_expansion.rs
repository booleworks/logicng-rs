use crate::cardinality_constraints::{AmoEncoder, CcConfig, CcEncoder};
use crate::formulas::{EncodedFormula, Formula, FormulaFactory, ToFormula};

const ENCODER: CcEncoder = CcEncoder::new(CcConfig::new().amo_encoder(AmoEncoder::Pure));

/// Transformation of a formula to a formula with expanded at-most-one and
/// exactly-one cardinality constraints. Each sub-formula of the formula that is
/// a pseudo-Boolean constraint of type AMO or EXO gets replaced by a pure
/// encoding such that the resulting formula is equivalent and free of
/// pseudo-Boolean constraints.
pub fn pure_expansion(formula: EncodedFormula, f: &FormulaFactory) -> EncodedFormula {
    match formula.unpack(f) {
        Formula::Pbc(_) => panic!("Pure encoding for a PBC of type other than AMO or EXO is currently not supported."),
        Formula::Cc(cc) => {
            if cc.is_amo() || cc.is_exo() {
                let mut enc = ENCODER.encode(cc, f);
                if cc.is_exo() {
                    enc.push(f.or(cc.variables.iter().map(|v| v.to_formula(f))));
                }
                f.and(&enc)
            } else {
                panic!("Pure encoding for a CC of type other than AMO or EXO is currently not supported.")
            }
        }
        Formula::Equiv((l, r)) => f.equivalence(pure_expansion(l, f), pure_expansion(r, f)),
        Formula::Impl((l, r)) => f.implication(pure_expansion(l, f), pure_expansion(r, f)),
        Formula::Or(ops) => f.or(ops.map(|op| pure_expansion(op, f))),
        Formula::And(ops) => f.and(ops.map(|op| pure_expansion(op, f))),
        Formula::Not(op) => f.not(pure_expansion(op, f)),
        Formula::True | Formula::False | Formula::Lit(_) => formula,
    }
}
