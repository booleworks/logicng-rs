use crate::cardinality_constraints::{AmoEncoder, CcConfig, CcEncoder};
use crate::errors::LngResult;
use crate::formulas::{EncodedFormula, Formula, FormulaFactory, ToFormula};
use crate::operations::OperationError;

const ENCODER: CcEncoder = CcEncoder::new(CcConfig::new().amo_encoder(AmoEncoder::Pure));

/// Transformation of a formula to a formula with expanded at-most-one and
/// exactly-one cardinality constraints. Each sub-formula of the formula that is
/// a pseudo-Boolean constraint of type AMO or EXO gets replaced by a pure
/// encoding such that the resulting formula is equivalent and free of
/// pseudo-Boolean constraints.
pub fn pure_expansion(formula: EncodedFormula, f: &FormulaFactory) -> LngResult<EncodedFormula> {
    match formula.unpack(f) {
        Formula::Pbc(_) => {
            return Err(OperationError::PureEncodingNoPbc.into());
        }
        Formula::Cc(cc) => {
            if cc.is_amo() || cc.is_exo() {
                let mut enc = ENCODER.encode(cc, f)?;
                if cc.is_exo() {
                    enc.push(f.or(cc.variables.iter().map(|v| v.to_formula(f))));
                }
                Ok(f.and(&enc))
            } else {
                return Err(OperationError::PureEncodingNoCc.into());
            }
        }
        Formula::Equiv((l, r)) => Ok(f.equivalence(pure_expansion(l, f)?, pure_expansion(r, f)?)),
        Formula::Impl((l, r)) => Ok(f.implication(pure_expansion(l, f)?, pure_expansion(r, f)?)),
        Formula::Or(ops) => Ok(f.or(ops.map(|op| pure_expansion(op, f)).collect::<Result<Vec<_>, _>>()?)),
        Formula::And(ops) => Ok(f.and(ops.map(|op| pure_expansion(op, f)).collect::<Result<Vec<_>, _>>()?)),
        Formula::Not(op) => Ok(f.not(pure_expansion(op, f)?)),
        Formula::True | Formula::False | Formula::Lit(_) => Ok(formula),
    }
}
