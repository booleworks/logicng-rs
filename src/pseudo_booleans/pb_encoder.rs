use std::sync::Arc;

use crate::errors::LngResult;
use crate::formulas::{EncodedFormula, FormulaFactory, FormulaType, Literal, PbConstraint};
use crate::pseudo_booleans::PbcError;
use crate::pseudo_booleans::pb_config::{PbAlgorithm, PbConfig};
use crate::util::exceptions::panic_unexpected_formula_type;

use super::{encode_adder_networks, encode_binary_merge, encode_swc};

/// An encoder for pseudo-boolean constraints.
#[derive(Clone, Default, Eq, PartialEq, Hash)]
pub struct PbEncoder {
    config: PbConfig,
}

impl PbEncoder {
    /// Constructs a new pseudo-boolean constraint encoder with a given
    /// configuration.
    pub const fn new(config: PbConfig) -> Self {
        Self { config }
    }

    /// Encodes a pseudo-boolean constraint and returns its CNF encoding.
    pub fn encode(&self, constraint: &PbConstraint, f: &FormulaFactory) -> LngResult<Arc<[EncodedFormula]>> {
        let normalized = constraint.normalize(f)?;
        match normalized.formula_type() {
            FormulaType::Pbc => {
                let pbc = normalized.as_pbc(f).unwrap();
                let enc = self.encode_internal(&pbc.literals, &pbc.coefficients, pbc.rhs, f)?;
                Ok(Arc::from(enc))
            }
            FormulaType::Cc => normalized.as_cc(f).unwrap().encode(f),
            FormulaType::And => {
                let operands = normalized.operands(f);
                let mut result = Vec::with_capacity(operands.len());
                for &op in &*operands {
                    match op.formula_type() {
                        FormulaType::Pbc => {
                            result.extend(self.encode(&op.as_pbc(f).unwrap(), f)?.iter().copied());
                        }
                        FormulaType::Cc => {
                            result.extend(op.as_cc(f).unwrap().encode(f)?.iter().copied());
                        }
                        _ => panic_unexpected_formula_type(op, Some(f)),
                    }
                }
                Ok(Arc::from(result))
            }
            FormulaType::True => Ok(Arc::new([])),
            FormulaType::False => Ok(Arc::new([f.falsum()])),
            _ => panic_unexpected_formula_type(normalized, Some(f)),
        }
    }

    fn encode_internal(&self, lits: &[Literal], coeffs: &[i64], rhs: i64, f: &FormulaFactory) -> LngResult<Vec<EncodedFormula>> {
        if rhs < 0 {
            return Ok(vec![f.falsum()]);
        }
        let original_rhs = rhs;
        let rhs: usize = rhs.try_into().map_err(|_| PbcError::TooLargeRhs { rhs })?;
        if rhs == usize::MAX {
            return Err(PbcError::TooLargeRhs { rhs: original_rhs }.into());
        }
        if rhs == 0 {
            Ok(lits.iter().map(|lit| EncodedFormula::from(lit.negate())).collect())
        } else {
            let mut simplified_lits = Vec::with_capacity(lits.len());
            let mut simplified_coeffs = Vec::with_capacity(coeffs.len());
            let mut result = Vec::new();
            for i in 0..lits.len() {
                let lit = lits[i];
                let coeff = coeffs[i];
                if coeff <= 0 {
                    return Err(PbcError::NormalizationOverflow { operation: "normalized coefficient is not positive" }.into());
                }
                let coeff: usize = coeff.try_into().map_err(|_| PbcError::TooLargeCoefficient { coefficient: coeff })?;
                if coeff <= rhs {
                    simplified_lits.push(lit);
                    simplified_coeffs.push(coeff);
                } else {
                    result.push(lit.negate().into());
                }
            }
            if simplified_lits.len() > 1 {
                result.extend(match self.config.pb_algorithm {
                    PbAlgorithm::Best | PbAlgorithm::Swc => encode_swc(&simplified_lits, &simplified_coeffs, rhs, f),
                    PbAlgorithm::BinaryMerge => encode_binary_merge(&self.config, simplified_lits, simplified_coeffs, rhs, f),
                    PbAlgorithm::AdderNetworks => encode_adder_networks(&simplified_lits, &simplified_coeffs, rhs, f),
                });
            }
            Ok(result)
        }
    }
}
