use std::cmp::Ordering;
use std::sync::Arc;

use crate::encodings::pseudo_booleans::pb_config::{PbAlgorithm, PbConfig};
use crate::formulas::{EncodedFormula, FormulaFactory, FormulaType, Literal, PbConstraint};
use crate::util::exceptions::panic_unexpected_formula_type;

use super::{encode_adder_networks, encode_binary_merge, encode_swc};

/// An encoder for pseudo-boolean constraints.
pub struct PbEncoder {
    config: PbConfig,
}

impl Default for PbEncoder {
    fn default() -> Self {
        Self { config: PbConfig::new() }
    }
}

impl PbEncoder {
    /// Constructs a new pseudo-boolean constraint encoder with a given
    /// configuration.
    pub const fn new(config: PbConfig) -> Self {
        Self { config }
    }

    /// Encodes a pseudo-boolean constraint and returns its CNF encoding.
    pub fn encode(&self, constraint: &PbConstraint, f: &FormulaFactory) -> Arc<[EncodedFormula]> {
        let normalized = constraint.normalize(f);
        match normalized.formula_type() {
            FormulaType::Pbc => {
                let pbc = normalized.as_pbc(f).unwrap();
                self.encode_internal(&pbc.literals, &pbc.coefficients, pbc.rhs, f).into()
            }
            FormulaType::Cc => normalized.as_cc(f).unwrap().encode(f),
            FormulaType::And => {
                let operands = normalized.operands(f);
                let mut result = Vec::with_capacity(operands.len());
                for &op in &*operands {
                    match op.formula_type() {
                        FormulaType::Pbc => {
                            result.extend(&mut self.encode(&op.as_pbc(f).unwrap(), f).iter());
                        }
                        FormulaType::Cc => {
                            result.extend(&mut op.as_cc(f).unwrap().encode(f).iter());
                        }
                        _ => panic_unexpected_formula_type(op, Some(f)),
                    }
                }
                result.into()
            }
            FormulaType::True => Arc::new([]),
            FormulaType::False => Arc::new([f.falsum()]),
            _ => panic_unexpected_formula_type(normalized, Some(f)),
        }
    }

    fn encode_internal(&self, lits: &[Literal], coeffs: &[i64], rhs: i64, f: &FormulaFactory) -> Vec<EncodedFormula> {
        match rhs.cmp(&0) {
            Ordering::Less => vec![f.falsum()],
            Ordering::Equal => lits.iter().map(|lit| EncodedFormula::from(lit.negate())).collect(),
            Ordering::Greater => {
                let mut simplified_lits = Vec::with_capacity(lits.len());
                let mut simplified_coeffs = Vec::with_capacity(coeffs.len());
                let mut result = Vec::new();
                for i in 0..lits.len() {
                    let lit = lits[i];
                    let coeff = coeffs[i];
                    if coeff <= rhs {
                        simplified_lits.push(lit);
                        simplified_coeffs.push(coeff);
                    } else {
                        result.push(lit.negate().into());
                    }
                }
                if simplified_lits.len() > 1 {
                    #[allow(clippy::cast_sign_loss)]
                    result.extend(match self.config.pb_algorithm {
                        PbAlgorithm::Best | PbAlgorithm::Swc => encode_swc(&simplified_lits, &simplified_coeffs, rhs as u64, f),
                        PbAlgorithm::BinaryMerge => encode_binary_merge(&self.config, simplified_lits, simplified_coeffs, rhs as u64, f),
                        PbAlgorithm::AdderNetworks => encode_adder_networks(&simplified_lits, &simplified_coeffs, rhs as u64, f),
                    });
                }
                result
            }
        }
    }
}
