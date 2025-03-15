use std::cmp::Ordering;
use std::sync::Arc;

use crate::datastructures::{EncodingResult, EncodingResultFF};
use crate::encodings::pseudo_booleans::pb_config::{PbAlgorithm, PbConfig};
use crate::encodings::CcEncoder;
use crate::formulas::{EncodedFormula, Formula, FormulaFactory, FormulaType, Literal, PbConstraint};
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
                let mut result = EncodingResultFF::new(f);
                self.encode_internal(&pbc.literals, &pbc.coefficients, pbc.rhs, &mut result);
                result.result.into()
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

    pub fn encode_on(&self, constraint: &PbConstraint, result: &mut dyn EncodingResult, f: &FormulaFactory) {
        let normalized = constraint.normalize(f);
        match normalized.unpack(f) {
            Formula::Pbc(pbc) => self.encode_internal(&pbc.literals, &pbc.coefficients, pbc.rhs, result),
            Formula::Cc(cc) => CcEncoder::default().encode_on(result, cc),
            Formula::And(operands) => {
                for op in operands {
                    match op.unpack(f) {
                        Formula::Pbc(pbc) => {
                            self.encode_internal(&pbc.literals, &pbc.coefficients, pbc.rhs, result);
                        }
                        Formula::Cc(cc) => {
                            CcEncoder::default().encode_on(result, cc);
                        }
                        _ => panic_unexpected_formula_type(op, Some(f)),
                    }
                }
            }
            Formula::True => {}
            Formula::False => result.add_clause_literals(&[]),
            _ => panic_unexpected_formula_type(normalized, Some(f)),
        }
    }

    fn encode_internal(&self, lits: &[Literal], coeffs: &[i64], rhs: i64, result: &mut dyn EncodingResult) {
        match rhs.cmp(&0) {
            Ordering::Less => result.add_clause_literals(&[]),
            Ordering::Equal => {
                for &lit in lits {
                    result.add_clause_literals(&[lit]);
                }
            }
            Ordering::Greater => {
                let mut simplified_lits = Vec::with_capacity(lits.len());
                let mut simplified_coeffs = Vec::with_capacity(coeffs.len());
                for i in 0..lits.len() {
                    let lit = lits[i];
                    let coeff = coeffs[i];
                    if coeff <= rhs {
                        simplified_lits.push(lit);
                        simplified_coeffs.push(coeff);
                    } else {
                        result.add_clause_literals(&[lit.negate()]);
                    }
                }
                if simplified_lits.len() > 1 {
                    #[allow(clippy::cast_sign_loss)]
                    match self.config.pb_algorithm {
                        PbAlgorithm::Best | PbAlgorithm::Swc => encode_swc(&simplified_lits, &simplified_coeffs, rhs as u64, result),
                        PbAlgorithm::BinaryMerge => {
                            encode_binary_merge(&self.config, simplified_lits, simplified_coeffs, rhs as u64, result);
                        }
                        PbAlgorithm::AdderNetworks => encode_adder_networks(&simplified_lits, &simplified_coeffs, rhs as u64, result),
                    };
                }
            }
        }
    }
}
