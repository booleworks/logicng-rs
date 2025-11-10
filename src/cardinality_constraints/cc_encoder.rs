#![allow(clippy::cast_possible_truncation, clippy::cast_sign_loss, clippy::cast_precision_loss, clippy::unused_self)]

use crate::cardinality_constraints::cc_config::{AlkEncoder, AmkEncoder, AmoEncoder, BimanderGroupSize, CcConfig, ExkEncoder};
use crate::cardinality_constraints::cc_incremental_data::CcIncrementalData;
use crate::datastructures::{EncodingResult, EncodingResultFF};
use crate::formulas::{CType, CardinalityConstraint, EncodedFormula, FormulaFactory, Literal, Variable};

use super::{
    build_amo_bimander, build_amo_binary, build_amo_commander, build_amo_ladder, build_amo_nested, build_amo_product, build_amo_pure,
    cc_cardinality_networks, cc_modular_totalizer, cc_totalizer,
};

/// An encoder for cardinality constraints.
#[derive(Clone, Default)]
pub struct CcEncoder {
    config: CcConfig,
}

impl CcEncoder {
    /// Constructs a new cardinality constraint encoder with a given configuration.
    pub const fn new(config: CcConfig) -> Self {
        Self { config }
    }

    /// Encodes a cardinality constraint and returns its CNF encoding.
    pub fn encode(&self, cc: &CardinalityConstraint, f: &FormulaFactory) -> Vec<EncodedFormula> {
        let mut result = EncodingResultFF::new(f);
        self.encode_on(&mut result, cc);
        result.result
    }

    /// Encodes a cardinality constraint in a given result.
    pub fn encode_on<R: EncodingResult>(&self, result: &mut R, cc: &CardinalityConstraint) {
        self.encode_constraint(cc, result);
    }

    /// Encodes an incremental cardinality constraint and returns its encoding.
    pub fn encode_incremental(&self, cc: &CardinalityConstraint, f: &FormulaFactory) -> (Vec<EncodedFormula>, Option<CcIncrementalData>) {
        let mut result = EncodingResultFF::new(f);
        let inc = self.encode_incremental_on(&mut result, cc);
        (result.result, inc)
    }

    /// Encodes an incremental cardinality constraint in a given result.
    pub fn encode_incremental_on(&self, result: &mut dyn EncodingResult, cc: &CardinalityConstraint) -> Option<CcIncrementalData> {
        self.encode_incremental_constraint(cc, result)
    }

    fn encode_constraint<R: EncodingResult>(&self, cc: &CardinalityConstraint, result: &mut R) {
        let rhs = cc
            .rhs
            .try_into()
            .unwrap_or_else(|_| panic!("Can only encode CCs with right-hand-sides up to {} on this architecture", usize::MAX));
        match cc.comparator {
            CType::LE => {
                if cc.rhs == 1 {
                    self.amo(result, &cc.variables);
                } else {
                    self.amk(result, &cc.variables, rhs, false);
                }
            }
            CType::LT => {
                if rhs == 2 {
                    self.amo(result, &cc.variables);
                } else {
                    self.amk(result, &cc.variables, rhs - 1, false);
                }
            }
            CType::GE => {
                self.alk(result, &cc.variables, rhs, false);
            }
            CType::GT => {
                self.alk(result, &cc.variables, rhs + 1, false);
            }
            CType::EQ => {
                if rhs == 1 {
                    self.exo(result, &cc.variables);
                } else {
                    self.exk(result, &cc.variables, rhs);
                }
            }
        }
    }

    fn encode_incremental_constraint(&self, cc: &CardinalityConstraint, result: &mut dyn EncodingResult) -> Option<CcIncrementalData> {
        let rhs = cc
            .rhs
            .try_into()
            .unwrap_or_else(|_| panic!("Can only encode CCs with right-hand-sides up to {} on this architecture", usize::MAX));
        match cc.comparator {
            CType::LE => self.amk(result, &cc.variables, rhs, true),
            CType::LT => self.amk(result, &cc.variables, rhs - 1, true),
            CType::GE => self.alk(result, &cc.variables, rhs, true),
            CType::GT => self.alk(result, &cc.variables, rhs + 1, true),
            CType::EQ => panic!("Incremental encodings are only supported for at-most-k and at-least k constraints."),
        }
    }

    fn amo<R: EncodingResult>(&self, result: &mut R, vars: &[Variable]) {
        if vars.len() <= 1 {
            // there is no constraint
        } else {
            match self.config.amo_encoder {
                AmoEncoder::Pure => build_amo_pure(result, vars),
                AmoEncoder::Ladder => build_amo_ladder(result, vars),
                AmoEncoder::Product { recursive_bound } => build_amo_product(recursive_bound, result, vars),
                AmoEncoder::Nested { group_size } => build_amo_nested(group_size, result, vars),
                AmoEncoder::Commander { group_size } => build_amo_commander(group_size, result, vars),
                AmoEncoder::Binary => build_amo_binary(result, vars),
                AmoEncoder::Bimander { group_size } => {
                    let group_size = match group_size {
                        BimanderGroupSize::Fixed(gs) => gs,
                        BimanderGroupSize::Half => vars.len() / 2,
                        BimanderGroupSize::Sqrt => (vars.len() as f64).sqrt() as usize,
                    };
                    build_amo_bimander(group_size, result, vars);
                }
                AmoEncoder::Best => {
                    if vars.len() <= 10 {
                        build_amo_pure(result, vars);
                    } else {
                        build_amo_product(CcConfig::DEFAULT_PRODUCT_RECURSIVE_BOUND, result, vars);
                    }
                }
            }
        }
    }

    fn amk(&self, result: &mut dyn EncodingResult, vars: &[Variable], rhs: usize, with_inc: bool) -> Option<CcIncrementalData> {
        if rhs >= vars.len() {
            // there is no constraint
            None
        } else if rhs == 0 {
            // no variable can be true
            for v in vars {
                result.add_clause(&[v.neg_lit()]);
            }
            None
        } else {
            match self.config.amk_encoder {
                AmkEncoder::Totalizer => cc_totalizer::build_amk(result, vars, rhs, with_inc),
                AmkEncoder::ModularTotalizer | AmkEncoder::Best => cc_modular_totalizer::build_amk(result, vars, rhs, with_inc),
                AmkEncoder::CardinalityNetwork => cc_cardinality_networks::build_amk(result, vars, rhs, with_inc),
            }
        }
    }

    fn alk(&self, result: &mut dyn EncodingResult, vars: &[Variable], rhs: usize, with_inc: bool) -> Option<CcIncrementalData> {
        if rhs > vars.len() {
            result.add_clause(&Vec::new());
            None
        } else if rhs == 0 {
            // there is no constraint
            None
        } else if rhs == 1 {
            result.add_clause(&vars.iter().map(Variable::pos_lit).collect::<Vec<Literal>>());
            None
        } else if rhs == vars.len() {
            for v in vars {
                result.add_clause(&[v.pos_lit()]);
            }
            None
        } else {
            match self.config.alk_encoder {
                AlkEncoder::Totalizer => cc_totalizer::build_alk(result, vars, rhs, with_inc),
                AlkEncoder::ModularTotalizer | AlkEncoder::Best => cc_modular_totalizer::build_alk(result, vars, rhs, with_inc),
                AlkEncoder::CardinalityNetwork => cc_cardinality_networks::build_alk(result, vars, rhs, with_inc),
            }
        }
    }

    fn exo<R: EncodingResult>(&self, result: &mut R, vars: &[Variable]) {
        if vars.is_empty() {
            result.add_clause(&Vec::new());
        } else if vars.len() == 1 {
            result.add_clause(&[vars[0].pos_lit()]);
        } else {
            let lits: Vec<Literal> = vars.iter().map(Variable::pos_lit).collect();
            self.amo(result, vars);
            result.add_clause(&lits);
        }
    }

    fn exk<R: EncodingResult>(&self, result: &mut R, vars: &[Variable], rhs: usize) {
        if rhs > vars.len() {
            result.add_clause(&Vec::new());
        } else if rhs == 0 {
            for var in vars {
                result.add_clause(&[var.neg_lit()]);
            }
        } else if rhs == vars.len() {
            for var in vars {
                result.add_clause(&[var.pos_lit()]);
            }
        } else {
            match self.config.exk_encoder {
                ExkEncoder::Totalizer | ExkEncoder::Best => cc_totalizer::build_exk(result, vars, rhs),
                ExkEncoder::CardinalityNetwork => cc_cardinality_networks::build_exk(result, vars, rhs),
            }
        }
    }
}
