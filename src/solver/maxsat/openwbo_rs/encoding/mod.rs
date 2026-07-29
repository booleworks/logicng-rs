#![allow(dead_code)]

mod adder;
mod cardinality_networks;
mod clauses;
mod gte;
mod ladder;
mod modular_totalizer;
mod swc;
mod totalizer;

use crate::errors::LngResult;
use crate::solver::lng_core_solver::{LngCoreSolver, LngLit};

use crate::solver::maxsat::openwbo_rs::config::{CardinalEncoding, OpenWboConfig, PbEncoding};
use crate::solver::maxsat::{IncrementalStrategy, MaxSatError};
use adder::Adder;
use cardinality_networks::CNetworks;
use gte::Gte;
use modular_totalizer::MTotalizer;
use swc::Swc;
use totalizer::Totalizer;

pub(crate) struct Encoder {
    cardinality: CardinalityEncoder,
    pb: PseudoBooleanEncoder,
    incremental: IncrementalStrategy,
}

enum CardinalityEncoder {
    CardinalityNetworks(CNetworks),
    Totalizer(Totalizer),
    ModularTotalizer(MTotalizer),
}

enum PseudoBooleanEncoder {
    Swc(Swc),
    Gte(Gte),
    Adder(Adder),
}

impl Encoder {
    pub(crate) fn new(
        cardinality_encoding: CardinalEncoding,
        pc_encoding: PbEncoding,
        incremental: IncrementalStrategy,
    ) -> Self {
        let cardinality = match cardinality_encoding {
            CardinalEncoding::Totalizer => {
                CardinalityEncoder::Totalizer(Totalizer::new(incremental))
            }
            CardinalEncoding::MTotalizer => CardinalityEncoder::ModularTotalizer(MTotalizer::new()),
            CardinalEncoding::CNetworks => {
                CardinalityEncoder::CardinalityNetworks(CNetworks::new())
            }
        };
        let pb = match pc_encoding {
            PbEncoding::Swc => PseudoBooleanEncoder::Swc(Swc::new()),
            PbEncoding::Gte => PseudoBooleanEncoder::Gte(Gte::new()),
            PbEncoding::Adder => PseudoBooleanEncoder::Adder(Adder::new()),
        };
        Self {
            cardinality,
            pb,
            incremental,
        }
    }

    pub(crate) fn from_config(config: &OpenWboConfig) -> Self {
        let mut encoder = Self::new(
            config.cardinal_encoding.clone(),
            config.pb_encoding.clone(),
            config.incremental_strategy,
        );
        encoder.set_pb_encoding(config.pb_encoding.clone());
        encoder
    }

    pub(crate) fn set_pb_encoding(&mut self, pb_encoding: PbEncoding) {
        self.pb = match pb_encoding {
            PbEncoding::Swc => PseudoBooleanEncoder::Swc(Swc::new()),
            PbEncoding::Gte => PseudoBooleanEncoder::Gte(Gte::new()),
            PbEncoding::Adder => PseudoBooleanEncoder::Adder(Adder::new()),
        };
    }

    fn set_modulo(&mut self, modulo: usize) {
        match &mut self.cardinality {
            CardinalityEncoder::ModularTotalizer(modular_totalizer) => {
                modular_totalizer.set_modulo(modulo)
            }
            CardinalityEncoder::CardinalityNetworks(_) | CardinalityEncoder::Totalizer(_) => {}
        }
    }

    pub(crate) fn set_incremental(&mut self, incremental: IncrementalStrategy) {
        self.incremental = incremental;
        if let CardinalityEncoder::Totalizer(totalizer) = &mut self.cardinality {
            totalizer.set_incremental(incremental);
        }
    }

    fn encode_amo(&mut self, s: &mut LngCoreSolver, lits: &[LngLit]) {
        ladder::encode_ladder(s, lits);
    }

    pub(crate) fn encode_cardinality(
        &mut self,
        s: &mut LngCoreSolver,
        lits: &[LngLit],
        rhs: usize,
    ) {
        match &mut self.cardinality {
            CardinalityEncoder::Totalizer(totalizer) => {
                totalizer.build(s, lits, rhs);
                if totalizer.has_created_encoding() {
                    totalizer.update(s, rhs);
                }
            }
            CardinalityEncoder::ModularTotalizer(modular_totalizer) => {
                modular_totalizer.encode(s, lits, rhs)
            }
            CardinalityEncoder::CardinalityNetworks(cardinality_networks) => {
                cardinality_networks.encode(s, lits, rhs)
            }
        }
    }

    fn predict_cardinality(
        &mut self,
        _s: &mut LngCoreSolver,
        lits: &[LngLit],
        rhs: usize,
        _max_value: usize,
    ) -> Option<usize> {
        match &mut self.cardinality {
            CardinalityEncoder::ModularTotalizer(_) => {
                Some(2usize.saturating_mul(lits.len()).saturating_mul(rhs))
            }
            CardinalityEncoder::CardinalityNetworks(_) | CardinalityEncoder::Totalizer(_) => None,
        }
    }

    pub(crate) fn update_cardinality(&mut self, s: &mut LngCoreSolver, rhs: usize) {
        match &mut self.cardinality {
            CardinalityEncoder::Totalizer(totalizer) => totalizer.update(s, rhs),
            CardinalityEncoder::ModularTotalizer(modular_totalizer) => {
                modular_totalizer.update(s, rhs)
            }
            CardinalityEncoder::CardinalityNetworks(cardinality_networks) => {
                cardinality_networks.update(s, rhs)
            }
        }
    }

    pub(crate) fn build_cardinality(
        &mut self,
        s: &mut LngCoreSolver,
        lits: &[LngLit],
        rhs: usize,
    ) -> LngResult<()> {
        match &mut self.cardinality {
            CardinalityEncoder::Totalizer(totalizer) => totalizer.build(s, lits, rhs),
            _ => {
                return Err(MaxSatError::UnsupportedEncoding {
                    method: "build_cardinality",
                }
                .into());
            }
        }
        Ok(())
    }

    fn add_cardinality(
        &mut self,
        s: &mut LngCoreSolver,
        other: &mut Encoder,
        rhs: usize,
    ) -> LngResult<()> {
        match (&mut self.cardinality, &mut other.cardinality) {
            (
                CardinalityEncoder::Totalizer(totalizer),
                CardinalityEncoder::Totalizer(other_totalizer),
            ) => totalizer.add(s, other_totalizer, rhs),
            _ => {
                return Err(MaxSatError::UnsupportedEncoding {
                    method: "add_cardinality",
                }
                .into());
            }
        }
        Ok(())
    }

    pub(crate) fn inc_update_cardinality(
        &mut self,
        s: &mut LngCoreSolver,
        join: &[LngLit],
        lits: &[LngLit],
        rhs: usize,
        assumptions: &mut Vec<LngLit>,
    ) -> LngResult<()> {
        match &mut self.cardinality {
            CardinalityEncoder::Totalizer(totalizer) => {
                if !join.is_empty() {
                    totalizer.join(s, join, rhs);
                }
                totalizer.update_with_assumptions(s, lits, rhs, assumptions);
            }
            _ => {
                return Err(MaxSatError::UnsupportedEncoding {
                    method: "inc_update_cardinality",
                }
                .into());
            }
        }
        Ok(())
    }

    pub(crate) fn encode_pb(
        &mut self,
        s: &mut LngCoreSolver,
        lits: &mut Vec<LngLit>,
        coeffs: &mut Vec<usize>,
        rhs: usize,
    ) {
        match &mut self.pb {
            PseudoBooleanEncoder::Swc(swc) => swc.encode(s, lits, coeffs, rhs),
            PseudoBooleanEncoder::Gte(gte) => gte.encode(s, lits, coeffs, rhs),
            PseudoBooleanEncoder::Adder(adder) => adder.encode(s, lits, coeffs, rhs),
        }
    }

    pub(crate) fn predict_pb(
        &mut self,
        s: &mut LngCoreSolver,
        lits: &mut Vec<LngLit>,
        coeffs: &mut Vec<usize>,
        rhs: usize,
    ) -> Option<usize> {
        match &mut self.pb {
            PseudoBooleanEncoder::Gte(gte) => Some(gte.predict(s, lits, coeffs, rhs)),
            PseudoBooleanEncoder::Swc(_) | PseudoBooleanEncoder::Adder(_) => None,
        }
    }

    pub(crate) fn update_pb(&mut self, s: &mut LngCoreSolver, rhs: usize) {
        match &mut self.pb {
            PseudoBooleanEncoder::Swc(swc) => swc.update(s, rhs),
            PseudoBooleanEncoder::Gte(gte) => gte.update(s, rhs),
            PseudoBooleanEncoder::Adder(adder) => adder.update(s, rhs),
        }
    }

    fn inc_encode_pb(
        &mut self,
        s: &mut LngCoreSolver,
        lits: &mut Vec<LngLit>,
        coeffs: &mut Vec<usize>,
        rhs: usize,
        assumptions: &mut Vec<LngLit>,
        size: usize,
    ) -> LngResult<()> {
        match &mut self.pb {
            PseudoBooleanEncoder::Swc(swc) => {
                swc.encode_incremental(s, lits, coeffs, rhs, assumptions, size)
            }
            _ => {
                return Err(MaxSatError::UnsupportedEncoding {
                    method: "inc_encode_pb",
                }
                .into());
            }
        }
        Ok(())
    }

    fn inc_update_pb(
        &mut self,
        s: &mut LngCoreSolver,
        lits: &[LngLit],
        coeffs: &[usize],
        rhs: usize,
    ) -> LngResult<()> {
        match &mut self.pb {
            PseudoBooleanEncoder::Swc(swc) => {
                swc.update_incremental(s, rhs);
                swc.join(s, lits, coeffs);
            }
            _ => {
                return Err(MaxSatError::UnsupportedEncoding {
                    method: "inc_update_pb",
                }
                .into());
            }
        }
        Ok(())
    }

    fn inc_update_pb_assumptions(&self, assumptions: &mut Vec<LngLit>) -> LngResult<()> {
        match &self.pb {
            PseudoBooleanEncoder::Swc(swc) => swc.update_assumptions(assumptions),
            _ => {
                return Err(MaxSatError::UnsupportedEncoding {
                    method: "inc_update_pb_assumptions",
                }
                .into());
            }
        }
        Ok(())
    }

    pub(crate) fn has_card_encoding(&self) -> bool {
        match &self.cardinality {
            CardinalityEncoder::Totalizer(totalizer) => totalizer.has_created_encoding(),
            CardinalityEncoder::ModularTotalizer(modular_totalizer) => {
                modular_totalizer.has_created_encoding()
            }
            CardinalityEncoder::CardinalityNetworks(cardinality_networks) => {
                cardinality_networks.has_created_encoding()
            }
        }
    }

    pub(crate) fn has_pb_encoding(&self) -> bool {
        match &self.pb {
            PseudoBooleanEncoder::Swc(swc) => swc.has_created_encoding(),
            PseudoBooleanEncoder::Gte(gte) => gte.has_created_encoding(),
            PseudoBooleanEncoder::Adder(_) => false,
        }
    }

    pub(crate) fn lits(&self) -> LngResult<&[LngLit]> {
        match &self.cardinality {
            CardinalityEncoder::Totalizer(totalizer) => Ok(totalizer.lits()),
            _ => {
                return Err(MaxSatError::UnsupportedEncoding { method: "lits" }.into());
            }
        }
    }

    pub(crate) fn outputs(&self) -> LngResult<&[LngLit]> {
        match &self.cardinality {
            CardinalityEncoder::Totalizer(totalizer) => Ok(totalizer.outputs()),
            _ => {
                return Err(MaxSatError::UnsupportedEncoding { method: "outputs" }.into());
            }
        }
    }

    fn join_encoding(
        &mut self,
        s: &mut LngCoreSolver,
        lits: &[LngLit],
        rhs: usize,
    ) -> LngResult<()> {
        match &mut self.cardinality {
            CardinalityEncoder::Totalizer(totalizer) => totalizer.join(s, lits, rhs),
            _ => {
                return Err(MaxSatError::UnsupportedEncoding {
                    method: "join_encoding",
                }
                .into());
            }
        }
        Ok(())
    }
}
