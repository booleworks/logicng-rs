use crate::datastructures::{EncodingResult, SolverExportLiteral};
use crate::encodings::cardinality_constraints::cc_config::{AlkEncoder, AmkEncoder};
use itertools::Itertools;

/// Incremental data for an at-most-k cardinality constraint.
///
/// When an at-most-k cardinality constraint is constructed, it is possible to
/// save incremental data with it. Then one can modify the constraint after
/// it was created by tightening the original bound.
pub struct CcIncrementalData {
    amk_encoder: Option<AmkEncoder>,
    alk_encoder: Option<AlkEncoder>,
    vector1: Vec<SolverExportLiteral>,
    vector2: Option<Vec<SolverExportLiteral>>,
    md: usize,
    n_vars: usize,
    pub(crate) current_rhs: usize,
}

impl CcIncrementalData {
    pub(super) const fn for_amk_modular_totalizer(
        rhs: usize,
        vector1: Vec<SolverExportLiteral>,
        vector2: Vec<SolverExportLiteral>,
        md: usize,
    ) -> Self {
        Self {
            amk_encoder: Some(AmkEncoder::ModularTotalizer),
            alk_encoder: None,
            vector1,
            vector2: Some(vector2),
            md,
            n_vars: 0,
            current_rhs: rhs,
        }
    }

    pub(super) const fn for_amk(amk_encoder: AmkEncoder, vector1: Vec<SolverExportLiteral>, rhs: usize) -> Self {
        Self { amk_encoder: Some(amk_encoder), alk_encoder: None, vector1, vector2: None, md: 0, n_vars: 0, current_rhs: rhs }
    }

    pub(super) const fn for_alk_modular_totalizer(
        rhs: usize,
        n_vars: usize,
        vector1: Vec<SolverExportLiteral>,
        vector2: Vec<SolverExportLiteral>,
        md: usize,
    ) -> Self {
        Self {
            amk_encoder: None,
            alk_encoder: Some(AlkEncoder::ModularTotalizer),
            vector1,
            vector2: Some(vector2),
            md,
            n_vars,
            current_rhs: rhs,
        }
    }

    pub(super) const fn for_alk(alk_encoder: AlkEncoder, vector1: Vec<SolverExportLiteral>, rhs: usize, n_vars: usize) -> Self {
        Self { amk_encoder: None, alk_encoder: Some(alk_encoder), vector1, vector2: None, md: 0, n_vars, current_rhs: rhs }
    }

    /// Tightens the upper bound of an at-most-k constraint and returns the resulting formula.
    ///
    /// Usage constraints:
    /// - New right-hand side must be smaller than current right-hand side.
    /// - Cannot be used for at-least-k constraints.
    pub fn new_upper_bound(&mut self, result: &mut dyn EncodingResult, rhs: u32) {
        self.compute_ub_constraint(result, rhs);
    }

    fn compute_ub_constraint(&mut self, result: &mut dyn EncodingResult, rhs: u32) {
        let rhs = rhs.try_into().unwrap_or_else(|_| panic!("Can only constrain to bounds up to {} on this architecture", usize::MAX));
        assert!(rhs < self.current_rhs, "New upper bound {rhs} does not tighten the current bound of {}", self.current_rhs);
        self.current_rhs = rhs;
        if let Some(encoder) = self.amk_encoder {
            match encoder {
                AmkEncoder::Totalizer => {
                    for l in self.vector1.iter().skip(rhs) {
                        result.add_clause(&[l.negate()]);
                    }
                }
                AmkEncoder::ModularTotalizer => {
                    self.add_modular_totalizer_constraints(result, rhs);
                }
                AmkEncoder::CardinalityNetwork => {
                    if self.vector1.len() > rhs {
                        result.add_clause(&[self.vector1[rhs].negate()]);
                    }
                }
                AmkEncoder::Best => panic!("Invalid at-most-k encoder 'Best'"),
            }
        } else {
            panic!("Cannot encode a new upper bound for an at-most-k constraint");
        }
    }

    /// Tightens the lower bound of an at-most-k constraint and returns the resulting formula.
    ///
    /// Usage constraints:
    /// - New right-hand side must be greater than current right-hand side.
    /// - Cannot be used for at-most-k constraints.
    pub fn new_lower_bound(&mut self, result: &mut dyn EncodingResult, rhs: u32) {
        self.compute_lb_constraint(result, rhs);
    }

    fn compute_lb_constraint(&mut self, result: &mut dyn EncodingResult, rhs: u32) {
        let rhs = rhs.try_into().unwrap_or_else(|_| panic!("Can only constrain to bounds up to {} on this architecture", usize::MAX));
        assert!(rhs > self.current_rhs, "New lower bound {rhs} does not tighten the current bound of {}", self.current_rhs);
        self.current_rhs = rhs;
        if let Some(encoder) = self.alk_encoder {
            match encoder {
                AlkEncoder::Totalizer => {
                    self.vector1.iter().take(rhs).for_each(|&l| result.add_clause(&[l]));
                }
                AlkEncoder::ModularTotalizer => {
                    self.add_modular_totalizer_constraints(result, self.n_vars - rhs);
                }
                AlkEncoder::CardinalityNetwork => {
                    let new_rhs = self.n_vars - rhs;
                    if self.vector1.len() > new_rhs {
                        result.add_clause(&[self.vector1[new_rhs].negate()]);
                    }
                }
                AlkEncoder::Best => panic!("Invalid at-least-k encoder 'Best'"),
            }
        } else {
            panic!("Cannot encode a new lower bound for an at-least-k constraint")
        };
    }

    fn add_modular_totalizer_constraints(&self, result: &mut dyn EncodingResult, rhs: usize) {
        let vector2 = self.vector2.as_ref().expect("Vector 2 must be initialized for modular totalizer");
        let u_limit = (rhs + 1) / self.md;
        let l_limit = (rhs + 1) - u_limit * self.md;
        assert!(u_limit <= self.vector1.len());
        assert!(l_limit <= vector2.len());
        self.vector1.iter().dropping(u_limit).for_each(|l| result.add_clause(&[l.negate()]));
        if u_limit != 0 && l_limit != 0 {
            let l1 = self.vector1[u_limit - 1].negate();
            vector2.iter().dropping(l_limit - 1).for_each(|l2| result.add_clause(&[l1, l2.negate()]));
        } else if u_limit == 0 {
            vector2.iter().dropping(l_limit - 1).for_each(|l| result.add_clause(&[l.negate()]));
        } else {
            result.add_clause(&[self.vector1[u_limit - 1].negate()]);
        }
    }
}
