use crate::cardinality_constraints::cc_config::{AlkEncoder, AmkEncoder};
use crate::cardinality_constraints::error::CcError;
use crate::datastructures::{EncodingResult, EncodingResultFF, EncodingResultSatSolver};
use crate::errors::LngResult;
use crate::formulas::{EncodedFormula, FormulaFactory, Literal};
use crate::solver::minisat::MiniSat;
use itertools::Itertools;

/// Incremental data for an at-most-k cardinality constraint. When an
/// at-most-k cardinality constraint is constructed, it is possible to
/// save incremental data with it. Then one can modify the constraint after
/// it was created by tightening the original bound.
pub struct CcIncrementalData {
    amk_encoder: Option<AmkEncoder>,
    alk_encoder: Option<AlkEncoder>,
    vector1: Vec<Literal>,
    vector2: Option<Vec<Literal>>,
    md: usize,
    n_vars: usize,
    pub(crate) current_rhs: usize,
}

impl CcIncrementalData {
    pub(super) fn for_amk_modular_totalizer(
        rhs: usize,
        vector1: Vec<Literal>,
        vector2: Vec<Literal>,
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

    pub(super) fn for_amk(amk_encoder: AmkEncoder, vector1: Vec<Literal>, rhs: usize) -> Self {
        Self {
            amk_encoder: Some(amk_encoder),
            alk_encoder: None,
            vector1,
            vector2: None,
            md: 0,
            n_vars: 0,
            current_rhs: rhs,
        }
    }

    pub(super) fn for_alk_modular_totalizer(
        rhs: usize,
        n_vars: usize,
        vector1: Vec<Literal>,
        vector2: Vec<Literal>,
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

    pub(super) fn for_alk(
        alk_encoder: AlkEncoder,
        vector1: Vec<Literal>,
        rhs: usize,
        n_vars: usize,
    ) -> Self {
        Self {
            amk_encoder: None,
            alk_encoder: Some(alk_encoder),
            vector1,
            vector2: None,
            md: 0,
            n_vars,
            current_rhs: rhs,
        }
    }

    /// Tightens the upper bound of an at-most-k constraint and returns the additional encoding.
    ///
    /// # Errors
    ///
    /// Returns an error if this incremental data does not belong to an at-most-k encoding,
    /// if the new bound does not tighten the current bound, or if the right-hand side cannot
    /// be represented on this architecture.
    pub fn new_upper_bound(
        &mut self,
        f: &FormulaFactory,
        rhs: u32,
    ) -> LngResult<Vec<EncodedFormula>> {
        let mut result = EncodingResultFF::new(f);
        self.compute_ub_constraint(&mut result, rhs)?;
        Ok(result.result)
    }

    /// Tightens the upper bound of an at-most-k constraint and encodes it on the solver.
    ///
    /// # Errors
    ///
    /// Returns an error if this incremental data does not belong to an at-most-k encoding,
    /// if the new bound does not tighten the current bound, or if the right-hand side cannot
    /// be represented on this architecture.
    pub fn new_upper_bound_for_solver(
        &mut self,
        solver: &mut MiniSat,
        f: &FormulaFactory,
        rhs: u32,
    ) -> LngResult<()> {
        let mut encoding_result = EncodingResultSatSolver::new(solver, None, f);
        self.compute_ub_constraint(&mut encoding_result, rhs)
    }

    fn compute_ub_constraint(
        &mut self,
        result: &mut dyn EncodingResult,
        rhs: u32,
    ) -> LngResult<()> {
        let rhs = rhs
            .try_into()
            .map_err(|_| CcError::TooLargeRhs { rhs: rhs as u64 })?;

        let Some(encoder) = self.amk_encoder else {
            return Err(CcError::NoAmkEncoder.into());
        };

        if rhs >= self.current_rhs {
            return Err(CcError::UpperBoundNotTighten {
                rhs,
                current: self.current_rhs,
            }
            .into());
        }

        self.current_rhs = rhs;

        match encoder {
            AmkEncoder::Totalizer => {
                self.vector1
                    .iter()
                    .skip(rhs)
                    .for_each(|l| result.add_clause(&[l.negate()]));
            }
            AmkEncoder::ModularTotalizer | AmkEncoder::Best => {
                self.add_modular_totalizer_constraints(result, rhs);
            }
            AmkEncoder::CardinalityNetwork => {
                if self.vector1.len() > rhs {
                    result.add_clause(&[self.vector1[rhs].negate()]);
                }
            }
        }
        Ok(())
    }

    /// Tightens the lower bound of an at-least-k constraint and returns the additional encoding.
    ///
    /// # Errors
    ///
    /// Returns an error if this incremental data does not belong to an at-least-k encoding,
    /// if the new bound does not tighten the current bound, or if the right-hand side cannot
    /// be represented on this architecture.
    pub fn new_lower_bound(
        &mut self,
        f: &FormulaFactory,
        rhs: u32,
    ) -> LngResult<Vec<EncodedFormula>> {
        let mut result = EncodingResultFF::new(f);
        self.compute_lb_constraint(&mut result, rhs)?;
        Ok(result.result)
    }

    /// Tightens the lower bound of an at-least-k constraint and encodes it on the solver.
    ///
    /// # Errors
    ///
    /// Returns an error if this incremental data does not belong to an at-least-k encoding,
    /// if the new bound does not tighten the current bound, or if the right-hand side cannot
    /// be represented on this architecture.
    pub fn new_lower_bound_for_solver<B: Clone>(
        &mut self,
        solver: &mut MiniSat<B>,
        f: &FormulaFactory,
        rhs: u32,
    ) -> LngResult<()> {
        let mut encoding_result = EncodingResultSatSolver::new(solver, None, f);
        self.compute_lb_constraint(&mut encoding_result, rhs)
    }

    fn compute_lb_constraint(
        &mut self,
        result: &mut dyn EncodingResult,
        rhs: u32,
    ) -> LngResult<()> {
        let rhs = rhs
            .try_into()
            .map_err(|_| CcError::TooLargeRhs { rhs: rhs as u64 })?;

        let Some(encoder) = self.alk_encoder else {
            return Err(CcError::NoAlkEncoder.into());
        };

        if rhs <= self.current_rhs {
            return Err(CcError::LowerBoundNotTighten {
                rhs,
                current: self.current_rhs,
            }
            .into());
        }

        self.current_rhs = rhs;

        if rhs > self.n_vars {
            result.add_clause(&Vec::new());
            return Ok(());
        }

        match encoder {
            AlkEncoder::Totalizer => {
                self.vector1
                    .iter()
                    .take(rhs)
                    .for_each(|&l| result.add_clause(&[l]));
            }
            AlkEncoder::ModularTotalizer | AlkEncoder::Best => {
                self.add_modular_totalizer_constraints(result, self.n_vars - rhs);
            }
            AlkEncoder::CardinalityNetwork => {
                let new_rhs = self.n_vars - rhs;
                if self.vector1.len() > new_rhs {
                    result.add_clause(&[self.vector1[new_rhs].negate()]);
                }
            }
        }
        Ok(())
    }

    fn add_modular_totalizer_constraints(&mut self, result: &mut dyn EncodingResult, rhs: usize) {
        let vector2 = self
            .vector2
            .as_ref()
            .expect("vector 2 must always be initialized for modular totalizer");
        let u_limit = (rhs + 1) / self.md;
        let l_limit = (rhs + 1) - u_limit * self.md;
        assert!(u_limit <= self.vector1.len());
        assert!(l_limit <= vector2.len());
        self.vector1
            .iter()
            .dropping(u_limit)
            .for_each(|l| result.add_clause(&[l.negate()]));
        if u_limit != 0 && l_limit != 0 {
            let l1 = self.vector1[u_limit - 1].negate();
            vector2
                .iter()
                .dropping(l_limit - 1)
                .for_each(|l2| result.add_clause(&[l1, l2.negate()]));
        } else if u_limit == 0 {
            vector2
                .iter()
                .dropping(l_limit - 1)
                .for_each(|l| result.add_clause(&[l.negate()]));
        } else {
            result.add_clause(&[self.vector1[u_limit - 1].negate()]);
        }
    }
}
