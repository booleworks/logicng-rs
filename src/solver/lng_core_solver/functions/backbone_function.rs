use crate::{
    backbones::Backbone,
    formulas::Variable,
    handlers::{ComputationHandler, LngResult},
    solver::lng_core_solver::SatSolver,
};

/// Types of backbones
#[derive(Eq, PartialEq, Copy, Clone, Debug)]
pub enum BackboneType {
    /// Backbones that only contain positive literals.
    OnlyPositive,
    /// Backbones that only contain negative literals.
    OnlyNegative,
    /// Backbones that contain positive as well as negative literals.
    PositiveAndNegative,
}

impl BackboneType {
    /// Returns `true` if and only if the type of backbone allows to contains
    /// literals with the given phase.
    pub const fn matches_phase(&self, phase: bool) -> bool {
        match self {
            Self::OnlyPositive => phase,
            Self::OnlyNegative => !phase,
            Self::PositiveAndNegative => true,
        }
    }
}

pub fn compute_backbone<B, V, I>(
    solver: &mut SatSolver<B>,
    variables: I,
    backbone_type: BackboneType,
    handler: &mut dyn ComputationHandler,
) -> LngResult<Backbone>
where
    I: IntoIterator<Item = V> + Copy,
    V: Into<Variable>,
{
    solver.underlying_solver().compute_backbone(variables, backbone_type, handler)
}
