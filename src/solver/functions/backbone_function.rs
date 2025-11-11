use crate::backbones::Backbone;
use crate::formulas::Variable;
use crate::solver::functions::backbone_function::BackboneType::PositiveAndNegative;
use crate::solver::minisat::MiniSat;
use BackboneType::{OnlyNegative, OnlyPositive};

/// Types of backbones
#[derive(Eq, PartialEq, Copy, Clone, Debug, Hash)]
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
            OnlyPositive => phase,
            OnlyNegative => !phase,
            PositiveAndNegative => true,
        }
    }
}

/// Configuration for backbones.
#[derive(Eq, PartialEq, Clone, Debug, Hash)]
pub struct BackboneConfig {
    variables: Vec<Variable>,
    backbone_type: BackboneType,
}

impl BackboneConfig {
    /// Construct a new configuration with the given variables.
    pub fn new(variables: Vec<Variable>) -> Self {
        Self { variables, backbone_type: PositiveAndNegative }
    }

    /// Returns the type of the backbone.
    #[must_use]
    pub const fn backbone_type(mut self, backbone_type: BackboneType) -> Self {
        self.backbone_type = backbone_type;
        self
    }

    /// Computes the backbone based on a solver and the configuration.
    pub fn compute_backbone(self, solver: &mut MiniSat) -> Backbone {
        let state_before_backbone = if solver.underlying_solver.config.incremental { Some(solver.save_state()) } else { None };
        let backbone = solver.underlying_solver.compute_backbone(self.variables, self.backbone_type);
        if let Some(state) = state_before_backbone {
            solver.load_state(&state);
        }
        backbone
    }
}
