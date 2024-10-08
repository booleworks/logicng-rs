use std::fmt::Display;

use crate::{datastructures::Model, formulas::EncodedFormula};

#[derive(Clone, Debug)]
pub enum LngEvent {
    NoEvent,
    DistributionPerformed,
    BddNewRefAdded,
    DnnfDtreeMinFillGraphInitialized,
    DnnfDtreeMinFillNewIteration,
    DnnfDtreeProcessingNextOrderVariable,
    DnnfShannonExpansion,
    SatConflictDetected,
    ModelEnumerationCommit,
    ModelEnumerationRollback,
    SubsumptionStartingUBTreeGeneration,
    SubsumptionAddedNewSet,
    ComputationFinished(LngComputation),
    ComputationStarted(LngComputation),
    EnumerationFoundModels(usize),
    FactorizationCreatedClause(EncodedFormula),
    MaxSatNewLowerBound(usize),
    MaxSatNewUpperBound(usize),
    OptimizationFoundBetterBound(Model),
}

impl Display for LngEvent {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("Event: ")?;
        match self {
            Self::NoEvent => f.write_str("No event"),
            Self::DistributionPerformed => f.write_str("Distribution preformed"),
            Self::BddNewRefAdded => f.write_str("New reference added in BDD"),
            Self::DnnfDtreeMinFillGraphInitialized => f.write_str("DNNF DTree MinFill Graph initialized"),
            Self::DnnfDtreeMinFillNewIteration => f.write_str("DNNF DTree MinFill new iteration"),
            Self::DnnfDtreeProcessingNextOrderVariable => f.write_str("DNNF DTree processing next order variable"),
            Self::DnnfShannonExpansion => f.write_str("DNNF Shannon Expansion"),
            Self::SatConflictDetected => f.write_str("SAT conflict detected"),
            Self::ModelEnumerationCommit => f.write_str("Model Enumeration Commit"),
            Self::ModelEnumerationRollback => f.write_str("Model Enumeration Rollback"),
            Self::SubsumptionStartingUBTreeGeneration => f.write_str("Starting UB Tree generation"),
            Self::SubsumptionAddedNewSet => f.write_str("Adding a new set to the UB Tree"),
            Self::ComputationFinished(lng_computation) => f.write_fmt(format_args!("Finished computation: {lng_computation}")),
            Self::ComputationStarted(lng_computation) => f.write_fmt(format_args!("Started computation: {lng_computation}")),
            Self::EnumerationFoundModels(count) => f.write_fmt(format_args!("Model enumeration found {count} new models")),
            Self::FactorizationCreatedClause(_) => f.write_str("Created clause during factorization"),
            Self::MaxSatNewLowerBound(lb) => f.write_fmt(format_args!("New Max SAT lower bound {lb}")),
            Self::MaxSatNewUpperBound(ub) => f.write_fmt(format_args!("New Max SAT upper bound {ub}")),
            Self::OptimizationFoundBetterBound(_) => f.write_str("Optimization Function found a better bound"),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum LngComputation {
    Sat,
    MaxSat,
    Factorization,
    Bdd,
    Dnnf,
    Backbone,
    AdvancedSimplification,
    Prime,
    ImplicantReduction,
    ImplicateReduction,
    Mus,
    Smus,
    Optimization,
    ModelEnumeration,
}

impl Display for LngComputation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::Sat => "SAT Call",
            Self::MaxSat => "MaxSAT Call",
            Self::Factorization => "Factorization",
            Self::Bdd => "BDD Computation",
            Self::Dnnf => "DNNF Computation",
            Self::Backbone => "Backbone Computation",
            Self::AdvancedSimplification => "Advanced Simplification",
            Self::Prime => "Prime Computation",
            Self::ImplicantReduction => "Implicant Reduction",
            Self::ImplicateReduction => "Implicate Reduction",
            Self::Mus => "MUS Computation",
            Self::Smus => "SMUS Computation",
            Self::Optimization => "Optimization Function",
            Self::ModelEnumeration => "Model Enumeration",
        })
    }
}
