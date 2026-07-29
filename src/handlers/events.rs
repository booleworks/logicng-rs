#![allow(missing_docs)]
use std::fmt::Display;

use crate::datastructures::Model;
use crate::formulas::EncodedFormula;

/// Event reported to a computation handler.
///
/// A handler can use these events to decide whether a computation should continue. If it returns
/// `false`, the event is stored as the cancellation cause in the corresponding
/// [`CancelableResult`](crate::handlers::CancelableResult).
#[derive(Clone, Debug)]
pub enum LngEvent {
    NoEvent,
    DistributionPerformed,
    BddNewRefAdded,
    DnnfDtreeGenerationStarted,
    DnnfDtreeMinFillGraphInitialized,
    DnnfDtreeMinFillNewIteration,
    DnnfDtreeProcessingNextOrderVariable,
    DnnfShannonExpansion,
    SatConflictDetected,
    ModelEnumerationCommit,
    ModelEnumerationRollback,
    SubsumptionStartingUBTreeGeneration,
    SubsumptionAddedNewSet,
    MaxSatSolverCall,
    ComputationFinished(LngComputation),
    ComputationStarted(LngComputation),
    EnumerationFoundModels(usize),
    FactorizationCreatedClause(EncodedFormula),
    OptimizationFoundBetterBound(Model),
    ExternalEvent(String),
}

impl Display for LngEvent {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("Event: ")?;
        match self {
            Self::NoEvent => f.write_str("no event"),
            Self::DistributionPerformed => f.write_str("distribution performed"),
            Self::BddNewRefAdded => f.write_str("new reference added in BDD"),
            Self::DnnfDtreeGenerationStarted => f.write_str("DNNF DTree generation started"),
            Self::DnnfDtreeMinFillGraphInitialized => {
                f.write_str("DNNF DTree MinFill graph initialized")
            }
            Self::DnnfDtreeMinFillNewIteration => f.write_str("DNNF DTree MinFill new iteration"),
            Self::DnnfDtreeProcessingNextOrderVariable => {
                f.write_str("DNNF DTree processing next order variable")
            }
            Self::DnnfShannonExpansion => f.write_str("DNNF Shannon expansion"),
            Self::SatConflictDetected => f.write_str("SAT conflict detected"),
            Self::ModelEnumerationCommit => f.write_str("model enumeration commit"),
            Self::ModelEnumerationRollback => f.write_str("model enumeration rollback"),
            Self::SubsumptionStartingUBTreeGeneration => f.write_str("starting UB tree generation"),
            Self::SubsumptionAddedNewSet => f.write_str("adding a new set to the UB tree"),
            Self::MaxSatSolverCall => f.write_fmt(format_args!("new MaxSAT solver call")),
            Self::ComputationFinished(lng_computation) => {
                f.write_fmt(format_args!("finished computation: {lng_computation}"))
            }
            Self::ComputationStarted(lng_computation) => {
                f.write_fmt(format_args!("started computation: {lng_computation}"))
            }
            Self::EnumerationFoundModels(count) => {
                f.write_fmt(format_args!("model enumeration found {count} new models"))
            }
            Self::FactorizationCreatedClause(_) => {
                f.write_str("created clause during factorization")
            }
            Self::OptimizationFoundBetterBound(_) => {
                f.write_str("optimization function found a better bound")
            }
            Self::ExternalEvent(s) => f.write_str(s),
        }
    }
}

/// Type of computation reported by [`LngEvent::ComputationStarted`] and
/// [`LngEvent::ComputationFinished`].
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
    ExternalComputation(&'static str),
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
            Self::ExternalComputation(s) => s,
        })
    }
}
