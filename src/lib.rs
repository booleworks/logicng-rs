#![doc = include_str!("../README.md")]
#![warn(clippy::all, clippy::pedantic, clippy::nursery, missing_docs)]
#![allow(
    clippy::similar_names,
    clippy::must_use_candidate,
    clippy::module_name_repetitions,
    clippy::missing_panics_doc,
    clippy::missing_errors_doc
)]

extern crate pest;
#[macro_use]
extern crate pest_derive;

/// Backbone computation.
pub mod backbones;
/// Cardinality constraint encoders.
pub mod cardinality_constraints;
mod collections;
/// Various datastructures.
pub mod datastructures;
/// Tools for analyzing unsatisfiable results.
pub mod explanations;
/// Types and datastructures to represent and manage formulas effectively.
pub mod formulas;
/// Graphs and Hypergraphs.
pub mod graphs;
/// Handlers for more control during some calculations.
pub mod handlers;
/// Functions for reading and writing formulas from/to files.
pub mod io;
/// Offline compilation of formulas for faster online queries.
pub mod knowledge_compilation;
/// Functions, Predicates, and Transformations for formulas.
pub mod operations;
mod parser;
/// Tool for assigning additional information to a formula.
pub mod propositions;
/// Pseudo-boolean constraint encoders.
pub mod pseudo_booleans;
/// Solvers for SAT and MaxSAT.
pub mod solver;
/// Additional utility.
pub mod util;
