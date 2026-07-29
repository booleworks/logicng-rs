// use std::collections::BTreeSet;
//
// use crate::datastructures::{Assignment, Model};
// use crate::errors::LngResult;
// use crate::formulas::{EncodedFormula, FormulaFactory, Variable};
// use crate::solver::maxsat_config::MaxSatConfig;
// use crate::solver::maxsat_solver::{Algorithm, MaxSatResult, MaxSatStats};
//
// use super::algorithms::{MaxSatAlgo, OpenWboAlgorithm};
//
// /// The main OpenWBO solver struct
// pub struct OpenWboSolver {
//     maxsat: MaxSatAlgo,
//     algorithm: OpenWboAlgorithm,
// }
//
// impl OpenWboSolver {
//     pub(crate) fn new(algorithm: &Algorithm, config: &MaxSatConfig) -> Self {
//         Self {
//             maxsat: MaxSatAlgo::new(config),
//             algorithm: OpenWboAlgorithm::from_config(algorithm, config),
//         }
//     }
//
//     pub(crate) fn status(&self) -> LngResult<MaxSatResult> {
//         Ok(self.maxsat.status.clone())
//     }
//
//     pub(crate) fn search(&mut self) -> LngResult<MaxSatResult> {
//         let state_before_solving = self.maxsat.save_state();
//         let result = self.algorithm.search(&mut self.maxsat);
//         self.maxsat.load_state(&state_before_solving)?;
//         if let Ok(status) = &result {
//             self.maxsat.status = status.clone();
//         }
//         result
//     }
//
//     pub(crate) fn model(&self, selector_variables: &BTreeSet<Variable>) -> LngResult<Model> {
//         self.maxsat.create_model(selector_variables)
//     }
//
//     pub(crate) fn assignment(
//         &self,
//         selector_variables: &BTreeSet<Variable>,
//     ) -> LngResult<Assignment> {
//         self.maxsat.create_assignment(selector_variables)
//     }
//
//     pub(crate) fn stats(&self) -> MaxSatStats {
//         self.maxsat.stats()
//     }
//
//     pub(crate) fn add_soft_clause(
//         &mut self,
//         w: u64,
//         formula: EncodedFormula,
//         f: &FormulaFactory,
//     ) -> LngResult<()> {
//         self.maxsat.add_formula_clause(Some(w), formula, f)
//     }
//
//     pub(crate) fn add_hard_clause(
//         &mut self,
//         formula: EncodedFormula,
//         f: &FormulaFactory,
//     ) -> LngResult<()> {
//         self.maxsat.add_formula_clause(None, formula, f)
//     }
// }
