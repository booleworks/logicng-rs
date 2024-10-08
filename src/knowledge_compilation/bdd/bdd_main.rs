use std::collections::{BTreeMap, BTreeSet};

use num_bigint::BigUint;

use crate::datastructures::Model;
use crate::formulas::{EncodedFormula, Formula, FormulaFactory, Literal, Variable};

use crate::handlers::{ComputationHandler, LngComputation, LngEvent, LngResult, NopHandler};
use crate::knowledge_compilation::bdd::bdd_construction::{
    and, bdd_high, bdd_low, bdd_var, equivalence, exists, for_all, implication, ith_var, nith_var, not, or,
};
use crate::knowledge_compilation::bdd::bdd_kernel::{BddKernel, BDD_FALSE, BDD_TRUE};
use crate::knowledge_compilation::bdd::bdd_model_enumeration::enumerate_all_models;
use crate::knowledge_compilation::bdd::bdd_normalform::normal_form;
use crate::knowledge_compilation::bdd::bdd_operations::{
    all_nodes, full_sat_one, node_count, path_count_one, path_count_zero, sat_count, sat_one, sat_one_set, var_profile,
};

use super::bdd_construction::restrict;
use super::bdd_operations::support;

/// The internal representation of a BDD.
#[derive(PartialEq, Eq, Debug)]
pub struct Bdd {
    index: usize,
}

impl Bdd {
    /// Generates a new BDD for the given formula with the given kernel.
    pub fn from_formula(formula: EncodedFormula, f: &FormulaFactory, kernel: &mut BddKernel) -> Self {
        Self { index: build_rec(formula, f, kernel, &mut NopHandler::new()).expect("Nop Handler never aborts.") }
    }

    /// Generates a new BDD for the given formula with the given kernel.
    pub fn from_formula_with_handler(
        formula: EncodedFormula,
        f: &FormulaFactory,
        kernel: &mut BddKernel,
        handler: &mut dyn ComputationHandler,
    ) -> LngResult<Self> {
        if !handler.should_resume(LngEvent::ComputationStarted(LngComputation::Bdd)) {
            return LngResult::Canceled(LngEvent::ComputationStarted(LngComputation::Bdd));
        }
        match build_rec(formula, f, kernel, handler) {
            Ok(index) => LngResult::Ok(Self { index }),
            Err(event) => LngResult::Canceled(event),
        }
    }

    /// Returns whether this BDD represents a tautology.
    pub const fn is_tautology(&self) -> bool {
        self.index == BDD_TRUE
    }

    /// Returns whether this BDD represents a contradiction.
    pub const fn is_contradicion(&self) -> bool {
        self.index == BDD_FALSE
    }

    /// Returns an arbitrary model for this BDD.  This model does not have to contain
    /// all variables of the BDD.
    pub fn model(&self, kernel: &mut BddKernel) -> Option<Model> {
        let model_bdd = sat_one(self.index, kernel);
        create_model(model_bdd, kernel)
    }

    /// Returns an arbitrary model of this BDD which contains at least the given
    /// variables or None if there is none.  If a variable is a don't care variable,
    /// it will be assigned with the given default value.
    pub fn model_for_variables(&self, default: bool, variables: &[Variable], f: &FormulaFactory, kernel: &mut BddKernel) -> Option<Model> {
        let var_bdd = bdd_from_variables(variables, f, kernel);
        let polarity = if default { BDD_TRUE } else { BDD_FALSE };
        let model_bdd = sat_one_set(self.index, var_bdd, polarity, kernel);
        create_model(model_bdd, kernel)
    }

    /// Returns a full model of this BDD or None if there is none.
    pub fn full_model(&self, kernel: &mut BddKernel) -> Option<Model> {
        let model_bdd = full_sat_one(self.index, kernel);
        create_model(model_bdd, kernel)
    }

    /// Enumerate all models of this BDD
    pub fn enumerate_all_models(&self, kernel: &mut BddKernel) -> Vec<Model> {
        enumerate_all_models(self.index, None, kernel)
    }

    /// Enumerate all models of this BDD projected to the given variables
    pub fn enumerate_all_models_projected(&self, variables: &[Variable], kernel: &mut BddKernel) -> Vec<Model> {
        enumerate_all_models(self.index, Some(variables), kernel)
    }

    /// Returns the number of nodes for this BDD.
    pub fn node_count(&self, kernel: &mut BddKernel) -> usize {
        node_count(self.index, kernel)
    }

    /// Returns the model count of this BDD.
    pub fn model_count(&self, kernel: &mut BddKernel) -> BigUint {
        sat_count(self.index, kernel)
    }

    /// Returns the number of clauses for the CNF formula of the BDD.
    pub fn number_of_clauses_cnf(&self, kernel: &mut BddKernel) -> BigUint {
        path_count_zero(self.index, kernel)
    }

    /// Returns the number of terms for the DNF formula of the BDD.
    pub fn number_of_terms_dnf(&self, kernel: &mut BddKernel) -> BigUint {
        path_count_one(self.index, kernel)
    }

    /// Returns a CNF formula for this BDD.
    pub fn cnf(&self, f: &FormulaFactory, kernel: &mut BddKernel) -> EncodedFormula {
        normal_form(self.index, true, f, kernel)
    }

    /// Returns a DNF formula for this BDD.
    pub fn dnf(&self, f: &FormulaFactory, kernel: &mut BddKernel) -> EncodedFormula {
        normal_form(self.index, false, f, kernel)
    }

    /// Returns how often each variable occurs in this BDD.
    pub fn variable_profile(&self, kernel: &mut BddKernel) -> BTreeMap<Variable, usize> {
        let var_profile = var_profile(self.index, kernel);
        let mut profile = BTreeMap::new();
        for (idx, count) in var_profile.iter().enumerate() {
            profile.insert(kernel.get_variable_for_index(idx).unwrap(), *count);
        }
        profile
    }

    /// Returns a formula representation of this BDD.  This is done by using the Shannon
    /// expansion.
    pub fn to_formula(&self, f: &FormulaFactory, kernel: &mut BddKernel) -> EncodedFormula {
        to_formula_rec(self.index, f, kernel)
    }

    /// Restricts the BDD with the given literals.
    #[must_use]
    pub fn restrict(&self, restriction: &[Literal], f: &FormulaFactory, kernel: &mut BddKernel) -> Self {
        let var_bdd = bdd_from_literals(restriction, f, kernel);
        Self { index: restrict(self.index, var_bdd, kernel) }
    }

    /// Existential quantifier elimination for a given set of variables.
    #[must_use]
    pub fn exists(&self, variables: &[Variable], f: &FormulaFactory, kernel: &mut BddKernel) -> Self {
        let var_bdd = bdd_from_variables(variables, f, kernel);
        Self { index: exists(self.index, var_bdd, kernel) }
    }

    /// Universal quantifier elimination for a given set of variables.
    #[must_use]
    pub fn for_all(&self, variables: &[Variable], f: &FormulaFactory, kernel: &mut BddKernel) -> Self {
        let var_bdd = bdd_from_variables(variables, f, kernel);
        Self { index: for_all(self.index, var_bdd, kernel) }
    }

    /// Returns all the variables this BDD depends on.
    pub fn support(&self, kernel: &mut BddKernel) -> BTreeSet<Variable> {
        let support_bdd = support(self.index, kernel);
        let model = create_model(support_bdd, kernel);
        let mut res = BTreeSet::new();
        if let Some(m) = model {
            assert!(m.neg().is_empty());
            for x in m.pos() {
                res.insert(*x);
            }
        }
        res
    }
}

fn build_rec(
    formula: EncodedFormula,
    f: &FormulaFactory,
    kernel: &mut BddKernel,
    handler: &mut dyn ComputationHandler,
) -> Result<usize, LngEvent> {
    use Formula::{And, Cc, Equiv, False, Impl, Lit, Not, Or, Pbc, True};
    match formula.unpack(f) {
        False => Ok(BDD_FALSE),
        True => Ok(BDD_TRUE),
        Lit(lit) => {
            let idx = kernel.get_or_add_var_index(lit.variable());
            if lit.phase() {
                Ok(ith_var(idx, kernel))
            } else {
                Ok(nith_var(idx, kernel))
            }
        }
        Not(op) => {
            let operand = build_rec(op, f, kernel, handler)?;
            let not_bdd = not(operand, kernel);
            let res = kernel.add_ref(not_bdd, handler)?;
            kernel.del_ref(operand);
            Ok(res)
        }
        Impl((left, right)) | Equiv((left, right)) => {
            let left_bdd = build_rec(left, f, kernel, handler)?;
            let right_bdd = build_rec(right, f, kernel, handler)?;
            let binary_bdd =
                if formula.is_impl() { implication(left_bdd, right_bdd, kernel) } else { equivalence(left_bdd, right_bdd, kernel) };
            let res = kernel.add_ref(binary_bdd, handler)?;
            kernel.del_ref(left_bdd);
            kernel.del_ref(right_bdd);
            Ok(res)
        }
        And(_) | Or(_) => {
            let operands = formula.operands(f);
            let mut res = build_rec(operands[0], f, kernel, handler)?;
            for op in &operands[1..operands.len()] {
                let operand_bdd = build_rec(*op, f, kernel, handler)?;
                let previous_bdd = res;
                let nary_bdd = if formula.is_and() { and(res, operand_bdd, kernel) } else { or(res, operand_bdd, kernel) };
                res = kernel.add_ref(nary_bdd, handler)?;
                kernel.del_ref(previous_bdd);
                kernel.del_ref(operand_bdd);
            }
            Ok(res)
        }
        Cc(_) | Pbc(_) => build_rec(f.nnf_of(formula), f, kernel, handler),
    }
}

fn create_model(model_bdd: usize, kernel: &mut BddKernel) -> Option<Model> {
    if model_bdd == BDD_FALSE {
        return None;
    }
    let mut pos = Vec::new();
    let mut neg = Vec::new();
    if model_bdd == BDD_TRUE {
        return Some(Model::new(pos, neg));
    }
    let nodes = all_nodes(model_bdd, kernel);
    for node in nodes {
        let variable = kernel.get_variable_for_index(node[1]);
        if let Some(var) = variable {
            if node[2] == BDD_FALSE {
                pos.push(var);
            } else if node[3] == BDD_FALSE {
                neg.push(var);
            } else {
                panic!("Expected that the model BDD has one unique path through the BDD.");
            }
        }
    }
    Some(Model::new(pos, neg))
}

fn bdd_from_variables(variables: &[Variable], f: &FormulaFactory, kernel: &mut BddKernel) -> usize {
    let formula = f.and(variables.iter().map(|x| EncodedFormula::from(*x)));
    build_rec(formula, f, kernel, &mut NopHandler::new()).expect("Nop Handler never aborts.")
}

fn bdd_from_literals(literals: &[Literal], f: &FormulaFactory, kernel: &mut BddKernel) -> usize {
    let formula = f.and(literals.iter().map(|x| EncodedFormula::from(*x)));
    build_rec(formula, f, kernel, &mut NopHandler::new()).expect("Nop Handler never aborts.")
}

fn to_formula_rec(index: usize, f: &FormulaFactory, kernel: &mut BddKernel) -> EncodedFormula {
    if index == BDD_FALSE {
        return f.falsum();
    } else if index == BDD_TRUE {
        return f.verum();
    }
    let var_index = bdd_var(index, kernel);
    let node_variable = *kernel.idx2var.get(&var_index).unwrap();
    let rec1 = to_formula_rec(bdd_high(index, kernel), f, kernel);
    let op1 = f.and([node_variable.into(), rec1]);
    let rec2 = to_formula_rec(bdd_low(index, kernel), f, kernel);
    let op2 = f.and([node_variable.negate().into(), rec2]);
    f.or([op1, op2])
}
