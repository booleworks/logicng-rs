use std::collections::{BTreeMap, BTreeSet};

use num_bigint::BigUint;

use crate::datastructures::Model;
use crate::errors::LngResult;
use crate::formulas::{EncodedFormula, Formula, FormulaFactory, Literal, Variable};

use crate::handlers::{CancelableResult, ComputationHandler, LngComputation, LngEvent, NopHandler};
use crate::knowledge_compilation::bdd::BddError;
use crate::knowledge_compilation::bdd::bdd_construction::{
    and, bdd_high, bdd_low, bdd_var, equivalence, exists, for_all, implication, ith_var, nith_var, not, or,
};
use crate::knowledge_compilation::bdd::bdd_kernel::{BDD_FALSE, BDD_TRUE, BddKernel};
use crate::knowledge_compilation::bdd::bdd_model_enumeration::enumerate_all_models;
use crate::knowledge_compilation::bdd::bdd_normalform::normal_form;
use crate::knowledge_compilation::bdd::bdd_operations::{
    all_nodes, full_sat_one, node_count, path_count_one, path_count_zero, sat_count, sat_one, sat_one_set, var_profile,
};

use super::bdd_construction::restrict;
use super::bdd_operations::support;

/// The internal representation of a BDD.
#[derive(PartialEq, Eq, Debug, Hash)]
pub struct Bdd {
    index: usize,
}

impl Bdd {
    /// Generates a new BDD for the given formula with the given kernel.
    ///
    /// # Errors
    ///
    /// Returns an error if the formula cannot be transformed as needed, or if
    /// the kernel has no free variables left for variables in the formula.
    pub fn from_formula(formula: EncodedFormula, f: &FormulaFactory, kernel: &mut BddKernel) -> LngResult<Self> {
        let rec = build_rec(formula, f, kernel, &mut NopHandler::new())?;
        let node = rec.result().expect("nop handler can never abort");
        Ok(Self { index: node })
    }

    /// Generates a new BDD for the given formula with the given kernel.
    ///
    /// # Errors
    ///
    /// Returns an error if the formula cannot be transformed as needed, or if
    /// the kernel has no free variables left for variables in the formula.
    /// Handler cancellation is reported as [`CancelableResult::Canceled`].
    pub fn from_formula_with_handler(
        formula: EncodedFormula,
        f: &FormulaFactory,
        kernel: &mut BddKernel,
        handler: &mut dyn ComputationHandler,
    ) -> LngResult<CancelableResult<Self>> {
        if !handler.should_resume(LngEvent::ComputationStarted(LngComputation::Bdd)) {
            return Ok(CancelableResult::Canceled(LngEvent::ComputationStarted(LngComputation::Bdd)));
        }
        let rec = build_rec(formula, f, kernel, handler)?;
        match rec {
            CancelableResult::Ok(index) => Ok(CancelableResult::Ok(Self { index })),
            CancelableResult::Canceled(e) | CancelableResult::Partial(_, e) => Ok(CancelableResult::Canceled(e)),
        }
    }

    /// Returns whether this BDD represents a tautology.
    pub const fn is_tautology(&self) -> bool {
        self.index == BDD_TRUE
    }

    /// Returns whether this BDD represents a contradiction.
    pub const fn is_contradiction(&self) -> bool {
        self.index == BDD_FALSE
    }

    /// Returns an arbitrary model for this BDD.  This model does not have to contain
    /// all variables of the BDD.
    ///
    /// # Errors
    ///
    /// Returns an error if the model BDD does not have a unique path or
    /// references an unknown variable index.
    pub fn model(&self, kernel: &mut BddKernel) -> LngResult<Option<Model>> {
        let model_bdd = sat_one(self.index, kernel);
        create_model(model_bdd, kernel)
    }

    /// Returns an arbitrary model of this BDD which contains at least the given
    /// variables or None if there is none.  If a variable is a don't care variable,
    /// it will be assigned with the given default value.
    ///
    /// # Errors
    ///
    /// Returns an error if one of the requested variables is not known to the
    /// kernel, if the kernel has no free variables left, or if the resulting
    /// model BDD does not have a unique path.
    pub fn model_for_variables(
        &self,
        default: bool,
        variables: &[Variable],
        f: &FormulaFactory,
        kernel: &mut BddKernel,
    ) -> LngResult<Option<Model>> {
        let var_bdd = bdd_from_variables(variables, f, kernel)?;
        let polarity = if default { BDD_TRUE } else { BDD_FALSE };
        let model_bdd = sat_one_set(self.index, var_bdd, polarity, kernel);
        create_model(model_bdd, kernel)
    }

    /// Returns a full model of this BDD or None if there is none.
    ///
    /// # Errors
    ///
    /// Returns an error if the model BDD does not have a unique path or
    /// references an unknown variable index.
    pub fn full_model(&self, kernel: &mut BddKernel) -> LngResult<Option<Model>> {
        let model_bdd = full_sat_one(self.index, kernel);
        create_model(model_bdd, kernel)
    }

    /// Enumerate all models of this BDD.
    ///
    /// # Errors
    ///
    /// Returns an error if an enumerated model references an unknown variable
    /// index.
    pub fn enumerate_all_models(&self, kernel: &mut BddKernel) -> LngResult<Vec<Model>> {
        enumerate_all_models(self.index, None, kernel)
    }

    /// Enumerate all models of this BDD projected to the given variables.
    ///
    /// # Errors
    ///
    /// Returns an error if one of the projected variables is not known to the
    /// kernel or an enumerated model references an unknown variable index.
    pub fn enumerate_all_models_projected(&self, variables: &[Variable], kernel: &mut BddKernel) -> LngResult<Vec<Model>> {
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
    ///
    /// # Errors
    ///
    /// Returns an error if a BDD path references an unknown variable index.
    pub fn cnf(&self, f: &FormulaFactory, kernel: &mut BddKernel) -> LngResult<EncodedFormula> {
        normal_form(self.index, true, f, kernel)
    }

    /// Returns a DNF formula for this BDD.
    ///
    /// # Errors
    ///
    /// Returns an error if a BDD path references an unknown variable index.
    pub fn dnf(&self, f: &FormulaFactory, kernel: &mut BddKernel) -> LngResult<EncodedFormula> {
        normal_form(self.index, false, f, kernel)
    }

    /// Returns how often each variable occurs in this BDD.
    ///
    /// # Errors
    ///
    /// Returns an error if the profile contains a variable index unknown to the
    /// kernel.
    pub fn variable_profile(&self, kernel: &mut BddKernel) -> LngResult<BTreeMap<Variable, usize>> {
        let var_profile = var_profile(self.index, kernel);
        let mut profile = BTreeMap::new();
        for (idx, count) in var_profile.iter().enumerate() {
            let var = kernel.get_variable_for_index(idx).ok_or(BddError::InvalidVarNum { var_num: idx })?;
            profile.insert(var, *count);
        }
        Ok(profile)
    }

    /// Returns a formula representation of this BDD.  This is done by using the Shannon
    /// expansion.
    ///
    /// # Errors
    ///
    /// Returns an error if the BDD references an unknown variable or node
    /// index.
    pub fn to_formula(&self, f: &FormulaFactory, kernel: &mut BddKernel) -> LngResult<EncodedFormula> {
        to_formula_rec(self.index, f, kernel)
    }

    /// Restricts the BDD with the given literals.
    ///
    /// # Errors
    ///
    /// Returns an error if one of the restriction variables is not known to the
    /// kernel, if the kernel has no free variables left, or if an intermediate
    /// BDD node index is invalid.
    #[must_use]
    pub fn restrict(&self, restriction: &[Literal], f: &FormulaFactory, kernel: &mut BddKernel) -> LngResult<Self> {
        let var_bdd = bdd_from_literals(restriction, f, kernel)?;
        Ok(Self { index: restrict(self.index, var_bdd, kernel) })
    }

    /// Existential quantifier elimination for a given set of variables.
    ///
    /// # Errors
    ///
    /// Returns an error if one of the variables is not known to the kernel, if
    /// the kernel has no free variables left, or if an intermediate BDD node
    /// index is invalid.
    #[must_use]
    pub fn exists(&self, variables: &[Variable], f: &FormulaFactory, kernel: &mut BddKernel) -> LngResult<Self> {
        let var_bdd = bdd_from_variables(variables, f, kernel)?;
        Ok(Self { index: exists(self.index, var_bdd, kernel) })
    }

    /// Universal quantifier elimination for a given set of variables.
    ///
    /// # Errors
    ///
    /// Returns an error if one of the variables is not known to the kernel, if
    /// the kernel has no free variables left, or if an intermediate BDD node
    /// index is invalid.
    #[must_use]
    pub fn for_all(&self, variables: &[Variable], f: &FormulaFactory, kernel: &mut BddKernel) -> LngResult<Self> {
        let var_bdd = bdd_from_variables(variables, f, kernel)?;
        Ok(Self { index: for_all(self.index, var_bdd, kernel) })
    }

    /// Returns all the variables this BDD depends on.
    ///
    /// # Errors
    ///
    /// Returns an error if the support BDD cannot be converted to a model or
    /// if that model contains a negative variable.
    pub fn support(&self, kernel: &mut BddKernel) -> LngResult<BTreeSet<Variable>> {
        let support_bdd = support(self.index, kernel);
        let model = create_model(support_bdd, kernel)?;
        let mut res = BTreeSet::new();
        if let Some(m) = model {
            if !m.neg().is_empty() {
                return Err(BddError::ModelNegVar.into());
            }
            for x in m.pos() {
                res.insert(*x);
            }
        }
        Ok(res)
    }
}

fn build_rec(
    formula: EncodedFormula,
    f: &FormulaFactory,
    kernel: &mut BddKernel,
    handler: &mut dyn ComputationHandler,
) -> LngResult<CancelableResult<usize>> {
    use Formula::{And, Cc, Equiv, False, Impl, Lit, Not, Or, Pbc, True};
    match formula.unpack(f) {
        False => Ok(CancelableResult::Ok(BDD_FALSE)),
        True => Ok(CancelableResult::Ok(BDD_TRUE)),
        Lit(lit) => handle_literal(kernel, lit),
        Not(op) => handle_not(f, kernel, handler, op),
        Impl((left, right)) | Equiv((left, right)) => handle_binary(formula, f, kernel, handler, left, right),
        And(_) | Or(_) => handle_nary(formula, f, kernel, handler),
        Cc(_) | Pbc(_) => build_rec(f.nnf_of(formula)?, f, kernel, handler),
    }
}

fn handle_literal(kernel: &mut BddKernel, lit: Literal) -> Result<CancelableResult<usize>, crate::errors::LngError> {
    let idx = kernel.get_or_add_var_index(lit.variable())?;
    if lit.phase() { Ok(CancelableResult::Ok(ith_var(idx, kernel)?)) } else { Ok(CancelableResult::Ok(nith_var(idx, kernel)?)) }
}

fn handle_not(
    f: &FormulaFactory,
    kernel: &mut BddKernel,
    handler: &mut dyn ComputationHandler,
    op: EncodedFormula,
) -> Result<CancelableResult<usize>, crate::errors::LngError> {
    let operand = build_rec(op, f, kernel, handler)?;
    match operand {
        CancelableResult::Ok(o) => {
            let not_bdd = not(o, kernel);
            let res = kernel.add_ref(not_bdd, handler);
            match res {
                Ok(r) => {
                    kernel.del_ref(o);
                    Ok(CancelableResult::Ok(r))
                }
                Err(e) => Ok(CancelableResult::Canceled(e)),
            }
        }
        _ => return Ok(operand),
    }
}

fn handle_binary(
    formula: EncodedFormula,
    f: &FormulaFactory,
    kernel: &mut BddKernel,
    handler: &mut dyn ComputationHandler,
    left: EncodedFormula,
    right: EncodedFormula,
) -> Result<CancelableResult<usize>, crate::errors::LngError> {
    let left = match build_rec(left, f, kernel, handler)? {
        CancelableResult::Ok(left) => left,
        CancelableResult::Canceled(c) | CancelableResult::Partial(_, c) => return Ok(CancelableResult::Canceled(c)),
    };
    let right = match build_rec(right, f, kernel, handler)? {
        CancelableResult::Ok(right) => right,
        CancelableResult::Canceled(c) | CancelableResult::Partial(_, c) => return Ok(CancelableResult::Canceled(c)),
    };

    let binary_bdd = if formula.is_impl() { implication(left, right, kernel) } else { equivalence(left, right, kernel) };
    let res = kernel.add_ref(binary_bdd, handler);

    match res {
        Ok(r) => {
            kernel.del_ref(left);
            kernel.del_ref(right);
            Ok(CancelableResult::Ok(r))
        }
        Err(e) => Ok(CancelableResult::Canceled(e)),
    }
}

fn handle_nary(
    formula: EncodedFormula,
    f: &FormulaFactory,
    kernel: &mut BddKernel,
    handler: &mut dyn ComputationHandler,
) -> Result<CancelableResult<usize>, crate::errors::LngError> {
    let operands = formula.operands(f);
    let mut res = match build_rec(operands[0], f, kernel, handler)? {
        CancelableResult::Ok(r) => r,
        CancelableResult::Canceled(c) | CancelableResult::Partial(_, c) => return Ok(CancelableResult::Canceled(c)),
    };
    for op in &operands[1..operands.len()] {
        let operand_bdd = match build_rec(*op, f, kernel, handler)? {
            CancelableResult::Ok(r) => r,
            CancelableResult::Canceled(c) | CancelableResult::Partial(_, c) => {
                kernel.del_ref(res);
                return Ok(CancelableResult::Canceled(c));
            }
        };
        let previous_bdd = res;
        let nary_bdd = if formula.is_and() { and(res, operand_bdd, kernel) } else { or(res, operand_bdd, kernel) };
        res = match kernel.add_ref(nary_bdd, handler) {
            Ok(r) => {
                kernel.del_ref(previous_bdd);
                kernel.del_ref(operand_bdd);
                r
            }
            Err(e) => {
                kernel.del_ref(previous_bdd);
                kernel.del_ref(operand_bdd);
                return Ok(CancelableResult::Canceled(e));
            }
        }
    }
    Ok(CancelableResult::Ok(res))
}

fn create_model(model_bdd: usize, kernel: &mut BddKernel) -> LngResult<Option<Model>> {
    if model_bdd == BDD_FALSE {
        return Ok(None);
    }
    let mut pos = Vec::new();
    let mut neg = Vec::new();
    if model_bdd == BDD_TRUE {
        return Ok(Some(Model::new(pos, neg)));
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
                return Err(BddError::NoUniquePath.into());
            }
        }
    }
    Ok(Some(Model::new(pos, neg)))
}

fn bdd_from_variables(variables: &[Variable], f: &FormulaFactory, kernel: &mut BddKernel) -> LngResult<usize> {
    let formula = f.and(variables.iter().map(|x| EncodedFormula::from(*x)));
    let rec = build_rec(formula, f, kernel, &mut NopHandler::new())?;
    let node = rec.result().expect("nop handler can never abort");
    Ok(node)
}

fn bdd_from_literals(literals: &[Literal], f: &FormulaFactory, kernel: &mut BddKernel) -> LngResult<usize> {
    let formula = f.and(literals.iter().map(|x| EncodedFormula::from(*x)));
    let rec = build_rec(formula, f, kernel, &mut NopHandler::new())?;
    let node = rec.result().expect("nop handler can never abort");
    Ok(node)
}

fn to_formula_rec(index: usize, f: &FormulaFactory, kernel: &mut BddKernel) -> LngResult<EncodedFormula> {
    if index == BDD_FALSE {
        return Ok(f.falsum());
    } else if index == BDD_TRUE {
        return Ok(f.verum());
    }
    let var_index = bdd_var(index, kernel)?;
    let node_variable = *kernel.idx2var.get(&var_index).ok_or(BddError::InvalidVarNum { var_num: var_index })?;
    let rec1 = to_formula_rec(bdd_high(index, kernel)?, f, kernel)?;
    let op1 = f.and([node_variable.into(), rec1]);
    let rec2 = to_formula_rec(bdd_low(index, kernel)?, f, kernel)?;
    let op2 = f.and([node_variable.negate().into(), rec2]);
    Ok(f.or([op1, op2]))
}
