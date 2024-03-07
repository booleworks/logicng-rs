#![allow(clippy::cast_possible_wrap)]

use std::collections::BTreeMap;
use std::fmt::Display;
use std::sync::Arc;
use CType::{GE, GT, LE, LT};

use crate::cardinality_constraints::CcEncoder;
use crate::datastructures::Assignment;
use crate::formulas::CType::EQ;
use crate::formulas::{EncodedFormula, FormulaFactory, Literal, Variable};
use crate::pseudo_booleans::PbEncoder;
use crate::solver::minisat::sat::Tristate;
use crate::solver::minisat::sat::Tristate::{False, True, Undef};
use crate::util::exceptions::panic_unexpected_formula_type;

use super::FormulaType;


/// Comparison types for pseudo-Boolean constraints.
#[derive(Hash, Eq, PartialEq, Debug, Clone, Copy)]
pub enum CType {
    /// equals
    EQ,
    /// greater than
    GT,
    /// greater equals
    GE,
    /// less than
    LT,
    /// less equals
    LE,
}

/// Cardinality constraints `CardinalityConstraint` are a special type of
/// formulas which enforce that a certain number of variables is assigned to
/// true.
///
/// `CardinalityConstraint` can be of type _at least k_, _exactly k_ or _at most
/// k_, for some integer `k`. For example, a cardinality constraint of type "at
/// most 1" is:
///
/// ```text
/// A + B + C <= 1
/// ```
///
/// And expresses the fact that from the variables `A`, `B`, `C` at most one
/// variable is assigned to true. Meaning the formula is satisfied by exactly 4
/// assignments
///
/// - `A, ~B, ~C`
/// - `~A, B, ~C`
/// - `~A, ~B, C`
/// - `~A, ~B, ~C`
///
/// At-most-one (AMO) and exactly-one (EXO) constraints play a special role
/// since they are very often used in real world problems. For example if you
/// think of a car configuration, a valid vehicle must have exactly one steering
/// wheel and can have at most one trailer hitch.
///
/// ## Creating Cardinality Constraints
///
/// On very few occasions you want to have a pure `CardinalityConstraint`
/// instance. More common is a cardinality constraint as a [`EncodedFormula`].
/// For that, you can use [`cc()`] in [`FormulaFactory`]. That function also
/// checks that your input is reasonable.
///
/// Additionally to [`cc()`], there are also [`amo()`] and [`exo()`] constructor
/// functions in `FormulaFactory`. Those are abbreviations for common
/// cardinality constraints:
/// - `amo()`: `v_1 + v_2 + ... + v_n <= 1` (_at most one_)
/// - `exo()`: `v_1 + v_2 + ... + v_n = 1` (_exactly one_)
///
/// `CardinalityConstraint` itself has no public constructor. But you can use
/// [`EncodedFormula::unpack()`] or [`EncodedFormula::as_cc()`] to get access to
/// the `CardinalityConstraint` within the `FormulaFactory`.
///
/// # Example
/// ```
/// # use logicng::formulas::{FormulaFactory, EncodedFormula, CType};
/// let f = FormulaFactory::new();
///
/// let a = f.var("a");
/// let b = f.var("b");
/// let c = f.var("c");
///
/// let cc: EncodedFormula = f.cc(CType::GE, 2, vec![a, b, c]);
/// let amo: EncodedFormula = f.amo(vec![a, b, c]);
/// let exo: EncodedFormula = f.exo(vec![a, b, c]);
///
/// assert_eq!(cc.to_string(&f), "a + b + c >= 2");
/// assert_eq!(amo.to_string(&f), "a + b + c <= 1");
/// assert_eq!(exo.to_string(&f), "a + b + c = 1")
/// ```
///
/// [`cc()`]: FormulaFactory::cc
/// [`amo()`]: FormulaFactory::cc
/// [`exo()`]: FormulaFactory::cc
#[derive(Hash, Eq, PartialEq, Clone, Debug)]
pub struct CardinalityConstraint {
    /// variables on the left side of the cardinality constraint.
    pub variables: Box<[Variable]>,
    /// comparator of the cardinality constraint.
    pub comparator: CType,
    /// value on the right side of the cardinality constraint.
    pub rhs: u32,
}

/// A pseudo-boolean constraint [`PbConstraint`] is a generalization of a
/// [`CardinalityConstraint`].
///
/// In a cardinality constraint, every variable has the same weight (i.e. 1); In
/// a pseudo-boolean constraint, each variable can have a different weight.
/// Further, pseudo-boolean constraints admit negated variables (literals),
/// whereas cardinality constraints only admit variables.
///
/// Pseudo-Boolean constraints have the form
///
/// ```text
/// c_1 * l_1 + c_2 * l_2 + ... + c_n * lit_n [?] k
/// ```
///
/// where:
///
/// - `l_i` are Boolean literals, evaluating to `true` and `false`, for `1 <= i
///   <= n`
/// - `c_i` are integer coefficients, the "weights" of the literals, for `1 <= i
///   <= n`
/// - `[?]` is a comparison operator `<=`, `<`, `>`, `>=` or `=`
///
/// A solution of a PB-constraint is an assignment of variables which satisfies
/// the constraint.
///
/// Some examples for pseudo-Boolean constraints are:
///
/// - Clauses: `A | ~B | C` is equivalent to `A + ~B + C >= 1`,
/// - Cardinality constraints: `A + B + C >= 3`. Cardinality constraints are a
///   special case of PB-constraints, where every coefficient is 1.
/// - General constraints: `A + 2*~B - 3*C = 2`
///
/// ## Creating Pseudo-boolean Constraints
///
/// On very few occasions you want to have a pure `PbConstraint` instance. More
/// common is a pseudo-boolean constraint as a [`EncodedFormula`]. For that, you
/// can use [`pbc()`] in [`FormulaFactory`]. That function also checks that your
/// input is reasonable and it creates a [`CardinalityConstraint`], if your
/// input is a cardinality constraint problem. By doing that, we can ensure that
/// no `PbConstraint` instance is a cardinality constraint problem.
///
/// `PbConstraint` itself has no public constructor. But you can use
/// [`EncodedFormula::unpack()`] or [`EncodedFormula::as_pbc()`] to get access
/// to the `PbConstraint` instance within the `FormulaFactory`.
///
/// [`pbc()`]: FormulaFactory::pbc
#[derive(Hash, Eq, PartialEq, Clone, Debug)]
pub struct PbConstraint {
    /// variables on the left side of the pseudo-boolean constraint.
    pub literals: Box<[Literal]>,
    /// coefficients of the pseudo-boolean constraint.
    pub coefficients: Box<[i64]>,
    /// comparator of the pseudo-boolean constraint.
    pub comparator: CType,
    /// value on the right side of the pseudo-boolean constraint.
    pub rhs: i64,
}

impl Display for CType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            EQ => "=",
            GT => ">",
            GE => ">=",
            LT => "<",
            LE => "<=",
        })
    }
}

impl CardinalityConstraint {
    pub(crate) fn new(variables: Box<[Variable]>, comparator: CType, rhs: u32) -> Self {
        Self { variables, comparator, rhs }
    }

    /// Returns true, if this `CardinalityConstraint` is a _at most one_ problem.
    ///
    /// # Example
    ///
    /// Basic Usage
    /// ```
    /// # use logicng::formulas::{FormulaFactory, ToFormula};
    /// let f = FormulaFactory::new();
    ///
    /// let formula1 = "a + b <= 1".to_formula(&f);
    /// let formula2 = "a + b < 2".to_formula(&f);
    /// let formula3 = "a + b = 1".to_formula(&f);
    ///
    /// let cc1 = formula1.as_cc(&f).unwrap();
    /// let cc2 = formula2.as_cc(&f).unwrap();
    /// let cc3 = formula3.as_cc(&f).unwrap();
    ///
    /// assert_eq!(cc1.is_amo(), true);
    /// assert_eq!(cc2.is_amo(), true);
    /// assert_eq!(cc3.is_amo(), false);
    /// ```
    pub fn is_amo(&self) -> bool {
        self.comparator == LE && self.rhs == 1 || self.comparator == LT && self.rhs == 2
    }

    /// Returns true, if this `CardinalityConstraint` is a _exactly one_ problem.
    ///
    /// # Example
    ///
    /// Basic Usage
    /// ```
    /// # use logicng::formulas::{FormulaFactory, ToFormula};
    /// let f = FormulaFactory::new();
    ///
    /// let formula1 = "a + b = 1".to_formula(&f);
    /// let formula2 = "a + b <= 1".to_formula(&f);
    /// let formula3 = "a + b < 2".to_formula(&f);
    ///
    /// let cc1 = formula1.as_cc(&f).unwrap();
    /// let cc2 = formula2.as_cc(&f).unwrap();
    /// let cc3 = formula3.as_cc(&f).unwrap();
    ///
    /// assert_eq!(cc1.is_exo(), true);
    /// assert_eq!(cc2.is_exo(), false);
    /// assert_eq!(cc3.is_exo(), false);
    /// ```
    pub fn is_exo(&self) -> bool {
        self.comparator == EQ && self.rhs == 1
    }

    /// Encodes this `CardinalityConstraint` into a vector of simple formulas.
    ///
    /// Some applications, such as _SAT solvers_, cannot deal with cardinality
    /// constraints in their "natural form" since a cardinality constraint is
    /// not a purely Boolean construct. Thus, the cardinality constraints have
    /// to be _encoded_ to CNF before added to the solver. An encoded
    /// cardinality constraint does not contain any signs like `<=`, `>=`, `<`,
    /// `>` and `=` anymore but is a proper Boolean formula in CNF. There exist
    /// many algorithms for encoding cardinality constraints, depending on their
    /// type.
    ///
    /// The exact encoding algorithm is defined in the [`CcConfig`] of the
    /// [`FormulaFactory`].
    ///
    /// [`CcConfig`]: crate::cardinality_constraints::CcConfig
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::formulas::{FormulaFactory, ToFormula};
    /// let f = FormulaFactory::new();
    ///
    /// let formula = "a + b = 1".to_formula(&f).as_cc(&f).unwrap();
    /// let encoded = formula.encode(&f);
    /// ```
    pub fn encode(&self, f: &FormulaFactory) -> Arc<[EncodedFormula]> {
        let index = f.ccs.lookup(self).expect("Cardinality Constraint must be present in FF");
        if let Some(cached) = f.caches.cc_encoding.get(&index) {
            return cached.clone();
        }
        let result: Arc<[_]> = Arc::from(CcEncoder::new(f.config.cc_config.clone()).encode(self, f));
        if f.config.caches.cc_encoding {
            f.caches.cc_encoding.insert(index, result.clone());
        }
        result
    }

    /// Evaluates this constraint based on `assignment`.
    ///
    /// Any literal not covered by `assignment` evaluates to `false` if it is
    /// positive, or to `true` if it is negative. In other words, it will be
    /// evaluated in such a way, that it is not satisfied. This behavior ensures
    /// that the constraint evaluates to a `true/false` value. Unlike
    /// [`restrict`], which only applies the literals of given assignment.
    /// However, this might not be enough to fully evaluate a constraint.
    ///
    /// [`restrict`]: CardinalityConstraint::restrict
    pub fn evaluate(&self, assignment: &Assignment) -> bool {
        let lhs = self.variables.iter().map(|v| assignment.evaluate_lit(v.pos_lit())).filter(|b| *b).count();
        evaluate_comparator(lhs as i64, self.comparator, self.rhs.into())
    }

    /// Restricts this constraint with the give assignment.
    ///
    /// If you want to fully evaluate a formula, consider to use `evaluate`.
    /// `evaluate` ensures that a formula evaluates to a `true/false` value by
    /// assuming that literals not in the assignment are unsatisfiable.
    ///
    /// [`evaluate`]: CardinalityConstraint::evaluate
    pub fn restrict(&self, assignment: &Assignment, f: &FormulaFactory) -> EncodedFormula {
        let mut satisfied = 0;
        let mut remaining = vec![];
        for &var in &*self.variables {
            match assignment.restrict_lit(var.pos_lit()).formula_type() {
                FormulaType::Lit(_) => remaining.push(var),
                FormulaType::True => satisfied += 1,
                FormulaType::False => {}
                _ => panic_unexpected_formula_type(var.into(), Some(f)),
            }
        }
        if satisfied > self.rhs {
            match self.comparator {
                EQ | LT | LE => f.falsum(),
                GT | GE => f.verum(),
            }
        } else if satisfied == self.rhs && self.comparator == LT {
            f.falsum()
        } else {
            f.cc(self.comparator, self.rhs - satisfied, remaining)
        }
    }

    /// Returns a negated copy of this constraint.
    pub fn negate(&self, f: &FormulaFactory) -> EncodedFormula {
        match self.comparator {
            EQ => {
                let lt = f.pbc(
                    LT,
                    self.rhs.into(),
                    self.variables.iter().map(Variable::pos_lit).collect::<Box<[_]>>(),
                    vec![1; self.variables.len()],
                );
                let gt = f.pbc(
                    GT,
                    self.rhs.into(),
                    self.variables.iter().map(Variable::pos_lit).collect::<Box<[_]>>(),
                    vec![1; self.variables.len()],
                );
                f.or([lt, gt])
            }
            GT => f.pbc(
                LE,
                self.rhs.into(),
                self.variables.iter().map(Variable::pos_lit).collect::<Box<[_]>>(),
                vec![1; self.variables.len()],
            ),
            GE => f.pbc(
                LT,
                self.rhs.into(),
                self.variables.iter().map(Variable::pos_lit).collect::<Box<[_]>>(),
                vec![1; self.variables.len()],
            ),
            LT => f.pbc(
                GE,
                self.rhs.into(),
                self.variables.iter().map(Variable::pos_lit).collect::<Box<[_]>>(),
                vec![1; self.variables.len()],
            ),
            LE => f.pbc(
                GT,
                self.rhs.into(),
                self.variables.iter().map(Variable::pos_lit).collect::<Box<[_]>>(),
                vec![1; self.variables.len()],
            ),
        }
    }

    /// Converts this formula into a string representation.
    ///
    /// Strings obtained by this function, can also be parsed back again.
    pub fn to_string(&self, f: &FormulaFactory) -> String {
        let lhs = self.variables.iter().map(|v| v.pos_lit().to_string(f)).collect::<Vec<String>>().join(" + ");
        format!("{lhs} {} {}", self.comparator, self.rhs)
    }
}

impl PbConstraint {
    pub(crate) fn new(literals: Box<[Literal]>, coefficients: Box<[i64]>, comparator: CType, rhs: i64) -> Self {
        Self { literals, coefficients, comparator, rhs }
    }

    /// Returns the value of the largest coefficient.
    pub fn max_weight(&self) -> i64 {
        *self.coefficients.iter().max().expect("A pseudo-boolean constraint without literals should never be created.")
    }

    /// Encodes this `PbConstraint` into a vector of simple formulas.
    ///
    /// Some applications, such as _SAT solvers_,
    /// cannot deal with pseudo-Boolean constraints in their "natural form"
    /// since a pseudo-Boolean constraint is not a purely Boolean construct.
    /// Thus, the constraints have to be *encoded* to CNF before added to the
    /// solver. An encoded pseudo-Boolean constraint does not contain any signs
    /// like `<=`, `>=`, `<`, `>` and `=` or any coefficients anymore but is a
    /// proper Boolean formula in CNF.  There exist many algorithms for encoding
    /// pseudo-Boolean constraints, depending on their type.
    ///
    /// The exact encoding algorithm is defined in the [`PbConfig`] of the
    /// [`FormulaFactory`].
    ///
    /// [`PbConfig`]: crate::pseudo_booleans::PbConfig
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::formulas::{FormulaFactory, ToFormula};
    /// let f = FormulaFactory::new();
    ///
    /// let formula = "2 * a + 3 * b = 2".to_formula(&f).as_pbc(&f).unwrap();
    /// let encoded = formula.encode(&f);
    /// ```
    pub fn encode(&self, f: &FormulaFactory) -> Arc<[EncodedFormula]> {
        let index = f.pbcs.lookup(self).expect("Pseudo-Boolean Constraint must be present in FF");
        if let Some(cached) = f.caches.pbc_encoding.get(&index) {
            return cached.clone();
        }
        let result: Arc<[_]> = PbEncoder::new(f.config.pb_config.clone()).encode(self, f);
        if f.config.caches.pbc_encoding {
            f.caches.pbc_encoding.insert(index, result.clone());
        }
        result
    }

    /// Evaluates this constraint based on `assignment`.
    ///
    /// Any literal not covered by `assignment` evaluates to `false` if it is
    /// positive, or to `true` if it is negative. In other words, it will be
    /// evaluated in such a way, that it is not satisfied. This behavior ensures
    /// that the constraint evaluates to a `true/false` value. Unlike
    /// [`restrict`], which only applies the literals of given assignment.
    /// However, this might not be enough to fully evaluate a constraint.
    ///
    /// [`restrict`]: PbConstraint::restrict
    pub fn evaluate(&self, assignment: &Assignment) -> bool {
        evaluate_comparator(self.evaluate_lhs(assignment), self.comparator, self.rhs)
    }

    /// Restricts this constraint with the give assignment.
    ///
    /// If you want to fully evaluate a formula, consider to use `evaluate`.
    /// `evaluate` ensures that a formula evaluates to a `true/false` value by
    /// assuming that literals not in the assignment are unsatisfiable.
    ///
    /// [`evaluate`]: PbConstraint::evaluate
    pub fn restrict(&self, assignment: &Assignment, f: &FormulaFactory) -> EncodedFormula {
        let mut new_lits = Vec::with_capacity(self.literals.len());
        let mut new_coeffs = Vec::with_capacity(self.coefficients.len());
        let mut lhs_fixed = 0;
        let mut min_value = 0;
        let mut max_value = 0;
        for i in 0..self.literals.len() {
            let lit = self.literals[i];
            match assignment.restrict_lit(lit).formula_type() {
                FormulaType::Lit(_) => {
                    new_lits.push(lit);
                    let coeff = self.coefficients[i];
                    new_coeffs.push(coeff);
                    if coeff > 0 {
                        max_value += coeff;
                    } else {
                        min_value += coeff;
                    };
                }
                FormulaType::True => lhs_fixed += self.coefficients[i],
                FormulaType::False => {}
                _ => unreachable!("The function `restrict_lit` can only produce `True`, `False`, or `Lit`."),
            }
        }

        if new_lits.is_empty() {
            return f.constant(evaluate_comparator(lhs_fixed, self.comparator, self.rhs));
        }

        let new_rhs = self.rhs - lhs_fixed;
        if self.comparator != EQ {
            let fixed = evaluate_coeffs(min_value, max_value, new_rhs, self.comparator);
            if fixed == True {
                return f.verum();
            } else if fixed == False {
                return f.falsum();
            }
        }
        f.pbc(self.comparator, new_rhs, new_lits, new_coeffs)
    }

    /// Returns a negated copy of this constraint as a [`EncodedFormula`].
    pub fn negate(&self, f: &FormulaFactory) -> EncodedFormula {
        match self.comparator {
            EQ => {
                let lt = f.pbc(LT, self.rhs, self.literals.clone(), self.coefficients.clone());
                let gt = f.pbc(GT, self.rhs, self.literals.clone(), self.coefficients.clone());
                f.or([lt, gt])
            }
            GT => f.pbc(LE, self.rhs, self.literals.clone(), self.coefficients.clone()),
            GE => f.pbc(LT, self.rhs, self.literals.clone(), self.coefficients.clone()),
            LT => f.pbc(GE, self.rhs, self.literals.clone(), self.coefficients.clone()),
            LE => f.pbc(GT, self.rhs, self.literals.clone(), self.coefficients.clone()),
        }
    }

    /// Normalizes this constraint s.t. it can be converted to CNF.
    pub fn normalize(&self, f: &FormulaFactory) -> EncodedFormula {
        let mut norm_ps = Vec::with_capacity(self.literals.len());
        let mut norm_cs = Vec::with_capacity(self.literals.len());
        let mut norm_rhs;
        match self.comparator {
            EQ => {
                for i in 0..self.literals.len() {
                    norm_ps.push(self.literals[i]);
                    norm_cs.push(self.coefficients[i]);
                }
                norm_rhs = self.rhs;
                let f1 = normalize_le(&mut norm_ps, &mut norm_cs, norm_rhs, f);
                norm_ps.clear();
                norm_cs.clear();
                for i in 0..self.literals.len() {
                    norm_ps.push(self.literals[i]);
                    norm_cs.push(-self.coefficients[i]);
                }
                norm_rhs = -self.rhs;
                let f2 = normalize_le(&mut norm_ps, &mut norm_cs, norm_rhs, f);
                f.and([f1, f2])
            }
            LT | LE => {
                for i in 0..self.literals.len() {
                    norm_ps.push(self.literals[i]);
                    norm_cs.push(self.coefficients[i]);
                }
                norm_rhs = if self.comparator == LE { self.rhs } else { self.rhs - 1 };
                normalize_le(&mut norm_ps, &mut norm_cs, norm_rhs, f)
            }
            GT | GE => {
                for i in 0..self.literals.len() {
                    norm_ps.push(self.literals[i]);
                    norm_cs.push(-self.coefficients[i]);
                }
                norm_rhs = if self.comparator == GE { -self.rhs } else { -self.rhs - 1 };
                normalize_le(&mut norm_ps, &mut norm_cs, norm_rhs, f)
            }
        }
    }

    /// Converts this formula into a string representation.
    ///
    /// Strings obtained by this function, can also be parsed back again.
    pub fn to_string(&self, f: &FormulaFactory) -> String {
        let lhs = self
            .literals
            .iter()
            .zip(self.coefficients.iter())
            .map(|pair| if *pair.1 == 1 { pair.0.to_string(f) } else { format!("{}*{}", pair.1, pair.0.to_string(f)) })
            .collect::<Vec<String>>()
            .join(" + ");
        format!("{lhs} {} {}", self.comparator, self.rhs)
    }

    fn evaluate_lhs(&self, assignment: &Assignment) -> i64 {
        let mut lhs = 0;
        for i in 0..self.literals.len() {
            let lit = &self.literals[i];
            if assignment.evaluate_lit(*lit) {
                lhs += self.coefficients[i];
            }
        }
        lhs
    }
}

/// Returns `true` if and only if the equation holds.
pub const fn evaluate_comparator(lhs: i64, comparator: CType, rhs: i64) -> bool {
    match comparator {
        EQ => lhs == rhs,
        GT => lhs > rhs,
        GE => lhs >= rhs,
        LT => lhs < rhs,
        LE => lhs <= rhs,
    }
}

const fn evaluate_coeffs(min_value: i64, max_value: i64, rhs: i64, comparator: CType) -> Tristate {
    let mut status = 0;
    if rhs >= min_value {
        status += 1;
    }
    if rhs > min_value {
        status += 1;
    }
    if rhs >= max_value {
        status += 1;
    }
    if rhs > max_value {
        status += 1;
    }
    match comparator {
        EQ => {
            if status == 0 || status == 4 {
                False
            } else {
                Undef
            }
        }
        LE => {
            if status >= 3 {
                True
            } else if status < 1 {
                False
            } else {
                Undef
            }
        }
        LT => {
            if status > 3 {
                True
            } else if status <= 1 {
                False
            } else {
                Undef
            }
        }
        GE => {
            if status <= 1 {
                True
            } else if status > 3 {
                False
            } else {
                Undef
            }
        }
        GT => {
            if status < 1 {
                True
            } else if status >= 3 {
                False
            } else {
                Undef
            }
        }
    }
}

fn normalize_le(ps: &mut Vec<Literal>, cs: &mut Vec<i64>, rhs: i64, f: &FormulaFactory) -> EncodedFormula {
    let mut c = rhs;
    let mut new_size: usize = 0;
    for i in 0..ps.len() {
        if cs[i] != 0 {
            ps[new_size] = ps[i];
            cs[new_size] = cs[i];
            new_size += 1;
        }
    }
    ps.truncate(new_size);
    cs.truncate(new_size);
    let mut var2consts = BTreeMap::new();
    for i in 0..ps.len() {
        let x = ps[i].variable();
        let consts = *var2consts.get(&x).unwrap_or(&(0, 0));
        if ps[i].phase() {
            var2consts.insert(x, (consts.0, consts.1 + cs[i]));
        } else {
            var2consts.insert(x, (consts.0 + cs[i], consts.1));
        }
    }
    let mut csps = Vec::with_capacity(var2consts.len());
    for (variable, (first, second)) in var2consts {
        if first < second {
            c -= first;
            csps.push((second - first, variable.pos_lit()));
        } else {
            c -= second;
            csps.push((first - second, variable.neg_lit()));
        }
    }
    let mut sum = 0;
    cs.clear();
    ps.clear();
    for (coeff, lit) in csps {
        if coeff != 0 {
            cs.push(coeff);
            ps.push(lit);
            sum += coeff;
        }
    }
    let mut changed = true;
    while changed {
        changed = false;
        if c < 0 {
            return f.falsum();
        }
        if sum <= c {
            return f.verum();
        }
        let mut div = c;
        for e in &*cs {
            div = gcd(div, *e);
        }
        if div != 0 && div != 1 {
            for e in &mut *cs {
                *e /= div;
            }
            c /= div;
            changed = true;
        }
    }
    f.pbc(LE, c, ps.clone(), cs.clone())
}

fn gcd(small: i64, big: i64) -> i64 {
    if small == 0 {
        big
    } else {
        gcd(big % small, small)
    }
}

#[allow(non_snake_case)]
#[cfg(test)]
mod tests {
    use crate::formulas::pbc_cc::evaluate_coeffs;
    use crate::formulas::CType::{EQ, GE, GT, LE, LT};
    use crate::formulas::{FormulaFactory, ToFormula};
    use crate::solver::minisat::sat::Tristate::{False, True, Undef};

    #[test]
    fn test_normalization() {
        let f = &FormulaFactory::new();
        let lits: Box<[_]> = vec![f.lit("a", true), f.lit("b", false), f.lit("c", true), f.lit("d", true), f.lit("b", false)].into();
        let coeffs: Box<[_]> = vec![2, -3, 3, 0, 1].into();
        let pb1 = f.pbc(EQ, 2, lits.clone(), coeffs.clone());
        let pb2 = f.pbc(GE, 1, lits.clone(), coeffs.clone());
        let pb3 = f.pbc(GT, 0, lits.clone(), coeffs.clone());
        let pb4 = f.pbc(LE, 1, lits.clone(), coeffs.clone());
        let pb5 = f.pbc(LT, 2, lits, coeffs);
        assert_eq!("(2*a + 2*b + 3*c <= 4) & (2*~a + 2*~b + 3*~c <= 3)".to_formula(f), pb1.as_pbc(f).unwrap().normalize(f));
        assert_eq!("2*~a + 2*~b + 3*~c <= 4".to_formula(f), pb2.as_pbc(f).unwrap().normalize(f));
        assert_eq!("2*~a + 2*~b + 3*~c <= 4".to_formula(f), pb3.as_pbc(f).unwrap().normalize(f));
        assert_eq!("2*a + 2*b + 3*c <= 3".to_formula(f), pb4.as_pbc(f).unwrap().normalize(f));
        assert_eq!("2*a + 2*b + 3*c <= 3".to_formula(f), pb5.as_pbc(f).unwrap().normalize(f));
    }

    #[test]
    fn test_normalization_trivial() {
        let f = &FormulaFactory::new();
        let lits: Box<[_]> = vec![f.lit("a", true), f.lit("b", false), f.lit("c", true), f.lit("d", true)].into();
        let coeffs: Box<[_]> = vec![2, -2, 3, 0].into();
        let pb1 = f.pbc(LE, 4, lits.clone(), coeffs.clone());
        let pb2 = f.pbc(LE, 5, lits.clone(), coeffs.clone());
        let pb3 = f.pbc(LE, 7, lits.clone(), coeffs.clone());
        let pb4 = f.pbc(LE, 10, lits.clone(), coeffs.clone());
        let pb5 = f.pbc(LE, -3, lits, coeffs);
        assert_eq!("2*a + 2*b + 3*c <= 6".to_formula(f), pb1.as_pbc(f).unwrap().normalize(f));
        assert_eq!(f.verum(), pb2.as_pbc(f).unwrap().normalize(f));
        assert_eq!(f.verum(), pb3.as_pbc(f).unwrap().normalize(f));
        assert_eq!(f.verum(), pb4.as_pbc(f).unwrap().normalize(f));
        assert_eq!(f.falsum(), pb5.as_pbc(f).unwrap().normalize(f));
    }

    #[test]
    fn test_normalization_simplifications() {
        let f = &FormulaFactory::new();
        let lits: Box<[_]> = vec![f.lit("a", true), f.lit("a", true), f.lit("c", true), f.lit("d", true)].into();
        let coeffs: Box<[_]> = vec![2, -2, 4, 4].into();
        let pb1 = f.pbc(LE, 4, lits, coeffs);
        assert_eq!("c + d <= 1".to_formula(f), pb1.as_pbc(f).unwrap().normalize(f));
        assert!(pb1.as_pbc(f).unwrap().normalize(f).is_cc());

        let lits2: Box<[_]> = vec![f.lit("a", true), f.lit("a", false), f.lit("c", true), f.lit("d", true)].into();
        let coeffs2: Box<[_]> = vec![2, 2, 4, 2].into();
        let pb2 = f.pbc(LE, 4, lits2, coeffs2);
        assert_eq!("2*c + d <= 1".to_formula(f), pb2.as_pbc(f).unwrap().normalize(f));
    }

    #[test]
    #[allow(clippy::cognitive_complexity)]
    fn test_evaluate_coeffs() {
        assert_eq!(evaluate_coeffs(-2, 2, -3, EQ), False);
        assert_eq!(evaluate_coeffs(-2, 2, 3, EQ), False);
        assert_eq!(evaluate_coeffs(-2, 2, -2, EQ), Undef);
        assert_eq!(evaluate_coeffs(-2, 2, 2, EQ), Undef);
        assert_eq!(evaluate_coeffs(-2, 2, 0, EQ), Undef);

        assert_eq!(evaluate_coeffs(-2, 2, -3, GE), True);
        assert_eq!(evaluate_coeffs(-2, 2, 3, GE), False);
        assert_eq!(evaluate_coeffs(-2, 2, -2, GE), True);
        assert_eq!(evaluate_coeffs(-2, 2, 2, GE), Undef);
        assert_eq!(evaluate_coeffs(-2, 2, 0, GE), Undef);

        assert_eq!(evaluate_coeffs(-2, 2, -3, GT), True);
        assert_eq!(evaluate_coeffs(-2, 2, 3, GT), False);
        assert_eq!(evaluate_coeffs(-2, 2, -2, GT), Undef);
        assert_eq!(evaluate_coeffs(-2, 2, 2, GT), False);
        assert_eq!(evaluate_coeffs(-2, 2, 0, GT), Undef);

        assert_eq!(evaluate_coeffs(-2, 2, -3, LE), False);
        assert_eq!(evaluate_coeffs(-2, 2, 3, LE), True);
        assert_eq!(evaluate_coeffs(-2, 2, -2, LE), Undef);
        assert_eq!(evaluate_coeffs(-2, 2, 2, LE), True);
        assert_eq!(evaluate_coeffs(-2, 2, 0, LE), Undef);

        assert_eq!(evaluate_coeffs(-2, 2, -3, LT), False);
        assert_eq!(evaluate_coeffs(-2, 2, 3, LT), True);
        assert_eq!(evaluate_coeffs(-2, 2, -2, LT), False);
        assert_eq!(evaluate_coeffs(-2, 2, 2, LT), Undef);
        assert_eq!(evaluate_coeffs(-2, 2, 0, LT), Undef);
    }
}
