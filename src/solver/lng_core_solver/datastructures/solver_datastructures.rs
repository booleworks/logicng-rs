use crate::propositions::Proposition;

/// Internal representation of a variable on the solver.
#[derive(Debug, Clone, Copy, PartialOrd, Ord, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct LngVar(pub usize);

impl LngVar {
    /// Last possible representation of a variable.
    pub const UNDEF: Self = Self(usize::MAX);
}

/// Internal representation of a literal on the solver.
#[derive(Debug, Clone, Copy, PartialOrd, Ord, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct LngLit(pub usize);

impl LngLit {
    /// Last possible representation of a literal.
    pub const UNDEF: Self = Self(usize::MAX);
    pub const ERROR: Self = Self(usize::MAX - 1);
}

/// Constructs an MiniSAT literal from a MiniSAT variable.
pub fn mk_lit(var: LngVar, sign: bool) -> LngLit {
    LngLit(var.0 + var.0 + usize::from(sign))
}

/// Constructs the negation of a MiniSAT literal.
pub const fn not(lit: LngLit) -> LngLit {
    LngLit(lit.0 ^ 1)
}

/// Returns the sign of the literal.
pub const fn sign(lit: LngLit) -> bool {
    lit.0 & 1 == 1
}

/// Returns the MiniSAT variable of MiniSAT variable.
pub const fn var(lit: LngLit) -> LngVar {
    LngVar(lit.0 >> 1)
}

#[derive(Debug, Clone, Copy, PartialOrd, Ord, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct LngState(pub usize);

#[derive(Debug, Eq, PartialEq, PartialOrd, Ord, Clone, Hash)]
pub struct SolverState {
    pub id: LngState,
    pub ok: bool,
    pub vars_size: usize,
    pub all_clause_size: usize,
    pub clause_size: usize,
    pub unit_clause_size: usize,
    pub pg_original_size: usize,
    pub pg_proof_size: usize,
}

#[allow(clippy::struct_excessive_bools)]
#[derive(Clone, PartialEq, Debug)]
pub struct LngClause {
    pub data: Vec<LngLit>,
    pub learnt_on_state: Option<LngState>,
    pub is_at_most: bool,
    pub activity: f64,
    pub seen: bool,
    pub lbd: usize,
    pub can_be_del: bool,
    pub one_watched: bool,
    pub at_most_watchers: Option<usize>,
}

impl LngClause {
    pub fn new(data: Vec<LngLit>, learnt_on_state: Option<LngState>, is_at_most: bool) -> Self {
        Self {
            data,
            learnt_on_state,
            is_at_most,
            activity: 0.0,
            seen: false,
            lbd: 0,
            can_be_del: true,
            one_watched: false,
            at_most_watchers: None,
        }
    }

    pub fn len(&self) -> usize {
        self.data.len()
    }

    pub fn get(&self, i: usize) -> LngLit {
        self.data[i]
    }

    pub fn set(&mut self, i: usize, lit: LngLit) {
        self.data[i] = lit;
    }

    pub fn increment_activity(&mut self, inc: f64) {
        self.activity += inc;
    }

    pub fn rescale_activity(&mut self) {
        self.activity *= 1e-20;
    }

    pub fn range_copy_from(&self, from: usize) -> Vec<LngLit> {
        self.data[from..].to_vec()
    }

    pub fn cardinality(&self) -> usize {
        self.data.len() - self.at_most_watchers.unwrap() + 1
    }
}

/// A MiniSAT Variable
#[derive(Clone, PartialEq, Debug)]
pub struct LngVariable {
    pub assignment: Tristate,
    pub level: Option<usize>,
    pub reason: Option<ClauseRef>,
    pub activity: f64,
    pub polarity: bool,
    pub decision: bool,
}

impl LngVariable {
    pub const fn new(polarity: bool, decision: bool) -> Self {
        Self { assignment: Tristate::Undef, level: None, polarity, decision, activity: 0.0, reason: None }
    }

    pub fn level_greater_zero(&self) -> bool {
        self.level.unwrap_or(0) > 0
    }

    pub fn increment_activity(&mut self, inc: f64) {
        self.activity += inc;
    }

    pub fn rescale_activity(&mut self) {
        self.activity *= 1e-100;
    }
}

/// Reference to a clause on the solver.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct ClauseRef(pub usize);

/// A watcher for clauses for MiniSAT solvers.
#[derive(Debug, Clone, Eq, PartialEq, PartialOrd, Ord)]
pub struct LngWatcher {
    /// Watched clause of this watcher.
    pub clause_ref: ClauseRef,
    /// Blocking literal of this watcher.
    pub blocking_literal: LngLit,
}

/// A tristate constant.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum Tristate {
    /// True
    True,
    /// False
    False,
    /// Undefined
    Undef,
}

impl Tristate {
    /// Returns the name of the state.
    pub fn name(&self) -> String {
        match self {
            Self::True => String::from("TRUE"),
            Self::False => String::from("FALSE"),
            Self::Undef => String::from("UNDEF"),
        }
    }

    /// Returns a negated tristate of itself.
    ///
    /// The negation of undefined is also undefined.
    #[must_use]
    pub const fn negate(&self) -> Self {
        match self {
            Self::True => Self::False,
            Self::False => Self::True,
            Self::Undef => Self::Undef,
        }
    }

    /// Builds a tristate from a boolean.
    pub const fn from_bool(value: bool) -> Self {
        if value {
            Self::True
        } else {
            Self::False
        }
    }
}

/// Class containing the information required for generating a proof.
#[derive(PartialEq, Eq, Debug)]
pub struct ProofInformation<Backpack> {
    pub(crate) clause: Vec<isize>,
    pub(crate) proposition: Option<Proposition<Backpack>>,
}

impl<Backpack> Clone for ProofInformation<Backpack> {
    fn clone(&self) -> Self {
        Self { clause: self.clause.clone(), proposition: self.proposition.clone() }
    }
}

impl<B> ProofInformation<B> {
    /// Constructs new proof information object.
    pub const fn new(clause: Vec<isize>, proposition: Option<Proposition<B>>) -> Self {
        Self { clause, proposition }
    }
}

#[cfg(test)]
mod tests {
    use super::{LngClause, LngLit, LngState, LngVariable, Tristate};

    #[test]
    pub fn test_lng_clause() {
        let vec = vec![LngLit(2), LngLit(4), LngLit(6)];
        let mut clause = LngClause::new(vec, Some(LngState(0)), false);
        clause.can_be_del = true;
        clause.lbd = 42;
        clause.seen = true;
        assert_eq!(
            &format!("{clause:?}"),
            "LngClause { data: [LngLit(2), LngLit(4), LngLit(6)], learnt_on_state: Some(LngState(0)), is_at_most: false, activity: 0.0, seen: true, lbd: 42, can_be_del: true, one_watched: false, at_most_watchers: None }"
        );
    }

    #[test]
    pub fn test_lng_variable() {
        let mut var = LngVariable::new(true, true);
        var.level = Some(12);
        var.reason = None;
        var.assignment = Tristate::True;
        assert_eq!(
            &format!("{var:?}"),
            "LngVariable { assignment: True, level: Some(12), reason: None, activity: 0.0, polarity: true, decision: true }"
        );
    }
}
