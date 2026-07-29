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
    /// Sentinel used when an operation reports a literal-level error.
    pub const ERROR: Self = Self(usize::MAX - 1);
}

/// Constructs an SatSolver literal from a SatSolver variable.
pub fn mk_lit(var: LngVar, sign: bool) -> LngLit {
    LngLit(var.0 + var.0 + usize::from(sign))
}

/// Constructs the negation of a SatSolver literal.
pub const fn not(lit: LngLit) -> LngLit {
    LngLit(lit.0 ^ 1)
}

/// Returns the sign of the literal.
pub const fn sign(lit: LngLit) -> bool {
    lit.0 & 1 == 1
}

/// Returns the SatSolver variable of SatSolver variable.
pub const fn var(lit: LngLit) -> LngVar {
    LngVar(lit.0 >> 1)
}

/// Identifier of a saved incremental solver state.
#[derive(Debug, Clone, Copy, PartialOrd, Ord, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct LngState(pub usize);

/// Snapshot metadata used to restore an earlier incremental solver state.
#[derive(Debug, Eq, PartialEq, PartialOrd, Ord, Clone, Hash)]
pub struct SolverState {
    /// Unique identifier of this state.
    pub id: LngState,
    /// Whether the solver was consistent when the state was saved.
    pub ok: bool,
    /// Number of variables present in the saved state.
    pub vars_size: usize,
    /// Size of the clause arena in the saved state.
    pub all_clause_size: usize,
    /// Number of original clauses in the saved state.
    pub clause_size: usize,
    /// Number of unit clauses in the saved state.
    pub unit_clause_size: usize,
    /// Number of original proof entries in the saved state.
    pub pg_original_size: usize,
    /// Number of generated proof entries in the saved state.
    pub pg_proof_size: usize,
    /// Number of propositions stored on the solver.
    pub propositions_size: usize,
}

/// Internal representation of a clause and its solver metadata.
#[allow(clippy::struct_excessive_bools)]
#[derive(Clone, PartialEq, Debug)]
pub struct LngClause {
    /// Literals contained in the clause.
    pub data: Vec<LngLit>,
    /// Incremental state on which this clause was learnt, if any.
    pub learnt_on_state: Option<LngState>,
    /// Whether this is a native at-most clause.
    pub is_at_most: bool,
    /// Clause activity used during learnt-clause reduction.
    pub activity: f64,
    /// Temporary conflict-analysis marker.
    pub seen: bool,
    /// Literal block distance of the clause.
    pub lbd: usize,
    /// Whether database reduction may delete this clause.
    pub can_be_del: bool,
    /// Whether the clause uses the one-watched representation.
    pub one_watched: bool,
    /// Number of watched literals for an at-most clause.
    pub at_most_watchers: Option<usize>,
}

impl LngClause {
    /// Creates a clause from its literals and basic classification metadata.
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

    /// Returns the number of literals in the clause.
    pub fn len(&self) -> usize {
        self.data.len()
    }

    /// Returns the literal at position `i`.
    pub fn get(&self, i: usize) -> LngLit {
        self.data[i]
    }

    /// Replaces the literal at position `i`.
    pub fn set(&mut self, i: usize, lit: LngLit) {
        self.data[i] = lit;
    }

    /// Increases the clause activity by `inc`.
    pub fn increment_activity(&mut self, inc: f64) {
        self.activity += inc;
    }

    /// Rescales clause activity to avoid floating-point overflow.
    pub fn rescale_activity(&mut self) {
        self.activity *= 1e-20;
    }

    /// Copies all literals starting at `from`.
    pub fn range_copy_from(&self, from: usize) -> Vec<LngLit> {
        self.data[from..].to_vec()
    }

    /// Returns the right-hand-side cardinality of an at-most clause.
    pub fn cardinality(&self) -> usize {
        self.data.len() - self.at_most_watchers.unwrap() + 1
    }
}

/// A SatSolver Variable
#[derive(Clone, PartialEq, Debug)]
pub struct LngVariable {
    /// Current truth assignment.
    pub assignment: Tristate,
    /// Decision level of the current assignment.
    pub level: Option<usize>,
    /// Clause that implied the current assignment.
    pub reason: Option<ClauseRef>,
    /// Variable activity used for branch selection.
    pub activity: f64,
    /// Preferred decision polarity.
    pub polarity: bool,
    /// Whether the variable may be selected as a decision variable.
    pub decision: bool,
}

impl LngVariable {
    /// Creates an unassigned solver variable.
    pub const fn new(polarity: bool, decision: bool) -> Self {
        Self {
            assignment: Tristate::Undef,
            level: None,
            polarity,
            decision,
            activity: 0.0,
            reason: None,
        }
    }

    /// Returns whether the variable is assigned above decision level zero.
    pub fn level_greater_zero(&self) -> bool {
        self.level.unwrap_or(0) > 0
    }

    /// Increases the variable activity by `inc`.
    pub fn increment_activity(&mut self, inc: f64) {
        self.activity += inc;
    }

    /// Rescales variable activity to avoid floating-point overflow.
    pub fn rescale_activity(&mut self) {
        self.activity *= 1e-100;
    }
}

/// Reference to a clause on the solver.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct ClauseRef(pub usize);

/// A watcher for clauses for SatSolver.
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
        if value { Self::True } else { Self::False }
    }
}

/// Class containing the information required for generating a proof.
#[derive(PartialEq, Eq, Debug, Clone)]
pub struct ProofInformation {
    pub(crate) clause: Vec<isize>,
    pub(crate) proposition: Option<PropositionID>,
}

impl ProofInformation {
    /// Constructs new proof information object.
    pub const fn new(clause: Vec<isize>, proposition: Option<PropositionID>) -> Self {
        Self {
            clause,
            proposition,
        }
    }
}

#[repr(transparent)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
/// Opaque identifier of a proposition registered on a SAT solver.
///
/// The identifier associates generated clauses and proof information with the
/// proposition from which they originated. It is only meaningful for the
/// solver instance which created it.
pub struct PropositionID(pub(crate) usize);

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
