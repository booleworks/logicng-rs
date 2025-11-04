use std::cell::RefCell;
use std::rc::Rc;

use crate::collections::MsClause;
use crate::propositions::Proposition;
use crate::solver::minisat::sat::Tristate::{False, True, Undef};

/// Internal representation of a variable on the solver.
#[derive(Debug, Clone, Copy, PartialOrd, Ord, PartialEq, Eq)]
#[repr(transparent)]
pub struct MsVar(pub usize);

impl MsVar {
    /// Last possible representation of a variable.
    pub const MAX: Self = Self(usize::MAX);
}

/// Internal representation of a literal on the solver.
#[derive(Debug, Clone, Copy, PartialOrd, Ord, PartialEq, Eq)]
#[repr(transparent)]
pub struct MsLit(pub usize);

impl MsLit {
    /// Last possible representation of a literal.
    pub const MAX: Self = Self(usize::MAX);
}

/// Reference to a clause on the solver.
pub type ClauseRef = Rc<RefCell<MsClause>>;

/// A watcher for clauses for MiniSAT solvers.
#[derive(Debug)]
pub struct MsWatcher {
    /// Watched clause of this watcher.
    pub clause_ref: ClauseRef,
    /// Blocking literal of this watcher.
    pub blocking_literal: Option<MsLit>,
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
            True => String::from("TRUE"),
            False => String::from("FALSE"),
            Undef => String::from("UNDEF"),
        }
    }

    /// Returns a negated tristate of itself.
    ///
    /// The negation of undefined is also undefined.
    #[must_use]
    pub const fn negate(&self) -> Self {
        match self {
            True => False,
            False => True,
            Undef => Undef,
        }
    }

    /// Builds a tristate from a boolean.
    pub const fn from_bool(value: bool) -> Self {
        if value { True } else { False }
    }
}

/// The different methods for clause minimization.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum ClauseMinimization {
    /// No minimization is performed.
    None,
    /// Local minimization is performed.
    Basic,
    /// Recursive minimization is performed.
    Deep,
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
    pub fn new(clause: Vec<isize>, proposition: Option<Proposition<B>>) -> Self {
        Self { clause, proposition }
    }
}
