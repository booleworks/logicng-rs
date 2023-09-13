/// A transformation takes a formula as input and returns another formula, thus
/// transforming the input formula. Examples for transformations are normal form
/// conversions like NNF, CNF, DNF, or formula simplification.
pub mod transformations;

/// A predicate takes a formula as input and computes a truth value on that
/// formula, e.g. whether a formula is in a certain normal form like NNF, CNF,
/// or DNF, or if it is satisfiable?
pub mod predicates;

/// A function takes a formula as input and computes some value on that formula.
/// This value can be a simple integer e.g. the depth of a formula, or a more
/// complex result type, like the list of sub-formulas.
pub mod functions;
