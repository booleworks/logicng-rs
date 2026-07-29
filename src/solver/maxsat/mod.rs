mod maxsat_error;
mod maxsat_solver;
/// MaxSAT algorithms and encodings ported from OpenWBO to Rust.
pub mod openwbo_rs;

pub use crate::backends::MaxSatResult;
pub use maxsat_error::*;
pub use maxsat_solver::*;
pub use openwbo_rs::*;
/// Provides a solver for MaxSAT problems.
///
/// Given an unsatisfiable formula in CNF, the MaxSAT problem is the problem of
/// finding an assignment which satisfies the maximum number of clauses and
/// therefore solves an optimization problem rather than a decision problem.
/// There are two extensions to MaxSAT Solving: 1) the distinction of hard/soft
/// clauses, and 2) additional weighted clauses, yielding four different
/// flavors of MaxSAT solving:
///
/// 1. Pure MaxSAT
/// 2. Partial MaxSAT
/// 3. Weighted MaxSAT
/// 4. Weighted Partial MaxSAT
///
/// In a **Partial MaxSAT problem** you can distinguish between hard and soft
/// clauses.  A hard clause _must_ be satisfied whereas a soft clause should be
/// satisfied but can be left unsatisfied.  This means the solver only optimizes
/// over the soft clauses.  If the hard clauses themselves are unsatisfiable, no
/// solution can be found.
///
/// In a **Weighted MaxSAT problem** clauses can have a positive weight.  The
/// solver then does not optimize the *number of satisfied clauses* but the *sum
/// of the weights of the satisfied clauses*.
///
/// The **Weighted Partial MaxSAT problem** is the combination of Partial MaxSAT
/// and weighted MaxSAT.  I.e. you can add hard clauses and weighted soft
/// clauses to the MaxSAT solver.
///
/// Note two important points:
///
/// 1. MaxSAT can be defined as weighted MaxSAT restricted to formulas whose
///    clauses have weight 1, and as Partial MaxSAT in the case that all the
///    clauses are declared to be soft.
/// 2. The above definitions talk about *clauses* on the solver, not arbitrary
///    formulas. In real-world use cases you often want to weight whole formulas
///    and not just clauses. LogicNG's MaxSAT solver API gives you this
///    possibility and internally translates the formulas and their weights
///    accordingly. This is a huge quality-of-life improvement when working with
///    the solvers.
///
///
/// # MaxSAT Algorithms and Implementations
///
/// The generic [`MaxSatSolver`] interface supports different solver backends
/// and algorithms. This crate includes the pure-Rust [`RustOpenWboBackend`],
/// which is created most conveniently through [`RustOpenWboFactory`]. Its
/// algorithms are ports of algorithms from
/// [OpenWBO](https://github.com/sat-group/open-wbo).
///
/// There are two orthogonal strategies to solve MaxSAT problems:
///
/// 1. Based on linear search
/// 2. Based on producing and iteratively relaxing unsatisfiable cores
///
/// Details on this distinction can be found in the paper [Algorithms for
/// Weighted Boolean Optimization](https://arxiv.org/pdf/0903.0843.pdf) by
/// Manquinho, Marques-Silva and Planes.
///
/// Here is an overview of the algorithms in LogicNG and their capabilities:
///
/// | Algorithm  | Strategy      | Unweighted | Weighted |
/// |------------|---------------|------------|----------|
/// | `LinearSU` | Linear Search | yes        | yes*     |
/// | `MSU3`     | Unsat-Core    | yes        | no       |
/// | `WBO`      | Unsat-Core    | yes        | yes      |
/// | `OLL`      | Unsat-Core    | yes        | yes      |
///
/// \* *`LinearSU` does not support weighted MaxSAT problems with the
/// `PbEncoding::Adder`*
///
/// All available algorithms support partial MaxSAT. `MSU3` does not support
/// weighted clauses or formulas.
///
/// `LinearSU` stands for linear SAT-UNSAT search. It starts with a model of the
/// relaxed formula and repeatedly tightens an upper bound on the cost. Its SAT
/// calls are satisfiable until the final call proves that the bound cannot be
/// improved.
///
/// `MSU3`, `WBO`, and `OLL` are core-guided algorithms. Which algorithm performs
/// best depends strongly on the problem family and should be evaluated for the
/// intended workload.
///
///
/// # Using MaxSAT Solvers in LogicNG
///
/// A MaxSAT solver is represented by the [`MaxSatSolver`] struct. It provides
/// the common operations for adding constraints, solving, cancellation, and
/// resetting a problem independently of a concrete backend.
///
/// The included Rust implementation is configured with [`OpenWboConfig`] and
/// connected to the generic solver through [`RustOpenWboFactory`].
///
/// ```
/// # use logicng::solver::maxsat::*;
///
/// let mut solver1 = MaxSatSolver::from_factory(&RustOpenWboFactory::new(OpenWboConfig::default())).unwrap();
///
/// let config = OpenWboConfig::default()
///                 .algorithm(Algorithm::LinearSu)
///                 .cardinal(CardinalEncoding::MTotalizer)
///                 .pb(PbEncoding::Gte);
/// let mut solver2 = MaxSatSolver::from_factory(&RustOpenWboFactory::new(config)).unwrap();
/// ```
///
/// Hard formulas are added with the method
/// [`MaxSatSolver::add_hard_formula`](crate::solver::maxsat::MaxSatSolver::add_hard_formula),
/// soft clauses are added with
/// [`MaxSatSolver::add_soft_formula`](crate::solver::maxsat::MaxSatSolver::add_soft_formula),
/// which takes a positive weight. For an unweighted clause, use the weight 1.
/// After adding all formulas, use [`MaxSatSolver::solve`] to solve the problem.
/// The returned [`MaxSatResult`] has one of three
/// states:
///
/// 1. `Unsatisfiable`: The hard clauses on the solver are already
///    unsatisfiable, optimization could not be performed
/// 2. `Optimum { bound, model }`: An optimal solution and its model were found.
/// 3. `Undef`: No search result is available.
///
/// The result is the minimum weight (or number of clauses if unweighted) of
/// clauses/formulas which have to be unsatisfied.  Therefore, if the minimum
/// number of weights is 0, the formula is satisfiable.
///
/// To reuse a solver for a different problem, call
/// [`MaxSatSolver::reset`](crate::solver::maxsat::MaxSatSolver::reset) first.
/// Note that this will only keep your algorithm and the configuration. All
/// added formulas will be deleted.
///
/// # Example
///
/// We look at some examples on how to use the MaxSAT solver with the following
/// simple set of formulas which are unsatisfiable together:
///
/// ```text
/// A & B & (C | D)
/// A => ~B
/// ~C
/// ~D
/// ```
///
/// ## Pure MaxSAT Solving
///
/// We generate a `MSU3` solver and add all formulas as soft clauses with weight
/// 1.  Therefore, we have a pure MaxSAT problem without distinction between
/// hard/soft clauses and without weights.
///
/// ```
/// # use logicng::solver::maxsat::*;
/// # use logicng::formulas::{ToFormula, FormulaFactory};
/// # use std::error::Error;
/// # fn main() -> Result<(), Box<dyn Error>> {
/// let f = FormulaFactory::new();
/// let config = OpenWboConfig::default().algorithm(Algorithm::Msu3);
/// let mut solver = MaxSatSolver::from_factory(&RustOpenWboFactory::new(config)).unwrap();
/// solver.add_soft_formula(1, "A & B & (C | D)".to_formula(&f), &f)?;
/// solver.add_soft_formula(1, "A => ~B".to_formula(&f), &f)?;
/// solver.add_soft_formula(1, "~C".to_formula(&f), &f)?;
/// solver.add_soft_formula(1, "~D".to_formula(&f), &f)?;
///
/// let MaxSatResult::Optimum { bound, model } = solver.solve()? else {
///     panic!("expected an optimum");
/// };
/// assert_eq!(bound, 1);
/// # Ok(())
/// # }
/// ```
///
/// In this case we can find an optimal solution: at least one formula remains
/// unsatisfied.  In this case the model assigns all variables to `false`, thus
/// the first formula is unsatisfied and all other formulas are satisfied.
///
/// As we will see in the next section, this is the only way of unsatisfying
/// _only one_ formula.  If the first formula holds, we have to unsatisfy at
/// least two other formulas.
///
///
/// ## Partial Weighted MaxSAT Solving
///
/// We generate a `Oll` solver and add once again the first formula as hard
/// clause and all other formulas as soft clauses with different weights.
/// Therefore, we have a partial weighted MaxSAT problem.
///
/// ```
/// # use logicng::solver::maxsat::*;
/// # use logicng::formulas::{ToFormula, FormulaFactory};
/// # use std::error::Error;
/// # fn main() -> Result<(), Box<dyn Error>> {
/// let f = FormulaFactory::new();
/// let config = OpenWboConfig::default().algorithm(Algorithm::Oll);
/// let mut solver =
///     MaxSatSolver::from_factory(&RustOpenWboFactory::new(config))?;
/// solver.add_hard_formula("A & B & (C | D)".to_formula(&f), &f)?;
/// solver.add_soft_formula(2, "A => ~B".to_formula(&f), &f)?;
/// solver.add_soft_formula(4, "~C".to_formula(&f), &f)?;
/// solver.add_soft_formula(8, "~D".to_formula(&f), &f)?;
///
/// let MaxSatResult::Optimum { bound, model } = solver.solve()? else {
///     panic!("expected an optimum");
/// };
/// assert_eq!(bound, 6);
/// #   Ok(())
/// # }
///
/// ```
///
/// In this case we can find an optimal solution once again.  Since the fourth
/// formula now has a large weight, the incentive to satisfy it is larger than
/// the incentive to satisfy the third formula.  So in contrast to the last
/// section the model now includes `C` and *not* `D`, thus unsatisfying the
/// third formula.
///
/// The result in this case is 6 - the sum of weights of all unsatisfied
/// formulas: the second formula with weight 2 and the third formula with weight
/// 4.
///
/// **Multiple Optimal Solutions**: Note that this is the only optimal solution
/// for this problem. **In general, however, there can be multiple optimal
/// solutions.**
///
/// ## Special Cases
///
/// Last we consider two special cases. First we try to solve a formula where
/// the hard clauses are already unsatisfiable:
///
/// ```
/// # use logicng::solver::maxsat::*;
/// # use logicng::formulas::{ToFormula, FormulaFactory};
/// # use std::error::Error;
/// # fn main() -> Result<(), Box<dyn Error>> {
/// let f = FormulaFactory::new();
/// let config = OpenWboConfig::default().algorithm(Algorithm::Oll);
/// let mut solver =
///     MaxSatSolver::from_factory(&RustOpenWboFactory::new(config))?;
/// solver.add_hard_formula("A & B & C".to_formula(&f), &f)?;
/// solver.add_hard_formula("A => ~B".to_formula(&f), &f)?;
/// solver.add_hard_formula("~C".to_formula(&f), &f)?;
/// solver.add_soft_formula(8, "X | Y".to_formula(&f), &f)?;
///
/// assert_eq!(solver.solve()?, MaxSatResult::Unsatisfiable);
/// # Ok(())
/// # }
/// ```
///
/// In this case the `solve()` method returns the state `Unsatisfiable`. There
/// is no model.
///
/// Now we try a formula which is satisfiable:
///
/// ```
/// # use logicng::solver::maxsat::*;
/// # use logicng::formulas::{ToFormula, FormulaFactory};
/// # use std::error::Error;
/// # fn main() -> Result<(), Box<dyn Error>> {
/// let f = FormulaFactory::new();
/// let config = OpenWboConfig::default().algorithm(Algorithm::Oll);
/// let mut solver =
///     MaxSatSolver::from_factory(&RustOpenWboFactory::new(config))?;
/// solver.add_hard_formula("A & B & C".to_formula(&f), &f)?;
/// solver.add_soft_formula(1, "~C | D".to_formula(&f), &f)?;
/// solver.add_soft_formula(1, "X | Y".to_formula(&f), &f)?;
///
/// let MaxSatResult::Optimum { bound, model } = solver.solve()? else {
///     panic!("expected an optimum");
/// };
/// assert_eq!(bound, 0);
/// # Ok(())
/// # }
/// ```
///
/// The solver found an optimal solution in this case.  Further, the result is 0
/// - indicating that *all* formulas were satisfied and no formula had to be
/// unsatisfied.
///
/// ## Minimum vs. Maximum: Solving the Dual Problem
///
/// As seen above, the solver tries to *maximize* the number of satisfied
/// clauses by *minimizing* the number of unsatisfied clauses. The returned
/// result is the sum of weights of the *unsatisfied* clauses.
///
/// But what when you want to know the minimal number of satisfied clauses? Then
/// you have to adjust your problem modelling accordingly.  Let us consider a
/// small example:
///
/// ```
/// # use logicng::solver::maxsat::*;
/// # use logicng::formulas::{ToFormula, FormulaFactory};
/// # use std::error::Error;
/// # fn main() -> Result<(), Box<dyn Error>> {
/// let f = FormulaFactory::new();
/// let config = OpenWboConfig::default().algorithm(Algorithm::Oll);
/// let mut solver =
///     MaxSatSolver::from_factory(&RustOpenWboFactory::new(config))?;
/// solver.add_hard_formula("(A & B & ~X & ~D) | (B & C & ~A) | (C & ~D & X)".to_formula(&f), &f)?;
/// solver.add_soft_formula(2, "A".to_formula(&f), &f)?;
/// solver.add_soft_formula(4, "B".to_formula(&f), &f)?;
/// solver.add_soft_formula(8, "C".to_formula(&f), &f)?;
/// solver.add_soft_formula(5, "D".to_formula(&f), &f)?;
/// solver.add_soft_formula(7, "X".to_formula(&f), &f)?;
/// # Ok(())
/// # }
/// ```
///
/// We have one hard formula and each variable in it has a given weight. Solving
/// the problem yields the assignment `pos=[B, C, D, X], neg=[~A]` with result
/// 2. This means when setting all variables except `A` to `true`, only one
/// formula (in this case variable) is unsatisfied and has weight 2.
///
/// If we give the variable weights a meaning, e.g. a price, then we have now
/// computed the *most expensive* variable assignment.  `B`, `C`, `D`, `X`
/// together have a price of 24.  In order to compute the *cheapest* variable
/// assignment, we should not try to maximize the positive literals, but instead
/// the negative literals: We want to set a maximal number of expensive
/// variables to `false`.  We can do this by negating the variables in the soft
/// formulas:
///
/// ```
/// # use logicng::solver::maxsat::*;
/// # use logicng::formulas::{ToFormula, FormulaFactory};
/// # use std::error::Error;
/// # fn main() -> Result<(), Box<dyn Error>> {
/// let f = FormulaFactory::new();
/// let config = OpenWboConfig::default().algorithm(Algorithm::Oll);
/// let mut solver =
///     MaxSatSolver::from_factory(&RustOpenWboFactory::new(config))?;
/// solver.add_hard_formula("(A & B & ~X & ~D) | (B & C & ~A) | (C & ~D & X)".to_formula(&f), &f)?;
/// solver.add_soft_formula(2, "~A".to_formula(&f), &f)?;
/// solver.add_soft_formula(4, "~B".to_formula(&f), &f)?;
/// solver.add_soft_formula(8, "~C".to_formula(&f), &f)?;
/// solver.add_soft_formula(5, "~D".to_formula(&f), &f)?;
/// solver.add_soft_formula(7, "~X".to_formula(&f), &f)?;
/// # Ok(())
/// # }
/// ```
///
/// Now the model is `pos=[A, B], neg=[~C, ~D, ~X]` with a result of
/// 6.  This means the cheapest variable assignment consists of only `A` and `B`
/// with a price of 6.
///
/// Once you wrap your head around this concept of duality you have a very
/// mighty tool to solve all kinds of optimization problems with MaxSAT solving.
/// We deviate from the convention of putting unit tests in the source file in this case,
/// s.t. the file don't become too large
pub(crate) mod tests;
