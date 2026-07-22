use crate::formulas::{EncodedFormula, FormulaFactory, Literal, Variable};
use crate::propositions::Proposition;
use crate::solver::lng_core_solver::SatSolver;

/// The result of an encoding.
///
/// Encodings are often used only when adding formulas to the SAT solver.
/// Therefore, it is not necessary to generate all the formulas required for the
/// encoding in the formula factory and therefore polluting the factory and the
/// heap.  This class can be used to connect an encoding directly with a SAT
/// solver and therefore introducing the variables only on the solver - not in
/// the factory. When working with many encodings, this can be a large
/// performance gain.
pub trait EncodingResult {
    /// Creates a new auxiliary variable.
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::formulas::FormulaFactory;
    /// # use logicng::datastructures::EncodingResultFF;
    /// # use logicng::formulas::{AUX_CC, AUX_CNF};
    /// # let f = FormulaFactory::new();
    /// # let mut encoding_result = EncodingResultFF::new(&f);
    /// use logicng::datastructures::EncodingResult;
    ///
    /// let variable1 = encoding_result.new_auxiliary_variable(AUX_CC);
    /// let variable2 = encoding_result.new_auxiliary_variable(AUX_CNF);
    /// ```
    fn new_auxiliary_variable(&mut self, aux_type: &str) -> Variable;

    /// Adds a clause to the result.
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::formulas::FormulaFactory;
    /// # use logicng::datastructures::EncodingResultFF;
    /// # use logicng::formulas::AUX_CC;
    /// # let f = FormulaFactory::new();
    /// # let mut encoding_result = EncodingResultFF::new(&f);
    /// use logicng::datastructures::EncodingResult;
    ///
    /// let literal1 = f.lit("A", false);
    /// let literal2 = encoding_result.new_auxiliary_variable(AUX_CC).pos_lit();
    /// encoding_result.add_clause(&[literal1, literal2]);
    /// ```
    fn add_clause(&mut self, lits: &[Literal]);
}

/// A [`EncodingResult`] that uses a [`FormulaFactory`] to create the variables
/// and clauses and writes them to a vector.
///
/// The result is written to the field [`EncodingResultFF::result`].
pub struct EncodingResultFF<'a> {
    f: &'a FormulaFactory,
    /// The destination for the clauses written by this encoding result.
    pub result: Vec<EncodedFormula>,
}

impl<'a> EncodingResultFF<'a> {
    /// Creates a new [`FormulaFactory`]-based [`EncodingResult`].
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::formulas::FormulaFactory;
    /// # use logicng::datastructures::EncodingResultFF;
    /// let f = FormulaFactory::new();
    /// let encoding_result = EncodingResultFF::new(&f);
    /// // ...
    /// let result = encoding_result.result;
    /// ```
    pub const fn new(f: &'a FormulaFactory) -> Self {
        Self {
            f,
            result: Vec::new(),
        }
    }

    /// Reference to the [`FormulaFactory`] used to build the clauses and
    /// variables for this result.
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::formulas::FormulaFactory;
    /// # use logicng::datastructures::EncodingResultFF;
    /// let f = FormulaFactory::new();
    /// let mut encoding_result = EncodingResultFF::new(&f);
    /// assert_eq!(f.id(), encoding_result.factory().id());
    /// ```
    pub const fn factory(&self) -> &FormulaFactory {
        self.f
    }
}

impl EncodingResult for EncodingResultFF<'_> {
    fn new_auxiliary_variable(&mut self, aux_type: &str) -> Variable {
        self.f.new_auxiliary_variable(aux_type)
    }

    fn add_clause(&mut self, lits: &[Literal]) {
        self.result.push(self.f.clause(lits));
    }
}

/// A [`EncodingResult`] writing the results directly onto the given SAT solver.
///
/// This encoding result avoids constructing formulas with a formula factory.
/// This can be useful if the result of the encoding is only used by the SAT
/// solver, so that all the formulas would just pollute the formula factory.
///
/// Auxiliary variables created with this encoding result are still added to
/// the given formula factory.
pub struct EncodingResultSatSolver<'s, 'f, B> {
    /// The SAT solver which is the destination for the constructed clauses.
    pub solver: &'s mut SatSolver<B>,
    proposition: Option<Proposition<B>>,
    f: &'f FormulaFactory,
}

impl<'s, 'f, B> EncodingResultSatSolver<'s, 'f, B> {
    /// Creates a new [`SatSolver`]-based [`EncodingResult`].
    ///
    /// Optionally, a `proposition` can be defined that is added together with
    /// the clauses when they are added to the solver.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::formulas::FormulaFactory;
    /// # use logicng::solver::lng_core_solver::SatSolver;
    /// # use logicng::datastructures::EncodingResultSatSolver;
    /// let f = FormulaFactory::new();
    /// let mut solver = SatSolver::new();
    /// let mut encoding_result = EncodingResultSatSolver::new(&mut solver, None, &f);
    /// // ...
    /// ```
    pub fn new(
        solver: &'s mut SatSolver<B>,
        proposition: Option<Proposition<B>>,
        f: &'f FormulaFactory,
    ) -> Self {
        Self {
            solver,
            proposition,
            f,
        }
    }

    /// Reference to the [`FormulaFactory`] used to create the auxiliary
    /// variables for this result.
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::formulas::FormulaFactory;
    /// # use logicng::solver::lng_core_solver::SatSolver;
    /// # use logicng::datastructures::EncodingResultSatSolver;
    /// let f = FormulaFactory::new();
    /// let mut solver = SatSolver::new();
    /// let encoding_result = EncodingResultSatSolver::new(&mut solver, None, &f);
    /// assert_eq!(f.id(), encoding_result.factory().id());
    /// ```
    pub const fn factory(&self) -> &FormulaFactory {
        self.f
    }
}

impl<B> EncodingResult for EncodingResultSatSolver<'_, '_, B> {
    fn new_auxiliary_variable(&mut self, aux_type: &str) -> Variable {
        let initial_phase = self.solver.config().initial_phase;
        let index = self.solver.underlying_solver().new_var(initial_phase, true);
        let variable = self.f.new_auxiliary_variable(aux_type);
        self.solver
            .underlying_solver()
            .add_variable(variable, index);
        variable
    }

    fn add_clause(&mut self, lits: &[Literal]) {
        // A formula-factory clause is structurally guaranteed to be a valid clause.
        let clause = self.f.clause(lits);
        if let Ok(literals) = clause.literals_for_clause_or_term(self.f) {
            let exported = crate::solver::lng_core_solver::generate_clause_vector_wo_config(
                &literals,
                self.solver.underlying_solver(),
            );
            self.solver
                .underlying_solver()
                .add_clause(exported, self.proposition.clone());
        }
    }
}
