use crate::formulas::{EncodedFormula, FormulaFactory, Literal, Variable, AUX_CC};
use crate::solver::minisat::sat::MsLit;
use crate::solver::minisat::MiniSat;

// TODO: for MiniSat, we also would need a proposition to be passed to `add_clause` methods
//       (actually, we need the FormulaFactory only for Vec<Formula> and we need a Proposition only for MiniSat)

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
    /// Returns a new auxiliary variable.
    fn new_cc_variable(&mut self, f: &FormulaFactory) -> Variable;
    /// Resets the result.
    fn reset(&mut self);
    /// Adds a clause to the result.
    fn add_clause(&mut self, f: &FormulaFactory, lits: &[Literal]);
    /// Adds a clause of length 1 to the result.
    fn add_clause1(&mut self, f: &FormulaFactory, literal: Literal);
    /// Adds a clause of length 2 to the result.
    fn add_clause2(&mut self, f: &FormulaFactory, literal1: Literal, literal2: Literal);
    /// Adds a clause of length 3 to the result.
    fn add_clause3(&mut self, f: &FormulaFactory, literal1: Literal, literal2: Literal, literal3: Literal);
    /// Adds a clause of length 4 to the result.
    fn add_clause4(&mut self, f: &FormulaFactory, literal1: Literal, literal2: Literal, literal3: Literal, literal4: Literal);
}

impl<B> EncodingResult for MiniSat<B> {
    fn new_cc_variable(&mut self, f: &FormulaFactory) -> Variable {
        let index = self.underlying_solver.new_var(self.config.initial_phase, true);
        let variable = f.new_auxiliary_variable(AUX_CC);
        self.underlying_solver.add_variable(variable, index);
        variable
    }

    fn reset(&mut self) {
        // do nothing
    }

    fn add_clause(&mut self, _f: &FormulaFactory, lits: &[Literal]) {
        let mut clause_vec = Vec::<MsLit>::with_capacity(lits.len());
        for lit in lits {
            clause_vec.push(self.add_literal(lit));
        }
        self.underlying_solver.add_clause(clause_vec, None);
        self.set_solver_to_undef();
    }

    fn add_clause1(&mut self, _f: &FormulaFactory, literal: Literal) {
        let clause_vec = vec![self.add_literal(&literal)];
        self.underlying_solver.add_clause(clause_vec, None);
        self.set_solver_to_undef();
    }

    fn add_clause2(&mut self, _f: &FormulaFactory, literal1: Literal, literal2: Literal) {
        let clause_vec = vec![self.add_literal(&literal1), self.add_literal(&literal2)];
        self.underlying_solver.add_clause(clause_vec, None);
        self.set_solver_to_undef();
    }

    fn add_clause3(&mut self, _f: &FormulaFactory, literal1: Literal, literal2: Literal, literal3: Literal) {
        let clause_vec = vec![self.add_literal(&literal1), self.add_literal(&literal2), self.add_literal(&literal3)];
        self.underlying_solver.add_clause(clause_vec, None);
        self.set_solver_to_undef();
    }

    fn add_clause4(&mut self, _f: &FormulaFactory, literal1: Literal, literal2: Literal, literal3: Literal, literal4: Literal) {
        let clause_vec =
            vec![self.add_literal(&literal1), self.add_literal(&literal2), self.add_literal(&literal3), self.add_literal(&literal4)];
        self.underlying_solver.add_clause(clause_vec, None);
        self.set_solver_to_undef();
    }
}

impl EncodingResult for Vec<EncodedFormula> {
    fn new_cc_variable(&mut self, f: &FormulaFactory) -> Variable {
        f.new_auxiliary_variable(AUX_CC)
    }

    fn reset(&mut self) {
        self.clear();
    }

    fn add_clause(&mut self, f: &FormulaFactory, lits: &[Literal]) {
        let clause = f.or(lits.iter().map(|lit| EncodedFormula::from(*lit)));
        self.push(clause);
    }

    fn add_clause1(&mut self, f: &FormulaFactory, literal: Literal) {
        let clause = f.or([EncodedFormula::from(literal)]);
        self.push(clause);
    }

    fn add_clause2(&mut self, f: &FormulaFactory, literal1: Literal, literal2: Literal) {
        let clause = f.or([EncodedFormula::from(literal1), EncodedFormula::from(literal2)]);
        self.push(clause);
    }

    fn add_clause3(&mut self, f: &FormulaFactory, literal1: Literal, literal2: Literal, literal3: Literal) {
        let clause = f.or([EncodedFormula::from(literal1), EncodedFormula::from(literal2), EncodedFormula::from(literal3)]);
        self.push(clause);
    }

    fn add_clause4(&mut self, f: &FormulaFactory, literal1: Literal, literal2: Literal, literal3: Literal, literal4: Literal) {
        let clause = f.or([
            EncodedFormula::from(literal1),
            EncodedFormula::from(literal2),
            EncodedFormula::from(literal3),
            EncodedFormula::from(literal4),
        ]);
        self.push(clause);
    }
}
