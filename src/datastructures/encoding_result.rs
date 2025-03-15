use crate::formulas::{EncodedFormula, FormulaFactory, Literal, Variable};
use crate::solver::lng_core_solver::LngLit;

#[derive(Clone, Copy, Debug, Eq, PartialEq, PartialOrd, Ord, Hash)]
pub enum SolverExportLiteral {
    FF(Literal),
    Solver(LngLit),
}

impl SolverExportLiteral {
    pub fn negate(self) -> SolverExportLiteral {
        match self {
            SolverExportLiteral::FF(literal) => SolverExportLiteral::FF(literal.negate()),
            SolverExportLiteral::Solver(ms_lit) => {
                let nl = crate::solver::lng_core_solver::not(ms_lit);
                SolverExportLiteral::Solver(nl)
            }
        }
    }

    pub fn expect_literal(self, expected: &str) -> Literal {
        match self {
            SolverExportLiteral::FF(literal) => literal,
            SolverExportLiteral::Solver(_) => panic!("{}", expected),
        }
    }

    pub fn expect_intern(self, expected: &str) -> LngLit {
        match self {
            SolverExportLiteral::Solver(ms_lit) => ms_lit,
            SolverExportLiteral::FF(_) => panic!("{}", expected),
        }
    }
}

impl From<Literal> for SolverExportLiteral {
    fn from(value: Literal) -> Self {
        Self::FF(value)
    }
}

impl From<Variable> for SolverExportLiteral {
    fn from(value: Variable) -> Self {
        Self::FF(value.pos_lit())
    }
}

/// The result of an encoding.
///
/// Encodings are often used only when adding formulas to the SAT solver.
/// Therefore, it is not necessary to generate all the formulas required for the
/// encoding in the formula factory and therefore polluting the factory and the
/// heap.  This class can be used to connect an encoding directly with a SAT
/// solver and therefore introducing the variables only on the solver - not in
/// the factory.  When working with many encodings, this can be a large
/// performance gain.
pub trait EncodingResult {
    fn new_auxiliary_variable(&mut self, aux_type: &str) -> SolverExportLiteral;
    fn add_clause_literals(&mut self, lits: &[Literal]);
    fn add_clause(&mut self, lits: &[SolverExportLiteral]);
}

pub struct EncodingResultFF<'a> {
    f: &'a FormulaFactory,
    pub result: Vec<EncodedFormula>,
}

impl<'a> EncodingResultFF<'a> {
    pub const fn new(f: &'a FormulaFactory) -> Self {
        Self { f, result: Vec::new() }
    }

    pub const fn factory(&self) -> &FormulaFactory {
        self.f
    }
}

impl EncodingResult for EncodingResultFF<'_> {
    fn new_auxiliary_variable(&mut self, aux_type: &str) -> SolverExportLiteral {
        self.f.new_auxiliary_variable(aux_type).into()
    }

    fn add_clause_literals(&mut self, lits: &[Literal]) {
        self.result.push(self.f.clause(lits));
    }

    fn add_clause(&mut self, lits: &[SolverExportLiteral]) {
        self.result
            .push(self.f.clause(lits.iter().map(|v| v.expect_literal("Encoding result for a factory does not create solver variables"))));
    }
}
