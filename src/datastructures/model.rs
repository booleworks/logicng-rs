use itertools::Itertools;

use crate::datastructures::Assignment;
use crate::formulas::{FormulaFactory, Literal, StringLiteral, Variable};

#[derive(Debug, Clone)]
/// A `Model` stores a set of positive and negative [`Variable`]s.
///
/// `Model` stores all variables in [`Vec`]s, this allows for a fast creation of
/// new models, but makes it unsuitable for evaluating formulas. It also does
/// not check for duplicates. For that you have to use [`Assignment`], which
/// uses hash-sets to store the variables.
///
/// # Conversion to `Assignment` and vice-versa
///
/// Depending of your use case it might be better to have a `Model` or an
/// [`Assignment`]. Both data-structures implement the `From` trait, such that
/// you can easily swap between both.
///
/// Convert from `Model` to [`Assignment`]:
/// ```
/// # use crate::logicng::formulas::FormulaFactory;
/// # use crate::logicng::datastructures::{Model, Assignment};
/// let f = FormulaFactory::new();
///
/// let a = f.var("a");
/// let b = f.var("b");
/// let model = Model::new(vec![a], vec![b]);
/// let assignment = Assignment::from(model);
/// ```
///
/// /// Convert from [`Assignment`] to `Model`:
/// ```
/// # use crate::logicng::formulas::FormulaFactory;
/// # use crate::logicng::datastructures::{Model, Assignment};
/// let f = FormulaFactory::new();
///
/// let a = f.var("a");
/// let b = f.var("b");
/// let assignment = Assignment::from_variables(&[a], &[b]);
/// let model = Model::from(assignment);
/// ```
pub struct Model {
    pos: Vec<Variable>,
    neg: Vec<Variable>,
}

impl Model {
    /// Creates a new model.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::datastructures::Model;
    /// # use logicng::formulas::FormulaFactory;
    /// let f = FormulaFactory::new();
    ///
    /// let a = f.var("a");
    /// let b = f.var("b");
    ///
    /// let model = Model::new(vec![a], vec![b]);
    /// ```
    pub fn new<P, N>(pos: P, neg: N) -> Self
    where
        P: Into<Vec<Variable>>,
        N: Into<Vec<Variable>>,
    {
        Self { pos: pos.into(), neg: neg.into() }
    }

    /// Creates a new model from slices.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::datastructures::Model;
    /// # use logicng::formulas::FormulaFactory;
    /// let f = FormulaFactory::new();
    ///
    /// let a = f.var("a");
    /// let b = f.var("b");
    ///
    /// let model = Model::from_variables(&[a], &[b]);
    /// ```
    pub fn from_variables(pos: &[Variable], neg: &[Variable]) -> Self {
        Self { pos: pos.into(), neg: neg.into() }
    }

    /// Converts a literal into a model.
    ///
    /// A positive literal is added to the positive variables, and a negative
    /// literal to the negative variables.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::datastructures::Model;
    /// # use logicng::formulas::FormulaFactory;
    /// let f = FormulaFactory::new();
    ///
    /// let a = f.lit("a", true);
    /// let b = f.lit("b", false);
    ///
    /// let model1 = Model::from_lit(a);
    /// let model2 = Model::from_lit(b);
    ///
    /// assert_eq!(model1.pos(), &vec![a.variable()]);
    /// assert_eq!(model2.neg(), &vec![b.variable()]);
    /// ```
    pub fn from_lit(lit: Literal) -> Self {
        if lit.phase() {
            Self { pos: vec![lit.variable()], neg: vec![] }
        } else {
            Self { pos: vec![], neg: vec![lit.variable()] }
        }
    }

    /// Creates a model from a single vector of literals.
    ///
    /// All positive literals are added to the positive variables, and all
    /// negative literals to the negative variables.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::datastructures::Model;
    /// # use logicng::formulas::FormulaFactory;
    /// let f = FormulaFactory::new();
    ///
    /// let a = f.lit("a", true);
    /// let b = f.lit("b", false);
    ///
    /// let model = Model::from_literals(&[a, b]);
    ///
    /// assert_eq!(model.pos(), &[a.variable()]);
    /// assert_eq!(model.neg(), &[b.variable()]);
    /// ```
    pub fn from_literals(literals: &[Literal]) -> Self {
        let mut pos = Vec::with_capacity(literals.len());
        let mut neg = Vec::with_capacity(literals.len());
        for lit in literals {
            if lit.phase() {
                pos.push(lit.variable());
            } else {
                neg.push(lit.variable());
            }
        }
        Self { pos, neg }
    }

    /// Creates a new model from slices of names.
    ///
    /// Uses names of already existing variables and adds those variables to the
    /// model. If a name has no existing variable in the formula factory, the
    /// function will return an error.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::datastructures::Model;
    /// # use logicng::formulas::FormulaFactory;
    /// # fn main() -> Result<(), String> {
    /// let f = FormulaFactory::new();
    ///
    /// let a = f.var("a");
    /// let b = f.var("b");
    ///
    /// let model = Model::from_names(&["a"], &["b"], &f)?;
    ///
    /// assert_eq!(model.pos(), &vec![a]);
    /// assert_eq!(model.neg(), &vec![b]);
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// If a name is not a variable, an error will be returned:
    /// ```
    /// # use logicng::datastructures::Model;
    /// # use logicng::formulas::FormulaFactory;
    /// let f = FormulaFactory::new();
    ///
    /// let a = f.var("a");
    ///
    /// let model = Model::from_names(&["a"], &["b"], &f);
    ///
    /// assert!(model.is_err());
    /// ```
    pub fn from_names(pos: &[&str], neg: &[&str], f: &FormulaFactory) -> Result<Self, String> {
        let pos = names_to_indices(pos, f)?;
        let neg = names_to_indices(neg, f)?;
        Ok(Self { pos, neg })
    }

    /// Returns all positive variables of this model.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::datastructures::Model;
    /// # use logicng::formulas::FormulaFactory;
    /// let f = FormulaFactory::new();
    ///
    /// let a = f.var("a");
    /// let b = f.var("b");
    ///
    /// let model = Model::new(vec![a], vec![b]);
    ///
    /// assert_eq!(model.pos(), &vec![a]);
    /// ```
    pub fn pos(&self) -> &[Variable] {
        &self.pos
    }

    /// Returns all negative variables of this model.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::datastructures::Model;
    /// # use logicng::formulas::FormulaFactory;
    /// let f = FormulaFactory::new();
    ///
    /// let a = f.var("a");
    /// let b = f.var("b");
    ///
    /// let model = Model::new(vec![a], vec![b]);
    ///
    /// assert_eq!(model.neg(), &vec![b]);
    /// ```
    pub fn neg(&self) -> &[Variable] {
        &self.neg
    }

    /// Returns the overall number of positive and negative variables.
    ///
    /// A variable added as positive and negative is counted twice. Also, any
    /// variable added multiple times is counted multiple times.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::datastructures::Model;
    /// # use logicng::formulas::FormulaFactory;
    /// let f = FormulaFactory::new();
    ///
    /// let a = f.var("a");
    /// let b = f.var("b");
    ///
    /// let model = Model::from_variables(&[a], &[b]);
    ///
    /// assert_eq!(model.len(), 2);
    /// ```
    pub fn len(&self) -> usize {
        self.pos.len() + self.neg.len()
    }

    /// Returns `true` if there is no variable in this model.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::datastructures::Model;
    /// # use logicng::formulas::FormulaFactory;
    /// let f = FormulaFactory::new();
    ///
    /// let a = f.var("a");
    /// let b = f.var("b");
    ///
    /// let model1 = Model::from_variables(&[a], &[b]);
    /// let model2 = Model::from_variables(&[], &[]);
    ///
    /// assert_eq!(model1.is_empty(), false);
    /// assert_eq!(model2.is_empty(), true);
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns a vector of [`Literal`] representing this model.
    ///
    /// All positive variables are returned as positive literals and all
    /// negative variables are returned as negative literals. The vector first
    /// consists of all positive literals and then of all negative literals.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::datastructures::Model;
    /// # use logicng::formulas::FormulaFactory;
    /// let f = FormulaFactory::new();
    ///
    /// let a = f.lit("a", true);
    /// let b = f.lit("b", false);
    ///
    /// let model = Model::from_literals(&[a, b]);
    ///
    /// assert_eq!(model.literals(), vec![a, b]);
    /// ```
    pub fn literals(&self) -> Vec<Literal> {
        let mut result = Vec::with_capacity(self.len());
        self.pos.iter().for_each(|var| result.push(Literal::Pos(*var)));
        self.neg.iter().for_each(|var| result.push(Literal::Neg(*var)));
        result
    }

    /// Returns a vector of [`StringLiteral`] representing this model.
    ///
    /// All positive variables are returned as positive literals and all
    /// negative variables are returned as negative literals. The vector first
    /// consists of all positive literals and then of all negative literals.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::datastructures::Model;
    /// # use logicng::formulas::FormulaFactory;
    /// let f = FormulaFactory::new();
    ///
    /// let a = f.lit("a", true);
    /// let b = f.lit("b", false);
    ///
    /// let model = Model::from_literals(&[a, b]);
    ///
    /// assert_eq!(model.string_literals(&f), vec![a.to_string_lit(&f), b.to_string_lit(&f)]);
    /// ```
    pub fn string_literals<'c>(&self, f: &'c FormulaFactory) -> Vec<StringLiteral<'c>> {
        let mut result = Vec::with_capacity(self.len());
        self.pos.iter().for_each(|var| result.push(Literal::Pos(*var).to_string_lit(f)));
        self.neg.iter().for_each(|var| result.push(Literal::Neg(*var).to_string_lit(f)));
        result
    }

    /// Compares two models and returns `true` if they are the same. The order
    /// of the elements and duplicates do not matter.
    ///
    /// This function can be slow, because both models will be converted to
    /// [`Assignment`]. Consider converting this model to an `Assignment`
    /// yourself, if you want compare it multiple times.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::datastructures::Model;
    /// # use logicng::formulas::FormulaFactory;
    /// let f = FormulaFactory::new();
    ///
    /// let a = f.lit("a", true);
    /// let b = f.lit("b", false);
    ///
    /// let model1 = Model::from_literals(&[a, b]);
    /// let model2 = Model::from_literals(&[a, b, b]);
    /// let model3 = Model::from_literals(&[a]);
    ///
    /// assert!(model1.compare(&model2));
    /// assert!(!model1.compare(&model3));
    /// ```
    pub fn compare(&self, other: &Self) -> bool {
        Assignment::from(self) == Assignment::from(other)
    }

    /// Creates a string representation of this model.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::datastructures::Model;
    /// # use logicng::formulas::FormulaFactory;
    /// let f = FormulaFactory::new();
    ///
    /// let a = f.var("a");
    /// let b = f.var("b");
    ///
    /// let model = Model::from_variables(&[a], &[b]);
    ///
    /// assert_eq!(model.to_string(&f), "Model{pos=[a], neg=[b]}");
    /// ```
    pub fn to_string(&self, f: &FormulaFactory) -> String {
        format!(
            "Model{{pos=[{}], neg=[{}]}}",
            self.pos.iter().map(|v| v.to_string_lit(f)).join(", "),
            self.neg.iter().map(|v| v.to_string_lit(f)).join(", ")
        )
    }
}

impl AsRef<Self> for Model {
    fn as_ref(&self) -> &Self {
        self
    }
}

impl<M: AsRef<Model>> From<M> for Assignment {
    fn from(model: M) -> Self {
        let m = model.as_ref();
        Self::from_variables(&m.pos, &m.neg)
    }
}

fn names_to_indices(names: &[&str], f: &FormulaFactory) -> Result<Vec<Variable>, String> {
    let mut result = Vec::with_capacity(names.len());
    for name in names {
        let index = match f.variables.lookup(name) {
            Some(_) => f.var(*name),
            None => {
                return Err(format!("Variable {} is not known in the given FormulaFactory", *name));
            }
        };
        result.push(index);
    }
    Ok(result)
}

#[cfg(test)]
mod tests {
    use crate::datastructures::{Assignment, Model};
    use crate::formulas::{FormulaFactory, StringLiteral};
    use crate::util::test_util::{lits, lits_list, vars_list};
    use std::collections::BTreeSet;

    #[test]
    fn test_constructor1() {
        let f = &FormulaFactory::new();
        let vars1 = vars_list("a b c", f);
        let vars2 = vars_list("x y", f);
        let model = Model::from_variables(&vars1, &vars2);
        assert_eq!(vars1, model.pos());
        assert_eq!(vars2, model.neg());
        assert_eq!(5, model.len());
    }

    #[test]
    fn test_constructor2() {
        let f = &FormulaFactory::new();
        let vars1 = vars_list("a b c", f);
        let vars2 = vars_list("x y", f);
        let lits = lits_list("a b c ~x ~y", f);
        let model = Model::from_literals(&lits);
        assert_eq!(vars1, model.pos());
        assert_eq!(vars2, model.neg());
        assert_eq!(5, model.len());
    }

    #[test]
    fn test_constructor3() {
        let f = &FormulaFactory::new();
        let vars1 = vars_list("a b c", f);
        let vars2 = vars_list("x y", f);
        let model = Model::from_names(&["a", "b", "c"], &["x", "y"], f).unwrap();
        assert_eq!(vars1, model.pos());
        assert_eq!(vars2, model.neg());
        assert_eq!(5, model.len());
    }

    #[test]
    fn test_is_empty() {
        let f = &FormulaFactory::new();
        let vars1 = vars_list("b a", f);
        let vars2 = vars_list("x y", f);
        let a1 = Model::new(vec![], vec![]);
        let a2 = Model::new(vars1.clone(), vec![]);
        let a3 = Model::new(vec![], vars2.clone());
        let a4 = Model::new(vars1, vars2);
        assert!(a1.is_empty());
        assert!(!a2.is_empty());
        assert!(!a3.is_empty());
        assert!(!a4.is_empty());
    }

    #[test]
    fn test_literals() {
        let f = &FormulaFactory::new();
        let vars1 = vars_list("b a", f);
        let vars2 = vars_list("x y", f);
        let a1 = Model::new(vec![], vec![]);
        let a2 = Model::new(vars1.clone(), vec![]);
        let a3 = Model::new(vec![], vars2.clone());
        let a4 = Model::new(vars1, vars2);
        assert_eq!(a1.literals(), vec![]);
        assert_eq!(lits_list("b a", f), a2.literals());
        assert_eq!(lits_list("~x ~y", f), a3.literals());
        assert_eq!(lits_list("b a ~x ~y", f), a4.literals());
    }

    #[test]
    fn test_string_literals() {
        let f = &FormulaFactory::new();
        let vars1 = vars_list("b a", f);
        let vars2 = vars_list("x y", f);
        let a1 = Model::new(vec![], vec![]);
        let a2 = Model::new(vars1.clone(), vec![]);
        let a3 = Model::new(vec![], vars2.clone());
        let a4 = Model::new(vars1, vars2);
        assert_eq!(Vec::<StringLiteral>::new(), a1.string_literals(f));
        assert_eq!(vec![StringLiteral::new("b", true), StringLiteral::new("a", true)], a2.string_literals(f));
        assert_eq!(vec![StringLiteral::new("x", false), StringLiteral::new("y", false),], a3.string_literals(f));
        assert_eq!(
            vec![
                StringLiteral::new("b", true),
                StringLiteral::new("a", true),
                StringLiteral::new("x", false),
                StringLiteral::new("y", false),
            ],
            a4.string_literals(f)
        );
    }

    #[test]
    fn test_to_assignment() {
        let f = &FormulaFactory::new();
        let vars1 = vars_list("b a", f);
        let vars2 = vars_list("x y", f);
        let a1 = Model::new(vec![], vec![]);
        let a2 = Model::new(vars1.clone(), vec![]);
        let a3 = Model::new(vec![], vars2.clone());
        let a4 = Model::new(vars1, vars2);
        assert_eq!(Assignment::from_set(BTreeSet::new()), a1.into());
        assert_eq!(Assignment::from_set(lits("b a", f)), a2.into());
        assert_eq!(Assignment::from_set(lits("~x ~y", f)), a3.into());
        assert_eq!(Assignment::from_set(lits("b a ~x ~y", f)), a4.into());
    }

    #[test]
    fn test_to_string() {
        let f = &FormulaFactory::new();
        let vars1 = vars_list("b a", f);
        let vars2 = vars_list("x y", f);
        let a1 = Model::new(vec![], vec![]);
        let a2 = Model::new(vars1.clone(), vec![]);
        let a3 = Model::new(vec![], vars2.clone());
        let a4 = Model::new(vars1, vars2);
        assert_eq!("Model{pos=[], neg=[]}", a1.to_string(f));
        assert_eq!("Model{pos=[b, a], neg=[]}", a2.to_string(f));
        assert_eq!("Model{pos=[], neg=[x, y]}", a3.to_string(f));
        assert_eq!("Model{pos=[b, a], neg=[x, y]}", a4.to_string(f));
    }
}
