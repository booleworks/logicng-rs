use crate::formulas::{EncodedFormula, FormulaFactory, Literal, ToFormula, Variable};
use std::collections::BTreeSet;

/// This class represents a backbone.
///
/// A backbone of a formula is a set of literals (positive and/or negative)
/// which are present in their respective polarity in every model of the given
/// formula.  Therefore, the literals must be set accordingly in order for the
/// formula to evaluate to true.
///
/// A backbone of a formula has up to three sets of variables
/// - Positive backbone variables: Variables that occur positive in each model
///   of the formula
/// - Negative backbone variables: Variables that occur negative in each model
///   of the formula
/// - Optional variables: Variables that are neither in the positive nor in the
///   negative backbone. Therefore these variables can be assigned to true or
///   false.
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct Backbone {
    /// Stores whether this Backbone is based on a satisfiable formula.
    pub sat: bool,

    /// Stores all positive backbone variables.
    pub positive_backbone: Option<BTreeSet<Variable>>,

    /// Stores all negative backbone variables.
    pub negative_backbone: Option<BTreeSet<Variable>>,

    /// Stores all optional variables.
    pub optional_variables: Option<BTreeSet<Variable>>,
}

impl Backbone {
    /// Constructs a new backbone for a satisfiable formula, containing the given
    /// backbone variables and optional variables.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::formulas::FormulaFactory;
    /// # use logicng::backbones::Backbone;
    /// # use std::collections::BTreeSet;
    /// let f = FormulaFactory::new();
    /// let mut positive = BTreeSet::new();
    /// positive.insert(f.var("A"));
    ///
    /// let backbone = Backbone::new_sat(Some(positive), None, None);
    /// ```
    pub const fn new_sat(
        positive_backbone: Option<BTreeSet<Variable>>,
        negative_backbone: Option<BTreeSet<Variable>>,
        optional_variables: Option<BTreeSet<Variable>>,
    ) -> Self {
        Self { sat: true, positive_backbone, negative_backbone, optional_variables }
    }

    /// Constructs a new empty backbone for an unsatisfiable formula.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::backbones::Backbone;
    /// let backbone = Backbone::new_unsat();
    /// ```
    pub const fn new_unsat() -> Self {
        Self { sat: false, positive_backbone: None, negative_backbone: None, optional_variables: None }
    }

    /// Returns `true` if the backbone is empty.
    ///
    /// A backbone is empty if its positive and negative variables are empty or
    /// `None`.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::formulas::FormulaFactory;
    /// # use logicng::backbones::Backbone;
    /// # use std::collections::BTreeSet;
    /// let f = FormulaFactory::new();
    ///
    /// let mut optional = BTreeSet::new();
    /// optional.insert(f.var("A"));
    ///
    /// let backbone = Backbone::new_sat(Some(BTreeSet::new()), None, Some(optional));
    ///
    /// assert!(backbone.is_empty());
    /// assert!(Backbone::new_unsat().is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        (self.positive_backbone.is_none() || self.positive_backbone.as_ref().unwrap().is_empty())
            && (self.negative_backbone.is_none() || self.negative_backbone.as_ref().unwrap().is_empty())
    }

    /// Returns all literals of the backbone. Positive backbone variables have
    /// positive polarity, negative backbone variables have negative polarity.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::formulas::FormulaFactory;
    /// # use logicng::backbones::Backbone;
    /// # use std::collections::BTreeSet;
    /// let f = FormulaFactory::new();
    ///
    /// let mut positive = BTreeSet::new();
    /// let mut negative = BTreeSet::new();
    /// let mut optional = BTreeSet::new();
    ///
    /// positive.insert(f.var("A"));
    /// negative.insert(f.var("B"));
    /// optional.insert(f.var("C"));
    ///
    /// let backbone = Backbone::new_sat(Some(positive), Some(negative), Some(optional));
    /// let complete_backbone = backbone.complete_backbone();
    ///
    /// assert_eq!(complete_backbone.len(), 2);
    /// assert!(complete_backbone.contains(&f.lit("A", true)));
    /// assert!(complete_backbone.contains(&f.lit("B", false)));
    /// ```
    pub fn complete_backbone(&self) -> BTreeSet<Literal> {
        let mut complete_backbone = BTreeSet::new();
        if let Some(positive_backbone) = self.positive_backbone.as_ref() {
            for var in positive_backbone {
                complete_backbone.insert(var.pos_lit());
            }
        };
        if let Some(negative_backbone) = self.negative_backbone.as_ref() {
            for var in negative_backbone {
                complete_backbone.insert(var.negate());
            }
        };
        complete_backbone
    }
}

impl ToFormula for Backbone {
    fn to_formula(&self, f: &FormulaFactory) -> EncodedFormula {
        if self.sat {
            f.and(self.complete_backbone().iter().map(|&lit| EncodedFormula::from(lit)))
        } else {
            f.falsum()
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::backbones::Backbone;
    use crate::formulas::formula_cache::formula_encoding::{Encoding, FormulaEncoding};
    use crate::formulas::{FormulaFactory, FormulaType, LitType, ToFormula, VarType, Variable};
    use std::collections::BTreeSet;

    #[test]
    fn test_unsat_backbone() {
        assert!(!Backbone::new_unsat().sat);
        assert_eq!(None, Backbone::new_unsat().positive_backbone);
        assert_eq!(None, Backbone::new_unsat().negative_backbone);
        assert_eq!(None, Backbone::new_unsat().optional_variables);
    }

    fn var(index: u64) -> Variable {
        Variable::FF(FormulaEncoding::encode(index, FormulaType::Lit(LitType::Pos(VarType::FF)), true))
    }
    #[test]
    fn test_is_empty() {
        let (v1, v2, v3, v4, v5) = (var(1), var(2), var(3), var(4), var(5));

        assert!(Backbone::new_unsat().is_empty());
        assert!(Backbone::new_sat(None, None, None).is_empty());
        assert!(Backbone::new_sat(None, None, Some(BTreeSet::from([v1, v2, v3]))).is_empty());
        assert!(Backbone::new_sat(Some(BTreeSet::new()), None, None).is_empty());
        assert!(Backbone::new_sat(None, Some(BTreeSet::new()), None).is_empty());
        assert!(Backbone::new_sat(Some(BTreeSet::new()), Some(BTreeSet::new()), None).is_empty());
        assert!(!Backbone::new_sat(Some(BTreeSet::from([v1, v2, v3])), None, None).is_empty());
        assert!(!Backbone::new_sat(None, Some(BTreeSet::from([v1, v2, v3])), None).is_empty());
        assert!(!Backbone::new_sat(Some(BTreeSet::from([v4, v5])), Some(BTreeSet::from([v1, v2, v3])), None).is_empty());
        assert!(!Backbone::new_sat(Some(BTreeSet::from([v4])), Some(BTreeSet::from([v1, v2, v3])), Some(BTreeSet::from([v5]))).is_empty());
    }

    #[test]
    fn test_complete_backbone() {
        let (v1, v2, v3, v4, v5) = (var(1), var(2), var(3), var(4), var(5));
        assert_eq!(BTreeSet::new(), Backbone::new_unsat().complete_backbone());
        assert_eq!(BTreeSet::new(), Backbone::new_sat(None, None, None).complete_backbone());
        assert_eq!(BTreeSet::new(), Backbone::new_sat(None, None, Some(BTreeSet::from([v1, v2, v3]))).complete_backbone());
        assert_eq!(BTreeSet::new(), Backbone::new_sat(Some(BTreeSet::new()), None, None).complete_backbone());
        assert_eq!(BTreeSet::new(), Backbone::new_sat(None, Some(BTreeSet::new()), None).complete_backbone());
        assert_eq!(BTreeSet::new(), Backbone::new_sat(Some(BTreeSet::new()), Some(BTreeSet::new()), None).complete_backbone());
        assert_eq!(
            BTreeSet::from([v1.pos_lit(), v2.pos_lit(), v3.pos_lit()]),
            Backbone::new_sat(Some(BTreeSet::from([v1, v2, v3])), None, None).complete_backbone()
        );
        assert_eq!(
            BTreeSet::from([v1.neg_lit(), v2.neg_lit(), v3.neg_lit()]),
            Backbone::new_sat(None, Some(BTreeSet::from([v1, v2, v3])), None).complete_backbone()
        );
        assert_eq!(
            BTreeSet::from([v1.neg_lit(), v2.neg_lit(), v3.neg_lit(), v4.pos_lit(), v5.pos_lit()]),
            Backbone::new_sat(Some(BTreeSet::from([v4, v5])), Some(BTreeSet::from([v1, v2, v3])), None).complete_backbone()
        );
        assert_eq!(
            BTreeSet::from([v1.neg_lit(), v2.neg_lit(), v3.neg_lit(), v4.pos_lit()]),
            Backbone::new_sat(Some(BTreeSet::from([v4])), Some(BTreeSet::from([v1, v2, v3])), Some(BTreeSet::from([v5])))
                .complete_backbone()
        );
    }

    #[test]
    fn test_to_formula() {
        let f = &FormulaFactory::new();
        let (v1, v2, v3, v4, v5) = (f.var("a"), f.var("b"), f.var("c"), f.var("d"), f.var("e"));
        assert_eq!(f.falsum(), Backbone::new_unsat().to_formula(f));
        assert_eq!(f.verum(), Backbone::new_sat(None, None, None).to_formula(f));
        assert_eq!(f.verum(), Backbone::new_sat(None, None, Some(BTreeSet::from([v1, v2, v3]))).to_formula(f));
        assert_eq!(f.verum(), Backbone::new_sat(Some(BTreeSet::new()), None, None).to_formula(f));
        assert_eq!(f.verum(), Backbone::new_sat(None, Some(BTreeSet::new()), None).to_formula(f));
        assert_eq!(f.verum(), Backbone::new_sat(Some(BTreeSet::new()), Some(BTreeSet::new()), None).to_formula(f));
        assert_eq!("a & b & c".to_formula(f), Backbone::new_sat(Some(BTreeSet::from([v1, v2, v3])), None, None).to_formula(f));
        assert_eq!("~a & ~b & ~c".to_formula(f), Backbone::new_sat(None, Some(BTreeSet::from([v1, v2, v3])), None).to_formula(f));
        assert_eq!(
            "~a & ~b & ~c & d & e".to_formula(f),
            Backbone::new_sat(Some(BTreeSet::from([v4, v5])), Some(BTreeSet::from([v1, v2, v3])), None).to_formula(f)
        );
        assert_eq!(
            "~a & ~b & ~c & d".to_formula(f),
            Backbone::new_sat(Some(BTreeSet::from([v4])), Some(BTreeSet::from([v1, v2, v3])), Some(BTreeSet::from([v5]))).to_formula(f)
        );
    }
}
