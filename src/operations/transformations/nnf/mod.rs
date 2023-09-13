use crate::formulas::{EncodedFormula, Formula, FormulaFactory};

/// Constructs the _NNF_ form of `formula`.
///
/// # Examples
///
/// Basic usage:
///
/// ```
/// # use logicng::formulas::FormulaFactory;
/// # use logicng::formulas::ToFormula;
/// # use logicng::operations::transformations::nnf;
/// let f = FormulaFactory::new();
///
/// let formula1 = "a => b".to_formula(&f);
/// let nnf = nnf(formula1, &f);
///
/// assert_eq!(nnf.to_string(&f), "~a | b");
/// ```
pub fn nnf(formula: EncodedFormula, f: &FormulaFactory) -> EncodedFormula {
    nnf_rec(formula, f, true)
}

fn nnf_rec(formula: EncodedFormula, f: &FormulaFactory, polarity: bool) -> EncodedFormula {
    if polarity {
        if let Some(nnf) = f.caches.nnf.get(formula) {
            return nnf;
        }
    }

    let nnf = match formula.unpack(f) {
        Formula::True | Formula::False | Formula::Lit(_) => {
            if polarity {
                formula
            } else {
                f.negate(formula)
            }
        }
        Formula::Not(op) => nnf_rec(op, f, !polarity),
        Formula::Or(ops) => {
            let new_ops = ops.map(|op| nnf_rec(op, f, polarity)).collect::<Box<[_]>>();
            if polarity {
                f.or(&new_ops)
            } else {
                f.and(&new_ops)
            }
        }
        Formula::And(ops) => {
            let new_ops = ops.map(|op| nnf_rec(op, f, polarity)).collect::<Box<[_]>>();
            if polarity {
                f.and(&new_ops)
            } else {
                f.or(&new_ops)
            }
        }
        Formula::Equiv((left, right)) => {
            let left_false = nnf_rec(left, f, false);
            let right_true = nnf_rec(right, f, true);
            let left_true = nnf_rec(left, f, true);
            let right_false = nnf_rec(right, f, false);
            if polarity {
                let op1 = f.or(&[left_false, right_true]);
                let op2 = f.or(&[left_true, right_false]);
                f.and(&[op1, op2])
            } else {
                let op1 = f.or(&[left_false, right_false]);
                let op2 = f.or(&[left_true, right_true]);
                f.and(&[op1, op2])
            }
        }
        Formula::Impl((left, right)) => {
            if polarity {
                let left_false = nnf_rec(left, f, false);
                let right_true = nnf_rec(right, f, true);
                f.or(&[left_false, right_true])
            } else {
                let left_true = nnf_rec(left, f, true);
                let right_false = nnf_rec(right, f, false);
                f.and(&[left_true, right_false])
            }
        }
        Formula::Cc(c) => {
            if polarity {
                let new_ops = c.encode(f).iter().map(|&op| nnf_rec(op, f, true)).collect::<Box<[_]>>();
                f.and(&new_ops)
            } else {
                nnf_rec(c.negate(f), f, true)
            }
        }
        Formula::Pbc(p) => {
            if polarity {
                let new_ops = p.encode(f).iter().map(|&op| nnf_rec(op, f, true)).collect::<Box<[_]>>();
                f.and(&new_ops)
            } else {
                nnf_rec(p.negate(f), f, true)
            }
        }
    };

    if polarity && f.config.caches.nnf {
        if f.config.caches.nnf {
            f.caches.nnf.insert(formula, nnf);
        }

        if f.config.caches.is_nnf {
            f.caches.is_nnf.insert(nnf, true);
        }
    }
    nnf
}

#[cfg(test)]
#[allow(non_snake_case)]
mod tests {
    use crate::formulas::ToFormula;
    use crate::util::test_util::F;

    #[test]
    fn test_constants() {
        let F = F::new();
        let f = &F.f;
        assert_eq!(f.nnf_of(F.TRUE), F.TRUE);
        assert_eq!(f.nnf_of(F.FALSE), F.FALSE);
    }

    #[test]
    fn test_literals() {
        let F = F::new();
        let f = &F.f;
        assert_eq!(f.nnf_of(F.A), F.A);
        assert_eq!(f.nnf_of(F.NA), F.NA);
    }

    #[test]
    fn test_binary_operators() {
        let F = F::new();
        let f = &F.f;
        assert_eq!(f.nnf_of(F.IMP1), "~a | b".to_formula(f));
        assert_eq!(f.nnf_of(F.IMP2), "a | ~b".to_formula(f));
        assert_eq!(f.nnf_of(F.IMP3), "~a | ~b | x | y".to_formula(f));
        assert_eq!(f.nnf_of(F.IMP4), "(~a | ~b) & (a | b) | (x | ~y) & (y | ~x)".to_formula(f));
        assert_eq!(f.nnf_of(F.EQ1), "(~a | b) & (~b | a)".to_formula(f));
        assert_eq!(f.nnf_of(F.EQ2), "(a | ~b) & (b | ~a)".to_formula(f));
        assert_eq!(f.nnf_of(F.EQ3), "(~a | ~b | x | y) & (~x & ~y | a & b)".to_formula(f));
    }

    #[test]
    fn test_nary_operators() {
        let F = F::new();
        let f = &F.f;
        let formula1 = "~(a | b) & c & ~(x & ~y) & (w => z)".to_formula(f);
        let formula2 = "~(a & b) | c | ~(x | ~y) | (w => z)".to_formula(f);
        assert_eq!(f.nnf_of(F.AND1), F.AND1);
        assert_eq!(f.nnf_of(F.OR1), F.OR1);
        assert_eq!(f.nnf_of(formula1), "~a & ~b & c & (~x | y) & (~w | z)".to_formula(f));
        assert_eq!(f.nnf_of(formula2), "~a  | ~b | c | (~x & y) | (~w | z)".to_formula(f));
    }

    #[test]
    fn test_not() {
        let F = F::new();
        let f = &F.f;
        let formula1 = "~a".to_formula(f);
        let formula2 = "~~a".to_formula(f);
        let formula3 = "~(a => b)".to_formula(f);
        let formula4 = "~(~(a | b) => ~(x | y))".to_formula(f);
        let formula5 = "~(a <=> b)".to_formula(f);
        let formula6 = "~(~(a | b) <=> ~(x | y))".to_formula(f);
        let formula7 = "~(a & b & ~x & ~y)".to_formula(f);
        let formula8 = "~(a | b | ~x | ~y)".to_formula(f);
        let formula9 = "~(a | b | ~x | ~y)".to_formula(f);
        assert_eq!(f.nnf_of(formula1), "~a".to_formula(f));
        assert_eq!(f.nnf_of(formula2), "a".to_formula(f));
        assert_eq!(f.nnf_of(formula3), "a & ~b".to_formula(f));
        assert_eq!(f.nnf_of(formula4), "~a & ~b & (x | y)".to_formula(f));
        assert_eq!(f.nnf_of(formula5), "(~a | ~b) & (a | b)".to_formula(f));
        assert_eq!(f.nnf_of(formula6), "((a | b) | (x | y)) & ((~a & ~b) | (~x & ~y))".to_formula(f));
        assert_eq!(f.nnf_of(formula7), "~a | ~b | x | y".to_formula(f));
        assert_eq!(f.nnf_of(formula8), "~a & ~b & x & y".to_formula(f));
        assert_eq!(f.nnf_of(formula9), "~a & ~b & x & y".to_formula(f));
    }
}
