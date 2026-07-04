use crate::errors::LngResult;
use crate::formulas::{CType, EncodedFormula, FormulaFactory, Literal};
use crate::parser::ParserError;
use pest::Parser;
use pest::iterators::Pair;
use std::str::FromStr;

#[derive(Parser)]
#[grammar = "parser/lng_pseudo_boolean_parser.pest"]
struct PseudoBooleanParser;

pub fn parse<I: AsRef<str>>(f: &FormulaFactory, input: I) -> LngResult<EncodedFormula> {
    let parsed = PseudoBooleanParser::parse(Rule::pseudo_boolean, input.as_ref())
        .map_err(|err| ParserError::Syntax(Box::new(err)))?
        .next()
        .ok_or(ParserError::UnexpectedEnd)?;

    let mut formula = f.verum();

    for x in parsed.into_inner() {
        match x.as_rule() {
            Rule::equivalence => {
                formula = parse_equivalence(f, x)?;
            }
            Rule::EOI => (),
            rule => return Err(ParserError::UnexpectedRule { rule: format!("{rule:?}") }.into()),
        }
    }

    Ok(formula)
}

fn parse_equivalence(f: &FormulaFactory, equivalence: Pair<Rule>) -> LngResult<EncodedFormula> {
    let mut implications = equivalence.into_inner().rev();
    let mut form = parse_implication(f, next_pair(&mut implications)?)?;

    for implication in implications {
        let form_left = parse_implication(f, implication)?;
        form = f.equivalence(form_left, form);
    }
    Ok(form)
}

fn parse_implication(f: &FormulaFactory, implication: Pair<Rule>) -> LngResult<EncodedFormula> {
    let mut disjunctions = implication.into_inner().rev();
    let mut form = parse_disjunction(f, next_pair(&mut disjunctions)?)?;

    for disjunction in disjunctions {
        let form_left = parse_disjunction(f, disjunction)?;
        form = f.implication(form_left, form);
    }
    Ok(form)
}

fn parse_disjunction(f: &FormulaFactory, disjunction: Pair<Rule>) -> LngResult<EncodedFormula> {
    let conjunctions = disjunction.into_inner();
    let mut conjs = Vec::default();

    for conjunction in conjunctions {
        conjs.push(parse_conjunction(f, conjunction)?);
    }

    if conjs.len() > 1 { Ok(f.or(&conjs)) } else { conjs.pop().ok_or(ParserError::UnexpectedEnd.into()) }
}

fn parse_conjunction(f: &FormulaFactory, conjunction: Pair<Rule>) -> LngResult<EncodedFormula> {
    let lits = conjunction.into_inner();
    let mut lits_vec = Vec::default();

    for lit in lits {
        lits_vec.push(parse_lit(f, lit)?);
    }

    if lits_vec.len() > 1 { Ok(f.and(&lits_vec)) } else { lits_vec.pop().ok_or(ParserError::UnexpectedEnd.into()) }
}

fn parse_lit(f: &FormulaFactory, lit: Pair<Rule>) -> LngResult<EncodedFormula> {
    let a = next_pair(&mut lit.into_inner())?;
    match a.as_rule() {
        Rule::comparison => parse_comparison(f, a),
        Rule::simp => parse_simp(f, a),
        rule => Err(ParserError::UnexpectedRule { rule: format!("{rule:?}") }.into()),
    }
}

fn parse_simp(f: &FormulaFactory, simp: Pair<Rule>) -> LngResult<EncodedFormula> {
    let mut tokens = simp.into_inner();
    let mut phase = true;
    let mut x = next_pair(&mut tokens)?;
    while x.as_rule() == Rule::not {
        phase = !phase;
        x = next_pair(&mut tokens)?;
    }

    let mut form = match x.as_rule() {
        Rule::literal => parse_literal(f, x),
        Rule::constant => parse_constant(f, x),
        Rule::equivalence => parse_equivalence(f, x),
        rule => Err(ParserError::UnexpectedRule { rule: format!("{rule:?}") }.into()),
    }?;

    if !phase {
        form = f.not(form);
    }
    Ok(form)
}

fn parse_comparison(f: &FormulaFactory, comparison: Pair<Rule>) -> LngResult<EncodedFormula> {
    let mut tokens = comparison.into_inner();
    let mut literals = Vec::default();
    let mut coefficients = Vec::default();
    let (l1, c1) = parse_mul(f, next_pair(&mut tokens)?)?;
    literals.push(l1);
    coefficients.push(c1);

    let comp_type = loop {
        let operator = next_pair(&mut tokens)?;
        match operator.as_rule() {
            Rule::add => {
                let (ln, cn) = parse_mul(f, next_pair(&mut tokens)?)?;
                literals.push(ln);
                coefficients.push(cn);
            }
            Rule::sub => {
                let (ln, cn) = parse_mul(f, next_pair(&mut tokens)?)?;
                literals.push(ln);
                coefficients.push(checked_neg_coefficient(cn)?);
            }
            Rule::comp_type => {
                break operator;
            }
            rule => return Err(ParserError::UnexpectedRule { rule: format!("{rule:?}") }.into()),
        }
    };

    let comparator = match next_pair(&mut comp_type.into_inner())?.as_rule() {
        Rule::eq => CType::EQ,
        Rule::le => CType::LE,
        Rule::lt => CType::LT,
        Rule::ge => CType::GE,
        Rule::gt => CType::GT,
        rule => return Err(ParserError::UnexpectedRule { rule: format!("{rule:?}") }.into()),
    };
    let rhs = parse_i64(next_pair(&mut tokens)?.as_str(), false)?;
    Ok(f.pbc(comparator, rhs, literals, coefficients))
}

fn parse_mul(f: &FormulaFactory, mul: Pair<Rule>) -> LngResult<(Literal, i64)> {
    let mut tokens = mul.into_inner();
    let mut x = next_pair(&mut tokens)?;

    let coefficient = if x.as_rule() == Rule::number {
        let r = parse_i64(x.as_str(), true)?;
        x = next_pair(&mut tokens)?;
        r
    } else {
        1
    };

    let lit = parse_literal(f, x)?.as_literal().ok_or(ParserError::UnexpectedRule { rule: "non-literal in multiplication".into() })?;
    Ok((lit, coefficient))
}

fn parse_literal(f: &FormulaFactory, literal: Pair<Rule>) -> LngResult<EncodedFormula> {
    let mut tokens = literal.into_inner();
    let x = next_pair(&mut tokens)?;
    if x.as_rule() == Rule::not {
        let formula = f.parsed_variable(next_pair(&mut tokens)?.as_str());
        Ok(f.negate(formula))
    } else {
        Ok(f.parsed_variable(x.as_str()))
    }
}

fn parse_constant(f: &FormulaFactory, constant: Pair<Rule>) -> LngResult<EncodedFormula> {
    let con = next_pair(&mut constant.into_inner())?.as_rule();
    match con {
        Rule::verum => Ok(f.verum()),
        Rule::falsum => Ok(f.falsum()),
        rule => Err(ParserError::UnexpectedRule { rule: format!("{rule:?}") }.into()),
    }
}

fn next_pair<'a, I>(pairs: &mut I) -> LngResult<Pair<'a, Rule>>
where
    I: Iterator<Item = Pair<'a, Rule>>,
{
    pairs.next().ok_or(ParserError::UnexpectedEnd.into())
}

fn parse_i64(value: &str, coefficient: bool) -> LngResult<i64> {
    i64::from_str(value).map_err(|_| {
        if coefficient {
            ParserError::CoefficientOverflow { value: value.to_string() }.into()
        } else {
            ParserError::IntegerOverflow { value: value.to_string() }.into()
        }
    })
}

fn checked_neg_coefficient(value: i64) -> LngResult<i64> {
    value.checked_neg().ok_or(ParserError::CoefficientOverflow { value: value.to_string() }.into())
}
