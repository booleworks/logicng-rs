use crate::formulas::{CType, EncodedFormula, FormulaFactory, Literal};
use pest::error::Error;
use pest::iterators::Pair;
use pest::Parser;

#[derive(Parser)]
#[grammar = "parser/lng_pseudo_boolean_parser.pest"]
struct PseudoBooleanParser;

pub fn parse<I: AsRef<str>>(f: &FormulaFactory, input: I) -> Result<EncodedFormula, Box<Error<Rule>>> {
    let parsed = PseudoBooleanParser::parse(Rule::pseudo_boolean, input.as_ref())?.next().unwrap();

    let mut formula = f.verum();

    for x in parsed.into_inner() {
        match x.as_rule() {
            Rule::equivalence => {
                formula = parse_equivalence(f, x);
            }
            Rule::EOI => (),
            _ => unreachable!(),
        }
    }

    Ok(formula)
}

fn parse_equivalence(f: &FormulaFactory, equivalence: Pair<Rule>) -> EncodedFormula {
    let mut implications = equivalence.into_inner().rev();
    let mut form = parse_implication(f, implications.next().unwrap());

    for implication in implications {
        let form_left = parse_implication(f, implication);
        form = f.equivalence(form_left, form);
    }
    form
}

fn parse_implication(f: &FormulaFactory, implication: Pair<Rule>) -> EncodedFormula {
    let mut disjunctions = implication.into_inner().rev();
    let mut form = parse_disjunction(f, disjunctions.next().unwrap());

    for disjunction in disjunctions {
        let form_left = parse_disjunction(f, disjunction);
        form = f.implication(form_left, form);
    }
    form
}

fn parse_disjunction(f: &FormulaFactory, disjunction: Pair<Rule>) -> EncodedFormula {
    let conjunctions = disjunction.into_inner();
    let mut conjs = Vec::default();

    for conjunction in conjunctions {
        conjs.push(parse_conjunction(f, conjunction));
    }

    if conjs.len() > 1 {
        f.or(&conjs)
    } else {
        conjs[0]
    }
}

fn parse_conjunction(f: &FormulaFactory, conjunction: Pair<Rule>) -> EncodedFormula {
    let lits = conjunction.into_inner();
    let mut lits_vec = Vec::default();

    for lit in lits {
        lits_vec.push(parse_lit(f, lit));
    }

    if lits_vec.len() > 1 {
        f.and(&lits_vec)
    } else {
        lits_vec[0]
    }
}

fn parse_lit(f: &FormulaFactory, lit: Pair<Rule>) -> EncodedFormula {
    let a = lit.into_inner().next().unwrap();
    match a.as_rule() {
        Rule::comparison => parse_comparison(f, a),
        Rule::simp => parse_simp(f, a),
        _ => unreachable!(),
    }
}

fn parse_simp(f: &FormulaFactory, simp: Pair<Rule>) -> EncodedFormula {
    let mut tokens = simp.into_inner();
    let mut phase = true;
    let mut x = tokens.next().unwrap();
    while x.as_rule() == Rule::not {
        phase = !phase;
        x = tokens.next().unwrap();
    }

    let mut form = match x.as_rule() {
        Rule::literal => parse_literal(f, x),
        Rule::constant => parse_constant(f, x),
        Rule::equivalence => parse_equivalence(f, x),
        _ => unreachable!(),
    };

    if !phase {
        form = f.not(form);
    }
    form
}

fn parse_comparison(f: &FormulaFactory, comparison: Pair<Rule>) -> EncodedFormula {
    let mut tokens = comparison.into_inner();
    let mut literals = Vec::default();
    let mut coefficients = Vec::default();
    let (l1, c1) = parse_mul(f, tokens.next().unwrap());
    literals.push(l1);
    coefficients.push(c1);

    let comp_type = loop {
        let operator = tokens.next().unwrap();
        match operator.as_rule() {
            Rule::add => {
                let (ln, cn) = parse_mul(f, tokens.next().unwrap());
                literals.push(ln);
                coefficients.push(cn);
            }
            Rule::sub => {
                let (ln, cn) = parse_mul(f, tokens.next().unwrap());
                literals.push(ln);
                coefficients.push(-cn);
            }
            Rule::comp_type => {
                break operator;
            }
            _ => unreachable!(),
        }
    };

    let comparator = match comp_type.into_inner().next().unwrap().as_rule() {
        Rule::eq => CType::EQ,
        Rule::le => CType::LE,
        Rule::lt => CType::LT,
        Rule::ge => CType::GE,
        Rule::gt => CType::GT,
        _ => unreachable!(),
    };
    let rhs = tokens.next().unwrap().as_str().parse().unwrap();
    f.pbc(comparator, rhs, literals, coefficients)
}

fn parse_mul(f: &FormulaFactory, mul: Pair<Rule>) -> (Literal, i64) {
    let mut tokens = mul.into_inner();
    let mut x = tokens.next().unwrap();

    let coefficient = if x.as_rule() == Rule::number {
        let r = x.as_str().parse().unwrap();
        x = tokens.next().unwrap();
        r
    } else {
        1
    };

    let lit = parse_literal(f, x).as_literal().unwrap();
    (lit, coefficient)
}

fn parse_literal(f: &FormulaFactory, literal: Pair<Rule>) -> EncodedFormula {
    let mut tokens = literal.into_inner();
    let x = tokens.next().unwrap();
    if x.as_rule() == Rule::not {
        let formula = f.parsed_variable(tokens.next().unwrap().as_str());
        f.negate(formula)
    } else {
        f.parsed_variable(x.as_str())
    }
}

fn parse_constant(f: &FormulaFactory, constant: Pair<Rule>) -> EncodedFormula {
    let con = constant.into_inner().next().unwrap().as_rule();
    match con {
        Rule::verum => f.verum(),
        Rule::falsum => f.falsum(),
        _ => unreachable!(),
    }
}
