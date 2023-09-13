use crate::formulas::{CType, FormulaFactory, Literal, Variable};
use crate::parser::pseudo_boolean_parser::parse;

#[test]
fn test_parse_empty() {
    let f = FormulaFactory::new();
    let a = f.variable("a");
    let b = f.variable("b");
    assert_eq!(parse(&f, "").unwrap(), f.verum());
    assert_eq!(parse(&f, " ").unwrap(), f.verum());
    assert_eq!(parse(&f, "\t").unwrap(), f.verum());
    assert_eq!(parse(&f, "\n").unwrap(), f.verum());
    assert_eq!(parse(&f, "\r").unwrap(), f.verum());
    assert_eq!(parse(&f, " \r\n\n  \t").unwrap(), f.verum());
    assert_eq!(parse(&f, "a\n&\tb").unwrap(), f.and(&[a, b]));
    assert_eq!(parse(&f, " a\r=>\t\tb").unwrap(), f.implication(a, b));
}

#[test]
fn test_parse_constants() {
    let f = FormulaFactory::new();
    assert_eq!(parse(&f, " $true  ").unwrap(), f.verum());
    assert_eq!(parse(&f, "    $false").unwrap(), f.falsum());
}

#[test]
fn test_parse_literals() {
    let f = FormulaFactory::new();
    assert_eq!(parse(&f, "A").unwrap(), f.variable("A"));
    assert_eq!(parse(&f, "a").unwrap(), f.variable("a"));
    assert_eq!(parse(&f, "a1").unwrap(), f.variable("a1"));
    assert_eq!(parse(&f, "aA_Bb_Cc_12_3").unwrap(), f.variable("aA_Bb_Cc_12_3"));
    assert_eq!(parse(&f, "~A").unwrap(), f.literal("A", false));
    assert_eq!(parse(&f, "~a").unwrap(), f.literal("a", false));
    assert_eq!(parse(&f, "~a1").unwrap(), f.literal("a1", false));
    assert_eq!(parse(&f, "~aA_Bb_Cc_12_3").unwrap(), f.literal("aA_Bb_Cc_12_3", false));
    assert_eq!(parse(&f, "~@aA_Bb_Cc_12_3").unwrap(), f.literal("@aA_Bb_Cc_12_3", false));
}

#[test]
fn test_parse_operators() {
    let f = FormulaFactory::new();
    let a = f.variable("a");
    let b = f.variable("b");
    let d = f.variable("d");
    let var = f.variable("Var");
    let na = f.literal("a", false);
    let nb = f.literal("b", false);
    let nc = f.literal("c", false);
    assert_eq!(parse(&f, "~a").unwrap(), f.not(a));
    assert_eq!(parse(&f, "~Var").unwrap(), f.not(var));
    assert_eq!(parse(&f, "a & b").unwrap(), f.and(&[a, b]));
    assert_eq!(parse(&f, "~a & ~b").unwrap(), f.and(&[na, nb]));
    assert_eq!(parse(&f, "~a & b & ~c & d").unwrap(), f.and(&[na, b, nc, d]));
    assert_eq!(parse(&f, "a | b").unwrap(), f.or(&[a, b]));
    assert_eq!(parse(&f, "~a | ~b").unwrap(), f.or(&[na, nb]));
    assert_eq!(parse(&f, "~a | b | ~c | d").unwrap(), f.or(&[na, b, nc, d]));
    assert_eq!(parse(&f, "a => b").unwrap(), f.implication(a, b));
    assert_eq!(parse(&f, "~a => ~b").unwrap(), f.implication(na, nb));
    assert_eq!(parse(&f, "a <=> b").unwrap(), f.equivalence(a, b));
    assert_eq!(parse(&f, "~a <=> ~b").unwrap(), f.equivalence(na, nb));
}

#[test]
fn test_parse_multiplication() {
    let f = FormulaFactory::new();
    let abc = f.variable("abc").as_literal().unwrap();
    let a = f.variable("a").as_literal().unwrap();
    let not_a = f.literal("a", false).as_literal().unwrap();
    let not_abc = f.literal("abc", false).as_literal().unwrap();
    assert_eq!(parse(&f, "13 * abc = 4").unwrap(), f.pbc(CType::EQ, 4, (&[abc]) as &[Literal], &[13_i64] as &[i64]));
    assert_eq!(parse(&f, "-13 * a = 4").unwrap(), f.pbc(CType::EQ, 4, (&[a]) as &[Literal], (&[-13_i64]) as &[i64]));
    assert_eq!(parse(&f, "13 * ~abc = -442").unwrap(), f.pbc(CType::EQ, -442, (&[not_abc]) as &[Literal], (&[13_i64]) as &[i64]));
    assert_eq!(parse(&f, "-13 * ~a = -442").unwrap(), f.pbc(CType::EQ, -442, (&[not_a]) as &[Literal], (&[-13_i64]) as &[i64]));
    assert_eq!(parse(&f, "13 * abc = 4").unwrap(), f.pbc(CType::EQ, 4, (&[abc]) as &[Literal], (&[13_i64]) as &[i64]));
    assert_eq!(parse(&f, "13 * abc > 4").unwrap(), f.pbc(CType::GT, 4, (&[abc]) as &[Literal], (&[13_i64]) as &[i64]));
    assert_eq!(parse(&f, "13 * abc >= 4").unwrap(), f.pbc(CType::GE, 4, (&[abc]) as &[Literal], (&[13_i64]) as &[i64]));
    assert_eq!(parse(&f, "13 * abc < 4").unwrap(), f.pbc(CType::LT, 4, (&[abc]) as &[Literal], (&[13_i64]) as &[i64]));
    assert_eq!(parse(&f, "13 * abc <= 4").unwrap(), f.pbc(CType::LE, 4, (&[abc]) as &[Literal], (&[13_i64]) as &[i64]));
}

#[test]
fn test_parse_addition() {
    let f = FormulaFactory::new();
    let a = f.variable("a").as_literal().unwrap();
    let c = f.variable("c").as_literal().unwrap();
    let d = f.literal("d", true).as_literal().unwrap();
    let not_b = f.literal("b", false).as_literal().unwrap();
    let not_d = f.literal("d", false).as_literal().unwrap();
    let not_c = f.literal("c", false).as_literal().unwrap();
    assert_eq!(parse(&f, "4 * c + -4 * ~d < -4").unwrap(), f.pbc(CType::LT, -4, (&[c, not_d]) as &[Literal], (&[4_i64, -4]) as &[i64]));
    assert_eq!(parse(&f, "5 * c + -5 * ~c >= -5").unwrap(), f.pbc(CType::GE, -5, (&[c, not_c]) as &[Literal], (&[5_i64, -5]) as &[i64]));
    assert_eq!(
        parse(&f, "6 * a + -6 * ~b + 12 * ~c > -6").unwrap(),
        f.pbc(CType::GT, -6, (&[a, not_b, not_c]) as &[Literal], (&[6_i64, -6, 12]) as &[i64])
    );
    assert_eq!(parse(&f, "c + -4 * ~d < -4").unwrap(), f.pbc(CType::LT, -4, (&[c, not_d]) as &[Literal], (&[1_i64, -4]) as &[i64]));
    assert_eq!(parse(&f, "5 * c + ~c >= -5").unwrap(), f.pbc(CType::GE, -5, (&[c, not_c]) as &[Literal], (&[5_i64, 1]) as &[i64]));
    assert_eq!(parse(&f, "c + d >= -5").unwrap(), f.pbc(CType::GE, -5, (&[c, d]) as &[Literal], (&[1_i64, 1]) as &[i64]));
    assert_eq!(parse(&f, "~c + ~d >= -5").unwrap(), f.pbc(CType::GE, -5, (&[not_c, not_d]) as &[Literal], (&[1_i64, 1]) as &[i64]));
    assert_eq!(parse(&f, "~c = -5").unwrap(), f.pbc(CType::EQ, -5, (&[not_c]) as &[Literal], (&[1_i64]) as &[i64]));
    let pbc = f.pbc(CType::EQ, -5, (&[c]) as &[Literal], (&[1_i64]) as &[i64]);
    assert_eq!(parse(&f, "~(c = -5)").unwrap(), f.not(pbc));
}

#[test]
#[allow(clippy::many_single_char_names)]
fn test_combination() {
    let f = FormulaFactory::new();
    let a = f.variable("a").as_literal().unwrap();
    let not_b = f.literal("b", false).as_literal().unwrap();
    let not_c = f.literal("c", false).as_literal().unwrap();
    let pbc = f.pbc(CType::GT, -6, (&[a, not_b, not_c]) as &[Literal], (&[6_i64, -6, 12]) as &[i64]);
    let x = f.variable("x");
    let y = f.variable("y");
    let z = f.variable("z");
    let yz = f.and(&[y, z]);
    let imp = f.implication(x, yz);
    assert_eq!(parse(&f, "(x => y & z) & (6 * a + -6 * ~b + 12 * ~c > -6)").unwrap(), f.and(&[imp, pbc]));
    assert_eq!(parse(&f, "~(6 * a - 6 * ~b - -12 * ~c > -6)").unwrap(), f.not(pbc));
}

#[test]
#[allow(clippy::cognitive_complexity, clippy::many_single_char_names)]
fn test_parse_precedences() {
    let f = FormulaFactory::new();
    let x = f.variable("x");
    let y = f.variable("y");
    let z = f.variable("z");
    let x_and_y = f.and(&[x, y]);
    let y_and_z = f.and(&[y, z]);
    let x_or_y = f.or(&[x, y]);
    let y_or_z = f.or(&[y, z]);
    let y_imp_z = f.implication(y, z);
    let y_eq_z = f.equivalence(y, z);
    let x_eq_y = f.equivalence(x, y);
    let x_imp_y = f.implication(x, y);
    assert_eq!(parse(&f, "x | y & z").unwrap(), f.or(&[x, y_and_z]));
    assert_eq!(parse(&f, "x & y | z").unwrap(), f.or(&[x_and_y, z]));
    assert_eq!(parse(&f, "x => y & z").unwrap(), f.implication(x, y_and_z));
    assert_eq!(parse(&f, "x & y => z").unwrap(), f.implication(x_and_y, z));
    assert_eq!(parse(&f, "x <=> y & z").unwrap(), f.equivalence(x, y_and_z));
    assert_eq!(parse(&f, "x & y <=> z").unwrap(), f.equivalence(x_and_y, z));
    assert_eq!(parse(&f, "x => y | z").unwrap(), f.implication(x, y_or_z));
    assert_eq!(parse(&f, "x | y => z").unwrap(), f.implication(x_or_y, z));
    assert_eq!(parse(&f, "x <=> y | z").unwrap(), f.equivalence(x, y_or_z));
    assert_eq!(parse(&f, "x | y <=> z").unwrap(), f.equivalence(x_or_y, z));
    assert_eq!(parse(&f, "x => y => z").unwrap(), f.implication(x, y_imp_z));
    assert_eq!(parse(&f, "x <=> y <=> z").unwrap(), f.equivalence(x, y_eq_z));
    assert_eq!(parse(&f, "(x | y) & z").unwrap(), f.and(&[x_or_y, z]));
    assert_eq!(parse(&f, "x & (y | z)").unwrap(), f.and(&[x, y_or_z]));
    assert_eq!(parse(&f, "(x => y) & z").unwrap(), f.and(&[x_imp_y, z]));
    assert_eq!(parse(&f, "x & (y => z)").unwrap(), f.and(&[x, y_imp_z]));
    assert_eq!(parse(&f, "(x => y) | z").unwrap(), f.or(&[x_imp_y, z]));
    assert_eq!(parse(&f, "x | (y => z)").unwrap(), f.or(&[x, y_imp_z]));
    assert_eq!(parse(&f, "(x <=> y) & z").unwrap(), f.and(&[x_eq_y, z]));
    assert_eq!(parse(&f, "x & (y <=> z)").unwrap(), f.and(&[x, y_eq_z]));
    assert_eq!(parse(&f, "(x <=> y) | z").unwrap(), f.or(&[x_eq_y, z]));
    assert_eq!(parse(&f, "x | (y <=> z)").unwrap(), f.or(&[x, y_eq_z]));
    assert_eq!(parse(&f, "x => y <=> z").unwrap(), f.equivalence(x_imp_y, z));
    assert_eq!(parse(&f, "x => (y <=> z)").unwrap(), f.implication(x, y_eq_z));

    let a = f.variable("A");
    let not_lit12 = f.literal("12", false);
    let not_b = f.literal("B", false);
    let not_x = f.literal("x", false);
    let pbc = f.pbc(
        CType::LE,
        -25,
        (&[not_lit12.as_literal().unwrap(), a.as_literal().unwrap(), not_b.as_literal().unwrap()]) as &[Literal],
        (&[1_i64, 13, 1]) as &[i64],
    );
    assert_eq!(parse(&f, "~12 - -13 * A + ~B <= -25 & x").unwrap(), f.and(&[pbc, x]));
    assert_eq!(parse(&f, "~12 - -13 * A + ~B <= -25 | ~x").unwrap(), f.or(&[pbc, not_x]));
    assert_eq!(parse(&f, "~12 - -13 * A + ~B <= -25 => ~x").unwrap(), f.implication(pbc, not_x));
    assert_eq!(parse(&f, "~x => ~12 - -13 * A + ~B <= -25").unwrap(), f.implication(not_x, pbc));
    assert_eq!(parse(&f, "~12 - -13 * A + ~B <= -25 <=> ~x").unwrap(), f.equivalence(pbc, not_x));
    assert_eq!(parse(&f, "~(~12 - -13 * A + ~B <= -25)").unwrap(), f.not(pbc));
}

#[test]
fn test_number_literals() {
    let f = FormulaFactory::new();
    let a = f.variable("A");
    let b = f.variable("B");
    let lit12 = f.literal("12", true);
    let not_lit12 = f.literal("12", false);
    let not_b = f.literal("B", false);
    assert_eq!(
        parse(&f, "12 + A <= 25").unwrap(),
        f.cc(CType::LE, 25, (&[lit12.as_variable().unwrap(), a.as_variable().unwrap()]) as &[Variable])
    );
    assert_eq!(parse(&f, "12 & A").unwrap(), f.and(&[lit12, a]));
    assert_eq!(parse(&f, "~12 & A").unwrap(), f.and(&[not_lit12, a]));
    assert_eq!(
        parse(&f, "12 * 12 + 13 * A + 10 * B <= 25").unwrap(),
        f.pbc(
            CType::LE,
            25,
            (&[lit12.as_literal().unwrap(), a.as_literal().unwrap(), b.as_literal().unwrap()]) as &[Literal],
            (&[12_i64, 13, 10]) as &[i64]
        )
    );
    assert_eq!(
        parse(&f, "-12 * ~12 + 13 * A + 10 * B <= 25").unwrap(),
        f.pbc(
            CType::LE,
            25,
            (&[not_lit12.as_literal().unwrap(), a.as_literal().unwrap(), b.as_literal().unwrap()]) as &[Literal],
            (&[-12_i64, 13, 10]) as &[i64]
        )
    );
    assert_eq!(
        parse(&f, "-12 * ~12 - 13 * A + 10 * B <= 25").unwrap(),
        f.pbc(
            CType::LE,
            25,
            (&[not_lit12.as_literal().unwrap(), a.as_literal().unwrap(), b.as_literal().unwrap()]) as &[Literal],
            (&[-12_i64, -13, 10]) as &[i64]
        )
    );
    assert_eq!(
        parse(&f, "-12 * ~12 - 13 * A + ~B <= 25").unwrap(),
        f.pbc(
            CType::LE,
            25,
            (&[not_lit12.as_literal().unwrap(), a.as_literal().unwrap(), not_b.as_literal().unwrap()]) as &[Literal],
            (&[-12_i64, -13, 1]) as &[i64]
        )
    );
    assert_eq!(
        parse(&f, "~12 - 13 * A + ~B <= 25").unwrap(),
        f.pbc(
            CType::LE,
            25,
            (&[not_lit12.as_literal().unwrap(), a.as_literal().unwrap(), not_b.as_literal().unwrap()]) as &[Literal],
            (&[1_i64, -13, 1]) as &[i64]
        )
    );
    assert_eq!(
        parse(&f, "~12 - -13 * A + ~B <= 25").unwrap(),
        f.pbc(
            CType::LE,
            25,
            (&[not_lit12.as_literal().unwrap(), a.as_literal().unwrap(), not_b.as_literal().unwrap()]) as &[Literal],
            (&[1_i64, 13, 1]) as &[i64]
        )
    );
    assert_eq!(
        parse(&f, "~12 - -13 * A + ~B <= -25").unwrap(),
        f.pbc(
            CType::LE,
            -25,
            (&[not_lit12.as_literal().unwrap(), a.as_literal().unwrap(), not_b.as_literal().unwrap()]) as &[Literal],
            (&[1_i64, 13, 1]) as &[i64]
        )
    );
}

#[test]
fn test_illegal_input() {
    let f = FormulaFactory::new();
    assert!(parse(&f, "$$%").is_err());
    assert!(parse(&f, ";;23").is_err());
    assert!(parse(&f, "{0}").is_err());
    assert!(parse(&f, "A + B").is_err());
    assert!(parse(&f, "A &").is_err());
    assert!(parse(&f, "A /").is_err());
    assert!(parse(&f, "-A").is_err());
    assert!(parse(&f, "A * B").is_err());
    assert!(parse(&f, "(A & B").is_err());
    assert!(parse(&f, "((A & B)").is_err());
    assert!(parse(&f, "(A & (C & D) B)").is_err());
    assert!(parse(&f, "A | A + (C | B + C)").is_err());
    assert!(parse(&f, "A | A & (C | B & C").is_err());
    assert!(parse(&f, "A & ~B)").is_err());
    assert!(parse(&f, "12)").is_err());
    assert!(parse(&f, "ab@cd)").is_err());
    assert!(parse(&f, "A & B => D | ~").is_err());
    assert!(parse(&f, "#").is_err());
    assert!(parse(&f, "~2 * A <= 42").is_err());
    assert!(parse(&f, "~~A <= 42").is_err()); // works in Java, because we do not enforce brackets around the negated PBC
    assert!(parse(&f, "~-2 * A <= 42").is_err()); // works in Java, because we do not enforce brackets around the negated PBC
    assert!(parse(&f, "~2 * A <= 42").is_err()); // also does not work in Java (which is somewhat inconsistent)
}
