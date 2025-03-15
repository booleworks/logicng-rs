use crate::datastructures::EncodingResultFF;
use crate::encodings::cardinality_constraints::cc_config::{AlkEncoder, AmkEncoder, CcConfig};
use crate::encodings::cardinality_constraints::cc_encoder::CcEncoder;
use crate::formulas::CType::{GE, GT, LE, LT};
use crate::formulas::{FormulaFactory, Variable};
use crate::solver::lng_core_solver::SatSolver;

const fn encoders() -> [CcEncoder; 3] {
    [
        CcEncoder::new(CcConfig::new().amk_encoder(AmkEncoder::Totalizer).alk_encoder(AlkEncoder::Totalizer)),
        CcEncoder::new(CcConfig::new().amk_encoder(AmkEncoder::CardinalityNetwork).alk_encoder(AlkEncoder::CardinalityNetwork)),
        CcEncoder::new(CcConfig::new().amk_encoder(AmkEncoder::ModularTotalizer).alk_encoder(AlkEncoder::ModularTotalizer)),
    ]
}

#[test]
fn test_incremental_data() {
    for encoder in encoders() {
        let f = &FormulaFactory::new();
        let mut result = EncodingResultFF::new(f);
        let num_lits = 10;
        let vars: Box<[Variable]> = (0..num_lits).map(|i| f.var(format!("v{i}"))).collect();

        let inc_data = encoder.encode_incremental(&mut result, &f.cc(LT, num_lits, vars.clone()).as_cc(f).unwrap()).unwrap();
        assert_eq!(inc_data.current_rhs, 9);

        let inc_data = encoder.encode_incremental(&mut result, &f.cc(GT, 1, vars.clone()).as_cc(f).unwrap()).unwrap();
        assert_eq!(inc_data.current_rhs, 2);

        let inc_data = encoder.encode_incremental(&mut result, &f.cc(LT, 1, vars.clone()).as_cc(f).unwrap());
        assert!(inc_data.is_none());
        assert!(result.result.contains(&vars[0].negate().into()));

        let inc_data = encoder.encode_incremental(&mut result, &f.cc(LE, num_lits + 1, vars.clone()).as_cc(f).unwrap());
        assert!(inc_data.is_none());

        let inc_data = encoder.encode_incremental(&mut result, &f.cc(GE, num_lits + 1, vars.clone()).as_cc(f).unwrap());
        assert!(inc_data.is_none());

        let inc_data = encoder.encode_incremental(&mut result, &f.cc(GE, num_lits, vars.clone()).as_cc(f).unwrap());
        assert!(inc_data.is_none());

        let inc_data = encoder.encode_incremental(&mut result, &f.cc(GE, 0, vars.clone()).as_cc(f).unwrap());
        assert!(inc_data.is_none());

        let inc_data = encoder.encode_incremental(&mut result, &f.cc(GE, 1, vars.clone()).as_cc(f).unwrap());
        assert!(inc_data.is_none());
    }
}

#[test]
fn test_simple_incremental_amk() {
    for encoder in encoders() {
        let f = &FormulaFactory::new();
        let mut result = EncodingResultFF::new(f);
        let vars: Box<[Variable]> = (0..10).map(|i| f.var(format!("v{i}"))).collect();
        let inc_data_option = encoder.encode_incremental(&mut result, &f.cc(LE, 9, vars.clone()).as_cc(f).unwrap());
        let mut inc_data = inc_data_option.unwrap();

        let mut solver = SatSolver::<()>::new();
        solver.add_formulas(encoder.encode(&f.cc(GE, 4, vars.clone()).as_cc(f).unwrap(), f), f);
        solver.add_formulas(encoder.encode(&f.cc(LE, 7, vars).as_cc(f).unwrap(), f), f);

        solver.add_formulas(&result.result, f);
        assert!(solver.sat(f));
        assert!(solver.sat(f));
        inc_data.new_upper_bound(&mut result, 8);
        solver.add_formulas(&result.result, f);
        assert!(solver.sat(f));
        assert_eq!(inc_data.current_rhs, 8);

        inc_data.new_upper_bound(&mut result, 7);
        solver.add_formulas(&result.result, f);
        assert!(solver.sat(f));
        inc_data.new_upper_bound(&mut result, 6);
        solver.add_formulas(&result.result, f);
        assert!(solver.sat(f));
        inc_data.new_upper_bound(&mut result, 5);
        solver.add_formulas(&result.result, f);
        assert!(solver.sat(f));
        inc_data.new_upper_bound(&mut result, 4);
        solver.add_formulas(&result.result, f);
        assert!(solver.sat(f));

        let state = solver.save_state();
        inc_data.new_upper_bound(&mut result, 3);
        solver.add_formulas(&result.result, f);
        assert!(!solver.sat(f));
        solver.load_state(&state);
        assert!(solver.sat(f));
        inc_data.new_upper_bound(&mut result, 2);
        solver.add_formulas(&result.result, f);
        assert!(!solver.sat(f));
    }
}

#[test]
fn test_simple_incremental_alk() {
    for encoder in encoders() {
        let f = &FormulaFactory::new();
        let mut result = EncodingResultFF::new(f);
        let vars: Box<[Variable]> = (0..10).map(|i| f.var(format!("v{i}"))).collect();
        let mut solver = SatSolver::<()>::new();
        solver.add_formulas(f.cc(GE, 4, vars.clone()).as_cc(f).unwrap().encode(f).as_ref(), f);
        solver.add_formulas(f.cc(LE, 7, vars.clone()).as_cc(f).unwrap().encode(f).as_ref(), f);

        let inc_data_option = encoder.encode_incremental(&mut result, &f.cc(GE, 2, vars).as_cc(f).unwrap());
        let mut inc_data = inc_data_option.unwrap();

        solver.add_formulas(&result.result, f);
        assert!(solver.sat(f));
        inc_data.new_lower_bound(&mut result, 3);
        solver.add_formulas(&result.result, f);
        assert!(solver.sat(f));
        inc_data.new_lower_bound(&mut result, 4);
        solver.add_formulas(&result.result, f);
        assert!(solver.sat(f));
        inc_data.new_lower_bound(&mut result, 5);
        solver.add_formulas(&result.result, f);
        assert!(solver.sat(f));
        inc_data.new_lower_bound(&mut result, 6);
        solver.add_formulas(&result.result, f);
        assert!(solver.sat(f));
        inc_data.new_lower_bound(&mut result, 7);
        solver.add_formulas(&result.result, f);
        assert!(solver.sat(f));

        let state = solver.save_state();
        inc_data.new_lower_bound(&mut result, 8);
        solver.add_formulas(&result.result, f);
        assert!(!solver.sat(f));
        solver.load_state(&state);
        assert!(solver.sat(f));
        inc_data.new_lower_bound(&mut result, 9);
        solver.add_formulas(&result.result, f);
        assert!(!solver.sat(f));
    }
}

#[test]
#[cfg_attr(not(feature = "long_running_tests"), ignore)]
fn test_large_upper_bound_amk() {
    for encoder in [&encoders()[0], &encoders()[2]] {
        let f = &FormulaFactory::new();
        let mut result = EncodingResultFF::new(f);
        let num_lits = 100;
        let vars: Box<[Variable]> = (0..num_lits).map(|i| f.var(format!("v{i}"))).collect();
        let mut current_bound = num_lits - 1;
        let mut solver = SatSolver::<()>::new();
        solver.add_formulas(f.cc(GE, 42, vars.clone()).as_cc(f).unwrap().encode(f).as_ref(), f);

        let inc_data_option = encoder.encode_incremental(&mut result, &f.cc(LE, current_bound, vars).as_cc(f).unwrap());
        let mut inc_data = inc_data_option.unwrap();

        solver.add_formulas(&result.result, f);
        while solver.sat(f) {
            current_bound -= 1;
            inc_data.new_upper_bound(&mut result, current_bound);
            solver.add_formulas(&result.result, f);
        }
        assert_eq!(current_bound, 41);
    }
}

#[test]
#[cfg_attr(not(feature = "long_running_tests"), ignore)]
fn test_large_lower_bound_alk() {
    for encoder in [&encoders()[0], &encoders()[2]] {
        let f = &FormulaFactory::new();
        let mut result = EncodingResultFF::new(f);
        let num_lits = 100;
        let vars: Box<[Variable]> = (0..num_lits).map(|i| f.var(format!("v{i}"))).collect();
        let mut current_bound = 2;
        let mut solver = SatSolver::<()>::new();
        solver.add_formulas(f.cc(LE, 87, vars.clone()).as_cc(f).unwrap().encode(f).as_ref(), f);

        let inc_data_option = encoder.encode_incremental(&mut result, &f.cc(GE, current_bound, vars).as_cc(f).unwrap());
        let mut inc_data = inc_data_option.unwrap();

        solver.add_formulas(&result.result, f);
        while solver.sat(f) {
            current_bound += 1;
            inc_data.new_lower_bound(&mut result, current_bound);
            solver.add_formulas(&result.result, f);
        }
        assert_eq!(current_bound, 88);
    }
}

#[test]
#[ignore = "Too large for MiniSat, requires Glucose"]
fn test_very_large_modular_totalizer_amk() {
    let encoder = encoders()[2].clone();
    let f = &FormulaFactory::new();
    let mut result = EncodingResultFF::new(f);
    let num_lits = 300;
    let vars: Box<[Variable]> = (0..num_lits).map(|i| f.var(format!("v{i}"))).collect();
    let mut current_bound = num_lits - 1;
    let mut solver = SatSolver::<()>::new();
    solver.add_formula(f.cc(GE, 234, vars.clone()), f);

    let inc_data_option = encoder.encode_incremental(&mut result, &f.cc(LE, current_bound, vars).as_cc(f).unwrap());
    let mut inc_data = inc_data_option.unwrap();

    solver.add_formulas(&result.result, f);
    while solver.sat(f) {
        current_bound -= 1;
        inc_data.new_upper_bound(&mut result, current_bound);
        solver.add_formulas(&result.result, f);
    }
    assert_eq!(current_bound, 233);
}
