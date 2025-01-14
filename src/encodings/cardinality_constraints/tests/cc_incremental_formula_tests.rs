use crate::encodings::cardinality_constraints::cc_config::{AlkEncoder, AmkEncoder, CcConfig};
use crate::encodings::cardinality_constraints::cc_encoder::CcEncoder;
use crate::formulas::CType::{GE, GT, LE, LT};
use crate::formulas::{FormulaFactory, Variable};
use crate::solver::minisat::sat::Tristate::{False, True};
use crate::solver::minisat::MiniSat;

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
        let num_lits = 10;
        let vars: Box<[Variable]> = (0..num_lits).map(|i| f.var(format!("v{i}"))).collect();

        let inc_data = encoder.encode_incremental(&f.cc(LT, num_lits, vars.clone()).as_cc(f).unwrap(), f).1.unwrap();
        assert_eq!(inc_data.current_rhs, 9);

        let inc_data = encoder.encode_incremental(&f.cc(GT, 1, vars.clone()).as_cc(f).unwrap(), f).1.unwrap();
        assert_eq!(inc_data.current_rhs, 2);

        let (formulas, inc_data) = encoder.encode_incremental(&f.cc(LT, 1, vars.clone()).as_cc(f).unwrap(), f);
        assert!(inc_data.is_none());
        assert!(formulas.contains(&vars[0].negate().into()));

        let (_, inc_data) = encoder.encode_incremental(&f.cc(LE, num_lits + 1, vars.clone()).as_cc(f).unwrap(), f);
        assert!(inc_data.is_none());

        let (_, inc_data) = encoder.encode_incremental(&f.cc(GE, num_lits + 1, vars.clone()).as_cc(f).unwrap(), f);
        assert!(inc_data.is_none());

        let (_, inc_data) = encoder.encode_incremental(&f.cc(GE, num_lits, vars.clone()).as_cc(f).unwrap(), f);
        assert!(inc_data.is_none());

        let (_, inc_data) = encoder.encode_incremental(&f.cc(GE, 0, vars.clone()).as_cc(f).unwrap(), f);
        assert!(inc_data.is_none());

        let (_, inc_data) = encoder.encode_incremental(&f.cc(GE, 1, vars.clone()).as_cc(f).unwrap(), f);
        assert!(inc_data.is_none());
    }
}

#[test]
fn test_simple_incremental_amk() {
    for encoder in encoders() {
        let f = &FormulaFactory::new();
        let vars: Box<[Variable]> = (0..10).map(|i| f.var(format!("v{i}"))).collect();
        let mut solver = MiniSat::new();
        solver.add_all(&f.cc(GE, 4, vars.clone()).as_cc(f).unwrap().encode(f), f);
        solver.add_all(&f.cc(LE, 7, vars.clone()).as_cc(f).unwrap().encode(f), f);

        let (cc, inc_data_option) = encoder.encode_incremental(&f.cc(LE, 9, vars).as_cc(f).unwrap(), f);
        let mut inc_data = inc_data_option.unwrap();

        solver.add_all(&cc, f);
        assert_eq!(solver.sat(), True);
        solver.add_all(&inc_data.new_upper_bound(f, 8), f);
        assert_eq!(solver.sat(), True);
        solver.add_all(&inc_data.new_upper_bound(f, 7), f);
        assert_eq!(solver.sat(), True);
        solver.add_all(&inc_data.new_upper_bound(f, 6), f);
        assert_eq!(solver.sat(), True);
        solver.add_all(&inc_data.new_upper_bound(f, 5), f);
        assert_eq!(solver.sat(), True);
        solver.add_all(&inc_data.new_upper_bound(f, 4), f);
        assert_eq!(solver.sat(), True);

        let state = solver.save_state();
        solver.add_all(&inc_data.new_upper_bound(f, 3), f);
        assert_eq!(solver.sat(), False);
        solver.load_state(&state);
        assert_eq!(solver.sat(), True);
        solver.add_all(&inc_data.new_upper_bound(f, 2), f);
        assert_eq!(solver.sat(), False);
    }
}

#[test]
fn test_simple_incremental_alk() {
    for encoder in encoders() {
        let f = &FormulaFactory::new();
        let vars: Box<[Variable]> = (0..10).map(|i| f.var(format!("v{i}"))).collect();
        let mut solver = MiniSat::new();
        solver.add_all(&f.cc(GE, 4, vars.clone()).as_cc(f).unwrap().encode(f), f);
        solver.add_all(&f.cc(LE, 7, vars.clone()).as_cc(f).unwrap().encode(f), f);

        let (cc, inc_data_option) = encoder.encode_incremental(&f.cc(GE, 2, vars).as_cc(f).unwrap(), f);
        let mut inc_data = inc_data_option.unwrap();

        solver.add_all(&cc, f);
        assert_eq!(solver.sat(), True);
        solver.add_all(&inc_data.new_lower_bound(f, 3), f);
        assert_eq!(solver.sat(), True);
        solver.add_all(&inc_data.new_lower_bound(f, 4), f);
        assert_eq!(solver.sat(), True);
        solver.add_all(&inc_data.new_lower_bound(f, 5), f);
        assert_eq!(solver.sat(), True);
        solver.add_all(&inc_data.new_lower_bound(f, 6), f);
        assert_eq!(solver.sat(), True);
        solver.add_all(&inc_data.new_lower_bound(f, 7), f);
        assert_eq!(solver.sat(), True);

        if solver.underlying_solver.config.incremental {
            let state = solver.save_state();
            solver.add_all(&inc_data.new_lower_bound(f, 8), f);
            assert_eq!(solver.sat(), False);
            solver.load_state(&state);
            assert_eq!(solver.sat(), True);
            solver.add_all(&inc_data.new_lower_bound(f, 9), f);
            assert_eq!(solver.sat(), False);
        }
    }
}

#[test]
#[cfg_attr(not(feature = "long_running_tests"), ignore)]
fn test_large_upper_bound_amk() {
    for encoder in [&encoders()[0], &encoders()[2]] {
        let f = &FormulaFactory::new();
        let num_lits = 100;
        let vars: Box<[Variable]> = (0..num_lits).map(|i| f.var(format!("v{i}"))).collect();
        let mut current_bound = num_lits - 1;
        let mut solver = MiniSat::new();
        solver.add_all(&f.cc(GE, 42, vars.clone()).as_cc(f).unwrap().encode(f), f);

        let (cc, inc_data_option) = encoder.encode_incremental(&f.cc(LE, current_bound, vars).as_cc(f).unwrap(), f);
        let mut inc_data = inc_data_option.unwrap();

        solver.add_all(&cc, f);
        while solver.sat() == True {
            current_bound -= 1;
            solver.add_all(&inc_data.new_upper_bound(f, current_bound), f);
        }
        assert_eq!(current_bound, 41);
    }
}

#[test]
#[cfg_attr(not(feature = "long_running_tests"), ignore)]
fn test_large_lower_bound_alk() {
    for encoder in [&encoders()[0], &encoders()[2]] {
        let f = &FormulaFactory::new();
        let num_lits = 100;
        let vars: Box<[Variable]> = (0..num_lits).map(|i| f.var(format!("v{i}"))).collect();
        let mut current_bound = 2;
        let mut solver = MiniSat::new();
        solver.add_all(&f.cc(LE, 87, vars.clone()).as_cc(f).unwrap().encode(f), f);

        let (cc, inc_data_option) = encoder.encode_incremental(&f.cc(GE, current_bound, vars).as_cc(f).unwrap(), f);
        let mut inc_data = inc_data_option.unwrap();

        solver.add_all(&cc, f);
        while solver.sat() == True {
            current_bound += 1;
            solver.add_all(&inc_data.new_lower_bound(f, current_bound), f);
        }
        assert_eq!(current_bound, 88);
    }
}

#[test]
#[ignore = "Too large for MiniSat, requires Glucose"]
fn test_very_large_modular_totalizer_amk() {
    let encoder = encoders()[2].clone();
    let f = &FormulaFactory::new();
    let num_lits = 300;
    let vars: Box<[Variable]> = (0..num_lits).map(|i| f.var(format!("v{i}"))).collect();
    let mut current_bound = num_lits - 1;
    let mut solver = MiniSat::new();
    solver.add(f.cc(GE, 234, vars.clone()), f);

    let (cc, inc_data_option) = encoder.encode_incremental(&f.cc(LE, current_bound, vars).as_cc(f).unwrap(), f);
    let mut inc_data = inc_data_option.unwrap();

    solver.add_all(&cc, f);
    while solver.sat() == True {
        current_bound -= 1;
        solver.add_all(&inc_data.new_upper_bound(f, current_bound), f);
    }
    assert_eq!(current_bound, 233);
}
