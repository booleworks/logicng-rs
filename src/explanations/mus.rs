use crate::{
    errors::LngResult,
    explanations::{ExplanationError, UnsatCore},
    formulas::{EncodedFormula, FormulaFactory, Literal},
    handlers::{CancelableResult, ComputationHandler, LngEvent, NopHandler},
    propositions::Proposition,
    solver::lng_core_solver::{SatSolver, SatSolverConfig, SolverState},
};

/// The algorithm for the MUS computation
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub enum MusAlgorithm {
    /// A naive deletion-based MUS algorithm
    Deletion,
    /// A deletion-based MUS algorithm using selection variables and SAT assumptions
    DeletionSelection,
    /// A core-guided MUS algorithm followed by selector-based deletion
    CoreGuided,
    /// A naive plain insertion-based MUS algorithm
    PlainInsertion,
}

/// Computes a minimal unsatisfiable subset (MUS) of the given formulas with the selected
/// algorithm.
///
/// # Example
///
/// ```
/// use logicng::explanations::{compute_mus_for_formulas, MusAlgorithm};
/// use logicng::formulas::FormulaFactory;
///
/// let f = FormulaFactory::new();
/// let formulas = vec![
///     f.variable("a"),
///     f.variable("b"),
///     f.or([f.literal("a", false), f.literal("b", false)]),
/// ];
///
/// let mus = compute_mus_for_formulas(MusAlgorithm::Deletion, &formulas, &f)?;
/// assert!(mus.is_mus);
/// assert_eq!(mus.propositions.len(), 3);
/// # Ok::<(), logicng::errors::LngError>(())
/// ```
///
/// # Errors
///
/// Returns an error if the formula list is empty, the formulas are satisfiable, or the SAT
/// solver encounters an error.
pub fn compute_mus_for_formulas(
    algo: MusAlgorithm,
    formulas: &[EncodedFormula],
    f: &FormulaFactory,
) -> LngResult<UnsatCore<String>> {
    let propositions: Vec<Proposition<String>> = formulas
        .iter()
        .map(|form| Proposition::standard_proposition(*form, ""))
        .collect();
    compute_mus(algo, &propositions, f)
}

///  Computes a MUS for the given formulas with the given MUS algorithm and
///  a handler to abort the computation.
///
/// # Errors
///
/// Returns an error if the formula list is empty, the formulas are satisfiable, or the SAT
/// solver encounters an error.
pub fn compute_mus_for_formulas_with_handler(
    algo: MusAlgorithm,
    formulas: &[EncodedFormula],
    f: &FormulaFactory,
    handler: &mut dyn ComputationHandler,
) -> LngResult<CancelableResult<UnsatCore<String>>> {
    let propositions: Vec<Proposition<String>> = formulas
        .iter()
        .map(|form| Proposition::standard_proposition(*form, ""))
        .collect();
    compute_mus_with_handler(algo, &propositions, f, handler)
}

/// Computes a minimal unsatisfiable subset (MUS) of the given propositions with the selected
/// algorithm.
///
/// Proposition backpacks are retained in the returned core.
///
/// # Example
///
/// ```
/// use logicng::explanations::{compute_mus, MusAlgorithm};
/// use logicng::formulas::FormulaFactory;
/// use logicng::propositions::Proposition;
///
/// let f = FormulaFactory::new();
/// let propositions = vec![
///     Proposition::with_backpack(f.variable("a"), "positive"),
///     Proposition::with_backpack(f.literal("a", false), "negative"),
/// ];
///
/// let mus = compute_mus(MusAlgorithm::PlainInsertion, &propositions, &f)?;
/// assert!(mus.is_mus);
/// assert_eq!(mus.propositions.len(), 2);
/// assert!(mus.propositions.iter().all(|p| p.backpack.is_some()));
/// # Ok::<(), logicng::errors::LngError>(())
/// ```
///
/// # Errors
///
/// Returns an error if the proposition list is empty, its formulas are satisfiable, or the SAT
/// solver encounters an error.
pub fn compute_mus<B: PartialEq>(
    algo: MusAlgorithm,
    propositions: &[Proposition<B>],
    f: &FormulaFactory,
) -> LngResult<UnsatCore<B>> {
    let mus = compute_mus_with_handler(algo, propositions, f, &mut NopHandler::new())?;
    Ok(mus.result().expect("nop handler can never abort"))
}

///  Computes a MUS for the given propositions with the given MUS algorithm
///  and a handler to abort the computation.
///
/// # Errors
///
/// Returns an error if the proposition list is empty, its formulas are satisfiable, or the SAT
/// solver encounters an error.
pub fn compute_mus_with_handler<B: PartialEq>(
    algo: MusAlgorithm,
    propositions: &[Proposition<B>],
    f: &FormulaFactory,
    handler: &mut dyn ComputationHandler,
) -> LngResult<CancelableResult<UnsatCore<B>>> {
    if propositions.is_empty() {
        return Err(ExplanationError::EmptyPropositions.into());
    }
    match algo {
        MusAlgorithm::Deletion => deletion_based_mus(propositions, f, handler),
        MusAlgorithm::DeletionSelection => {
            deletion_based_mus_with_selectors(propositions, f, handler)
        }
        MusAlgorithm::CoreGuided => core_guided_mus(propositions, f, handler),
        MusAlgorithm::PlainInsertion => insertion_based_mus(propositions, f, handler),
    }
}

fn deletion_based_mus_with_selectors<B>(
    propositions: &[Proposition<B>],
    f: &FormulaFactory,
    handler: &mut dyn ComputationHandler,
) -> LngResult<CancelableResult<UnsatCore<B>>> {
    if !handler.should_resume(LngEvent::MusComputationStarted) {
        return Ok(CancelableResult::Canceled(LngEvent::MusComputationStarted));
    }
    deletion_based_mus_with_selectors_internal(propositions, f, handler)
}

fn deletion_based_mus_with_selectors_internal<B>(
    propositions: &[Proposition<B>],
    f: &FormulaFactory,
    handler: &mut dyn ComputationHandler,
) -> LngResult<CancelableResult<UnsatCore<B>>> {
    let mut solver: SatSolver<B> = SatSolver::new_with_backpack();
    let mut selectors: Vec<Literal> = Vec::with_capacity(propositions.len());
    for proposition in propositions {
        let selector = f.new_auxiliary_variable("MUS_SELECTOR").pos_lit();
        solver.add(f.implication(selector.into(), proposition.formula), f)?;
        selectors.push(selector);
    }

    match solver
        .sat_call()
        .handler(handler)
        .add_formulas(selectors.iter().copied())
        .sat(f)?
    {
        CancelableResult::Ok(false) => {}
        CancelableResult::Ok(true) => {
            return Err(ExplanationError::SatisfiableFormula.into());
        }
        CancelableResult::Canceled(e) | CancelableResult::Partial(_, e) => {
            return Ok(CancelableResult::Canceled(e));
        }
    }

    let mut active_selectors = selectors.clone();
    let mut required = vec![false; propositions.len()];
    for i in (0..selectors.len()).rev() {
        active_selectors.remove(i);
        match solver
            .sat_call()
            .handler(handler)
            .add_formulas(active_selectors.iter().copied())
            .sat(f)?
        {
            CancelableResult::Ok(true) => {
                active_selectors.insert(i, selectors[i]);
                required[i] = true;
            }
            CancelableResult::Ok(false) => {}
            CancelableResult::Canceled(e) | CancelableResult::Partial(_, e) => {
                return Ok(CancelableResult::Canceled(e));
            }
        }
    }

    let mus = propositions
        .iter()
        .zip(required)
        .filter(|(_, required)| *required)
        .map(|(proposition, _)| proposition.clone())
        .collect();
    Ok(CancelableResult::Ok(UnsatCore::new(mus, true)))
}

fn core_guided_mus<B: PartialEq>(
    propositions: &[Proposition<B>],
    f: &FormulaFactory,
    handler: &mut dyn ComputationHandler,
) -> LngResult<CancelableResult<UnsatCore<B>>> {
    if !handler.should_resume(LngEvent::MusComputationStarted) {
        return Ok(CancelableResult::Canceled(LngEvent::MusComputationStarted));
    }

    let config = SatSolverConfig::default().proof_generation(true);
    let mut solver: SatSolver<B> = SatSolver::from_config_with_backpack(config);
    solver.add_propositions(propositions.iter().cloned(), f)?;

    let core = {
        let mut call = solver.sat_call().handler(handler).solve(f)?;
        match call.get_sat_result()? {
            CancelableResult::Ok(true) => {
                return Err(ExplanationError::SatisfiableFormula.into());
            }
            CancelableResult::Ok(false) => call.unsat_core(f)?.expect("unsatisfiable SAT call"),
            CancelableResult::Canceled(e) | CancelableResult::Partial(_, e) => {
                return Ok(CancelableResult::Canceled(e));
            }
        }
    };

    deletion_based_mus_with_selectors_internal(&core.propositions, f, handler)
}

fn deletion_based_mus<B>(
    propositions: &[Proposition<B>],
    f: &FormulaFactory,
    handler: &mut dyn ComputationHandler,
) -> LngResult<CancelableResult<UnsatCore<B>>> {
    if !handler.should_resume(LngEvent::MusComputationStarted) {
        return Ok(CancelableResult::Canceled(LngEvent::MusComputationStarted));
    }
    let mut mus: Vec<Proposition<B>> = Vec::with_capacity(propositions.len());
    let mut solver_states: Vec<SolverState> = Vec::with_capacity(propositions.len());
    let mut solver: SatSolver<B> = SatSolver::new_with_backpack();
    for prop in propositions {
        solver_states.push(solver.save_state().expect("supports save state"));
        solver.add_proposition(prop.clone(), f)?;
    }
    match solver.sat_call().handler(handler).sat(f)? {
        CancelableResult::Ok(sat) => {
            if sat {
                return Err(ExplanationError::SatisfiableFormula.into());
            }
        }
        CancelableResult::Canceled(e) | CancelableResult::Partial(_, e) => {
            return Ok(CancelableResult::Canceled(e));
        }
    };
    for i in (0..solver_states.len()).rev() {
        solver.load_state(&solver_states[i])?;
        solver.add_propositions(mus.iter().cloned(), f)?;
        match solver.sat_call().handler(handler).sat(f)? {
            CancelableResult::Ok(sat) => {
                if sat {
                    mus.push(propositions[i].clone());
                }
            }
            CancelableResult::Canceled(e) | CancelableResult::Partial(_, e) => {
                return Ok(CancelableResult::Canceled(e));
            }
        };
    }
    Ok(CancelableResult::Ok(UnsatCore::new(mus, true)))
}

fn insertion_based_mus<B>(
    propositions: &[Proposition<B>],
    f: &FormulaFactory,
    handler: &mut dyn ComputationHandler,
) -> LngResult<CancelableResult<UnsatCore<B>>> {
    if !handler.should_resume(LngEvent::MusComputationStarted) {
        return Ok(CancelableResult::Canceled(LngEvent::MusComputationStarted));
    }
    let mut current_formula = propositions.to_vec();
    let mut mus = Vec::with_capacity(propositions.len());
    while !current_formula.is_empty() {
        let mut current_subset = Vec::with_capacity(current_formula.len());
        let mut solver: SatSolver<B> = SatSolver::new_with_backpack();
        solver.add_propositions(mus.iter().cloned(), f)?;
        let mut count = current_formula.len();
        loop {
            match solver.sat_call().handler(handler).sat(f)? {
                CancelableResult::Ok(false) => break,
                CancelableResult::Ok(true) => {
                    if count == 0 {
                        return Err(ExplanationError::SatisfiableFormula.into());
                    }
                    count -= 1;
                    let remove_proposition = current_formula[count].clone();
                    current_subset.push(remove_proposition.clone());
                    solver.add_proposition(remove_proposition, f)?;
                }
                CancelableResult::Canceled(e) | CancelableResult::Partial(_, e) => {
                    return Ok(CancelableResult::Canceled(e));
                }
            }
        }
        current_formula = current_subset;
        if let Some(transition_proposition) = current_formula.pop() {
            mus.push(transition_proposition);
        }
    }
    Ok(CancelableResult::Ok(UnsatCore::new(mus, true)))
}

#[cfg(test)]
mod tests {
    use crate::{
        errors::LngError,
        formulas::FormulaFactory,
        handlers::{ComputationHandler, LngComputation},
        io::read_cnf,
        propositions::StandardProposition,
        solver::lng_core_solver::tests::generate_pigeon_hole,
    };

    use super::*;

    struct BoundedSatHandler {
        starts: usize,
        bound: usize,
    }

    impl BoundedSatHandler {
        const fn new(bound: usize) -> Self {
            Self { starts: 0, bound }
        }
    }

    impl ComputationHandler for BoundedSatHandler {
        fn should_resume(&mut self, event: LngEvent) -> bool {
            if matches!(event, LngEvent::ComputationStarted(LngComputation::Sat)) {
                self.starts += 1;
                self.starts <= self.bound
            } else {
                true
            }
        }
    }

    fn pigeon_hole_propositions(n: usize, f: &FormulaFactory) -> Vec<StandardProposition> {
        generate_pigeon_hole(n, f)
            .operands(f)
            .into_iter()
            .flat_map(|formula| formula.operands(f))
            .map(Proposition::new)
            .collect()
    }

    fn test_file(path: &str, f: &FormulaFactory) -> Vec<StandardProposition> {
        read_cnf(path, f)
            .expect("test DIMACS file can be read")
            .into_iter()
            .map(Proposition::new)
            .collect()
    }

    fn assert_mus(original: &[StandardProposition], mus: &UnsatCore<String>, f: &FormulaFactory) {
        assert!(mus.is_mus);
        assert!(mus.propositions.len() <= original.len());
        assert!(mus.propositions.iter().all(|p| original.contains(p)));

        let mut solver: SatSolver<String> = SatSolver::new_with_backpack();
        solver
            .add_propositions(mus.propositions.iter().cloned(), f)
            .unwrap();
        assert!(!solver.sat_call().sat(f).unwrap().result().unwrap());

        for omitted in 0..mus.propositions.len() {
            let mut solver: SatSolver<String> = SatSolver::new_with_backpack();
            solver
                .add_propositions(
                    mus.propositions
                        .iter()
                        .enumerate()
                        .filter(|(index, _)| *index != omitted)
                        .map(|(_, proposition)| proposition.clone()),
                    f,
                )
                .unwrap();
            assert!(solver.sat_call().sat(f).unwrap().result().unwrap());
        }
    }

    #[test]
    fn rejects_empty_proposition_list() {
        let f = FormulaFactory::new();
        let error = compute_mus::<String>(MusAlgorithm::Deletion, &[], &f).unwrap_err();
        assert_eq!(
            error,
            LngError::Explanation(ExplanationError::EmptyPropositions)
        );
    }

    #[test]
    fn algorithm_configuration() {
        let algorithm = MusAlgorithm::Deletion;
        assert_eq!(algorithm, MusAlgorithm::Deletion);
        assert_eq!(format!("{algorithm:?}"), "Deletion");
        assert_eq!(
            format!("{:?}", MusAlgorithm::DeletionSelection),
            "DeletionSelection"
        );
        assert_eq!(format!("{:?}", MusAlgorithm::CoreGuided), "CoreGuided");
    }

    #[test]
    fn rejects_satisfiable_formula_sets() {
        let f = FormulaFactory::new();
        let propositions: [StandardProposition; 1] = [Proposition::new(f.variable("a"))];
        for algorithm in [
            MusAlgorithm::Deletion,
            MusAlgorithm::DeletionSelection,
            MusAlgorithm::CoreGuided,
            MusAlgorithm::PlainInsertion,
        ] {
            assert_eq!(
                compute_mus(algorithm, &propositions, &f).unwrap_err(),
                LngError::Explanation(ExplanationError::SatisfiableFormula)
            );
        }
    }

    #[test]
    fn easy_examples_mus_algorithms() {
        let f = FormulaFactory::new();
        for propositions in [
            pigeon_hole_propositions(3, &f),
            pigeon_hole_propositions(4, &f),
            pigeon_hole_propositions(5, &f),
            test_file("resources/sat/3col40_5_10.shuffled.cnf", &f),
            test_file("resources/sat/x1_16.shuffled.cnf", &f),
        ] {
            for algorithm in [
                MusAlgorithm::PlainInsertion,
                MusAlgorithm::DeletionSelection,
                MusAlgorithm::CoreGuided,
            ] {
                let mus = compute_mus(algorithm, &propositions, &f).unwrap();
                assert_mus(&propositions, &mus, &f);
            }
        }
    }

    #[test]
    #[cfg_attr(not(feature = "long_running_tests"), ignore = "long running test")]
    fn deletion_based_mus() {
        let f = FormulaFactory::new();
        for propositions in [
            pigeon_hole_propositions(3, &f),
            pigeon_hole_propositions(4, &f),
            pigeon_hole_propositions(5, &f),
            pigeon_hole_propositions(6, &f),
            pigeon_hole_propositions(7, &f),
            test_file("resources/sat/3col40_5_10.shuffled.cnf", &f),
            test_file("resources/sat/x1_16.shuffled.cnf", &f),
            test_file("resources/sat/grid_10_20.shuffled.cnf", &f),
            test_file("resources/sat/ca032.shuffled.cnf", &f),
        ] {
            let mus = compute_mus(MusAlgorithm::Deletion, &propositions, &f).unwrap();
            assert_mus(&propositions, &mus, &f);
        }
    }

    #[test]
    #[cfg_attr(not(feature = "long_running_tests"), ignore = "long running test")]
    fn deletion_selection_based_mus() {
        let f = FormulaFactory::new();
        for propositions in [
            pigeon_hole_propositions(3, &f),
            pigeon_hole_propositions(4, &f),
            pigeon_hole_propositions(5, &f),
            pigeon_hole_propositions(6, &f),
            pigeon_hole_propositions(7, &f),
            test_file("resources/sat/3col40_5_10.shuffled.cnf", &f),
            test_file("resources/sat/x1_16.shuffled.cnf", &f),
            test_file("resources/sat/grid_10_20.shuffled.cnf", &f),
            test_file("resources/sat/ca032.shuffled.cnf", &f),
        ] {
            let mus = compute_mus(MusAlgorithm::DeletionSelection, &propositions, &f).unwrap();
            assert_mus(&propositions, &mus, &f);
        }
    }

    #[test]
    #[cfg_attr(not(feature = "long_running_tests"), ignore = "long running test")]
    fn core_guided_mus() {
        let f = FormulaFactory::new();
        for propositions in [
            pigeon_hole_propositions(3, &f),
            pigeon_hole_propositions(4, &f),
            pigeon_hole_propositions(5, &f),
            pigeon_hole_propositions(6, &f),
            pigeon_hole_propositions(7, &f),
            test_file("resources/sat/3col40_5_10.shuffled.cnf", &f),
            test_file("resources/sat/x1_16.shuffled.cnf", &f),
            test_file("resources/sat/grid_10_20.shuffled.cnf", &f),
            test_file("resources/sat/ca032.shuffled.cnf", &f),
        ] {
            let mus = compute_mus(MusAlgorithm::CoreGuided, &propositions, &f).unwrap();
            assert_mus(&propositions, &mus, &f);
        }
    }

    #[test]
    fn cancellation_points() {
        let f = FormulaFactory::new();
        let propositions = test_file("resources/sat/unsat/bf0432-007.cnf", &f);
        for algorithm in [
            MusAlgorithm::Deletion,
            MusAlgorithm::DeletionSelection,
            MusAlgorithm::CoreGuided,
            MusAlgorithm::PlainInsertion,
        ] {
            for bound in 0..10 {
                let result = compute_mus_with_handler(
                    algorithm,
                    &propositions,
                    &f,
                    &mut BoundedSatHandler::new(bound),
                )
                .unwrap();
                assert!(result.is_canceled());
            }
        }
    }

    #[test]
    fn plain_insertion_cancellation_points_on_large_formula() {
        let f = FormulaFactory::new();
        let propositions = test_file("resources/sat/too_large_gr_rcs_w5.shuffled.cnf", &f);
        for bound in 0..20 {
            let result = compute_mus_with_handler(
                MusAlgorithm::PlainInsertion,
                &propositions,
                &f,
                &mut BoundedSatHandler::new(bound),
            )
            .unwrap();
            assert!(result.is_canceled());
        }
    }
}
