extern crate cxx;
use std::fmt::{Display, Formatter};

#[cxx::bridge(namespace = "wrapper")]
pub mod ffi {
    #[repr(i32)]
    #[derive(Clone, Debug, Eq, PartialEq)]
    pub enum StatusCode {
        Satisfiable = 10,
        Unsatisfiable = 20,
        Optimum = 30,
        Unknown = 40,
        Error = 50,
    }

    #[repr(i32)]
    #[derive(Clone, Debug, Eq, PartialEq)]
    pub enum OpenWboError {
        NoError,
        MaxSATError,
        OutOfMemoryError,
        InvalidRequest,
    }

    #[repr(i32)]
    #[derive(Clone, Debug, Eq, PartialEq)]
    pub enum Verbosity {
        Minimal,
        Some,
    }

    #[repr(i32)]
    #[derive(Clone, Debug, Eq, PartialEq)]
    pub enum Weight {
        None,
        Normal,
        Diversify,
    }

    #[repr(i32)]
    #[derive(Clone, Debug, Eq, PartialEq)]
    pub enum CardEncoding {
        CNetworks,
        Totalizer,
        MTotalizer,
    }

    #[repr(i32)]
    #[derive(Clone, Debug, Eq, PartialEq)]
    pub enum PB {
        Swc,
        Gte,
        Adder,
    }

    #[repr(i32)]
    #[derive(Clone, Debug, Eq, PartialEq)]
    pub enum Merge {
        Sequential,
        SequentialSorted,
        Binary,
    }

    #[repr(i32)]
    #[derive(Clone, Debug, Eq, PartialEq)]
    pub enum GraphType {
        Vig,
        CVig,
        Res,
    }

    extern "C++" {
        include!("open_wbo_ffi/open_wbo_wrapper/include/library.h");

        //Opaque Types
        pub type MaxSAT;
        pub type MaxSATFormula;
        pub type Clause;

        //Enums
        pub type Verbosity;
        pub type Weight;
        pub type StatusCode;
        pub type CardEncoding;
        pub type PB;
        pub type Merge;
        pub type GraphType;
        pub type OpenWboError;

        /// Creates a _OpenWBO_ MaxSAT instance with the LinearSU algorithm and the given configuration.
        ///
        /// This function is generated using `cxx` and the returned value is a pointer/opaque type referencing
        /// the a internal _OpenWBO_ type.
        ///
        /// # Safety
        ///
        /// We flag all FFI-functions as unsafe. If this function fails, the return value is null.
        pub unsafe fn linear_su(verbosity: Verbosity, bmo: bool, enc: CardEncoding, pb: PB) -> *mut MaxSAT;

        /// Creates a _OpenWBO_ MaxSAT instance with the WBO algorithm and the given configuration.
        ///
        /// This function is generated using `cxx` and the returned value is a pointer/opaque type referencing
        /// the a internal _OpenWBO_ type.
        ///
        /// # Safety
        ///
        /// We flag all FFI-functions as unsafe. If this function fails, the return value is null.
        pub unsafe fn wbo(verbosity: Verbosity, weight: Weight, symmetry: bool, limit: i32) -> *mut MaxSAT;

        /// Creates a _OpenWBO_ MaxSAT instance with the OLL algorithm and the given configuration.
        ///
        /// This function is generated using `cxx` and the returned value is a pointer/opaque type referencing
        /// the a internal _OpenWBO_ type.
        ///
        /// # Safety
        ///
        /// We flag all FFI-functions as unsafe. If this function fails, the return value is null.
        pub unsafe fn oll(verbosity: Verbosity, enc: CardEncoding) -> *mut MaxSAT;

        /// Creates a _OpenWBO_ MaxSAT instance with the PART-MSU3 algorithm and the given configuration.
        ///
        /// This function is generated using `cxx` and the returned value is a pointer/opaque type referencing
        /// the a internal _OpenWBO_ type.
        ///
        /// # Safety
        ///
        /// We flag all FFI-functions as unsafe. If this function fails, the return value is null.
        pub unsafe fn part_msu_3(verbosity: Verbosity, merge: Merge, graph: GraphType, enc: CardEncoding) -> *mut MaxSAT;

        /// Creates a _OpenWBO_ MaxSAT instance with the MSU3 algorithm and the given configuration.
        ///
        /// This function is generated using `cxx` and the returned value is a pointer/opaque type referencing
        /// the a internal _OpenWBO_ type.
        ///
        /// # Safety
        ///
        /// We flag all FFI-functions as unsafe. If this function fails, the return value is null.
        pub unsafe fn msu_3(verbosity: Verbosity) -> *mut MaxSAT;

        /// Creates a new _OpenWBO_ formula for MaxSAT problems.
        ///
        /// This function is generated using `cxx` and the returned value is a pointer/opaque type referencing
        /// the a internal _OpenWBO_ type.
        ///
        /// # Safety
        ///
        /// We flag all FFI-functions as unsafe. If this function fails, the return value is null.
        pub unsafe fn new_formula() -> *mut MaxSATFormula;

        /// Creates a new _OpenWBO_ clause. Which can be added to a _OpenWBO_ formula.
        ///
        /// This function is generated using `cxx` and the returned value is a pointer/opaque type referencing
        /// the a internal _OpenWBO_ type.
        ///
        /// # Safety
        ///
        /// We flag all FFI-functions as unsafe. If this function fails, the return value is null.
        pub unsafe fn new_clause() -> *mut Clause;

        /// Adds a literal to a clause and to the formula, the clause will be added to.
        /// The variable name is the absolute value of a integer. If the value is negative, the literal is seen as negated.
        /// `0` is a invalid input.
        ///
        /// This function is generated using `cxx`.
        ///
        /// # Safety
        ///
        /// We flag all FFI-functions as unsafe. This function can fail, you need to use `get_error()` to check for that.
        /// It fails if `var == 0`.  
        pub unsafe fn add_literal(formula: *mut MaxSATFormula, clause: *mut Clause, var: i32);

        /// Adds a _OpenWBO_ clause as hard clause to the _OpenWBO_ formula.
        ///
        /// This function is generated using `cxx`.
        ///
        /// # Safety
        ///
        /// We flag all FFI-functions as unsafe. This function should not fail.
        pub unsafe fn add_hard_clause(formula: *mut MaxSATFormula, clause: *mut Clause);

        /// Adds a _OpenWBO_ clause as soft clause to the _OpenWBO_ formula. The weight needs to be `>= 1`.
        ///
        /// This function is generated using `cxx`.
        ///
        /// # Safety
        ///
        /// We flag all FFI-functions as unsafe. This function fails, if the passed weight is a invalid value.
        /// You need to use `get_error()` to check for that.
        pub unsafe fn add_soft_clause(formula: *mut MaxSATFormula, weight: u64, clause: *mut Clause);

        /// Adds a _OpenWBO_ formula to a _OpenWBO_ MaxSAT algorithm.
        /// After adding the formula to the algorithm, it should no longer be extended/edited.
        ///
        /// This function is generated using `cxx`.
        ///
        /// # Safety
        ///
        /// We flag all FFI-functions as unsafe. This function should not fail.
        pub unsafe fn load_formula(algorithm: *mut MaxSAT, formula: *mut MaxSATFormula);

        /// Performs the MaxSAT search. The passed algorithm needs to have a loaded formula.
        /// The formula must meet the restrictions of the algorithm and the configuration.
        ///
        /// This function is generated using `cxx`.
        ///
        /// # Safety
        ///
        /// We flag all FFI-functions as unsafe. This function can fail, if the formula and
        /// configuration are incompatible, an unexpected error happens, or the programs runs out of memory.
        /// You need to use `get_error()` to check for that.
        pub unsafe fn search(algorithm: *mut MaxSAT) -> StatusCode;

        /// Get an array of boolean values, representing the result of the search.
        /// This is only possible if the search was successful (Optimum, Satisfiable).
        /// The returned array will have the length of ``get_model_size()``.
        ///
        /// This function is generated using `cxx`.
        ///
        /// # Safety
        ///
        /// We flag all FFI-functions as unsafe. This function can fail, if the search was not executed or successful.
        /// You need to use `get_error()` to check for that.
        pub unsafe fn get_model(algorithm: *mut MaxSAT) -> *mut bool;

        /// Returns the size of the model.
        ///
        /// This function is generated using `cxx`.
        ///
        /// # Safety
        ///
        /// We flag all FFI-functions as unsafe. This function should not fail.
        pub unsafe fn get_model_size(algorithm: *mut MaxSAT) -> u32;

        /// Frees the memory of the passed algorithm and its inherit formula (if there is one).
        ///
        /// This function is generated using `cxx`.
        ///
        /// # Safety
        ///
        /// We flag all FFI-functions as unsafe. This function should not fail.
        pub unsafe fn drop_algorithm(algorithm: *mut MaxSAT);

        /// Frees the memory of the model.
        ///
        /// This function is generated using `cxx`.
        ///
        /// # Safety
        ///
        /// We flag all FFI-functions as unsafe. This function should not fail.
        pub unsafe fn drop_model(model: *mut bool);

        /// Frees the memory of the formula.
        ///
        /// This function is generated using `cxx`.
        ///
        /// # Safety
        ///
        /// We flag all FFI-functions as unsafe.
        /// Calling this function on a formula added to an _OpenWBO_ MaxSAT algorithm is unsafe, and will lead to memory corruption.
        pub unsafe fn drop_formula(formula: *mut MaxSATFormula);

        /// Frees the memory of the clause.
        ///
        /// This function is generated using `cxx`.
        ///
        /// # Safety
        ///
        /// We flag all FFI-functions as unsafe.
        /// Calling this function on a clause added to a formula is unsafe, and will lead to memory corruption.
        pub unsafe fn drop_clause(formula: *mut Clause);

        /// This function is generated using `cxx`.
        ///
        /// # Safety
        ///
        /// We flag all FFI-functions as unsafe. This function should not fail.
        pub unsafe fn nb_cores(algorithm: *mut MaxSAT) -> i32;

        /// This function is generated using `cxx`.
        ///
        /// # Safety
        ///
        /// We flag all FFI-functions as unsafe. This function should not fail.
        pub unsafe fn nb_symmetry_clauses(algorithm: *mut MaxSAT) -> i32;

        /// This function is generated using `cxx`.
        ///
        /// # Safety
        ///
        /// We flag all FFI-functions as unsafe. This function should not fail.
        pub unsafe fn nb_satisfiable(algorithm: *mut MaxSAT) -> i32;

        /// This function is generated using `cxx`.
        ///
        /// # Safety
        ///
        /// We flag all FFI-functions as unsafe. This function should not fail.
        pub unsafe fn sum_size_cores(algorithm: *mut MaxSAT) -> u64;

        /// This function is generated using `cxx`.
        ///
        /// # Safety
        ///
        /// We flag all FFI-functions as unsafe. This function should not fail.
        pub unsafe fn ub_cost(algorithm: *mut MaxSAT) -> u64;

        /// Returns the last error detected in the _OpenWBO_ library.
        ///
        /// This function is generated using `cxx`.
        ///
        /// # Safety
        ///
        /// We flag all FFI-functions as unsafe. This function should not fail.
        pub unsafe fn get_error() -> OpenWboError;
    }
}

impl Display for ffi::OpenWboError {
    //noinspection RsUnreachablePatterns
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let msg = match *self {
            Self::NoError => "NoError",
            Self::MaxSATError => "MaxSATError",
            Self::OutOfMemoryError => "OutOfMemoryError",
            Self::InvalidRequest => "InvalidRequest",
            _ => unreachable!(),
        };
        f.write_str(msg)
    }
}
