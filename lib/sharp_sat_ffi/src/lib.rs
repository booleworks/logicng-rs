extern crate cxx;

#[cxx::bridge(namespace = "wrapper")]
pub mod ffi {
    extern "C++" {
        include!("logicng-sharp-sat-sys/sharp_sat_wrapper/include/library.h");
        pub type Solver;

        /// Creates a new instance of a SharpSAT solver.
        ///
        /// This function is generated using `cxx` and the returned value is a
        /// pointer/opaque type referencing the a internal _SharpSAT_ type.
        ///
        /// # Safety
        ///
        /// We flag all FFI-functions as unsafe. This function should not fail.
        pub unsafe fn new_solver() -> *mut Solver;

        /// Frees a SharpSAT solver and all its allocated resources. Make sure
        /// to only call this once for each solver instance.
        ///
        /// This function is generated using `cxx`.
        ///
        /// # Safety
        ///
        /// We flag all FFI-functions as unsafe. If this function is called
        /// multiple times on the same solver instance it may result in
        /// undefined behavior.
        pub unsafe fn drop_solver(solver: *mut Solver);

        /// Adds a new clause to the passed solver instance.
        ///
        /// This function is generated using `cxx`.
        ///
        /// # Safety
        ///
        /// We flag all FFI-functions as unsafe. To ensure correct behavior the following must hold:
        /// - `clause` is a slice/array of i32 and `size` is the size of that array.
        /// - `size` > 0
        ///
        /// The values of clauses are copied. So the array can be reused afterwards.
        pub unsafe fn add_clause(solver: *mut Solver, clauses: *const i32, size: u32);

        /// Solves the formula on the passed solver instance. Returns the result
        /// as a string representing the decimal number.
        ///
        /// This function is generated using `cxx`.
        ///
        /// # Safety
        ///
        /// We flag all FFI-functions as unsafe. This function should not fail.
        pub unsafe fn solve(solver: *mut Solver) -> &'static CxxString;
    }
}
