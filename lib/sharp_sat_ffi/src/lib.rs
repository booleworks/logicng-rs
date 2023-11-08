extern crate cxx;

#[cxx::bridge(namespace = "wrapper")]
pub mod ffi {
    extern "C++" {
        include!("logicng-sharp-sat-sys/sharp_sat_wrapper/include/library.h");
        pub type Solver;

        pub unsafe fn new_solver() -> *mut Solver;

        pub unsafe fn drop_solver(solver: *mut Solver);

        pub unsafe fn add_clause(solver: *mut Solver, clauses: *const i32, size: u32);

        pub unsafe fn solve(solver: *mut Solver) -> &'static CxxString;
    }
}
