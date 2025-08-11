#![feature(rustc_private)]

// rustc crates
extern crate rustc_ast;
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_interface;
extern crate rustc_macros;
extern crate rustc_middle;
extern crate rustc_mir_build;
extern crate rustc_query_system;
extern crate rustc_session;
extern crate rustc_span;
extern crate rustc_target;

// Local modules
mod driver;
mod hir_reducer;
mod pretty_print;
mod rthir;

fn main() {
    driver::run_verif();
}
