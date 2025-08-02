use rustc_driver::{run_compiler, Callbacks, Compilation};
use rustc_interface::interface::{Compiler};
use rustc_middle::ty::TyCtxt;
//use rustc_middle::thir;

struct MyCallbacks {}

impl Callbacks for MyCallbacks {
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        tcx.mir_keys(())
            .iter();

        Compilation::Stop
    }
}

pub fn run_tautrust() {
    let mut args = Vec::new();
    let mut args_iter = std::env::args();
	while let Some(arg) = args_iter.next() {
        match arg.as_str() {
            _ => args.push(arg),
        };
    }
	run_compiler(&args, &mut MyCallbacks {});
    let x = 0;
    println!("{}", x);
}