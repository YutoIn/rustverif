//! rustc_driver を使ってコンパイラを操作するモジュール

use crate::chc::{chc_to_smt, ChcGen, ChcRule};
use crate::hir_reducer::reduce_thir;
use crate::rthir::RThir;
use rustc_data_structures::fx::FxHashMap;
use rustc_driver::{run_compiler, Callbacks, Compilation};
use rustc_hir::def_id::LocalDefId;
use rustc_interface::interface::Compiler;
use rustc_middle::ty::TyCtxt;
use std::path::PathBuf;

/// プログラム内の全関数のRTHIRをマップとして取得する
fn get_fn_map<'tcx>(tcx: TyCtxt<'tcx>) -> FxHashMap<LocalDefId, RThir<'tcx>> {
    let mut fn_map = FxHashMap::default();
    let mir_keys = tcx.mir_keys(());
    for def_id in mir_keys {
        if !def_id.to_def_id().is_local() {
            continue;
        }
        if let Ok((thir, _)) = tcx.thir_body(*def_id) {
            let thir = thir.steal();
            let rthir = reduce_thir(tcx, def_id.to_def_id(), thir);
            fn_map.insert(*def_id, rthir);
        }
    }
    fn_map
}

/// コンパイラのコールバックを実装する構造体
struct MyCallbacks {}

impl Callbacks for MyCallbacks {
    /// 型解析後に呼び出されるフック
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        println!("--- Starting Analysis ---");
        // 全ての関数をRTHIRへ変換
        let fn_map = get_fn_map(tcx);
        println!("\n--- Generating Constrained Horn Clauses (CHC) ---");
        // 各関数ごとにCHCを生成し、すべてのルールを集める
        let mut all_rules: Vec<ChcRule<'tcx>> = Vec::new();
        for (_def_id, rthir) in fn_map.iter() {
            let mut chc_gen = ChcGen::new(tcx);
            match chc_gen.process_fun(rthir) {
                Ok(()) => {
                    all_rules.extend(chc_gen.rules.into_iter());
                }
                Err(e) => {
                    eprintln!("Error generating CHC for {:?}: {:?}", rthir.def_id, e);
                }
            }
        }
        println!("\n--- Generated SMT-LIB2 for CHC ---");
        let smt_string = chc_to_smt(&all_rules);
        println!("{}", smt_string);
        Compilation::Stop
    }
}

/// rustcのsysrootパスを取得する
fn find_sysroot() -> String {
    let output = std::process::Command::new("rustc")
        .arg("--print")
        .arg("sysroot")
        .output()
        .expect("Failed to run `rustc --print sysroot`");
    String::from_utf8(output.stdout).unwrap().trim().to_string()
}

/// 検証プロセスを実行するメイン関数
pub fn run_verif() {
    // 解析対象のダミーファイルを作成
    let input_file = PathBuf::from("input.rs");
    let input_code = r#"
// Dummy functions to make the compiler happy
fn seven(n: i64) -> i64 
// todo
// require: n <= i64::MAX - 3
// ensure: n == 7
{
    if n <= 4 {
        n + 3
    } else {
        seven(seven(n - 4))
    }
}
fn main() {
    let _r = seven(42) - 7;
}
"#;
    std::fs::write(&input_file, input_code).expect("Failed to write to input.rs");
    // コンパイラに渡す引数を設定
    let args: Vec<String> = vec![
        "thir-extractor".to_string(),
        input_file.to_str().unwrap().to_string(),
        "-Zno-steal-thir".to_string(),
        "--sysroot".to_string(),
        find_sysroot(),
    ];
    println!("Running compiler with args: {:?}", &args[1..]);
    println!("============================================");
    // コンパイラを実行
    let result = std::panic::catch_unwind(|| {
        run_compiler(&args, &mut MyCallbacks {});
    });
    if result.is_err() {
        eprintln!("Compiler run panicked! This can happen when using unstable nightly rustc APIs.");
    }
    // ダミーファイルを削除
    let _ = std::fs::remove_file(input_file);
}
