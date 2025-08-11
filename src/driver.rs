//! rustc_driver を使ってコンパイラを操作するモジュール

use crate::hir_reducer::reduce_thir;
use crate::rthir::RThir;
use crate::smt_converter::to_smt_lib;
use crate::symbolic_exec::symbolic_exec_body;
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
        println!("--- Starting Symbolic Execution ---");

        // 1. プログラム内の全関数のRTHIRをマップとして取得
        let fn_map = get_fn_map(tcx);

        // 2. main関数のDefIdを取得
        if let Some((main_def_id, _)) = tcx.entry_fn(()) {
            // DefIdをLocalDefIdに変換
            if let Some(main_local_def_id) = main_def_id.as_local() {
                // 3. マップからmain関数のRTHIRを取得
                if let Some(main_rthir) = fn_map.get(&main_local_def_id) {
                    println!("\nFound main function: {:?}", main_def_id);
                    println!("--- Analyzing main function ---");

                    // 4. main関数をエントリーポイントとしてシンボリック実行を開始
                    match symbolic_exec_body(main_rthir) {
                        Ok(final_env) => {
                            println!("\n--- Symbolic Execution Finished ---");
                            println!("Final Environment: {:#?}", final_env);

                            // 5. SMT-LIB形式に変換して出力
                            println!("\n--- Generated SMT-LIB ---");
                            let smt_lib_str = to_smt_lib(&final_env);
                            println!("{}", smt_lib_str);
                        }
                        Err(e) => {
                            eprintln!("\nError during symbolic execution: {:?}", e);
                        }
                    }
                } else {
                    eprintln!("Could not find RTHIR for main function.");
                }
            } else {
                eprintln!("Entry function is not a local function.");
            }
        } else {
            eprintln!("Could not find entry function (main).");
        }

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
fn main() {
    let x = 1;
    let y = 2;
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
