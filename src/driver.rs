// std crates
use std::path::PathBuf;

// rustc crates
use rustc_driver::{run_compiler, Callbacks, Compilation};
use rustc_interface::interface::Compiler;
use rustc_middle::ty::TyCtxt;

// Local modules
use crate::hir_reducer::reduce_thir;

struct MyCallbacks {}

impl Callbacks for MyCallbacks {
    /// 型解析後に呼び出されるフック
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        println!("--- Extracting and Printing RTHIR for all functions ---");

        // コンパイル対象内のすべてのMIRキー（≒関数）を取得
        let mir_keys = tcx.mir_keys(());

        for def_id in mir_keys {
            // ローカルクレート内の関数のみを対象とする
            if !def_id.to_def_id().is_local() {
                continue;
            }

            // THIRを取得
            if let Ok((thir, _entry_expr)) = tcx.thir_body(*def_id) {
                println!(); // Add a newline for better separation
                // `steal`で所有権を取得
                let thir = thir.steal();
                // THIRをRTHIRに変換
                let rthir = reduce_thir(tcx, def_id.to_def_id(), thir);
                // プリティプリント
                println!("{:#?}", rthir);
            } else {
                println!("\n// Could not get THIR for `{}`", tcx.def_path_str(def_id.to_def_id()));
            }
        }

        println!("\n\n--- RTHIR extraction complete ---");
        // これ以上コンパイルを続けない
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
}
"#;
    std::fs::write(&input_file, input_code).expect("Failed to write to input.rs");

    // コンパイラに渡す引数を設定
    let args: Vec<String> = vec![
        "thir-extractor".to_string(),
        input_file.to_str().unwrap().to_string(),
        // THIRの所有権を`steal`するために必要
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
