//! Env構造体をSMT-LIB 2フォーマットに変換するモジュール

use crate::env::Env;
use rustc_middle::ty::TyKind;

/// rustcの型(TyKind)をSMTのソート(型)を表す文字列に変換する
fn ty_to_smt_sort(ty: &TyKind) -> &'static str {
    match ty {
        TyKind::Int(_) | TyKind::Uint(_) => "Int",
        TyKind::Bool => "Bool",
        // TODO: 他の型もサポートする
        _ => "Int", // 未対応の型は一旦Intとして扱う
    }
}

/// Env構造体をSMT-LIB 2形式の文字列に変換する
pub fn to_smt_lib(env: &Env) -> String {
    let mut smt_string = String::new();

    // --- 1. 変数宣言 (declare-const) ---
    smt_string.push_str(";; 1. Variable Declarations\n");
    for (name, ty) in &env.smt_vars {
        let sort = ty_to_smt_sort(ty);
        smt_string.push_str(&format!("(declare-const {} {})\n", name, sort));
    }
    smt_string.push('\n');

    // --- 2. パス条件と表明 (assert) ---
    // シンボリック実行中に蓄積された表明（変数束縛、assume, assert）を出力
    smt_string.push_str(";; 2. Assertions\n");
    for condition in &env.path {
        smt_string.push_str(&format!("(assert {})\n", condition));
    }
    smt_string.push('\n');

    // --- 3. SMTソルバーへのコマンド ---
    smt_string.push_str(";; 3. Solver Commands\n");
    smt_string.push_str("(check-sat)\n");
    smt_string.push_str("(get-model)\n");

    smt_string
}
