//! Env構造体をSMT-LIB 2フォーマットに変換するモジュール

use crate::env::Env;
use rustc_middle::ty::TyKind;

/// rustcの型(TyKind)をSMTのソート(型)を表す文字列に変換する
fn ty_to_smt_sort(ty: &TyKind) -> &'static str {
    match ty {
        TyKind::Int(_) => "Int",
        TyKind::Bool => "Bool",
        // TODO: 他の型もサポートする
        _ => "Int", // 未対応の型は一旦Intとして扱う
    }
}

/// Env構造体をSMT-LIB 2形式の文字列に変換する
pub fn to_smt_lib<'tcx>(env: &Env<'tcx>) -> String {
    let mut smt_string = String::new();

    // --- 1. 変数宣言 (declare-const) ---
    // シンボリック実行中に見つかった変数をSMTソルバーに宣言します。
    smt_string.push_str(";; 1. Variable Declarations\n");
    for (name, ty) in &env.smt_vars {
        let sort = ty_to_smt_sort(ty);
        smt_string.push_str(&format!("(declare-const {} {})\n", name, sort));
    }
    smt_string.push('\n');

    // --- 2. 変数の値に関する表明 (assert) ---
    // 各変数がシンボリック実行によって得られた値（論理式）と等しいことを表明します。
    smt_string.push_str(";; 2. Variable Value Assertions\n");
    for (var_id, lir) in &env.var_map {
        // var_idをSMTで使える変数名に変換 (smt_varsに登録したものと同じ形式)
        let var_name = format!("{:?}", var_id);
        let value_expr = lir.get_var_expr();
        smt_string.push_str(&format!("(assert (= {} {}))\n", var_name, value_expr));
    }
    smt_string.push('\n');

    // --- 3. パス条件に関する表明 (assert) ---
    // (今後のステップで実装) if文などの分岐条件を表明します。
    if !env.path.is_empty() {
        smt_string.push_str(";; 3. Path Condition Assertions\n");
        for condition in &env.path {
            smt_string.push_str(&format!("(assert {})\n", condition));
        }
        smt_string.push('\n');
    }

    // --- 4. SMTソルバーへのコマンド ---
    smt_string.push_str(";; 4. Solver Commands\n");
    smt_string.push_str("(check-sat)\n");
    smt_string.push_str("(get-model)\n");

    smt_string
}
