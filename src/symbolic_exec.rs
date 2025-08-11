//! RTHIRのシンボリック実行を行うモジュール

use crate::env::Env;
use crate::errors::VerifError;
use crate::lir::{Lir, LirKind};
use crate::rthir::{RExpr, RExprKind, RPatKind, RThir};
use rustc_ast::ast as Ast;
use std::rc::Rc;

/// RTHIRの式を評価し、LIRに変換する
fn eval_rvalue<'tcx>(
    _env: &mut Env<'tcx>,
    r_expr: Rc<RExpr<'tcx>>,
) -> Result<Lir<'tcx>, VerifError> {
    let lir_kind = match &r_expr.kind {
        // リテラルをSMT形式の文字列に変換
        RExprKind::Literal { lit, neg } => {
            let val_str = match lit.node {
                Ast::LitKind::Int(val, _) => val.to_string(),
                // TODO: 他のリテラルの種類も実装
                _ => return Err(VerifError::Unimplemented),
            };

            let expr_str = if *neg {
                format!("(- {})", val_str)
            } else {
                val_str
            };
            LirKind::VarExpr {
                var_expr: expr_str,
                ty: r_expr.ty.kind().clone(),
            }
        }
        // TODO: 他の式の種類も実装
        _ => return Err(VerifError::Unimplemented),
    };
    Ok(Lir::new(lir_kind, r_expr))
}

/// `let`文をシンボリック実行する
fn symbolic_exec_let_stmt<'tcx>(
    env: &mut Env<'tcx>,
    pattern: &RExpr<'tcx>,
    initializer: &Option<Rc<RExpr<'tcx>>>,
) -> Result<(), VerifError> {
    // 右辺の初期化式を評価
    let initializer_lir = if let Some(init_expr) = initializer {
        eval_rvalue(env, init_expr.clone())?
    } else {
        // TODO: 初期化なしの場合の処理
        return Err(VerifError::Unimplemented);
    };

    // パターンから変数IDを取得し、Envに登録
    if let RExprKind::Pat { kind } = &pattern.kind {
        match kind {
            RPatKind::Binding { var, ty, .. } => {
                // SMTソルバーで使う変数名を作成 (例: "LocalVarId(HirId(DefId(0:3).5))")
                let smt_var_name = format!("{:?}", var);
                // SMT変数を宣言リストに追加
                env.smt_vars.push((smt_var_name, ty.kind().clone()));

                // 変数マップにLIRを登録
                env.var_map.insert(*var, initializer_lir);
                return Ok(());
            }
        }
    }

    Err(VerifError::UnexpectedRThir)
}

/// 文をシンボリック実行する
fn symbolic_exec_stmt<'tcx>(
    env: &mut Env<'tcx>,
    stmt: &RExpr<'tcx>,
) -> Result<(), VerifError> {
    match &stmt.kind {
        RExprKind::LetStmt { pattern, initializer } => {
            symbolic_exec_let_stmt(env, pattern, initializer)
        }
        _ => Err(VerifError::Unimplemented),
    }
}

/// 関数のボディをシンボリック実行する
pub fn symbolic_exec_body<'tcx>(rthir: &RThir<'tcx>) -> Result<Env<'tcx>, VerifError> {
    let mut env = Env::new();

    // main関数のbodyはBlockであるはず
    if let RExprKind::Block { stmts, .. } = &rthir.body.kind {
        // 各文を順番に実行
        for stmt in stmts {
            symbolic_exec_stmt(&mut env, stmt)?;
        }
    } else {
        return Err(VerifError::UnexpectedRThir);
    }
    Ok(env)
}
