//! LIR (Logical Intermediate Representation) の定義

use crate::rthir::RExpr;
use rustc_middle::ty::TyKind;
use std::rc::Rc;

/// LIRの本体。現在は変数の値を表す文字列のみを持つ
#[derive(Clone, Debug)]
pub enum LirKind<'tcx> {
    VarExpr {
        var_expr: String,
        ty: TyKind<'tcx>,
    },
}

/// 値の式を論理式として扱うための構造体
#[derive(Clone)]
pub struct Lir<'tcx> {
    pub kind: LirKind<'tcx>,
    /// Span情報を取得するためにRExprを持っておく
    pub expr: Rc<RExpr<'tcx>>,
}

impl<'tcx> std::fmt::Debug for Lir<'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Lir")
            .field("kind", &self.kind)
            // RExpr全体をプリントすると循環するため、spanのみ表示
            .field("expr_span", &self.expr.span)
            .finish()
    }
}

impl<'tcx> Lir<'tcx> {
    /// 新しいLirインスタンスを作成する
    pub fn new(kind: LirKind<'tcx>, expr: Rc<RExpr<'tcx>>) -> Self {
        Self { kind, expr }
    }

    /// 値の式（SMT形式の文字列）を取得する
    pub fn get_var_expr(&self) -> String {
        match &self.kind {
            LirKind::VarExpr { var_expr, .. } => var_expr.clone(),
        }
    }

    /// 値の式（SMT形式の文字列）を設定する
    pub fn set_var_expr(&mut self, new_expr: String) {
        match &mut self.kind {
            LirKind::VarExpr { var_expr, .. } => {
                *var_expr = new_expr;
            }
        }
    }
}
