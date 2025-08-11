// std crates
use std::rc::Rc;

// rustc crates
use rustc_hir::def_id::DefId;
use rustc_hir::BindingMode;
use rustc_middle::thir::LocalVarId;
use rustc_middle::ty::{Ty, TyCtxt};
use rustc_span::{Span, Symbol};

/// 関数全体を表すRTHIRのルート構造体
pub struct RThir<'tcx> {
    pub def_id: DefId,
    pub params: Vec<RParam<'tcx>>,
    pub body: Rc<RExpr<'tcx>>,
    pub tcx: TyCtxt<'tcx>,
}

/// 関数の引数を表す構造体
pub struct RParam<'tcx> {
    pub pat: Option<Rc<RExpr<'tcx>>>,
}

/// RTHIRの式を表す構造体
#[derive(Clone)]
pub struct RExpr<'tcx> {
    pub kind: RExprKind<'tcx>,
    pub span: Span,
    pub ty: Ty<'tcx>,
}

/// RTHIRの式の種類を表すenum
#[derive(Clone)]
pub enum RExprKind<'tcx> {
    /// ブロック式
    Block {
        stmts: Vec<Rc<RExpr<'tcx>>>,
        expr: Option<Rc<RExpr<'tcx>>>,
    },
    /// 変数参照
    VarRef {
        id: LocalVarId,
    },
    /// リテラル
    Literal {
        lit: rustc_span::source_map::Spanned<rustc_ast::ast::LitKind>,
        neg: bool,
    },
    /// let文
    LetStmt {
        pattern: Rc<RExpr<'tcx>>,
        initializer: Option<Rc<RExpr<'tcx>>>,
    },
    /// パターン
    Pat {
        kind: RPatKind<'tcx>,
    },
}

/// パターンの種類を表すenum
#[derive(Clone)]
pub enum RPatKind<'tcx> {
    Binding {
        name: Symbol,
        mode: BindingMode,
        var: LocalVarId,
        ty: Ty<'tcx>,
        subpattern: Option<Rc<RExpr<'tcx>>>,
        is_primary: bool,
    },
}
