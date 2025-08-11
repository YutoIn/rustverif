// std crates
use std::rc::Rc;

// rustc crates
use rustc_hir::def_id::DefId;
use rustc_middle::thir::*;
use rustc_middle::ty::TyCtxt;

// Local modules
use crate::rthir::*;

/// THIRからRTHIRへの変換器
struct Reducer<'a, 'tcx> {
    thir: &'a Thir<'tcx>,
    tcx: TyCtxt<'tcx>,
}

impl<'a, 'tcx> Reducer<'a, 'tcx> {
    fn new(tcx: TyCtxt<'tcx>, thir: &'a Thir<'tcx>) -> Self {
        Self { thir, tcx }
    }

    fn reduce_expr(&self, expr_id: ExprId) -> Rc<RExpr<'tcx>> {
        let expr = &self.thir[expr_id];
        let (kind, span) = {
            let mut current_expr = expr;
            while let ExprKind::Scope { value, .. } = &current_expr.kind {
                current_expr = &self.thir[*value];
            }
            (&current_expr.kind, current_expr.span)
        };

        let r_expr_kind = match kind {
            ExprKind::Block { block } => {
                let block = &self.thir[*block];
                let stmts = block.stmts.iter().map(|s| self.reduce_stmt(*s)).collect();
                let expr = block.expr.map(|e| self.reduce_expr(e));
                RExprKind::Block { stmts, expr }
            }
            ExprKind::VarRef { id } => RExprKind::VarRef { id: *id },
            ExprKind::Literal { lit, neg, .. } => RExprKind::Literal { lit: *lit, neg: *neg },
            other => unimplemented!("Unsupported RExprKind: {:?}", other),
        };

        Rc::new(RExpr {
            kind: r_expr_kind,
            span,
            ty: expr.ty,
        })
    }

    fn reduce_stmt(&self, stmt_id: StmtId) -> Rc<RExpr<'tcx>> {
        let stmt = &self.thir[stmt_id];
        let (kind, span) = match &stmt.kind {
            StmtKind::Let { pattern, initializer, span, .. } => {
                let pattern = self.reduce_pat(pattern);
                let initializer = initializer.map(|i| self.reduce_expr(i));
                (RExprKind::LetStmt { pattern, initializer }, *span)
            }
            StmtKind::Expr { expr, .. } => return self.reduce_expr(*expr),
        };

        Rc::new(RExpr {
            kind,
            span,
            ty: self.tcx.types.unit, // Stmtの型はunit
        })
    }

    fn reduce_pat(&self, pat: &Pat<'tcx>) -> Rc<RExpr<'tcx>> {
        let kind = match &pat.kind {
            PatKind::Binding { name, mode, var, ty, subpattern, is_primary } => {
                let subpattern = subpattern.as_ref().map(|p| self.reduce_pat(p));
                RPatKind::Binding {
                    name: *name,
                    mode: *mode,
                    var: *var,
                    ty: *ty,
                    subpattern,
                    is_primary: *is_primary,
                }
            }
            other => unimplemented!("Unsupported RPatKind: {:?}", other),
        };

        Rc::new(RExpr {
            kind: RExprKind::Pat { kind },
            span: pat.span,
            ty: pat.ty,
        })
    }
}

/// THIRをRTHIRに変換
pub fn reduce_thir<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId, thir: Thir<'tcx>) -> RThir<'tcx> {
    let binding = thir.clone();
    let reducer = Reducer::new(tcx, &binding);
    let body = reducer.reduce_expr(thir.exprs.last_index().unwrap());

    let params = thir
        .params
        .into_iter()
        .map(|p| RParam { pat: p.pat.map(|pat| reducer.reduce_pat(&pat)) })
        .collect();

    RThir {
        def_id,
        params,
        body,
        tcx,
    }
}
