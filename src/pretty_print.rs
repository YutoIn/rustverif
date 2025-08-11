// RTHIRプリティプリンタ

use crate::rthir::*;
use rustc_middle::ty::TyCtxt;
use rustc_span::FileNameDisplayPreference;
use std::fmt;

/// インデント付きで文字列を出力するヘルパー関数
fn print_with_indent(f: &mut fmt::Formatter<'_>, s: &str, indent: usize) -> fmt::Result {
    writeln!(f, "{}{}", "  ".repeat(indent), s)
}

/// RThir の Debug トレイト実装
impl fmt::Debug for RThir<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let params_str = if self.params.is_empty() { "[]" } else { "[...]" };
        writeln!(f, "{:?}, params: {}", self.def_id, params_str)?;
        writeln!(f, "body:")?;
        format_expr(f, self.tcx, &self.body, 1)
    }
}

/// RExprを再帰的にフォーマットする
fn format_expr(f: &mut fmt::Formatter<'_>, tcx: TyCtxt<'_>, expr: &RExpr<'_>, indent: usize) -> fmt::Result {
    print_with_indent(f, "Expr {", indent)?;
    print_with_indent(
        f,
        &format!(
            "span: {}",
            tcx.sess
                .source_map()
                .span_to_string(expr.span, FileNameDisplayPreference::Short)
        ),
        indent + 1,
    )?;
    print_with_indent(f, "kind:", indent + 1)?;
    format_expr_kind(f, tcx, &expr.kind, indent + 2)?;
    print_with_indent(f, "}", indent)
}

/// RExprKindを再帰的にフォーマットする
fn format_expr_kind(f: &mut fmt::Formatter<'_>, tcx: TyCtxt<'_>, kind: &RExprKind<'_>, indent: usize) -> fmt::Result {
    match kind {
        RExprKind::Block { stmts, expr } => {
            print_with_indent(f, "Block {", indent)?;
            print_with_indent(f, "stmts: [", indent + 1)?;
            for stmt in stmts {
                format_expr(f, tcx, stmt, indent + 2)?;
            }
            print_with_indent(f, "]", indent + 1)?;

            print_with_indent(f, "expr: [", indent + 1)?;
            if let Some(e) = expr {
                format_expr(f, tcx, e, indent + 2)?;
            }
            print_with_indent(f, "]", indent + 1)?;

            print_with_indent(f, "}", indent)
        }
        RExprKind::LetStmt { pattern, initializer } => {
            print_with_indent(f, "LetStmt {", indent)?;
            print_with_indent(f, "pattern:", indent + 1)?;
            format_expr(f, tcx, pattern, indent + 2)?;
            print_with_indent(f, ",", indent + 1)?;
            if let Some(init) = initializer {
                print_with_indent(f, "initializer: Some(", indent + 1)?;
                format_expr(f, tcx, init, indent + 2)?;
                print_with_indent(f, ")", indent + 1)?;
            }
            print_with_indent(f, "}", indent)
        }
        RExprKind::Pat { kind } => {
            print_with_indent(f, "Pat {", indent)?;
            print_with_indent(f, "PatKind {", indent + 1)?;
            format_pat_kind(f, tcx, kind, indent + 2)?;
            print_with_indent(f, "}", indent + 1)?;
            print_with_indent(f, "}", indent)
        }
        RExprKind::Literal { lit, neg } => {
            print_with_indent(f, "Literal(", indent)?;
            print_with_indent(f, &format!("lit: {:?},", lit), indent + 1)?;
            print_with_indent(f, &format!("neg: {:?}", neg), indent + 1)?;
            print_with_indent(f, ")", indent)
        }
        RExprKind::VarRef { id } => {
            print_with_indent(f, &format!("VarRef {{ id: {:?} }}", id), indent)
        }
    }
}

/// RPatKindを再帰的にフォーマットする
fn format_pat_kind(f: &mut fmt::Formatter<'_>, _tcx: TyCtxt<'_>, kind: &RPatKind<'_>, indent: usize) -> fmt::Result {
    match kind {
        RPatKind::Binding { name, mode, var, ty, subpattern, is_primary, } => {
            print_with_indent(f, "Binding {", indent)?;
            print_with_indent(f, &format!(r#"name: "{}""#, name), indent + 1)?;
            print_with_indent(f, &format!("mode: {:?}", mode), indent + 1)?;
            print_with_indent(f, &format!("var: {:?}", var), indent + 1)?;
            print_with_indent(f, &format!("ty: {:?}", ty), indent + 1)?;
            print_with_indent(f, &format!("is_primary: {:?}", is_primary), indent + 1)?;
            let sub_str = if subpattern.is_some() { "Some(...)" } else { "None" };
            print_with_indent(f, &format!("subpattern: {}", sub_str), indent + 1)?;
            print_with_indent(f, "}", indent)
        }
    }
}
