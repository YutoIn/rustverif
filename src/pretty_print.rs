//! RTHIR のためのプリティプリンタ

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
        writeln!(f, "{:?}, params: [", self.def_id)?;
        for param in &self.params {
            print_with_indent(f, "Param {", 1)?;
            if let Some(pat) = &param.pat {
                print_with_indent(f, "param: Some(", 2)?;
                format_expr(f, self.tcx, pat, 3)?;
                print_with_indent(f, ")", 2)?;
            }
            print_with_indent(f, "}", 1)?;
        }
        writeln!(f, "]")?;
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
        RExprKind::VarRef { id } => print_with_indent(f, &format!("VarRef {{ id: {:?} }}", id), indent),
        RExprKind::Binary { op, lhs, rhs } => {
            print_with_indent(f, "Binary {", indent)?;
            print_with_indent(f, &format!("op: {:?}", op), indent + 1)?;
            print_with_indent(f, "lhs:", indent + 1)?;
            format_expr(f, tcx, lhs, indent + 2)?;
            print_with_indent(f, "rhs:", indent + 1)?;
            format_expr(f, tcx, rhs, indent + 2)?;
            print_with_indent(f, "}", indent)
        }
        RExprKind::Call { fun, args, fn_def_id } => {
            print_with_indent(f, "Call {", indent)?;
            print_with_indent(f, &format!("fn_def_id: {:?}", fn_def_id), indent + 1)?;
            print_with_indent(f, "fun:", indent + 1)?;
            format_expr(f, tcx, fun, indent + 2)?;
            print_with_indent(f, "args: [", indent + 1)?;
            for arg in args {
                format_expr(f, tcx, arg, indent + 2)?;
            }
            print_with_indent(f, "]", indent + 1)?;
            print_with_indent(f, "}", indent)
        }
        RExprKind::ZstLiteral => print_with_indent(f, "ZstLiteral", indent),
        RExprKind::If { cond, then, else_opt } => {
            print_with_indent(f, "If {", indent)?;
            print_with_indent(f, "cond:", indent + 1)?;
            format_expr(f, tcx, cond, indent + 2)?;
            print_with_indent(f, "then:", indent + 1)?;
            format_expr(f, tcx, then, indent + 2)?;
            if let Some(e) = else_opt {
                print_with_indent(f, "else:", indent + 1)?;
                format_expr(f, tcx, e, indent + 2)?;
            }
            print_with_indent(f, "}", indent)
        }
    }
}

/// RPatKindを再帰的にフォーマットする
fn format_pat_kind(f: &mut fmt::Formatter<'_>, _tcx: TyCtxt<'_>, kind: &RPatKind<'_>, indent: usize) -> fmt::Result {
    match kind {
        RPatKind::Binding { name, var, ty, subpattern, .. } => {
            print_with_indent(f, "Binding {", indent)?;
            print_with_indent(f, &format!(r#"name: "{}""#, name), indent + 1)?;
            print_with_indent(f, &format!("var: {:?}", var), indent + 1)?;
            print_with_indent(f, &format!("ty: {:?}", ty), indent + 1)?;
            let sub_str = if subpattern.is_some() { "Some(...)" } else { "None" };
            print_with_indent(f, &format!("subpattern: {}", sub_str), indent + 1)?;
            print_with_indent(f, "}", indent)
        }
    }
}
