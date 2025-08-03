// std crates
use std::fmt;
use std::rc::Rc;

// rustc crates
use rustc_driver::{run_compiler, Callbacks, Compilation};
use rustc_hir::BindingMode;
use rustc_interface::interface::Compiler;
use rustc_middle::thir::*;
use rustc_middle::ty::{self, Ty, TyCtxt};
use rustc_span::Span;

// --- RTHIR (Reduced THIR) Data Structures ---

#[derive(Debug)]
pub struct RThir<'tcx> {
    pub params: Vec<RParam<'tcx>>,
    pub body: Rc<RExpr<'tcx>>,
}

#[derive(Debug)]
pub struct RParam<'tcx> {
    pub pat: Option<Rc<RExpr<'tcx>>>,
}

#[derive(Clone)]
pub struct RExpr<'tcx> {
    pub kind: RExprKind<'tcx>,
    pub span: Span,
    pub ty: Ty<'tcx>,
}

#[derive(Clone, Debug)]
pub enum RExprKind<'tcx> {
    Block {
        stmts: Vec<Rc<RExpr<'tcx>>>,
        expr: Option<Rc<RExpr<'tcx>>>,
    },
    VarRef {
        id: LocalVarId,
    },
    Literal {
        lit: rustc_span::source_map::Spanned<rustc_ast::ast::LitKind>,
        neg: bool,
    },
    LetStmt {
        pattern: Rc<RExpr<'tcx>>,
        initializer: Option<Rc<RExpr<'tcx>>>,
    },
    Pat {
        kind: RPatKind<'tcx>,
    },
}

#[derive(Clone, Debug)]
pub enum RPatKind<'tcx> {
    Binding {
        name: rustc_span::Symbol,
        mode: BindingMode,
        var: LocalVarId,
        ty: Ty<'tcx>,
        subpattern: Option<Rc<RExpr<'tcx>>>,
        is_primary: bool,
    },
}

// --- THIR to RTHIR Conversion Logic ---

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
        let mut kind = &expr.kind;
        let mut span = expr.span;

        while let ExprKind::Scope { value, .. } = kind {
            let inner_expr = &self.thir[*value];
            kind = &inner_expr.kind;
            span = inner_expr.span;
        }

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
            ty: self.tcx.types.unit,
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

pub fn reduce_thir<'tcx>(tcx: TyCtxt<'tcx>, thir: Thir<'tcx>) -> RThir<'tcx> {
    let binding = thir.clone();
    let reducer = Reducer::new(tcx, &binding);
    let body = reducer.reduce_expr(thir.exprs.last_index().unwrap());

    let params = thir
        .params
        .into_iter()
        .map(|p| RParam { pat: p.pat.map(|pat| reducer.reduce_pat(&pat)) })
        .collect();

    RThir { params, body }
}

// --- Custom Debug Printing for RTHIR ---

fn print_with_indent(f: &mut fmt::Formatter<'_>, s: &str, indent: usize) -> fmt::Result {
    writeln!(f, "{}{}", "  ".repeat(indent), s)
}

fn format_expr_recursive(f: &mut fmt::Formatter<'_>, expr: &RExpr<'_>, indent: usize) -> fmt::Result {
    print_with_indent(f, "Expr {", indent)?;
    print_with_indent(f, &format!("span: {:?}", expr.span), indent + 1)?;
    print_with_indent(f, "kind:", indent + 1)?;

    match &expr.kind {
        RExprKind::Block { stmts, expr: block_expr } => {
            print_with_indent(f, "Block {", indent + 2)?;
            if !stmts.is_empty() {
                print_with_indent(f, "stmts: [", indent + 3)?;
                for stmt in stmts {
                    format_expr_recursive(f, stmt, indent + 4)?;
                }
                print_with_indent(f, "]", indent + 3)?;
            }
            if let Some(e) = block_expr {
                print_with_indent(f, "expr:", indent + 3)?;
                format_expr_recursive(f, e, indent + 4)?;
            }
            print_with_indent(f, "}", indent + 2)?;
        }
        RExprKind::LetStmt { pattern, initializer } => {
            print_with_indent(f, "LetStmt {", indent + 2)?;
            print_with_indent(f, "pattern:", indent + 3)?;
            format_expr_recursive(f, pattern, indent + 4)?;
            if let Some(init) = initializer {
                print_with_indent(f, ",", indent + 2)?;
                print_with_indent(f, "initializer: Some(", indent + 3)?;
                format_expr_recursive(f, init, indent + 4)?;
                print_with_indent(f, ")", indent + 3)?;
            }
            print_with_indent(f, "}", indent + 2)?;
        }
        RExprKind::Pat { kind } => {
            print_with_indent(f, "Pat {", indent + 2)?;
            print_with_indent(f, "PatKind {", indent + 3)?;
            match kind {
                RPatKind::Binding { name, mode, var, ty, subpattern, is_primary } => {
                    print_with_indent(f, "Binding {", indent + 4)?;
                    print_with_indent(f, &format!("name: {:?}", name), indent + 5)?;
                    print_with_indent(f, &format!("mode: {:?}", mode), indent + 5)?;
                    print_with_indent(f, &format!("var: {:?}", var), indent + 5)?;
                    print_with_indent(f, &format!("ty: {:?}", ty), indent + 5)?;
                    if let Some(sub) = subpattern {
                        print_with_indent(f, "subpattern: Some(", indent + 5)?;
                        format_expr_recursive(f, sub, indent + 6)?;
                        print_with_indent(f, ")", indent + 5)?;
                    } else {
                        print_with_indent(f, "subpattern: None", indent + 5)?;
                    }
                    print_with_indent(f, &format!("is_primary: {:?}", is_primary), indent + 5)?;
                    print_with_indent(f, "}", indent + 4)?;
                }
            }
            print_with_indent(f, "}", indent + 3)?;
            print_with_indent(f, "}", indent + 2)?;
        }
        RExprKind::Literal { lit, neg } => {
            print_with_indent(f, "Literal {", indent + 2)?;
            print_with_indent(f, &format!("lit: {:?}", lit), indent + 3)?;
            print_with_indent(f, &format!("neg: {:?}", neg), indent + 3)?;
            print_with_indent(f, "}", indent + 2)?;
        }
        _ => {
            print_with_indent(f, &format!("{:?}", expr.kind), indent + 2)?;
        }
    }
    print_with_indent(f, "}", indent)?;
    Ok(())
}

impl fmt::Debug for RExpr<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        format_expr_recursive(f, self, 0)
    }
}


struct MyCallbacks {}

impl Callbacks for MyCallbacks {
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        println!("--- Extracting and Printing RTHIR for all functions ---");

        let mir_keys = tcx.mir_keys(());

        for def_id in mir_keys {
            println!("\n// RTHIR for `{}`", tcx.def_path_str(def_id.to_def_id()));
            println!("// -----------------------------------------");

            if let Ok((thir, _entry_expr)) = tcx.thir_body(*def_id) {
                let thir = thir.steal();
                let rthir = reduce_thir(tcx, thir);
                println!("{:#?}", rthir);
            } else {
                println!("// Could not get THIR for `{}`", tcx.def_path_str(def_id.to_def_id()));
            }
        }

        println!("\n\n--- RTHIR extraction complete ---");
        Compilation::Stop
    }
}

fn find_sysroot() -> String {
    let output = std::process::Command::new("rustc")
        .arg("--print")
        .arg("sysroot")
        .output()
        .expect("Failed to run `rustc --print sysroot`");
    String::from_utf8(output.stdout).unwrap().trim().to_string()
}

pub fn run_verif() {
    let input_file = "input.rs";
    let input_code = r#"
fn main() {
    let x = 0;
}
"#;
    std::fs::write(input_file, input_code).expect("Failed to write to input.rs");

    let args: Vec<String> = vec![
        "thir-extractor".to_string(),
        input_file.to_string(),
        "-Zno-steal-thir".to_string(),
        "--sysroot".to_string(),
        find_sysroot(),
    ];

    println!("Running compiler with args: {:?}", &args[1..]);
    println!("============================================");

    let result = std::panic::catch_unwind(|| {
        run_compiler(&args, &mut MyCallbacks {});
    });

    if result.is_err() {
        eprintln!("Compiler run panicked! This can happen when using unstable nightly rustc APIs.");
    }

    let _ = std::fs::remove_file(input_file);
}
