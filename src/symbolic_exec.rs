//! RTHIRのシンボリック実行を行うモジュール

use crate::env::Env;
use crate::errors::VerifError;
use crate::lir::{Lir, LirKind};
use crate::rthir::{RExpr, RExprKind, RPatKind, RThir};
use rustc_ast::ast as Ast;
use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def_id::LocalDefId;
use rustc_middle::mir::BinOp;
use rustc_middle::ty::TyCtxt;
use std::rc::Rc;

/// BinOpをSMTの演算子文字列に変換する
fn binop_to_smt_str(op: BinOp) -> &'static str {
    match op {
        BinOp::Add => "+",
        BinOp::Sub => "-",
        BinOp::Mul => "*",
        BinOp::Div => "div",
        BinOp::Eq => "=",
        BinOp::Lt => "<",
        BinOp::Le => "<=",
        BinOp::Ne => "distinct",
        BinOp::Ge => ">=",
        BinOp::Gt => ">",
        _ => unimplemented!("Unsupported BinOp: {:?}", op),
    }
}

/// RTHIRの式を評価し、LIRに変換する
fn eval_rvalue<'tcx>(
    env: &Env<'tcx>,
    r_expr: Rc<RExpr<'tcx>>,
    tcx: TyCtxt<'tcx>,
) -> Result<Lir<'tcx>, VerifError> {
    match &r_expr.kind {
        RExprKind::Literal { lit, neg } => {
            let val_str = match lit.node {
                Ast::LitKind::Int(val, _) => val.to_string(),
                _ => return Err(VerifError::Unimplemented),
            };
            let expr_str = if *neg {
                format!("(- {})", val_str)
            } else {
                val_str
            };
            Ok(Lir::new(
                LirKind::VarExpr {
                    var_expr: expr_str,
                    ty: r_expr.ty.kind().clone(),
                },
                r_expr,
            ))
        }
        RExprKind::VarRef { id } => env
            .var_map
            .get(id)
            .cloned()
            .ok_or(VerifError::Unimplemented),
        RExprKind::Binary { op, lhs, rhs } => {
            let lhs_lir = eval_rvalue(env, lhs.clone(), tcx)?;
            let rhs_lir = eval_rvalue(env, rhs.clone(), tcx)?;
            let smt_op = binop_to_smt_str(*op);
            let expr_str = format!(
                "({} {} {})",
                smt_op,
                lhs_lir.get_var_expr(),
                rhs_lir.get_var_expr()
            );
            Ok(Lir::new(
                LirKind::VarExpr {
                    var_expr: expr_str,
                    ty: r_expr.ty.kind().clone(),
                },
                r_expr,
            ))
        }
        RExprKind::Call { fn_def_id, .. } => {
            let fn_name = tcx.def_path_str(*fn_def_id);
            if fn_name.ends_with("rand_int") {
                return Ok(Lir::new(
                    LirKind::VarExpr {
                        var_expr: "RAND".to_string(),
                        ty: r_expr.ty.kind().clone(),
                    },
                    r_expr,
                ));
            }
            Err(VerifError::Unimplemented)
        }
        _ => Err(VerifError::Unimplemented),
    }
}

/// `let`文をシンボリック実行する
fn symbolic_exec_let_stmt<'tcx>(
    env: &mut Env<'tcx>,
    pattern: &RExpr<'tcx>,
    initializer: &Option<Rc<RExpr<'tcx>>>,
    tcx: TyCtxt<'tcx>,
) -> Result<(), VerifError> {
    let initializer_lir = if let Some(init_expr) = initializer {
        eval_rvalue(env, init_expr.clone(), tcx)?
    } else {
        return Err(VerifError::Unimplemented);
    };

    if let RExprKind::Pat { kind } = &pattern.kind {
        match kind {
            RPatKind::Binding { var, name, ty, .. } => {
                let var_name = name.as_str().to_string();
                env.var_name_map.insert(*var, var_name.clone());

                let final_lir = if initializer_lir.get_var_expr() == "RAND" {
                    env.smt_vars.push((var_name.clone(), ty.kind().clone()));
                    Lir::new(
                        LirKind::VarExpr {
                            var_expr: var_name,
                            ty: ty.kind().clone(),
                        },
                        Rc::new(pattern.clone()),
                    )
                } else {
                    env.smt_vars.push((var_name.clone(), ty.kind().clone()));
                    let assert_str =
                        format!("(= {} {})", var_name, initializer_lir.get_var_expr());
                    env.path.push(assert_str);
                    Lir::new(
                        LirKind::VarExpr {
                            var_expr: var_name,
                            ty: ty.kind().clone(),
                        },
                        Rc::new(pattern.clone()),
                    )
                };
                env.var_map.insert(*var, final_lir);
                return Ok(());
            }
        }
    }
    Err(VerifError::UnexpectedRThir)
}

/// 関数呼び出しをシンボリック実行する
fn symbolic_exec_call<'tcx>(
    env: &mut Env<'tcx>,
    fn_def_id: &rustc_hir::def_id::DefId,
    args: &[Rc<RExpr<'tcx>>],
    tcx: TyCtxt<'tcx>,
    fn_map: &FxHashMap<LocalDefId, RThir<'tcx>>,
) -> Result<(), VerifError> {
    let fn_name = tcx.def_path_str(*fn_def_id);

    if fn_name.ends_with("t3assume") || fn_name.ends_with("t3assert") {
        let cond_expr = args.get(0).ok_or(VerifError::UnexpectedRThir)?;
        let cond_lir = eval_rvalue(env, cond_expr.clone(), tcx)?;
        let cond_str = if fn_name.ends_with("t3assert") {
            format!("(not {})", cond_lir.get_var_expr())
        } else {
            cond_lir.get_var_expr()
        };
        env.path.push(cond_str);
        Ok(())
    } else if let Some(callee_def_id) = fn_def_id.as_local() {
        let callee_rthir = fn_map
            .get(&callee_def_id)
            .ok_or(VerifError::Unimplemented)?;
        
        let mut arg_lirs = Vec::new();
        for arg_expr in args {
            arg_lirs.push(eval_rvalue(env, arg_expr.clone(), tcx)?);
        }

        let mut temp_var_map = env.var_map.clone();
        for (arg_lir, param) in arg_lirs.iter().zip(&callee_rthir.params) {
             if let Some(param_pat) = &param.pat {
                if let RExprKind::Pat { kind: RPatKind::Binding { var, .. } } = &param_pat.kind {
                    temp_var_map.insert(*var, arg_lir.clone());
                }
            }
        }
        
        let original_var_map = env.var_map.clone();
        env.var_map = temp_var_map;
        
        let result = symbolic_exec_body(env, callee_rthir, tcx, fn_map);
        
        env.var_map = original_var_map;
        
        result
    } else {
        Err(VerifError::Unimplemented)
    }
}

/// if式をシンボリック実行する
fn symbolic_exec_if<'tcx>(
    env: &mut Env<'tcx>,
    cond: &RExpr<'tcx>,
    then: &RExpr<'tcx>,
    tcx: TyCtxt<'tcx>,
    fn_map: &FxHashMap<LocalDefId, RThir<'tcx>>,
) -> Result<(), VerifError> {
    let cond_lir = eval_rvalue(env, Rc::new(cond.clone()), tcx)?;
    env.path.push(cond_lir.get_var_expr());
    symbolic_exec_body_from_expr(env, then, tcx, fn_map)
}

/// 式からシンボリック実行を開始する
fn symbolic_exec_body_from_expr<'tcx>(
    env: &mut Env<'tcx>,
    expr: &RExpr<'tcx>,
    tcx: TyCtxt<'tcx>,
    fn_map: &FxHashMap<LocalDefId, RThir<'tcx>>,
) -> Result<(), VerifError> {
    match &expr.kind {
        RExprKind::Block { stmts, .. } => {
            for stmt in stmts {
                symbolic_exec_stmt(env, stmt, tcx, fn_map)?;
            }
            Ok(())
        }
        _ => symbolic_exec_stmt(env, expr, tcx, fn_map),
    }
}

/// 文をシンボリック実行する
fn symbolic_exec_stmt<'tcx>(
    env: &mut Env<'tcx>,
    stmt: &RExpr<'tcx>,
    tcx: TyCtxt<'tcx>,
    fn_map: &FxHashMap<LocalDefId, RThir<'tcx>>,
) -> Result<(), VerifError> {
    match &stmt.kind {
        RExprKind::LetStmt {
            pattern,
            initializer,
        } => symbolic_exec_let_stmt(env, pattern, initializer, tcx),
        RExprKind::Call {
            fn_def_id, args, ..
        } => symbolic_exec_call(env, fn_def_id, args, tcx, fn_map),
        RExprKind::If { cond, then, .. } => {
            symbolic_exec_if(env, cond, then, tcx, fn_map)
        }
        _ => Err(VerifError::Unimplemented),
    }
}

/// 関数のボディをシンボリック実行する
pub fn symbolic_exec_body<'tcx>(
    env: &mut Env<'tcx>,
    rthir: &RThir<'tcx>,
    tcx: TyCtxt<'tcx>,
    fn_map: &FxHashMap<LocalDefId, RThir<'tcx>>,
) -> Result<(), VerifError> {
    symbolic_exec_body_from_expr(env, &rthir.body, tcx, fn_map)
}
