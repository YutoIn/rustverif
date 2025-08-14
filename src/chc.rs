//! CHC (Constrained Horn Clause) 生成器およびSMT-LIB2出力を提供するモジュール
//!
//! 本モジュールは、関数のボディを解析して制約付きホーン節を生成します。
//! これは従来のシンボリック実行とは異なり、各関数を述語とみなし、
//! 条件分岐や関数呼び出しを条件部として扱います。

use crate::env::Env;
use crate::errors::VerifError;
use crate::lir::{Lir, LirKind};
use crate::rthir::{RExpr, RExprKind, RPatKind, RThir};
use rustc_ast::ast as Ast;
use rustc_middle::mir::BinOp;
use rustc_middle::ty::{TyCtxt, TyKind};
use std::rc::Rc;

/// 単一のCHCルールを表します。
#[derive(Clone)]
pub struct ChcRule<'tcx> {
    /// ヘッド述語。関数名と引数名および返り値名を含むS式。
    pub head: String,
    /// 量化変数のリストとその型。
    pub vars: Vec<(String, TyKind<'tcx>)>,
    /// 条件部の制約（述語呼び出しや条件式）のリスト。
    pub conds: Vec<String>,
    /// 返り値が満たすべき式の文字列表現。
    pub ret_expr: String,
}

/// CHC生成器。本構造体は環境および生成されたルールを保持します。
pub struct ChcGen<'tcx> {
    /// 生成されたCHCルールのリスト。
    pub rules: Vec<ChcRule<'tcx>>,
    /// 型コンテキスト。
    tcx: TyCtxt<'tcx>,
    /// 変数名解決および式評価に用いる環境。
    env: Env<'tcx>,
}

impl<'tcx> ChcGen<'tcx> {
    /// 新しいCHC生成器を作成します。
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            rules: Vec::new(),
            tcx,
            env: Env::new(),
        }
    }

    /// 関数ごとのCHC生成を行います。
    ///
    /// 関数の引数や返り値を量化変数として登録し、関数本体を解析してルールを生成します。
    pub fn process_fun(&mut self, rthir: &RThir<'tcx>) -> Result<(), VerifError> {
        let fn_name = self.tcx.def_path_str(rthir.def_id);
        // 引数名と型を抽出し、環境に登録する。
        let mut param_names = Vec::new();
        for param in &rthir.params {
            if let Some(pat_expr) = &param.pat {
                if let RExprKind::Pat { kind } = &pat_expr.kind {
                    match kind {
                        RPatKind::Binding { name, var, ty, .. } => {
                            let var_name = name.as_str().to_string();
                            param_names.push((var_name.clone(), ty.kind().clone()));
                            // 環境に名前を登録
                            self.env.var_name_map.insert(*var, var_name.clone());
                            // LIRとして環境に登録
                            let lir = Lir::new(
                                LirKind::VarExpr {
                                    var_expr: var_name.clone(),
                                    ty: ty.kind().clone(),
                                },
                                pat_expr.clone(),
                            );
                            self.env.var_map.insert(*var, lir);
                        }
                    }
                }
            }
        }
        // 返り値の型と名前を用意する
        let ret_ty = rthir.body.ty.kind().clone();
        let ret_name = "ret".to_string();
        let mut vars = param_names.clone();
        vars.push((ret_name.clone(), ret_ty));
        // ヘッド述語のS式を構築する (関数名 引数... 返り値)
        let param_name_list: Vec<String> = param_names.iter().map(|(n, _)| n.clone()).collect();
        let head_string = format!("({} {} {})", fn_name, param_name_list.join(" "), ret_name);
        // 本体からCHCルールを生成する
        self.add_rules(head_string, Vec::new(), vars, rthir.body.clone())
    }

    /// 式に対するCHCルール生成を再帰的に行います。
    ///
    /// `head` はルールの帰結述語、`conds` はこれまでに蓄積された条件、`vars` は量化変数の集合です。
    fn add_rules(
        &mut self,
        head: String,
        conds: Vec<String>,
        vars: Vec<(String, TyKind<'tcx>)>,
        expr: Rc<RExpr<'tcx>>,
    ) -> Result<(), VerifError> {
        match &expr.kind {
            RExprKind::If {
                cond,
                then,
                else_opt,
            } => {
                // 条件を評価して両方の枝を処理する
                let cond_lir = self.eval_rvalue(cond.clone())?;
                let cond_str = cond_lir.get_var_expr();
                // then側
                let mut conds_then = conds.clone();
                conds_then.push(cond_str.clone());
                self.add_rules(head.clone(), conds_then, vars.clone(), then.clone())?;
                // else側
                if let Some(else_expr) = else_opt {
                    let mut conds_else = conds.clone();
                    conds_else.push(format!("(not {})", cond_str));
                    self.add_rules(head, conds_else, vars, else_expr.clone())?;
                }
                Ok(())
            }
            RExprKind::LetStmt {
                pattern,
                initializer,
            } => {
                // let文の場合、初期化子が関数呼び出しか純粋式かで処理を分ける
                if let Some(init_expr) = initializer {
                    match &init_expr.kind {
                        RExprKind::Call {
                            fn_def_id, args, ..
                        } => {
                            // 関数呼び出しは述語呼び出しとして条件に追加する
                            let mut arg_strs = Vec::new();
                            for arg in args {
                                let lir = self.eval_rvalue(arg.clone())?;
                                arg_strs.push(lir.get_var_expr());
                            }
                            let callee_name = self.tcx.def_path_str(*fn_def_id);
                            // 新しい変数名と型を取り出す
                            let (var_name, var_ty) = if let RExprKind::Pat { kind } = &pattern.kind
                            {
                                if let RPatKind::Binding { name, var, ty, .. } = kind {
                                    let name_str = name.as_str().to_string();
                                    // 環境に登録
                                    self.env.var_name_map.insert(*var, name_str.clone());
                                    let lir = Lir::new(
                                        LirKind::VarExpr {
                                            var_expr: name_str.clone(),
                                            ty: ty.kind().clone(),
                                        },
                                        pattern.clone(),
                                    );
                                    self.env.var_map.insert(*var, lir);
                                    (name_str, ty.kind().clone())
                                } else {
                                    return Err(VerifError::UnexpectedRThir);
                                }
                            } else {
                                return Err(VerifError::UnexpectedRThir);
                            };
                            let mut new_vars = vars.clone();
                            new_vars.push((var_name.clone(), var_ty.clone()));
                            // 述語呼び出しとして条件に追加
                            let call_str = format!(
                                "({} {} {})",
                                callee_name,
                                arg_strs.join(" "),
                                var_name.clone()
                            );
                            let mut new_conds = conds.clone();
                            new_conds.push(call_str);
                            // 現在の実装では let の後続の式にアクセスできないため、返り値を束縛変数とするルールを生成する
                            let rule = ChcRule {
                                head: head.clone(),
                                vars: new_vars,
                                conds: new_conds,
                                ret_expr: var_name,
                            };
                            self.rules.push(rule);
                            Ok(())
                        }
                        _ => {
                            // 純粋な式の場合、式を評価しその等式を条件に追加する
                            if let RExprKind::Pat { kind } = &pattern.kind {
                                if let RPatKind::Binding { name, var, ty, .. } = kind {
                                    let var_name = name.as_str().to_string();
                                    let expr_lir = self.eval_rvalue(init_expr.clone())?;
                                    let expr_str = expr_lir.get_var_expr();
                                    // 環境に登録
                                    self.env.var_name_map.insert(*var, var_name.clone());
                                    let lir = Lir::new(
                                        LirKind::VarExpr {
                                            var_expr: expr_str.clone(),
                                            ty: ty.kind().clone(),
                                        },
                                        init_expr.clone(),
                                    );
                                    self.env.var_map.insert(*var, lir);
                                    let mut new_vars = vars.clone();
                                    new_vars.push((var_name.clone(), ty.kind().clone()));
                                    let mut new_conds = conds.clone();
                                    new_conds.push(format!(
                                        "(= {} {})",
                                        var_name.clone(),
                                        expr_str
                                    ));
                                    // letの後続の式にアクセスできないため、返り値を束縛変数としたルールを生成する
                                    let rule = ChcRule {
                                        head: head.clone(),
                                        vars: new_vars,
                                        conds: new_conds,
                                        ret_expr: var_name,
                                    };
                                    self.rules.push(rule);
                                    Ok(())
                                } else {
                                    Err(VerifError::UnexpectedRThir)
                                }
                            } else {
                                Err(VerifError::UnexpectedRThir)
                            }
                        }
                    }
                } else {
                    // 初期化子がないletは未対応
                    Err(VerifError::Unimplemented)
                }
            }
            RExprKind::Block {
                stmts: _,
                expr: block_expr_opt,
            } => {
                // ブロック式は最終式のみを対象として処理する。
                if let Some(block_expr) = block_expr_opt {
                    self.add_rules(head, conds, vars, block_expr.clone())
                } else {
                    // 戻り値を持たないブロックはユニット型とみなし、ダミー値を返すルールを生成する
                    let rule = ChcRule {
                        head,
                        vars,
                        conds,
                        ret_expr: "0".to_string(),
                    };
                    self.rules.push(rule);
                    Ok(())
                }
            }
            // その他の純粋式は即座にルールを生成する。
            RExprKind::Binary { .. }
            | RExprKind::VarRef { .. }
            | RExprKind::Literal { .. }
            | RExprKind::Call { .. }
            | RExprKind::ZstLiteral
            | RExprKind::Pat { .. } => {
                let lir = self.eval_rvalue(expr.clone())?;
                let ret_expr = lir.get_var_expr();
                let rule = ChcRule {
                    head,
                    vars,
                    conds,
                    ret_expr,
                };
                self.rules.push(rule);
                Ok(())
            }
        }
    }

    /// RExprをSMT形式の文字列表現に評価します。
    ///
    /// 環境から変数名を解決し、リテラルや二項演算はSMTの演算子に変換します。
    fn eval_rvalue(&mut self, r_expr: Rc<RExpr<'tcx>>) -> Result<Lir<'tcx>, VerifError> {
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
            RExprKind::VarRef { id } => {
                // 環境から変数のLIRを取得する
                self.env
                    .var_map
                    .get(id)
                    .cloned()
                    .ok_or(VerifError::Unimplemented)
            }
            RExprKind::Binary { op, lhs, rhs } => {
                let lhs_lir = self.eval_rvalue(lhs.clone())?;
                let rhs_lir = self.eval_rvalue(rhs.clone())?;
                let smt_op = match op {
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
                    _ => return Err(VerifError::Unimplemented),
                };
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
            RExprKind::Call {
                fn_def_id, args, ..
            } => {
                // 関数呼び出しは未解釈関数として扱う
                let fn_name = self.tcx.def_path_str(*fn_def_id);
                let mut arg_strs = Vec::new();
                for arg in args {
                    let lir = self.eval_rvalue(arg.clone())?;
                    arg_strs.push(lir.get_var_expr());
                }
                let expr_str = if arg_strs.is_empty() {
                    format!("({})", fn_name)
                } else {
                    format!("({} {})", fn_name, arg_strs.join(" "))
                };
                Ok(Lir::new(
                    LirKind::VarExpr {
                        var_expr: expr_str,
                        ty: r_expr.ty.kind().clone(),
                    },
                    r_expr,
                ))
            }
            RExprKind::ZstLiteral => Ok(Lir::new(
                LirKind::VarExpr {
                    var_expr: "0".to_string(),
                    ty: r_expr.ty.kind().clone(),
                },
                r_expr,
            )),
            RExprKind::Pat { .. }
            | RExprKind::LetStmt { .. }
            | RExprKind::Block { .. }
            | RExprKind::If { .. } => Err(VerifError::UnexpectedRThir),
        }
    }
}

/// CHCルールのリストをSMT-LIB2の文字列に変換します。
///
/// 各述語について宣言を行い、各ルールを(forall ...) (assert ...) の形で出力します。
pub fn chc_to_smt<'tcx>(rules: &[ChcRule<'tcx>]) -> String {
    let mut smt_string = String::new();
    smt_string.push_str(";; CHC rules in SMT-LIB 2 format\n");
    use std::collections::BTreeMap;
    // 述語名とその引数のソートを集める
    let mut predicates: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for rule in rules {
        // ヘッドのS式をパースし、述語名を取得する
        let trimmed = rule.head.trim();
        if trimmed.starts_with('(') && trimmed.ends_with(')') {
            let inner = &trimmed[1..trimmed.len() - 1];
            let mut parts = inner.split_whitespace();
            if let Some(fn_name) = parts.next() {
                // 引数のソートはvarsから取得する
                let sorts: Vec<String> = rule
                    .vars
                    .iter()
                    .map(|(_, ty)| match ty {
                        TyKind::Int(_) | TyKind::Uint(_) => "Int".to_string(),
                        TyKind::Bool => "Bool".to_string(),
                        _ => "Int".to_string(),
                    })
                    .collect();
                predicates.entry(fn_name.to_string()).or_insert(sorts);
            }
        }
    }
    // 述語宣言を出力する
    for (fn_name, sorts) in predicates.iter() {
        let param_sorts = sorts
            .iter()
            .map(|s| s.as_str())
            .collect::<Vec<_>>()
            .join(" ");
        smt_string.push_str(&format!(
            "(declare-fun {} ({}) Bool)\n",
            fn_name, param_sorts
        ));
    }
    // 各ルールを出力する
    for rule in rules {
        smt_string.push_str("(assert ");
        // 量化子の開始
        smt_string.push_str("(forall (");
        for (name, ty) in &rule.vars {
            let sort = match ty {
                TyKind::Int(_) | TyKind::Uint(_) => "Int",
                TyKind::Bool => "Bool",
                _ => "Int",
            };
            smt_string.push_str(&format!("({} {}) ", name, sort));
        }
        if !rule.vars.is_empty() {
            // 末尾の空白を除去
            smt_string.pop();
        }
        smt_string.push_str(") ");
        // 前提部の構築：condsとretの等式をandでまとめる
        let mut antecedents = Vec::new();
        for cond in &rule.conds {
            antecedents.push(cond.clone());
        }
        // retの等式を追加
        antecedents.push(format!("(= ret {})", rule.ret_expr));
        let antecedent_str = if antecedents.len() == 1 {
            antecedents[0].clone()
        } else {
            format!("(and {})", antecedents.join(" "))
        };
        // (=> antecedent head) を構築
        smt_string.push_str(&format!("(=> {} {}))", antecedent_str, rule.head));
        // forall の閉じ
        smt_string.push_str(")\n");
    }
    // ソルバーコマンド
    smt_string.push_str("(check-sat)\n(get-model)\n");
    smt_string
}
