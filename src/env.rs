//! シンボリック実行の環境を管理する

use crate::lir::Lir;
use rustc_data_structures::fx::FxHashMap;
use rustc_middle::thir::LocalVarId;
use rustc_middle::ty::TyKind;

/// シンボリック実行の状態を保持する環境
#[derive(Clone, Debug)]
pub struct Env<'tcx> {
    /// SMTソルバーで宣言される変数のリスト (名前, 型)
    pub smt_vars: Vec<(String, TyKind<'tcx>)>,
    /// パス条件 (SMT形式の制約リスト)
    pub path: Vec<String>,
    /// RTHIRの変数IDとLIRの値を対応付けるマップ
    pub var_map: FxHashMap<LocalVarId, Lir<'tcx>>,
}

impl<'tcx> Env<'tcx> {
    /// 新しいEnvインスタンスを作成する
    pub fn new() -> Self {
        Self {
            smt_vars: Vec::new(),
            path: Vec::new(),
            var_map: FxHashMap::default(),
        }
    }
}
