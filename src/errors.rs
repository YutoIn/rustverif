//! 検証器で利用するエラーの定義

#[derive(Debug, Clone)]
pub enum VerifError {
    /// RTHIRの構造が想定と異なる場合のエラー
    UnexpectedRThir,
    /// その他の予期しないエラー
    Unimplemented,
}
