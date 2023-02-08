//! Abstract Syntax Tree.

use crate::parser::lexer::{BinOp, UnaryOp};
use crate::span::Spanned;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Root {
    pub items: Vec<Spanned<Item>>,
}

/// Represents either a [`Root`] or a [`Stmt`]. This is used in the REPL interface where both are
/// allowed at the top-level.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RootOrStmt {
    Root(Root),
    Stmt(Stmt),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Item {
    Fn(Spanned<FnItem>),
    Struct(Spanned<StructItem>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FnItem {
    pub ident: Spanned<String>,
    pub args: Spanned<FnArgs>,
    pub ret_ty: Option<Spanned<String>>,
    pub body: Spanned<BlockExpr>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FnArgs {
    pub args: Vec<Spanned<Binding>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Stmt {
    ExprStmt(Spanned<Expr>),
    Let(Spanned<LetStmt>),
    Return(Spanned<ReturnStmt>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LetStmt {
    pub binding: Spanned<Binding>,
    pub expr: Spanned<Expr>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReturnStmt {
    pub expr: Spanned<Expr>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    Ident(Spanned<String>),
    Block(Spanned<BlockExpr>),

    Binary(Spanned<BinaryExpr>),
    Unary(Spanned<UnaryExpr>),
    Call(Spanned<CallExpr>),

    LitBool(bool),
    LitInt(i64),
    /// The float is stored as a string representation.
    LitFloat(String),
    LitStr(String),
    LitChar(char),

    If(Spanned<IfExpr>),
    While(Spanned<WhileExpr>),
    For(Spanned<ForExpr>),
    Loop(Spanned<LoopExpr>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BlockExpr {
    pub stmts: Vec<Spanned<Stmt>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BinaryExpr {
    pub lhs: Box<Spanned<Expr>>,
    pub op: Spanned<BinOp>,
    pub rhs: Box<Spanned<Expr>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UnaryExpr {
    pub op: Spanned<UnaryOp>,
    pub expr: Box<Spanned<Expr>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CallExpr {
    pub callee: Box<Spanned<Expr>>,
    pub args: Vec<Spanned<Expr>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IfExpr {
    pub cond: Box<Spanned<Expr>>,
    pub then: Spanned<BlockExpr>,
    pub else_: Option<Spanned<BlockExpr>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WhileExpr {
    pub cond: Box<Spanned<Expr>>,
    pub body: Spanned<BlockExpr>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ForExpr {
    pub binding: Spanned<Binding>,
    pub iter: Box<Spanned<Expr>>,
    pub body: Spanned<BlockExpr>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LoopExpr {
    pub body: Spanned<BlockExpr>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Binding {
    pub ident: Spanned<String>,
    pub ty: Option<Spanned<String>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructItem {
    pub ident: Spanned<String>,
    pub fields: Vec<Spanned<StructField>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructField {
    pub ident: Spanned<String>,
    pub ty: Spanned<String>,
}
