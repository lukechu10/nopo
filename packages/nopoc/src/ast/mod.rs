//! Abstract Syntax Tree.

pub mod visitor;

use crate::parser::lexer::{BinOp, UnaryOp};
use crate::span::Spanned;

/// Represents the root of the AST. A source file is composed of a single root node.
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

/// Attributes can be attached to an item.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Attributes {
    pub attrs: Vec<Spanned<Attribute>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Attribute {
    pub ident: Spanned<String>,
}

/// Represents the visibility of an item.
///
/// There is no keyword for private items because everything is private by default.
///
/// In that case, the span of the visibility is empty and is just the start of the item.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Vis {
    Pub,
    Priv,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Item {
    Fn(Spanned<FnItem>),
    ExternFn(Spanned<ExternFnItem>),
    Struct(Spanned<StructItem>),
    Mod(Spanned<ModItem>),
    Use(Spanned<UseItem>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FnItem {
    pub attrs: Spanned<Attributes>,
    pub vis: Spanned<Vis>,
    pub ident: Spanned<String>,
    pub args: Spanned<FnArgs>,
    pub ret_ty: Option<Spanned<String>>,
    /// The body of the function. Syntaxically, this can only be a [`BlockExpr`] but this field is
    /// of type [`Expr`] to make it easier to implement the visitor pattern.
    pub body: Spanned<Expr>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FnArgs {
    pub args: Vec<Spanned<Binding>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExternFnItem {
    pub attrs: Spanned<Attributes>,
    pub vis: Spanned<Vis>,
    pub ident: Spanned<String>,
    pub args: Spanned<FnArgs>,
    pub ret_ty: Option<Spanned<String>>,
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
    FnCall(Spanned<FnCallExpr>),

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
pub struct FnCallExpr {
    pub callee: Box<Spanned<Expr>>,
    pub args: Spanned<FnCallArgs>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FnCallArgs {
    pub args: Vec<Spanned<Expr>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IfExpr {
    pub cond: Box<Spanned<Expr>>,
    pub then: Box<Spanned<Expr>>,
    pub else_: Option<Box<Spanned<Expr>>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WhileExpr {
    pub cond: Box<Spanned<Expr>>,
    pub body: Box<Spanned<Expr>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ForExpr {
    pub binding: Spanned<Binding>,
    pub iter: Box<Spanned<Expr>>,
    pub body: Box<Spanned<Expr>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LoopExpr {
    pub body: Box<Spanned<Expr>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Binding {
    pub ident: Spanned<String>,
    pub ty: Option<Spanned<String>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructItem {
    pub attrs: Spanned<Attributes>,
    pub vis: Spanned<Vis>,
    pub ident: Spanned<String>,
    pub fields: Vec<Spanned<StructField>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructField {
    pub ident: Spanned<String>,
    pub ty: Spanned<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModItem {
    pub attrs: Spanned<Attributes>,
    pub vis: Spanned<Vis>,
    pub path: Spanned<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UseItem {
    pub attrs: Spanned<Attributes>,
    pub vis: Spanned<Vis>,
    pub path: Spanned<String>,
}
