//! Abstract Syntax Tree.

pub mod visitor;

use la_arena::{Arena, Idx};

use crate::parser::lexer::{BinOp, UnaryOp};
use crate::span::Spanned;

pub type ItemId = Idx<Spanned<Item>>;

/// Represents the root of the AST. A source file is composed of a single root node.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Root {
    pub items: Arena<Spanned<Item>>,
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

/// An item is a top-level source element. An item can be a function, a struct, a module, or a use
/// statement.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Item {
    Let(Spanned<LetItem>),
    Type(Spanned<TypeItem>),
    Mod(Spanned<ModItem>),
    Use(Spanned<UseItem>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LetItem {
    pub attrs: Spanned<Attributes>,
    pub vis: Spanned<Vis>,
    pub ident: Spanned<String>,
    pub params: Vec<Spanned<Param>>,
    pub ret_ty: Option<Spanned<Type>>,
    pub expr: Box<Spanned<Expr>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Param {
    pub ident: Spanned<String>,
    pub ty: Option<Spanned<Type>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeItem {
    pub attrs: Spanned<Attributes>,
    pub vis: Spanned<Vis>,
    /// Identifier of the type constructor.
    pub ident: Spanned<String>,
    pub ty_params: Vec<Spanned<TypeParam>>,
    pub def: Spanned<TypeDef>,
}

/// Type parameters for the type constructor.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeParam {
    pub ident: Spanned<String>,
}

/// RHS of a `type` item. A [`TypeItem`] either defines a record type or an ADT (Algebraic Data
/// Type).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeDef {
    Adt(Spanned<AdtDef>),
    Record(Spanned<RecordDef>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AdtDef {
    pub data_constructors: Vec<Spanned<DataConstructor>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DataConstructor {
    pub ident: Spanned<String>,
    pub of: Vec<Spanned<Type>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecordDef {
    pub fields: Vec<Spanned<RecordField>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecordField {
    pub ident: Spanned<String>,
    pub ty: Box<Spanned<Type>>,
}

/// A reference to a type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    Path(Spanned<PathType>),
    Fn(Spanned<FnType>),
    Tuple(Spanned<TupleType>),
    /// The result of the application of a type constructor.
    Constructed(Spanned<ConstructedType>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PathType {
    pub path: Vec<Spanned<String>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FnType {
    pub arg_ty: Box<Spanned<Type>>,
    pub ret_ty: Box<Spanned<Type>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TupleType {
    pub fields: Vec<Spanned<Type>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstructedType {
    pub constructor: Box<Spanned<Type>>,
    pub arg: Box<Spanned<Type>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    Ident(Spanned<IdentExpr>),

    Block(Spanned<BlockExpr>),

    Binary(Spanned<BinaryExpr>),
    Unary(Spanned<UnaryExpr>),

    Index(Spanned<IndexExpr>),

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
    Return(Spanned<ReturnExpr>),

    Let(Spanned<LetExpr>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IdentExpr {
    pub ident: Spanned<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BlockExpr {
    pub exprs: Vec<Spanned<Expr>>,
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
pub struct IndexExpr {
    pub lhs: Box<Spanned<Expr>>,
    pub index: Box<Spanned<Expr>>,
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
pub struct ReturnExpr {
    pub expr: Box<Spanned<Expr>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LetExpr {
    pub ident: Spanned<String>,
    pub params: Vec<Spanned<Param>>,
    pub ret_ty: Option<Spanned<Type>>,
    pub expr: Box<Spanned<Expr>>,
    pub _in: Box<Spanned<Expr>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Binding {
    pub ident: Spanned<String>,
    pub ty: Option<Spanned<String>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModItem {
    pub attrs: Spanned<Attributes>,
    pub vis: Spanned<Vis>,
    pub ident: Spanned<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UseItem {
    pub attrs: Spanned<Attributes>,
    pub vis: Spanned<Vis>,
    pub path: Spanned<String>,
}
