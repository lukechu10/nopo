//! Abstract Syntax Tree.

pub mod visitor;

use std::fmt;

use la_arena::{Arena, Idx};
use smol_str::SmolStr;

use crate::parser::lexer::{BinOp, UnaryOp};
use nopo_diagnostics::span::Spanned;

pub type LetId = Idx<Spanned<LetItem>>;
pub type TypeId = Idx<Spanned<TypeItem>>;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum ItemId {
    Let(LetId),
    Type(TypeId),
}

/// Represents the root of the AST. A source file is composed of a single root node.
#[derive(Debug, PartialEq, Eq)]
pub struct Root {
    pub let_items: Arena<Spanned<LetItem>>,
    pub type_items: Arena<Spanned<TypeItem>>,
    /// The order of the items. This is used for variable scoping.
    pub items: Vec<ItemId>,
    pub mod_items: Vec<Spanned<ModItem>>,
    pub use_items: Vec<Spanned<UseItem>>,
}

/// Attributes can be attached to an item.
#[derive(Debug, PartialEq, Eq)]
pub struct Attributes {
    pub attrs: Vec<Spanned<Attribute>>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct Attribute {
    pub ident: Spanned<Ident>,
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

#[derive(Debug, PartialEq, Eq)]
pub struct LetItem {
    pub attrs: Spanned<Attributes>,
    pub vis: Spanned<Vis>,
    pub ident: Spanned<Ident>,
    pub params: Vec<Spanned<Param>>,
    pub ret_ty: Option<Spanned<Type>>,
    pub expr: Box<Spanned<Expr>>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct Param {
    pub ident: Spanned<Ident>,
    pub ty: Option<Spanned<Type>>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct TypeItem {
    pub attrs: Spanned<Attributes>,
    pub vis: Spanned<Vis>,
    /// Identifier of the type constructor.
    pub ident: Spanned<Ident>,
    pub ty_params: Vec<Spanned<TypeParam>>,
    pub def: Spanned<TypeDef>,
}

/// Type parameters for the type constructor.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct TypeParam {
    pub ident: Spanned<Ident>,
}

/// RHS of a `type` item. A [`TypeItem`] either defines a record type or an ADT (Algebraic Data
/// Type).
#[derive(Debug, PartialEq, Eq)]
pub enum TypeDef {
    Adt(Spanned<AdtDef>),
    Record(Spanned<RecordDef>),
    Err,
}

#[derive(Debug, PartialEq, Eq)]
pub struct AdtDef {
    pub data_constructors: Vec<Spanned<DataConstructor>>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct DataConstructor {
    pub ident: Spanned<Ident>,
    pub of: Vec<Spanned<Type>>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct RecordDef {
    pub fields: Vec<Spanned<RecordField>>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct RecordField {
    pub ident: Spanned<Ident>,
    pub ty: Box<Spanned<Type>>,
}

/// A reference to a type.
#[derive(Debug, PartialEq, Eq)]
pub enum Type {
    Path(Spanned<PathType>),
    Fn(Spanned<FnType>),
    Tuple(Spanned<TupleType>),
    /// The result of the application of a type constructor.
    Constructed(Spanned<ConstructedType>),
    Param(Spanned<TypeParam>),
    Err,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct PathType {
    pub path: Vec<Spanned<Ident>>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct FnType {
    pub arg_ty: Box<Spanned<Type>>,
    pub ret_ty: Box<Spanned<Type>>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct TupleType {
    pub fields: Vec<Spanned<Type>>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct ConstructedType {
    pub constructor: Box<Spanned<Type>>,
    pub arg: Box<Spanned<Type>>,
}

#[derive(Debug, PartialEq, Eq)]
pub enum Expr {
    Ident(Spanned<IdentExpr>),

    Block(Spanned<BlockExpr>),
    Lambda(Spanned<LambdaExpr>),
    Tuple(Spanned<TupleExpr>),
    Record(Spanned<RecordExpr>),

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

    Err,
}

#[derive(Debug, PartialEq, Eq)]
pub struct IdentExpr {
    pub ident: Spanned<Ident>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct BlockExpr {
    pub exprs: Vec<Spanned<Expr>>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct LambdaExpr {
    pub params: Vec<Spanned<LambdaParam>>,
    pub expr: Box<Spanned<Expr>>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct LambdaParam {
    pub ident: Spanned<Ident>,
}

/// A tuple expression. A tuple with only one element should be represented as just an expression
/// without the tuple.
#[derive(Debug, PartialEq, Eq)]
pub struct TupleExpr {
    pub elements: Vec<Spanned<Expr>>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct RecordExpr {
    pub fields: Vec<Spanned<RecordFieldExpr>>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct RecordFieldExpr {
    pub ident: Spanned<Ident>,
    pub expr: Spanned<Expr>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct BinaryExpr {
    pub lhs: Box<Spanned<Expr>>,
    pub op: Spanned<BinOp>,
    pub rhs: Box<Spanned<Expr>>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct UnaryExpr {
    pub op: Spanned<UnaryOp>,
    pub expr: Box<Spanned<Expr>>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct IndexExpr {
    pub lhs: Box<Spanned<Expr>>,
    pub index: Box<Spanned<Expr>>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct IfExpr {
    pub cond: Box<Spanned<Expr>>,
    pub then: Box<Spanned<Expr>>,
    pub else_: Box<Spanned<Expr>>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct WhileExpr {
    pub cond: Box<Spanned<Expr>>,
    pub body: Box<Spanned<Expr>>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct ForExpr {
    pub binding: Spanned<Binding>,
    pub iter: Box<Spanned<Expr>>,
    pub body: Box<Spanned<Expr>>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct LoopExpr {
    pub body: Box<Spanned<Expr>>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct ReturnExpr {
    pub expr: Box<Spanned<Expr>>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct LetExpr {
    pub ident: Spanned<Ident>,
    pub ret_ty: Option<Spanned<Type>>,
    pub expr: Box<Spanned<Expr>>,
    pub _in: Box<Spanned<Expr>>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct Binding {
    pub ident: Spanned<Ident>,
    pub ty: Option<Spanned<Ident>>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct ModItem {
    pub attrs: Spanned<Attributes>,
    pub vis: Spanned<Vis>,
    pub ident: Spanned<Ident>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct UseItem {
    pub attrs: Spanned<Attributes>,
    pub vis: Spanned<Vis>,
    pub path: Spanned<Ident>,
}

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub enum Ident {
    Ok(SmolStr),
    Err,
}

// Pretty printing implementations.

impl fmt::Display for Ident {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Ident::Ok(str) => write!(f, "{str}"),
            Ident::Err => write!(f, "ERR"),
        }
    }
}

// TODO: precedence aware pretty-printing
impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Path(Spanned(PathType { path }, _)) => {
                for ident in path {
                    write!(f, "{ident}")?;
                }
            }
            Type::Fn(Spanned(FnType { arg_ty, ret_ty }, _)) => write!(f, "({arg_ty} -> {ret_ty})")?,
            Type::Tuple(Spanned(TupleType { fields }, _)) => {
                write!(f, "(")?;
                for field in fields {
                    write!(f, "{field}")?;
                }
                write!(f, ")")?;
            }
            Type::Constructed(Spanned(ConstructedType { constructor, arg }, _)) => {
                write!(f, "({constructor} {arg})")?
            }
            Type::Param(Spanned(TypeParam { ident }, _)) => write!(f, "'{ident}")?,
            Type::Err => write!(f, "ERR")?,
        }
        Ok(())
    }
}
