//! Stores all the information needed for each pass. This allows easy sharing of data between
//! passes.

use std::collections::HashMap;
use std::fmt;
use std::path::PathBuf;

use la_arena::{Arena, ArenaMap, Idx};
use nopo_diagnostics::span::{Span, Spanned};
use nopo_diagnostics::Diagnostics;
use nopo_parser::ast::{
    DataConstructor, Expr, Ident, IdentExpr, LambdaParam, LetExpr, LetItem, MacroExpr, Param,
    Pattern, RecordFieldExpr, Type, TypeId, TypeItem, TypeParam,
};
use smol_str::SmolStr;

use crate::map::NodeMap;

#[derive(Debug)]
pub struct Db {
    pub bindings: Arena<Binding>,
    pub data_defs: Arena<DataDef>,

    // `CollectModules`
    /// Mapping from import expressions to the canonical path of the module.
    pub module_imports_map: NodeMap<MacroExpr, PathBuf>,

    // `ResolveSymbols`
    /// Mapping from identifiers/let-items/let-exprs etc. to their bindings.
    pub bindings_map: BindingsMap,
    /// Mapping from types/type-items to their type data.
    pub types_map: TypesMap,

    // `UnifyTypes`
    /// Contains the type of all the bindings.
    pub binding_types_map: HashMap<BindingId, ResolvedType>,

    // `TypeCheckRecords`
    /// Map from identifiers to the field position in the record.
    pub record_field_map: NodeMap<Expr, u32>,
    /// Map from record field expressions to the field position in the record.
    pub record_expr_field_map: NodeMap<RecordFieldExpr, u32>,

    // `GenModuleTypes`
    /// Map from module (specified by a path) to the type of the module.
    pub module_types_map: HashMap<PathBuf, RecordSymbol>,

    pub diagnostics: Diagnostics,
}

impl Db {
    pub fn new(diagnostics: Diagnostics) -> Self {
        Self {
            data_defs: Arena::default(),
            bindings: Arena::default(),
            module_imports_map: NodeMap::default(),
            bindings_map: BindingsMap::default(),
            types_map: TypesMap::default(),
            binding_types_map: HashMap::default(),
            record_field_map: NodeMap::default(),
            record_expr_field_map: NodeMap::default(),
            module_types_map: HashMap::default(),
            diagnostics,
        }
    }
}

/// Represents a symbol that can be referred to by an identifier.
#[derive(Debug)]
pub struct Binding {
    pub ident: Ident,
    pub is_data_constructor: bool,
    /// The number of arguments that is expected for this data-constructor.
    pub data_constructor_args: usize,
    /// The tag of sum type constructed by the data-constructor.
    pub data_constructor_tag: u32,
}
pub type BindingId = Idx<Binding>;

impl Binding {
    /// Create a new binding that is __NOT__ a data-constructor.
    pub fn new(ident: Ident) -> Self {
        Self {
            ident,
            is_data_constructor: false,
            data_constructor_args: 0, // TODO: do not have dummy field.
            data_constructor_tag: 0,  // TODO: above
        }
    }

    /// Create a new binding that is a data-constructor.
    pub fn new_data_constructor(ident: Ident, args: usize, tag: u32) -> Self {
        Self {
            ident,
            is_data_constructor: true,
            data_constructor_args: args,
            data_constructor_tag: tag,
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum ResolvedBinding {
    Ok(BindingId),
    Err,
}

impl ResolvedBinding {
    pub fn unwrap(self) -> BindingId {
        match self {
            ResolvedBinding::Ok(id) => id,
            ResolvedBinding::Err => panic!("unwrapping an errored resolved binding"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeSymbol {
    Path(Ident),
    Param(Ident),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ResolvedType {
    /// Type of a data-definition. This can be either an ADT or a record.
    /// Holds the definition site of the data type.
    Data(TypeId),
    /// Type of a tuple.
    Tuple(Vec<Self>),
    /// Modules have special types because they are only inhabited by the value of the module
    /// itself. It is also impossible to explicitly refer to a module type.
    Module(PathBuf),
    Fn {
        arg: Box<Self>,
        ret: Box<Self>,
    },
    Constructed {
        constructor: Box<Self>,
        arg: Box<Self>,
    },
    // Built-in types.
    Bool,
    Int,
    Float,
    String,
    Char,
    /// A type parameter.
    ///
    /// Unlike type variables, these are initially universally quantified, such that constraining
    /// the type param to a specific type is a contradiction (since there is more than a single
    /// type in the domain).
    Param(TypeVar),
    /// A type variable. This can either be free or bound. Type vars can not be explicitly
    /// referenced (TODO: update when inferred types are added).
    ///
    /// Since identifiers cannot start with numbers, automatically generated type vars are always
    /// integers.
    Var(TypeVar),
    /// Universal types.
    /// `'a . f('a)` where `f` is any type potentially containing `'a`.
    ForAll {
        var: TypeVar,
        ty: Box<Self>,
    },
    /// Type could not be resolved.
    Err,
}

pub type TypeVar = SmolStr;

impl ResolvedType {
    /// Create a new resolved type representing a curried function.
    ///
    /// For example, a function with params `a`, `b`, `c` and return value `ret` would become the
    /// type `a -> (b -> (c -> ret))`.
    pub fn new_curried_function(args: &[Self], ret: Self) -> Self {
        match args.split_first() {
            Some((first, rest @ [_, ..])) => Self::Fn {
                arg: Box::new(first.clone()),
                ret: Box::new(Self::new_curried_function(rest, ret)),
            },
            Some((first, _rest @ [])) => Self::Fn {
                arg: Box::new(first.clone()),
                ret: Box::new(ret),
            },
            None => ret,
        }
    }

    /// Uncurries a function.
    pub fn uncurry_function(self) -> (Vec<Self>, Self) {
        match self {
            Self::Fn { arg, ret } => {
                let (mut args, ret) = ret.uncurry_function();
                args.insert(0, *arg);
                (args, ret)
            }
            _ => (Vec::new(), self),
        }
    }

    /// Create a new resolved type representing a curried constructed type.
    ///
    /// For example, a type `foo` with type params `'a`, `'b` would become the type `(foo 'a) 'b`.
    pub fn new_curried_constructed_ty(constructor: Self, args: &[Self]) -> Self {
        match args.split_first() {
            Some((first, rest @ [_, ..])) => Self::new_curried_constructed_ty(
                Self::Constructed {
                    constructor: Box::new(constructor.clone()),
                    arg: Box::new(first.clone()),
                },
                rest,
            ),
            Some((first, _rest @ [])) => Self::Constructed {
                constructor: Box::new(constructor.clone()),
                arg: Box::new(first.clone()),
            },
            None => constructor,
        }
    }

    /// Create a new resolved type referring to a type item.
    pub fn of_type_item(id: TypeId, type_item_map: &ArenaMap<TypeId, DataDef>) -> Self {
        let ty_params = type_item_map[id]
            .ty_params
            .iter()
            .map(|param| Self::Var(param.ident.as_ref().clone().into()))
            .collect::<Vec<_>>();
        Self::new_curried_constructed_ty(Self::Data(id), &ty_params)
    }

    pub fn ident_of_constructed(&self) -> Option<TypeId> {
        match self {
            Self::Data(id) => Some(*id),
            Self::Constructed {
                constructor,
                arg: _,
            } => constructor.ident_of_constructed(),
            _ => None,
        }
    }

    pub fn num_of_constructed(&self) -> usize {
        match self {
            Self::Constructed {
                constructor,
                arg: _,
            } => constructor.num_of_constructed() + 1,
            _ => 0,
        }
    }

    /// Pretty print the type.
    pub fn pretty<'a>(&'a self, map: &'a ArenaMap<TypeId, DataDef>) -> ResolvedTypePretty<'a> {
        ResolvedTypePretty(self, map)
    }
}

/// Pretty printer for [`ResolvedType`].
pub struct ResolvedTypePretty<'a>(&'a ResolvedType, &'a ArenaMap<TypeId, DataDef>);
impl fmt::Display for ResolvedTypePretty<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.0 {
            ResolvedType::Data(id) => write!(f, "{}", self.1[*id].ident)?,
            ResolvedType::Tuple(types) => {
                write!(f, "(")?;
                if let Some(first) = types.first() {
                    write!(f, "{}", first.pretty(self.1))?;
                }
                for ty in types.iter().skip(1) {
                    write!(f, ", {}", ty.pretty(self.1))?;
                }
                write!(f, ")")?;
            }
            ResolvedType::Module(path) => write!(f, "module {{{path:?}}}")?,
            ResolvedType::Fn { arg, ret } => {
                write!(f, "({} -> {})", arg.pretty(self.1), ret.pretty(self.1))?
            }
            ResolvedType::Constructed { constructor, arg } => {
                write!(f, "({} {})", constructor.pretty(self.1), arg.pretty(self.1))?
            }
            ResolvedType::Bool => write!(f, "bool")?,
            ResolvedType::Int => write!(f, "int")?,
            ResolvedType::Float => write!(f, "float")?,
            ResolvedType::String => write!(f, "string")?,
            ResolvedType::Char => write!(f, "char")?,
            ResolvedType::Param(var) => write!(f, "'{var}")?,
            ResolvedType::Var(var) => write!(f, "{{{var}}}")?,
            ResolvedType::ForAll { var, ty } => write!(f, "forall '{var} . {}", ty.pretty(self.1))?,
            ResolvedType::Err => write!(f, "ERR")?,
        }

        Ok(())
    }
}

/// Information about type data.
#[derive(Debug)]
pub struct DataDef {
    pub ident: Spanned<Ident>,
    pub kind: TypeKind,
    pub ty_params: Vec<Spanned<TypeParam>>,
    pub span: Span,
}
#[derive(Debug)]
pub enum TypeKind {
    Record(RecordSymbol),
    Adt(AdtSymbol),
    /// Temporary dummy variable.
    Tmp,
}
impl TypeKind {
    pub fn as_record(&self) -> Option<&RecordSymbol> {
        if let Self::Record(v) = self {
            Some(v)
        } else {
            None
        }
    }

    pub fn as_adt(&self) -> Option<&AdtSymbol> {
        if let Self::Adt(v) = self {
            Some(v)
        } else {
            None
        }
    }
}

#[derive(Debug, Clone)]
pub struct RecordSymbol {
    /// A map from the identifier to the resolved type and the position of the field in the record.
    pub fields: HashMap<Ident, (ResolvedType, u32)>,
}

#[derive(Debug)]
pub struct AdtSymbol {
    pub variants: Vec<AdtVariant>,
}

#[derive(Debug)]
pub struct AdtVariant {
    pub ident: Ident,
    pub types: Vec<ResolvedType>,
}

#[derive(Debug, Default)]
pub struct TypesMap {
    // #[deprecated]
    pub items_by_id: ArenaMap<TypeId, DataDef>,
    pub items: NodeMap<TypeItem, DataDef>,
    pub types: NodeMap<Type, ResolvedType>,
}

#[derive(Debug, Default)]
pub struct BindingsMap {
    /// Mapping from identifiers to their bindings.
    pub idents: NodeMap<IdentExpr, ResolvedBinding>,
    /// Mapping from data-constructors to their bindings. Data-constructors are treated just like
    /// functions.
    pub data_constructors: NodeMap<DataConstructor, BindingId>,
    /// Mapping from let params to their bindings.
    pub params: NodeMap<Param, BindingId>,
    /// Mapping from let items to their bindings.
    pub let_items: NodeMap<LetItem, BindingId>,
    /// Mapping from let expressions to their bindings.
    pub let_exprs: NodeMap<LetExpr, BindingId>,
    /// Mapping from lambda params to their bindings.
    pub lambda_params: NodeMap<LambdaParam, BindingId>,
    /// Mapping from pattern bindings to their bindings.
    pub pattern: NodeMap<Pattern, BindingId>,
    /// Mapping from pattern tags to their bindings.
    pub pattern_tags: NodeMap<Pattern, ResolvedBinding>,
}
