//! Symbol resolution.

pub mod scope;

use std::collections::{HashMap, HashSet};

use la_arena::Idx;

use crate::ast::visitor::{walk_item, Visitor};
use crate::ast::{ExternFnItem, FnItem, Item, Root};
use crate::span::{Span, Spanned};

use self::scope::Scope;

use super::{ModPath, ParseResult};

/// A refernece to a [`SymbolData`] allocated inside an arena.
pub type SymbolId = Idx<SymbolData>;

/// A reference to a [`TypeSymbol`] allocated inside an arena.
pub type TypeId = Idx<TypeData>;

/// Represents any kind of symbol.
#[derive(Debug)]
pub struct SymbolData {
    /// The identifier of the symbol.
    pub ident: Spanned<String>,
    /// The actual information of the symbol.
    pub kind: SymbolKind,
    /// The declaration span.
    pub span: Span,
}

#[derive(Debug)]
pub enum SymbolKind {
    Fn(FnSymbol),
    Type(TypeId),
    Mod(ModSymbol),
    /// A local variable inside a function body.
    /// Since those symbols are not visible from outside of the function body in which they are
    /// declared in, these are only resolved after all global symbols are collected.
    Let(LetSymbol),
    /// A dummy value. This is because everything in the global scope can reference anything else
    /// in the global scope. We must therefore collect all the symbol identifiers first before
    /// resolving their bodies.
    Tmp,
}

#[derive(Debug)]
pub struct TypeData {
    pub ident: Spanned<String>,
    pub kind: TypeKind,
    pub span: Span,
}

/// A symbol that is a type.
#[derive(Debug)]
pub enum TypeKind {
    Struct(StructSymbol),
    Enum(EnumSymbol),
    /// A dummy value.
    Tmp,
}

#[derive(Debug)]
pub enum ResolvedType {
    Id(TypeId),
    /// Type could not be resolved.
    Error,
}

#[derive(Debug)]
pub struct FnSymbol {
    pub param_ty: Vec<ResolvedType>,
}

#[derive(Debug)]
pub struct StructSymbol {
    pub fields: HashMap<String, ResolvedType>,
}

#[derive(Debug)]
pub struct EnumSymbol {
    pub variants: HashSet<String>,
}

#[derive(Debug)]
pub struct ModSymbol {
    pub symbols: HashMap<String, SymbolId>,
}

#[derive(Debug)]
pub struct LetSymbol {
    pub ident: String,
    pub ty: TypeId,
}

/// Resolves symbols. Also performs type-checking as this is needed for resolving fields/methods.
#[derive(Debug, Default)]
pub struct SymbolResolution {
    pub symbol_arena: la_arena::Arena<SymbolData>,
    pub type_arena: la_arena::Arena<TypeData>,
}

impl SymbolResolution {
    pub fn new() -> Self {
        Self::default()
    }

    /// Resolve all the top-level items. Returns a [`ModSymbol`] containing all the resolved items.
    pub fn resolve_top_level_items(&mut self, parse_result: &ParseResult) -> ModSymbol {
        let mut pass = ModSymbolResolutionPass {
            symbol_arena: &mut self.symbol_arena,
            type_arena: &mut self.type_arena,
            top_level_symbols: HashMap::new(),
            parse_result,
            mod_path: ModPath::entry(),
        };
        pass.visit_root(parse_result.get_entry_root());
        ModSymbol {
            symbols: pass.top_level_symbols,
        }
    }
}

/// Resovles symbols in a `mod`, i.e. find out what each identifier is refering to.
struct ModSymbolResolutionPass<'a> {
    symbol_arena: &'a mut la_arena::Arena<SymbolData>,
    type_arena: &'a mut la_arena::Arena<TypeData>,
    top_level_symbols: HashMap<String, SymbolId>,
    parse_result: &'a ParseResult,
    mod_path: ModPath,
}

impl<'a> Visitor for ModSymbolResolutionPass<'a> {
    fn visit_item(&mut self, item: &Spanned<Item>) {
        // Collect all the top-level symbols.
        match &**item {
            Item::Fn(Spanned(fn_item, span)) => self.top_level_symbols.insert(
                fn_item.ident.to_string(),
                self.symbol_arena.alloc(SymbolData {
                    ident: fn_item.ident.clone(),
                    kind: SymbolKind::Tmp,
                    span: *span,
                }),
            ),
            Item::ExternFn(Spanned(extern_fn_item, span)) => self.top_level_symbols.insert(
                extern_fn_item.ident.to_string(),
                self.symbol_arena.alloc(SymbolData {
                    ident: extern_fn_item.ident.clone(),
                    kind: SymbolKind::Tmp,
                    span: *span,
                }),
            ),
            Item::Struct(Spanned(struct_item, span)) => self.top_level_symbols.insert(
                struct_item.ident.to_string(),
                self.symbol_arena.alloc(SymbolData {
                    ident: struct_item.ident.clone(),
                    kind: SymbolKind::Tmp,
                    span: *span,
                }),
            ),
            Item::Mod(Spanned(mod_item, span)) => self.top_level_symbols.insert(
                mod_item.ident.to_string(),
                self.symbol_arena.alloc(SymbolData {
                    ident: mod_item.ident.clone(),
                    kind: SymbolKind::Tmp,
                    span: *span,
                }),
            ),
            Item::Use(_) => todo!(),
        };

        walk_item(self, item);
    }

    fn visit_root(&mut self, root: &Root) {
        // Collect all top-level symbols.
        let mut items = Vec::new();
        for item in &root.items {
            self.visit_item(item);
            // FIXME: do not use this hack to get SymbolId from visit_item.
            let symbol_id = self
                .symbol_arena
                .iter()
                .last()
                .expect("visit_item should create a new SymbolId")
                .0;
            items.push((item, symbol_id));
        }

        // Fill out the SymbolKind::Tmp placeholders.
        self.alloc_type_items(&items);

        let global: HashMap<_, _> = self
            .symbol_arena
            .iter()
            .map(|symbol| (symbol.1.ident.to_string(), symbol.0))
            .collect();
        let scope = Scope {
            global,
            stack: Vec::new(),
        };

        self.finish_top_level_items(&items, &scope);
    }
}

impl<'a> ModSymbolResolutionPass<'a> {
    /// Allocate a new [`TypeData`] for all items that are types.
    fn alloc_type_items(&mut self, items: &[(&Spanned<Item>, SymbolId)]) {
        // Replace all type items with temporary type.
        for &(item, symbol_id) in items {
            match &**item {
                Item::Struct(_) => {
                    let symbol_data = &mut self.symbol_arena[symbol_id];
                    let type_id = self.type_arena.alloc(TypeData {
                        ident: symbol_data.ident.clone(),
                        kind: TypeKind::Tmp,
                        span: symbol_data.span,
                    });
                    symbol_data.kind = SymbolKind::Type(type_id);
                }
                _ => {}
            }
        }
    }

    // Replace all tmp placeholders.
    fn finish_top_level_items(&mut self, items: &[(&Spanned<Item>, SymbolId)], scope: &Scope) {
        for &(item, symbol_id) in items {
            match &**item {
                Item::Fn(Spanned(FnItem { args, .. }, _))
                | Item::ExternFn(Spanned(ExternFnItem { args, .. }, _)) => {
                    let param_ty = args
                        .args
                        .iter()
                        .map(|x| {
                            let Some(ty) = &x.ty else {
                                eprintln!("ommited type not allowed in fn declaration");
                                return ResolvedType::Error;
                            };
                            let Some(symbol) = self.resolve_ident(scope, ty) else {
                                eprintln!("could not find type {}", ty.as_str());
                                return ResolvedType::Error;
                            };

                            if let SymbolKind::Type(ty) = &symbol.kind {
                                ResolvedType::Id(*ty)
                            } else {
                                eprintln!("symbol is not a type"); // FIXME: implement proper diagnostics
                                ResolvedType::Error
                            }
                        })
                        .collect();
                    self.symbol_arena[symbol_id].kind = SymbolKind::Fn(FnSymbol { param_ty })
                }
                Item::Struct(Spanned(struct_item, _)) => {
                    let fields = struct_item
                        .fields
                        .iter()
                        .map(|x| {
                            let Some(symbol) = self.resolve_ident(scope, &**x.ty) else {
                                eprintln!("could not find type {}", x.ty.as_str());
                                return (x.ident.to_string(), ResolvedType::Error);
                            };

                            let ty = if let SymbolKind::Type(ty) = &symbol.kind {
                                ResolvedType::Id(*ty)
                            } else {
                                eprintln!("symbol is not a type"); // FIXME: implement proper diagnostics
                                ResolvedType::Error
                            };
                            (x.ident.to_string(), ty)
                        })
                        .collect();
                    let type_id = match self.symbol_arena[symbol_id].kind {
                        SymbolKind::Type(type_id) => type_id,
                        _ => unreachable!("SymbolKind should be a Type"),
                    };
                    self.type_arena[type_id].kind = TypeKind::Struct(StructSymbol { fields });
                }
                Item::Mod(Spanned(mod_item, _)) => {
                    // Recursively create a new ModSymbolResolutionPass.
                    let mod_path = self.mod_path.clone().extend(mod_item.ident.to_string());
                    let file_id = self
                        .parse_result
                        .mod_path_map
                        .get(&mod_path)
                        .expect("mod should already be parsed");
                    let root = &self.parse_result.files[file_id].ast;
                    let mut pass = ModSymbolResolutionPass {
                        symbol_arena: &mut self.symbol_arena,
                        type_arena: &mut self.type_arena,
                        top_level_symbols: HashMap::new(),
                        parse_result: self.parse_result,
                        mod_path,
                    };
                    pass.visit_root(root);
                    self.symbol_arena[symbol_id].kind = SymbolKind::Mod(ModSymbol {
                        symbols: pass.top_level_symbols,
                    });
                }
                Item::Use(_) => todo!(),
            }
        }
    }

    fn resolve_ident(&self, scope: &Scope, ident: &str) -> Option<&SymbolData> {
        // Check stack first.
        for frame in scope.stack.iter().rev() {
            if *self.symbol_arena[frame.symbol].ident == ident {
                return Some(&self.symbol_arena[frame.symbol]);
            }
        }

        // If not found, check global scope.
        scope.global.get(ident).map(|x| &self.symbol_arena[*x])
    }
}
