//! Symbol resolution and type-checking.
//!
//! This happens in phases:
//!
//! # Phase 1
//! Go through the module and collect the identifiers of all let and type items.
//!
//! # Phase 2
//! Now that we know all the names of all the types, we can resolve the bodies of the types
//! themselves.
//!
//! # Phase 3
//! Now that we know all the bodies of all the types, we can finally resolve the bodies of the let
//! items.

pub mod scope;

use std::collections::{HashMap, HashSet};

use la_arena::Idx;

use crate::ast::visitor::{walk_item, Visitor};
use crate::ast::{Item, ItemId, LetItem, Root};
use crate::span::{Span, Spanned};

use self::scope::Scope;

use super::{ModPath, ParseResult};

/// Phase 1: Collect names of all items in module.
#[derive(Debug)]
pub struct TypeSymbol {
    pub ident: Spanned<String>,
    pub id: ItemId,
}
#[derive(Debug)]
pub struct LetSymbol {
    pub ident: Spanned<String>,
    pub id: ItemId,
}
pub type TypeSymbolId = Idx<TypeSymbol>;
pub type LetSymbolId = Idx<LetSymbol>;

/// Phase 2: Resolve type contents.
#[derive(Debug)]
pub struct TypeData {
    pub ident: Spanned<String>,
    pub kind: TypeKind,
    pub span: Span,
}
#[derive(Debug)]
pub enum TypeKind {
    Record(RecordSymbol),
    Adt(AdtSymbol),
}
#[derive(Debug)]
pub struct RecordSymbol {
    pub fields: HashMap<String, ResolvedType>,
}
#[derive(Debug)]
pub struct AdtSymbol {
    pub variants: HashSet<String>,
}
pub type TypeId = Idx<TypeData>;

/// Phase 3: Resolve let bodies.
#[derive(Debug)]
pub struct LetData {
    pub ident: Spanned<String>,
    pub span: Span,
}

#[derive(Debug)]
pub enum ResolvedType {
    Id(TypeId),
    /// Type could not be resolved.
    Error,
}

#[derive(Debug)]
pub struct ModSymbol {
    pub symbols: HashMap<String, SymbolId>,
}

#[derive(Debug)]
pub struct LetSymbol {
    pub ident: String,
    pub param_ty: Vec<ResolvedType>,
    pub ret_ty: Option<ResolvedType>,
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
    fn visit_item(&mut self, idx: ItemId, item: &Spanned<Item>) {
        // Collect all the top-level symbols.
        match &**item {
            Item::Let(Spanned(let_item, span)) => self.top_level_symbols.insert(
                let_item.ident.to_string(),
                self.symbol_arena.alloc(SymbolData {
                    ident: let_item.ident.clone(),
                    kind: SymbolKind::Tmp,
                    span: *span,
                }),
            ),
            Item::Type(Spanned(type_item, span)) => self.top_level_symbols.insert(
                type_item.ident.to_string(),
                self.symbol_arena.alloc(SymbolData {
                    ident: type_item.ident.clone(),
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
                Item::Type(_) => {
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
                Item::Let(Spanned(
                    LetItem {
                        ident,
                        params,
                        ret_ty,
                        ..
                    },
                    _,
                )) => {
                    let param_ty = params
                        .iter()
                        .map(|x| {
                            let Some(ty) = &x.ty else {
                                eprintln!("ommited type not allowed in top-level let declaration");
                                return ResolvedType::Error;
                            };
                            let Some(symbol) = self.resolve_ident(scope, ty) else {
                                eprintln!("could not find type {ty:?}");
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
                    let ret_ty = {
                        if let Some(ret_ty) = ret_ty {
                            if let Some(ret_ty) = self.resolve_ident(scope, ret_ty) {
                                if let SymbolKind::Type(ret_ty) = &ret_ty.kind {
                                    Some(ResolvedType::Id(*ret_ty))
                                } else {
                                    eprintln!("symbol is not a type");
                                    Some(ResolvedType::Error)
                                }
                            } else {
                                eprintln!("could not find type {ret_ty:?}");
                                Some(ResolvedType::Error)
                            }
                        } else {
                            None
                        }
                    };
                    self.symbol_arena[symbol_id].kind = SymbolKind::Let(LetSymbol {
                        ident: ident.to_string(),
                        param_ty,
                        ret_ty,
                    });
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
                    self.type_arena[type_id].kind = TypeKind::Record(RecordSymbol { fields });
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
