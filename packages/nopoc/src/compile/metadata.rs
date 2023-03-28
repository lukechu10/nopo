use std::fmt;

use la_arena::Arena;

use crate::ast::{Item, Root, Vis};

use super::ModPath;

/// Metadata about a symbol.
///
/// This includes the kind of the symbol (function, struct, etc...), the visibility, the identifier,
/// and the absolute path.
///
/// This should be allocated in an arena since symbols can reference each other and also themselves.
pub struct SymbolMeta {
    pub kind: SymbolKind,
    pub vis: Vis,
    pub mod_path: ModPath,
    pub ident: String,
}

impl fmt::Debug for SymbolMeta {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.vis == Vis::Pub {
            write!(f, "pub ")?;
        } else {
            write!(f, "prv ")?;
        }
        write!(f, "Symbol@{}", self.kind)?;
        if self.mod_path.0.is_empty() {
            write!(f, "\"{}\"", self.ident)
        } else {
            write!(f, "\"{}.{}\"", self.mod_path, self.ident)
        }
    }
}

pub enum SymbolKind {
    Fn,
    Struct,
}

impl fmt::Display for SymbolKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SymbolKind::Fn => write!(f, "fn"),
            SymbolKind::Struct => write!(f, "struct"),
        }
    }
}

#[derive(Debug, Default)]
pub struct PackageMetadata {
    /// A list of all symbols in this package.
    pub arena: Arena<SymbolMeta>,
}

#[derive(Debug, Default)]
pub struct ModuleMetadata {}

impl PackageMetadata {
    pub fn extract_from_ast(&mut self, mod_path: ModPath, root: &Root) {
        for item in &root.items {
            let vis = *match &**item {
                Item::Fn(x) => x.vis,
                Item::ExternFn(x) => x.vis,
                Item::Struct(x) => x.vis,
                Item::Mod(x) => x.vis,
                Item::Use(x) => x.vis,
            };

            let symbol = match &**item {
                Item::Fn(x) => &x.ident,
                Item::ExternFn(x) => &x.ident,
                Item::Struct(x) => &x.ident,
                Item::Mod(x) => &x.path,
                Item::Use(_) => {
                    if vis == Vis::Pub {
                        todo!("pub use");
                    } else {
                        // TODO
                        ""
                    }
                }
            };
            let kind = match &**item {
                Item::Fn(_) | Item::ExternFn(_) => SymbolKind::Fn,
                Item::Struct(_) | Item::Mod(_) => SymbolKind::Struct,
                _ => return,
            };
            self.arena.alloc(SymbolMeta {
                kind,
                vis,
                mod_path: mod_path.clone(),
                ident: symbol.to_string(),
            });
        }
    }
}
