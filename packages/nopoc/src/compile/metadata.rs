use std::fmt;

use crate::ast::{Item, Root, Vis};

use super::ModPath;

pub struct Symbol {
    pub mod_path: ModPath,
    pub ident: String,
}

impl fmt::Debug for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.mod_path.0.is_empty() {
            write!(f, "Symbol@\"{}\"", self.ident)
        } else {
            write!(f, "Symbol@\"{}.{}\"", self.mod_path, self.ident)
        }
    }
}

#[derive(Debug, Default)]
pub struct PackageMetadata {
    /// A list of all public symbols.
    pub symbols: Vec<Symbol>,
}

impl PackageMetadata {
    pub fn extract_from_ast(&mut self, mod_path: ModPath, root: &Root) {
        for item in &root.items {
            let vis = match &**item {
                Item::Fn(x) => x.vis,
                Item::Struct(x) => x.vis,
                Item::Mod(x) => x.vis,
                Item::Use(x) => x.vis,
            };

            if *vis == Vis::Pub {
                let symbol = match &**item {
                    Item::Fn(x) => &x.ident,
                    Item::Struct(x) => &x.ident,
                    Item::Mod(x) => &x.path,
                    Item::Use(_) => todo!("pub use"),
                };
                self.symbols.push(Symbol {
                    mod_path: mod_path.clone(),
                    ident: symbol.to_string(),
                });
            }
        }
    }
}
