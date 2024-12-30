//! Pass to generate an unique type for every module.

use std::collections::HashMap;
use std::path::PathBuf;

use nopo_diagnostics::span::Spanned;
use nopo_parser::ast::{Ident, LetId, LetItem, Root, TypeDef, TypeId, TypeItem, Vis};
use nopo_parser::visitor::{walk_root, Visitor};

use crate::db::{Db, RecordSymbol, ResolvedType};

/// A pass for generating an unique type for every module.
///
/// Writes the generated type to the [`Db`] struct indexed by the module path.
pub struct GenModuleType<'a> {
    /// The resulting type of the moduke.
    ty: RecordSymbol,
    /// Counter used for indices of the fields in the resulting record type.
    counter: u32,
    /// The path of the module file.
    path: PathBuf,
    db: &'a mut Db,
}

impl<'a> GenModuleType<'a> {
    pub fn new(path: PathBuf, db: &'a mut Db) -> Self {
        Self {
            ty: RecordSymbol {
                fields: HashMap::new(),
            },
            counter: 0,
            path,
            db,
        }
    }

    /// Add a new symbol to be exported from the module. Write down the symbol identifier and
    /// type.
    fn add_symbol(&mut self, ident: Ident, ty: ResolvedType) {
        self.ty.fields.insert(ident, (ty, self.counter));
        self.counter += 1;
    }
}

impl Visitor for GenModuleType<'_> {
    fn visit_root(&mut self, root: &Root) {
        walk_root(self, root);

        self.db
            .module_types_map
            .insert(self.path.clone(), self.ty.clone());
    }

    fn visit_type_item(&mut self, idx: TypeId, item: &Spanned<TypeItem>) {
        if *item.vis == Vis::Pub {
            self.add_symbol(item.ident.as_ref().clone(), ResolvedType::Data(idx));

            // If the item is a ADT, add all the data constructors as exported symbols.
            if let TypeDef::Adt(record_def) = &*item.def {
                for data_constructor in &record_def.data_constructors {
                    let binding = &self.db.bindings_map.data_constructors[data_constructor];
                    let ty = &self.db.binding_types_map[binding];
                    self.add_symbol(data_constructor.ident.as_ref().clone(), ty.clone());
                }
            }
        }
    }

    fn visit_let_item(&mut self, _idx: LetId, item: &Spanned<LetItem>) {
        if *item.vis == Vis::Pub {
            let binding = &self.db.bindings_map.let_items[item];
            let ty = &self.db.binding_types_map[binding];
            self.add_symbol(item.ident.as_ref().clone(), ty.clone());
        }
    }
}
