//! Pass to generate an unique type for every module.

use std::collections::HashMap;
use std::path::PathBuf;

use nopo_diagnostics::span::Spanned;
use nopo_parser::ast::{Ident, LetId, LetItem, Root, TypeDef, TypeId, TypeItem, Vis};
use nopo_parser::visitor::{walk_root, Visitor};

use crate::db::{Db, RecordSymbol, ResolvedType};

pub struct GenModuleType<'a> {
    ty: RecordSymbol,
    counter: u32,
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

    fn add_symbol(&mut self, ident: Ident, ty: ResolvedType) {
        self.ty.fields.insert(ident, (ty, self.counter));
        self.counter += 1;
    }
}

impl<'a> Visitor for GenModuleType<'a> {
    fn visit_root(&mut self, root: &Root) {
        walk_root(self, root);

        self.db
            .module_types_map
            .insert(self.path.clone(), self.ty.clone());
    }

    fn visit_type_item(&mut self, idx: TypeId, item: &Spanned<TypeItem>) {
        if *item.vis == Vis::Pub {
            self.add_symbol(item.ident.as_ref().clone(), ResolvedType::Ident(idx));

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
