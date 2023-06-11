//! Type unification / type inference.
//!
//! We want to infer the type of every binding.

use la_arena::ArenaMap;
use nopo_diagnostics::span::Spanned;

use crate::ast::visitor::Visitor;
use crate::ast::{TypeId, TypeItem, Root};

use super::resolution::{BindingId, ResolveLetContents, ResolvedType};

#[derive(Debug)]
pub struct UnifyTypes {
    /// Data from symbol resolution.
    resolution: ResolveLetContents,
    binding_types_map: ArenaMap<BindingId, ResolvedType>,
}

impl UnifyTypes {
    pub fn new(resolution: ResolveLetContents) -> Self {
        Self {
            resolution,
            binding_types_map: ArenaMap::new(),
        }
    }
}

impl Visitor for UnifyTypes {
    fn visit_root(&mut self, root: &Root) {
        // Visit type items first since we know the types of all the data constructors.
        for (idx, item) in root.type_items.iter() {
            self.visit_type_item(idx, item)
        }
    }

    fn visit_type_item(&mut self, _idx: TypeId, item: &Spanned<TypeItem>) {}
}
