use std::collections::HashMap;

use super::SymbolId;

/// Keeps track of all symbols that are in scope.
pub struct Scope {
    /// The current global scope, indexed by ident.
    pub global: HashMap<String, SymbolId>,
    /// The stack of scopes.
    pub stack: Vec<ScopeFrame>,
}

pub struct ScopeFrame {
    pub symbol: SymbolId,
}
