use std::collections::HashMap;
use std::ops::{Index, IndexMut};

/// A map from AST nodes to `T`.
///
/// This internally relies on the fact that AST nodes are never moved in memory so we can use the
/// pointer value as a key in the lookup table.
#[derive(Debug)]
pub struct NodeMap<N, T> {
    map: HashMap<*const N, T>,
}

impl<N, T> NodeMap<N, T> {
    /// Insert a new value for the given AST node.
    pub fn insert(&mut self, key: &N, value: T) -> Option<T> {
        self.map.insert(key as *const N, value)
    }

    /// Get the value for the [`N`].
    pub fn get(&mut self, key: &N) -> Option<&T> {
        self.map.get(&(key as *const N))
    }
}

impl<N, T> Index<&N> for NodeMap<N, T> {
    type Output = T;

    fn index(&self, index: &N) -> &Self::Output {
        &self.map[&(index as *const N)]
    }
}

impl<N, T> IndexMut<&N> for NodeMap<N, T> {
    fn index_mut(&mut self, index: &N) -> &mut Self::Output {
        self.map.get_mut(&(index as *const N)).unwrap()
    }
}

impl<N, T> Default for NodeMap<N, T> {
    fn default() -> Self {
        Self {
            map: HashMap::new(),
        }
    }
}
