use std::collections::HashMap;
use std::fmt;
use std::path::{Path, PathBuf};

#[derive(Debug)]
pub enum FileDesc {
    Path(PathBuf),
    Virtual { name: String, source: String },
}

#[derive(Debug, Default)]
pub struct FileIdMap {
    map: HashMap<FileId, FileDesc>,
    /// The id for the next file.
    counter: u16,
}

impl FileIdMap {
    pub fn new() -> Self {
        Self::default()
    }

    fn new_id(&mut self) -> FileId {
        let id = FileId(self.counter);
        self.counter += 1;
        id
    }

    pub fn insert_new_file(&mut self, path: PathBuf) -> FileId {
        let id = self.new_id();
        self.map.insert(id, FileDesc::Path(path));
        id
    }

    /// Create a new virtual file. If a virtual file already exists, replaces it.
    pub fn create_virtual_file(&mut self, name: &str, source: String) -> FileId {
        let id = self.new_id();
        self.map.insert(
            id,
            FileDesc::Virtual {
                name: name.to_string(),
                source,
            },
        );
        id
    }

    pub fn is_virtual(&self, id: FileId) -> bool {
        matches!(self.map[&id], FileDesc::Virtual { .. })
    }

    /// Get the path of the file. If the file is a virtual file, then this panics.
    #[track_caller]
    pub fn get_file_path(&self, id: FileId) -> &Path {
        match &self.map[&id] {
            FileDesc::Path(path) => path,
            _ => panic!("{id:?} references a virtual file"),
        }
    }

    pub fn get_file_display(&self, id: FileId) -> String {
        match &self.map[&id] {
            FileDesc::Path(path) => path.display().to_string(),
            FileDesc::Virtual { name, .. } => name.clone(),
        }
    }

    pub fn get_virtual_source(&self, id: FileId) -> &str {
        match &self.map[&id] {
            FileDesc::Path(_) => panic!("{id:?} references a real file"),
            FileDesc::Virtual { source, .. } => source
        }
    }
}

/// An unique identifier for every file in the current package.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FileId(pub u16);

impl FileId {
    /// A dummy file id that should only be used for testing purposes. All other file ids should be
    /// generated by a file id map.
    pub const DUMMY: FileId = FileId(u16::MAX);
}

/// A span of text in a source file.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Span {
    /// The index of the first character in the span.
    pub start: u32,
    /// The index of the first character after the span.
    pub end: u32,
    /// The file in which this span lives.
    pub file_id: FileId,
}

impl Span {
    /// Crete a dummy span. This is used notably as the span for the identifier of the very most
    /// top-level module of a package.
    pub fn dummy(file_id: FileId) -> Self {
        Self {
            start: 0,
            end: 0,
            file_id,
        }
    }
}

impl fmt::Debug for Span {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}..{}", self.start, self.end)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Spanned<T>(pub T, pub Span);

impl<T: fmt::Debug> fmt::Debug for Spanned<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({}..{}) ", self.1.start, self.1.end)?;
        self.0.fmt(f)
    }
}

impl<T> std::ops::Deref for Spanned<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
impl<T> std::ops::DerefMut for Spanned<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

pub fn spanned<T>(span: Span, node: T) -> Spanned<T> {
    Spanned(node, span)
}

impl<T> Spanned<T> {
    /// Get the unspanned node.
    pub fn unspan(self) -> T {
        self.0
    }

    pub fn respan(self, span: Span) -> Self {
        spanned(span, self.0)
    }

    pub fn span(&self) -> Span {
        self.1
    }
}

/// Used for diagnostics.
pub trait GetSpan {
    fn span(&self) -> Span;
}

impl<T> GetSpan for Spanned<T> {
    fn span(&self) -> Span {
        self.1
    }
}

impl GetSpan for Span {
    fn span(&self) -> Span {
        *self
    }
}
