use std::fmt;

/// A span of text in a source file.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Span {
    /// The index of the first character in the span.
    pub start: usize,
    /// The index of the first character after the span.
    pub end: usize,
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
