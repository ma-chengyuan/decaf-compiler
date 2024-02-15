use std::fmt;
use std::rc::Rc;

/// Represents a source file and its content.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Source {
    pub filename: String,
    pub content: String,
}

impl fmt::Display for Source {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.filename)
    }
}

/// Represents a location in a source file.
#[derive(Debug, Clone)]
pub struct Location {
    pub source: Rc<Source>,
    pub offset: usize,
    pub line: usize,
    pub column: usize,
}

impl fmt::Display for Location {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}:{}", self.source, self.line, self.column)
    }
}

/// Represents a span in a source file.
/// TODO: enforce that start and end point to the same source.
#[derive(Debug, Clone)]
pub struct Span {
    /// The start location of the span.
    pub start: Location,
    /// The end location of the span (exclusive).
    pub end: Location,
}

impl fmt::Display for Span {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}-{}", self.start, self.end)
    }
}

/// A spanned value, directly convertible from a parsed token.
#[derive(Clone)]
pub struct Spanned<T> {
    pub inner: T,
    pub span: Span,
}

impl<T: fmt::Debug> fmt::Debug for Spanned<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.inner)
    }
}
