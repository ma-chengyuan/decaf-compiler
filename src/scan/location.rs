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

impl Span {
    pub fn merge(&self, other: &Span) -> Span {
        assert_eq!(self.start.source, other.start.source);
        assert_eq!(self.end.source, other.end.source);
        let start = if self.start.offset < other.start.offset {
            self.start.clone()
        } else {
            other.start.clone()
        };
        let end = if self.end.offset > other.end.offset {
            self.end.clone()
        } else {
            other.end.clone()
        };
        Span { start, end }
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
