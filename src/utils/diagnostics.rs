#![allow(dead_code)]
//! Enjoy Rust-like diagnostics!

// The code may be crappy and slow, but error-reporting is not on the critical
// path anyways.

use std::{
    collections::{BTreeMap, HashMap},
    rc::Rc,
};

use colored::{Color, ColoredString, Colorize};

use crate::scan::location::{Source, Span};

#[derive(Debug, Clone)]
pub struct DiagnosticItem {
    pub span: Span,
    pub message: String,
    pub color: Option<Color>,
}

#[derive(Debug, Clone)]
pub struct Diagnostic {
    pre_text: String,
    /// Maps from source to line number to items
    items: HashMap<Rc<Source>, BTreeMap<usize, Vec<DiagnosticItem>>>,
    post_text: String,
}

const DIAGONSTIC_LINE_NUMBER_WIDTH: usize = 4;

impl Diagnostic {
    pub fn new() -> Self {
        Self {
            pre_text: Default::default(),
            items: HashMap::new(),
            post_text: Default::default(),
        }
    }

    pub fn with_pre_text(mut self, pre_text: &str) -> Self {
        self.pre_text = pre_text.into();
        self
    }

    pub fn with_post_text(mut self, post_text: &str) -> Self {
        self.post_text = post_text.into();
        self
    }

    pub fn add_item(mut self, mut item: DiagnosticItem) -> Self {
        for span in item.span.per_line().into_iter().rev() {
            let line = span.start().line;
            let items = self
                .items
                .entry(span.start().source.clone())
                .or_default()
                .entry(line)
                .or_default();
            items.push(DiagnosticItem {
                message: std::mem::take(&mut item.message),
                color: item.color,
                span,
            });
            // Sort items by col in ascending order
            items.sort_by_key(|item| item.span.start().column);
        }
        self
    }

    pub fn write(&self, writer: &mut dyn std::io::Write) -> std::io::Result<()> {
        writeln!(writer, "{}", self.pre_text)?;

        let spacing = " ".repeat(DIAGONSTIC_LINE_NUMBER_WIDTH);
        let arrow = "-->".cyan().bold();
        let vertical_bar = "|".cyan().bold();
        let ellipsis = "...".cyan().bold();

        for (source, line_items) in &self.items {
            writeln!(writer, "{}{} {}:", spacing, arrow, source.filename)?;
            let source_str = source.content.iter().collect::<String>();
            let lines = source_str.lines().collect::<Vec<_>>();
            let mut last_line = 0;
            for (line, items) in line_items {
                // Print out a transition from the last line
                if line - last_line == 1 {
                    writeln!(writer, "{} {}", spacing, vertical_bar)?
                } else {
                    writeln!(writer, "{}{}", spacing, ellipsis)?
                }
                last_line = *line;
                // Print out the source line with the line number
                let line_number = format!("{:width$}", line, width = DIAGONSTIC_LINE_NUMBER_WIDTH)
                    .cyan()
                    .bold();
                writeln!(
                    writer,
                    "{} {} {}",
                    line_number,
                    vertical_bar,
                    lines[line - 1]
                )?;
                // Calculate how many lines down the source line it will take to layout all the items.
                // For example, if there are 3 items, 2 of which have non-empty
                // messages, then the layout will be:
                // xxx | source line source line source line
                //     |        ^^^^ ------ ^^^^ ^^^^^^^^^^^ message 0      -> depth 0
                //     |             |                                      -> depth 1
                //     |             message 2                              -> depth 2
                // Items are laid out from right to left.
                let total_depth = items.iter().rev().fold(0, |acc, item| {
                    if item.message.is_empty() {
                        // Empty messages are just a caret, they don't take up
                        // vertical space at all. But non-empty messages to the
                        // left will need to start at at least depth 2 to avoid
                        // running into the caret of this item.
                        acc.max(2)
                    } else {
                        // Non-empty messages take up at # lines + 1 black line
                        // for separation
                        acc + item.message.lines().count() + 1
                    }
                });
                let total_depth = (total_depth - 1).max(1);
                // A temporary buffer to store the elements to be printed.
                // elements[i] = [ (column offset, content) at depth i ]
                let mut elements: Vec<Vec<(/*column offset*/ usize, ColoredString)>> =
                    vec![vec![]; total_depth];
                // The depth, or # lines down from the source line, of the next
                // item with non-empty message
                let mut next_item_depth = 0;
                // Iterate over items from right to left
                for item in items.iter().rev() {
                    // cumulative_height: the depth of the first line of the message
                    // caret_length: the length of the caret, at least 1
                    let caret_length = (item.span.end().column - item.span.start().column).max(1);
                    let color = |s: &str| match item.color {
                        Some(color) => s.color(color),
                        None => s.normal(),
                    };
                    // Compute the caret string and the column offset to start the message
                    let (caret, item_col) = if next_item_depth == 0 || item.message.is_empty() {
                        (
                            // Empirically, Rust seems to use ^ for these kinds
                            // of caret. Not sure if that observation is
                            // correct.
                            color(&"^".repeat(caret_length)).bold(),
                            // Message of the right most item can start just ot
                            // the right of the caret on the same line
                            item.span.start().column + caret_length + 1,
                        )
                    } else {
                        // Message of other non-empty items will need to start
                        // beneath the caret and connect to the caret with a
                        // vertical line, which we draw here.
                        for element in elements.iter_mut().take(next_item_depth).skip(1) {
                            element.push((item.span.start().column, color("|").bold()));
                        }
                        (
                            color(&"-".repeat(caret_length)).bold(),
                            item.span.start().column, // The message and the vertical line are left-aligned with the caret (for Rust's diagnostics at least)
                        )
                    };
                    elements[0].push((item.span.start().column, caret));
                    // Same as the computation for total_depth
                    if item.message.is_empty() {
                        next_item_depth = next_item_depth.max(2);
                    } else {
                        for line in item.message.lines() {
                            let line = color(line).bold();
                            elements[next_item_depth].push((item_col, line));
                            next_item_depth += 1;
                        }
                        next_item_depth += 1;
                    }
                }
                for mut element in elements {
                    element.sort_by_key(|(col, _)| *col);
                    let mut line = String::new();
                    let mut cumulative_col = 1;
                    for (col, content) in element {
                        assert!(col >= cumulative_col);
                        line.push_str(&" ".repeat(col - cumulative_col));
                        line.push_str(&content.to_string());
                        cumulative_col = col + content.chars().count();
                    }
                    writeln!(writer, "{} {} {}", spacing, vertical_bar, line)?;
                }
            }
        }
        writeln!(writer, "{} {}", spacing, vertical_bar)?;
        if !self.post_text.is_empty() {
            let eq = "=".cyan().bold();
            for line in self.post_text.lines() {
                writeln!(writer, "{} {} {}", spacing, eq, line.bold())?;
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;

    use colored::{Color, Colorize};

    use crate::scan::location::{Location, Source, Span};

    use super::DiagnosticItem;

    #[test]
    fn test_visual_inspection() {
        // Run with cargo test -- --nocapture
        let source = Rc::new(Source {
            filename: "test".into(),
            content: r#"
fn main() {
    println!("Hello, world!");
} /* 
    Very long comments
*/
            "#
            .trim_start()
            .chars()
            .collect(),
        });
        macro_rules! test_span {
            ($o1:literal : $l1:literal : $c1:literal - $o2:literal : $l2:literal : $c2:literal) => {
                Span::new(
                    Location {
                        source: source.clone(),
                        offset: $o1,
                        line: $l1,
                        column: $c1,
                    },
                    Location {
                        source: source.clone(),
                        offset: $o2,
                        line: $l2,
                        column: $c2,
                    },
                )
            };
        }
        let item_1 = DiagnosticItem {
            span: test_span!(0:1:1 - 2:1:3),
            message: "test".into(),
            color: None,
        };
        let item_2 = DiagnosticItem {
            span: test_span!(3:1:4 - 44:3:2),
            message: "multi line test\nmulti line test".into(),
            color: Some(Color::Red),
        };
        let item_3 = DiagnosticItem {
            span: test_span!(45:3:3 - 74:5:3),
            message: "test again".into(),
            color: Some(Color::Green),
        };
        let item_4 = DiagnosticItem {
            span: test_span!(44:3:2 - 45:3:3),
            message: "sandwiched :(".into(),
            color: Some(Color::Blue),
        };
        let diag = super::Diagnostic::new()
            .with_pre_text(&"some pre text".green().bold().to_string())
            .add_item(item_1)
            .add_item(item_2)
            .add_item(item_3)
            .add_item(item_4)
            .with_post_text("some post text");
        diag.write(&mut std::io::stderr()).unwrap();
    }
}
