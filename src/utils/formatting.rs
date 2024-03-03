use core::fmt;

pub struct TableRow {
    cells: Vec<String>,
}

impl TableRow {
    pub fn new() -> Self {
        Self { cells: Vec::new() }
    }

    pub fn add<T>(mut self, cell: T) -> Self
    where
        T: ToString,
    {
        self.cells.push(cell.to_string());
        self
    }
}

pub struct Table {
    rows: Vec<TableRow>,
}

impl Table {
    pub fn new() -> Self {
        Self { rows: Vec::new() }
    }

    pub fn add_row(&mut self, row: TableRow) {
        self.rows.push(row);
    }
}

impl fmt::Display for Table {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let max_cols = self
            .rows
            .iter()
            .map(|row| row.cells.len())
            .max()
            .unwrap_or(0);
        let mut max_widths = vec![0; max_cols];
        for row in &self.rows {
            for (i, cell) in row.cells.iter().enumerate() {
                max_widths[i] = max_widths[i].max(cell.len());
            }
        }
        for row in &self.rows {
            for (i, cell) in row.cells.iter().enumerate() {
                write!(f, "{:width$}", cell, width = max_widths[i] + 1)?;
            }
            writeln!(f)?;
        }
        Ok(())
    }
}
