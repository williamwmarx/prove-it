// Ported from Z3 (src/math/lp/static_matrix.h, src/math/lp/static_matrix_def.h), MIT license, see
// z3-license.txt. The sparse tableau: every row cell knows the offset of its column cell and back,
// and cells are removed by moving the last cell of the strip into their place, so the order of
// the cells is Z3's.
use prove_num::Rational;

use crate::lp::lar_term::LarTerm;

// The -1 of TypeScript's row offsets: the column is not in the row.
const NO_OFFSET: usize = usize::MAX;

fn get_term_cells(term: &LarTerm) -> Vec<(usize, Rational)> {
    term.iter()
        .map(|entry| (entry.0, entry.1.clone()))
        .collect()
}

#[derive(Clone, Debug)]
pub struct RowCell {
    pub column: usize,
    pub offset: usize,
    pub coeff: Rational,
}

#[derive(Clone, Copy, Debug)]
pub struct ColumnCell {
    pub row: usize,
    pub offset: usize,
}

#[derive(Default)]
pub struct StaticMatrix {
    pub rows: Vec<Vec<RowCell>>,
    pub columns: Vec<Vec<ColumnCell>>,
    row_offsets: Vec<usize>,
}

impl StaticMatrix {
    pub fn new() -> StaticMatrix {
        StaticMatrix::default()
    }

    pub fn get_row_count(&self) -> usize {
        self.rows.len()
    }

    pub fn get_column_count(&self) -> usize {
        self.columns.len()
    }

    pub fn get_val(&self, cell: &ColumnCell) -> &Rational {
        &self.rows[cell.row][cell.offset].coeff
    }

    pub fn add_row(&mut self) {
        self.rows.push(Vec::new());
    }

    pub fn add_column(&mut self) {
        self.columns.push(Vec::new());
        self.row_offsets.push(NO_OFFSET);
    }

    pub fn pop_column(&mut self) {
        self.columns.pop();
        self.row_offsets.pop();
    }

    pub fn add_columns_up_to(&mut self, column: usize) {
        while column >= self.columns.len() {
            self.add_column();
        }
    }

    pub fn clear(&mut self) {
        self.rows.clear();
        self.columns.clear();
        self.row_offsets.clear();
    }

    // set: appends a nonzero cell to the row and to the column.
    pub fn set(&mut self, row: usize, column: usize, coeff: Rational) {
        if coeff.is_zero() {
            return;
        }
        self.add_new_element(row, column, coeff);
    }

    pub fn add_new_element(&mut self, row: usize, column: usize, coeff: Rational) {
        let column_offset = self.columns[column].len();
        self.rows[row].push(RowCell {
            column,
            offset: column_offset,
            coeff,
        });
        let row_offset = self.rows[row].len() - 1;
        self.columns[column].push(ColumnCell {
            row,
            offset: row_offset,
        });
    }

    // TypeScript passes the row's cells and the cell; here the row and the cell's offset in it.
    pub fn remove_element(&mut self, row: usize, cell_offset: usize) {
        let column = self.rows[row][cell_offset].column;
        let column_offset = self.rows[row][cell_offset].offset;
        let row_offset = self.columns[column][column_offset].offset;
        let last_column_offset = self.columns[column].len() - 1;
        if column_offset != last_column_offset {
            let moved = self.columns[column][last_column_offset];
            self.columns[column][column_offset] = moved;
            self.rows[moved.row][moved.offset].offset = column_offset;
        }
        let last_row_offset = self.rows[row].len() - 1;
        if row_offset != last_row_offset {
            let tail = self.rows[row][last_row_offset].clone();
            self.columns[tail.column][tail.offset].offset = row_offset;
            self.rows[row][row_offset] = tail;
        }
        self.columns[column].pop();
        self.rows[row].pop();
    }

    fn scan_row_to_offsets(&mut self, row: usize) {
        for (index, cell) in self.rows[row].iter().enumerate() {
            self.row_offsets[cell.column] = index;
        }
    }

    // pivot_row_to_row_given_cell: eliminates the pivot column from the row of the cell by adding a
    // multiple of the pivot row.
    pub fn pivot_row_to_row_given_cell(
        &mut self,
        pivot_row: usize,
        cell: ColumnCell,
        pivot_column: usize,
    ) {
        let target = cell.row;
        let alpha = self.get_val(&cell).neg();
        self.remove_element(target, cell.offset);
        self.scan_row_to_offsets(target);
        let previous_size = self.rows[target].len();
        let mut cancelled = 0;
        for index in 0..self.rows[pivot_row].len() {
            let column = self.rows[pivot_row][index].column;
            if column == pivot_column {
                continue;
            }
            let offset = self.row_offsets[column];
            if offset == NO_OFFSET {
                let coeff = alpha.mul(&self.rows[pivot_row][index].coeff);
                self.add_new_element(target, column, coeff);
                continue;
            }
            let product = self.rows[pivot_row][index].coeff.mul(&alpha);
            let target_cell = &mut self.rows[target][offset];
            target_cell.coeff = target_cell.coeff.add(&product);
            if target_cell.coeff.is_zero() {
                cancelled += 1;
            }
        }
        for index in 0..previous_size {
            let column = self.rows[target][index].column;
            self.row_offsets[column] = NO_OFFSET;
        }
        let mut index = previous_size;
        while index > 0 && cancelled > 0 {
            index -= 1;
            if !self.rows[target][index].coeff.is_zero() {
                continue;
            }
            self.remove_element(target, index);
            cancelled -= 1;
        }
    }

    pub fn multiply_row(&mut self, row: usize, alpha: &Rational) {
        for cell in &mut self.rows[row] {
            cell.coeff = cell.coeff.mul(alpha);
        }
    }

    pub fn divide_row(&mut self, row: usize, alpha: &Rational) {
        for cell in &mut self.rows[row] {
            cell.coeff = cell.coeff.div(alpha);
        }
    }

    // add_rows: adds row from multiplied by alpha to row to.
    pub fn add_rows(&mut self, alpha: &Rational, from: usize, to: usize) {
        let cells: Vec<(usize, Rational)> = self.rows[from]
            .iter()
            .map(|cell| (cell.column, cell.coeff.clone()))
            .collect();
        self.add_cells_to_row(to, &cells, alpha, NO_OFFSET);
    }

    // pivot_row_to_row_given_cell_with_sign: eliminates the pivot column from the row of the cell by
    // adding the pivot row times the sign.
    pub fn pivot_row_to_row_given_cell_with_sign(
        &mut self,
        pivot_row: usize,
        cell: ColumnCell,
        pivot_column: usize,
        sign: i64,
    ) {
        let cells: Vec<(usize, Rational)> = self.rows[pivot_row]
            .iter()
            .map(|cell| (cell.column, cell.coeff.clone()))
            .collect();
        self.pivot_cells_to_row(&cells, cell, pivot_column, sign);
    }

    // pivot_term_to_row_given_cell: the same with the cells of a term in place of the pivot row.
    pub fn pivot_term_to_row_given_cell(
        &mut self,
        term: &LarTerm,
        cell: ColumnCell,
        pivot_column: usize,
        sign: i64,
    ) {
        self.pivot_cells_to_row(&get_term_cells(term), cell, pivot_column, sign);
    }

    // add_term_to_row: adds the term multiplied by alpha to the row.
    pub fn add_term_to_row(&mut self, alpha: &Rational, term: &LarTerm, row: usize) {
        for entry in term.iter() {
            self.add_columns_up_to(entry.0);
        }
        self.add_cells_to_row(row, &get_term_cells(term), alpha, NO_OFFSET);
    }

    fn pivot_cells_to_row(
        &mut self,
        cells: &[(usize, Rational)],
        cell: ColumnCell,
        pivot_column: usize,
        sign: i64,
    ) {
        let target = cell.row;
        let alpha = self.get_val(&cell).neg().mul(&Rational::from_i64(sign));
        self.remove_element(target, cell.offset);
        self.add_cells_to_row(target, cells, &alpha, pivot_column);
    }

    // The cells times alpha added to the row, skipping a column, and the cells that cancel removed
    // from the end. NO_OFFSET as the skipped column skips none, as TypeScript's -1.
    fn add_cells_to_row(
        &mut self,
        row: usize,
        cells: &[(usize, Rational)],
        alpha: &Rational,
        skipped_column: usize,
    ) {
        self.scan_row_to_offsets(row);
        let previous_size = self.rows[row].len();
        for source in cells {
            if source.0 == skipped_column {
                continue;
            }
            let offset = self.row_offsets[source.0];
            if offset == NO_OFFSET {
                self.add_new_element(row, source.0, alpha.mul(&source.1));
            } else {
                let target_cell = &mut self.rows[row][offset];
                target_cell.coeff = target_cell.coeff.add(&source.1.mul(alpha));
            }
        }
        for index in 0..previous_size {
            let column = self.rows[row][index].column;
            self.row_offsets[column] = NO_OFFSET;
        }
        for index in (0..self.rows[row].len()).rev() {
            if self.rows[row][index].coeff.is_zero() {
                self.remove_element(row, index);
            }
        }
    }

    pub fn transpose_rows(&mut self, first: usize, second: usize) {
        self.rows.swap(first, second);
        for cell in &self.rows[first] {
            self.columns[cell.column][cell.offset].row = first;
        }
        for cell in &self.rows[second] {
            self.columns[cell.column][cell.offset].row = second;
        }
    }

    // fill_last_row_with_pivoting: the row of a new basic column for a term, with the basic columns
    // of the term substituted by their rows.
    pub fn fill_last_row_with_pivoting(
        &mut self,
        term: &LarTerm,
        basic: usize,
        basis_heading: &[i64],
    ) {
        // TypeScript's sparse work array, whose holes are zero.
        let mut work: Vec<Rational> = Vec::new();
        let mut index: Vec<usize> = Vec::new();
        fn get_work(work: &[Rational], column: usize) -> Rational {
            work.get(column).cloned().unwrap_or_else(Rational::zero)
        }
        fn set_work(work: &mut Vec<Rational>, column: usize, value: Rational) {
            if work.len() <= column {
                work.resize(column + 1, Rational::zero());
            }
            work[column] = value;
        }
        fn erase_from_index(index: &mut Vec<usize>, column: usize) {
            if let Some(position) = index.iter().position(|entry| *entry == column) {
                index.remove(position);
            }
        }
        set_work(&mut work, basic, Rational::one());
        index.push(basic);
        for entry in term.iter() {
            set_work(&mut work, entry.0, entry.1.neg());
            index.push(entry.0);
        }
        let pivot_columns: Vec<usize> = std::iter::once(basic)
            .chain(term.iter().map(|entry| entry.0))
            .collect();
        // pivotOut: the column's row, when it is basic, substituted into the work row.
        for column in pivot_columns {
            let row_index = basis_heading[column];
            if row_index < 0 {
                continue;
            }
            let alpha = get_work(&work, column);
            if alpha.is_zero() {
                continue;
            }
            for cell in &self.rows[row_index as usize] {
                if cell.column == column {
                    continue;
                }
                let was_zero = get_work(&work, cell.column).is_zero();
                let value = get_work(&work, cell.column).sub(&alpha.mul(&cell.coeff));
                set_work(&mut work, cell.column, value);
                if was_zero {
                    index.push(cell.column);
                } else if get_work(&work, cell.column).is_zero() {
                    erase_from_index(&mut index, cell.column);
                }
            }
            set_work(&mut work, column, Rational::zero());
            erase_from_index(&mut index, column);
        }
        let last_row = self.rows.len() - 1;
        for column in index {
            self.set(last_row, column, get_work(&work, column));
        }
        let last_column = self.columns.len() - 1;
        self.set(last_row, last_column, Rational::one());
    }
}
