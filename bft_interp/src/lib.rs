//! Brainfuck interpreter
//!
//! This crate contains all the interpreter logic for the BrainfuckVM.

use bft_types::BrainfuckProg;
use std::default::Default;

/// Represents a Brainfuck Virtual Machine.
///
/// The Brainfuck Virtual Machine interperets and runs BrainfuckProg programs.
/// The type T specifies what type the BrainfuckVM data cells are.
#[derive(Debug)]
pub struct BrainfuckVM<T> {
    cells: Vec<T>,
    cur_cell: usize,
    is_growable: bool,
}

impl<T> BrainfuckVM<T>
where
    T: Clone,
    T: Default,
{
    /// Returns a new BrainfuckVM with num_cells.
    ///
    /// # Arguments
    ///
    /// * `num_cells` - Number of data cells in the BrainfuckVM (default: 30000)
    /// * `is_growable` - Sets whether the number of cells can change.
    ///
    /// # Example
    ///
    /// ```
    /// use bft_interp::BrainfuckVM;
    /// let bfvm: BrainfuckVM<u8> = BrainfuckVM::new(0, false);
    /// ```
    pub fn new(num_cells: usize, is_growable: bool) -> Self {
        let n = if num_cells == 0 { 30_000 } else { num_cells };
        let cells: Vec<T> = vec![T::default(); n];
        BrainfuckVM {
            cells,
            cur_cell: 0,
            is_growable,
        }
    }

    pub fn run_prog(&self, bf_prog: &BrainfuckProg) {
        for instr in bf_prog.program() {
            println!("[{}:{}] {}", instr.line1(), instr.column(), instr);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::BrainfuckVM;

    #[test]
    fn test_brainfuckvm_init() {
        let bfvm: BrainfuckVM<u8> = BrainfuckVM::new(0, false);
        assert_eq!(bfvm.cells.len(), 30_000);

        for num_cells in 1..11 {
            let bfvm: BrainfuckVM<u8> = BrainfuckVM::new(num_cells, false);
            assert_eq!(bfvm.cells.len(), num_cells);
        }
    }
}
