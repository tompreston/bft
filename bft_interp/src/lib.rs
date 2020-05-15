//! Brainfuck interpreter
//!
//! This crate contains all the interpreter logic for the BrainfuckVM.

use bft_types::{BrainfuckInstr, BrainfuckProg};
use std::default::Default;
use std::fmt::Debug;

#[derive(Debug)]
pub enum BrainfuckVMError<'a> {
    InvalidPosition(&'a BrainfuckInstr),
}

/// Describes the traits we expect the Brainfuck VW generic cell-type to have.
pub trait BrainfuckCellKind: Debug + Default + Clone {
    /// Increment the cell (wraps on overflow).
    fn wrapping_increment(&self) -> Self;

    /// Decrement the cell (wraps on underflow).
    fn wrapping_decrement(&self) -> Self;
}

/// An implementation of the BrainfuckCellKind traits for the u8 type.
impl BrainfuckCellKind for u8 {
    fn wrapping_increment(&self) -> u8 {
        self.wrapping_add(1)
    }

    fn wrapping_decrement(&self) -> u8 {
        self.wrapping_sub(1)
    }
}

/// Represents a Brainfuck Virtual Machine.
///
/// The Brainfuck Virtual Machine interperets and runs BrainfuckProg programs.
/// The type T specifies what type the BrainfuckVM data cells are.
#[derive(Debug)]
pub struct BrainfuckVM<'a, T> {
    /// Data cells in the Brainfuck Virtual Machine.
    cells: Vec<T>,

    /// If we overflow on the data cells, this sets if we automatically increase
    /// the cells vector.
    is_growable: bool,

    /// The data pointer. This is analogous to the head reading a data tape.
    head: usize,

    /// The program counter. This is the index of the current instruction.
    pc: usize,

    /// The Brainfuck program we are running.
    program: &'a BrainfuckProg,
}

impl<'a, T> BrainfuckVM<'a, T>
where
    T: BrainfuckCellKind,
{
    /// Returns a new BrainfuckVM with num_cells.
    ///
    /// # Arguments
    ///
    /// * `program` - The Brainfuck program.
    /// * `num_cells` - Number of data cells in the BrainfuckVM (default: 30000)
    /// * `is_growable` - Sets whether the number of cells can change.
    ///
    /// # Example
    ///
    /// ```
    /// # use bft_interp::BrainfuckVM;
    /// # use bft_types::BrainfuckProg;
    /// let prog = BrainfuckProg::new("fake/path.bf", "<>[[[]-]+],.".to_string());
    /// let bfvm: BrainfuckVM<u8> = BrainfuckVM::new(&prog, 0, false);
    /// ```
    pub fn new(program: &'a BrainfuckProg, num_cells: usize, is_growable: bool) -> Self {
        let n = if num_cells == 0 { 30_000 } else { num_cells };
        let cells: Vec<T> = vec![T::default(); n];
        BrainfuckVM {
            cells,
            is_growable,
            head: 0,
            pc: 0,
            program,
        }
    }

    pub fn run_program(&self) {
        for instr in self.program.instrs() {
            println!("[{}:{}] {}", instr.line1(), instr.column(), instr);
        }
    }

    /// Move the tape head one cell to the left. Returns an error if we are at
    /// cell 0.
    pub fn move_head_left(&mut self) -> Result<(), BrainfuckVMError> {
        if self.head == 0 {
            return Err(BrainfuckVMError::InvalidPosition(
                &self.program.instrs()[self.pc],
            ));
        }
        self.head -= 1;
        Ok(())
    }

    /// Move the tape head one cell to the right. Returns an error if we cannot
    /// grow the tape.
    pub fn move_head_right(&mut self) -> Result<(), BrainfuckVMError> {
        let new_head = self.head + 1;
        if new_head >= self.cells.len() {
            return Err(BrainfuckVMError::InvalidPosition(
                &self.program.instrs()[self.pc],
            ));
        }
        self.head = new_head;
        Ok(())
    }

    /// Increment the current data cell (wraps on overflow).
    pub fn cell_increment(&mut self) {
        self.cells[self.head] = self.cells[self.head].wrapping_increment();
    }

    /// Decrement the current data cell (wraps on overflow).
    pub fn cell_decrement(&mut self) {
        self.cells[self.head] = self.cells[self.head].wrapping_decrement();
    }
}

#[cfg(test)]
mod tests {
    use super::BrainfuckProg;
    use super::BrainfuckVM;

    const FKPATH: &str = "fake/path.bf";

    #[test]
    fn test_brainfuckvm_init() {
        let prog = BrainfuckProg::new(FKPATH, "<>[[[]-]+],.".to_string());
        let bfvm: BrainfuckVM<u8> = BrainfuckVM::new(&prog, 0, false);
        assert_eq!(bfvm.cells.len(), 30_000);

        for num_cells in 1..11 {
            let bfvm: BrainfuckVM<u8> = BrainfuckVM::new(&prog, num_cells, false);
            assert_eq!(bfvm.cells.len(), num_cells);
        }
    }

    #[test]
    fn test_brainfuckvm_move_head_left() {
        let prog = BrainfuckProg::new(FKPATH, "<>[[[]-]+],.".to_string());
        let mut bfvm: BrainfuckVM<u8> = BrainfuckVM::new(&prog, 0, false);
        bfvm.move_head_right().unwrap();
        bfvm.move_head_left().unwrap();
    }

    #[test]
    #[should_panic]
    fn test_brainfuckvm_move_head_left_before_zero() {
        let prog = BrainfuckProg::new(FKPATH, "<>[[[]-]+],.".to_string());
        let mut bfvm: BrainfuckVM<u8> = BrainfuckVM::new(&prog, 0, false);
        bfvm.move_head_right().unwrap();
        bfvm.move_head_left().unwrap();
        bfvm.move_head_left().unwrap();
    }

    #[test]
    fn test_brainfuckvm_move_head_right() {
        let prog = BrainfuckProg::new(FKPATH, "<>[[[]-]+],.".to_string());
        let mut bfvm: BrainfuckVM<u8> = BrainfuckVM::new(&prog, 2, false);
        bfvm.move_head_right().unwrap();
    }

    #[test]
    #[should_panic]
    fn test_brainfuckvm_move_head_right_after_max_not_growable() {
        let prog = BrainfuckProg::new(FKPATH, "<>[[[]-]+],.".to_string());
        let mut bfvm: BrainfuckVM<u8> = BrainfuckVM::new(&prog, 2, false);
        bfvm.move_head_right().unwrap();
        bfvm.move_head_right().unwrap();
    }

    #[test]
    fn test_brainfuckvm_cell_increment() {
        let prog = BrainfuckProg::new(FKPATH, "<>[[[]-]+],.".to_string());
        let num_cells = 123;
        let mut bfvm: BrainfuckVM<u8> = BrainfuckVM::new(&prog, num_cells, false);

        // We're going to test incrementing every cell
        for cell_increment in 0..num_cells {
            // Increment until we overflow
            for i in 0..=u8::MAX {
                // Check the value of every cell
                for cell_check in 0..num_cells {
                    if cell_check == cell_increment {
                        assert_eq!(bfvm.cells[cell_check], i);
                    } else {
                        assert_eq!(bfvm.cells[cell_check], 0);
                    }
                }
                bfvm.cell_increment();
            }
            // Now we expect the overflow and every cell should be 0
            for cell_check in 0..num_cells {
                assert_eq!(bfvm.cells[cell_check], 0);
            }

            if cell_increment < num_cells - 1 {
                bfvm.move_head_right().unwrap();
            }
        }
    }

    // TODO decrement. Maybe we can do this generically since it'll be repeating
    // above.
}
