//! Brainfuck interpreter
//!
//! This crate contains all the interpreter logic for the BrainfuckVM.

#![deny(missing_docs)]

use bft_types::{BrainfuckInstr, BrainfuckInstrRaw, BrainfuckProg};
use std::default::Default;
use std::fmt;
use std::io;

use thiserror::Error;

/// Represents a Brainfuck Virtual Machine Error.
#[derive(Error, fmt::Debug)]
pub enum BrainfuckVMError {
    /// When the data head index is out of bounds
    #[error("invalid position for data head, instr {0}")]
    InvalidPosition(BrainfuckInstr),

    /// When an io::Error occurs when reading or writing
    #[error("IO error occured, instr {0}, {0}")]
    IOError(BrainfuckInstr, io::Error),

    /// When the program counter is out of bounds
    #[error("invalid program counter, instr {0}")]
    InvalidProgramCounter(BrainfuckInstr),

    /// When an unmatched or right bracket is found
    #[error("unmatched bracket, instr {0}")]
    UnmatchedBracket(BrainfuckInstr),
}

/// Describes the traits we expect the Brainfuck VW generic cell-type to have.
/// Implementations of this trait must also implement the supertraits:
/// Debug, Default and Clone
pub trait BrainfuckCellKind: fmt::Debug + Default + Clone {
    /// Increment the cell (wraps on overflow).
    fn wrapping_increment(&mut self);

    /// Decrement the cell (wraps on underflow).
    fn wrapping_decrement(&mut self);

    /// Load u8 value into cell.
    fn load_from_u8(&mut self, value: u8);

    /// Return u8 value from cell.
    fn as_u8(&self) -> u8;
}

/// An implementation of the BrainfuckCellKind traits for the u8 type.
impl BrainfuckCellKind for u8 {
    fn wrapping_increment(&mut self) {
        *self = self.wrapping_add(1)
    }

    fn wrapping_decrement(&mut self) {
        *self = self.wrapping_sub(1)
    }

    fn load_from_u8(&mut self, value: u8) {
        *self = value
    }

    fn as_u8(&self) -> u8 {
        *self
    }
}

/// Represents a Brainfuck Virtual Machine.
///
/// The Brainfuck Virtual Machine interperets and runs BrainfuckProg programs.
/// The type T specifies what type the BrainfuckVM data cells are.
#[derive(fmt::Debug)]
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
    /// let prog = BrainfuckProg::new("fake/path.bf", "<>[[[]-]+],.");
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

    /// Interpret the input Brainfuck program, and write data to output.
    pub fn interpret<R, W>(&mut self, mut input: R, mut output: W) -> Result<(), BrainfuckVMError>
    where
        R: io::Read,
        W: io::Write,
    {
        let bf_instrs = self.program.instrs();
        let last_instr = bf_instrs.len() - 1;

        while self.pc <= last_instr {
            let bf_instr = &bf_instrs[self.pc];

            self.pc = match bf_instr.instr() {
                BrainfuckInstrRaw::Increment => self.cell_increment(),
                BrainfuckInstrRaw::Decrement => self.cell_decrement(),
                BrainfuckInstrRaw::MoveHeadLeft => self.move_head_left(),
                BrainfuckInstrRaw::MoveHeadRight => self.move_head_right(),
                BrainfuckInstrRaw::WhileStart => self.while_start(),
                BrainfuckInstrRaw::WhileEnd => self.while_end(),
                BrainfuckInstrRaw::CellRead => self.cell_read(&mut input),
                BrainfuckInstrRaw::CellWrite => self.cell_write(&mut output),
            }?;
        }

        // End of program
        Ok(())
    }

    /// Move the tape head one cell to the left. Returns the next program
    /// counter or an error if we are at cell 0.
    ///
    /// # Example
    ///
    /// ```
    /// # use bft_interp::BrainfuckVM;
    /// # use bft_types::BrainfuckProg;
    /// let prog = BrainfuckProg::new("fake/path.bf", "<>[[[]-]+],.");
    /// let mut bfvm: BrainfuckVM<u8> = BrainfuckVM::new(&prog, 0, false);
    /// assert!(bfvm.move_head_right().is_ok());
    /// assert!(bfvm.move_head_left().is_ok());
    /// ```
    pub fn move_head_left(&mut self) -> Result<usize, BrainfuckVMError> {
        if self.head == 0 {
            return Err(BrainfuckVMError::InvalidPosition(self.current_instr()));
        }
        self.head -= 1;
        Ok(self.pc + 1)
    }

    /// Move the tape head one cell to the right. Returns the next program
    /// counter, or an error if we cannot grow the tape.
    ///
    /// # Example
    ///
    /// ```
    /// # use bft_interp::BrainfuckVM;
    /// # use bft_types::BrainfuckProg;
    /// let prog = BrainfuckProg::new("fake/path.bf", "<>[[[]-]+],.");
    /// let mut bfvm: BrainfuckVM<u8> = BrainfuckVM::new(&prog, 0, false);
    /// assert!(bfvm.move_head_right().is_ok());
    /// ```
    pub fn move_head_right(&mut self) -> Result<usize, BrainfuckVMError> {
        // If we're at the end, add another cell and let Rust decide how to grow
        // the Vector
        if self.head == self.cells.len() - 1 && self.is_growable {
            self.cells.push(Default::default());
            return self.move_head_right();
        }
        // If we're out-of-bounds return an error, maybe head >> cells.len()
        if self.head >= self.cells.len() - 1 {
            return Err(BrainfuckVMError::InvalidPosition(self.current_instr()));
        }
        self.head += 1;
        Ok(self.pc + 1)
    }

    /// Increment the current data cell (wraps on overflow). Returns the next
    /// program counter.
    ///
    /// # Example
    ///
    /// ```
    /// # use bft_interp::BrainfuckVM;
    /// # use bft_types::BrainfuckProg;
    /// let prog = BrainfuckProg::new("fake/path.bf", "<>[[[]-]+],.");
    /// let mut bfvm: BrainfuckVM<u8> = BrainfuckVM::new(&prog, 0, false);
    /// assert_eq!(bfvm.cell_increment().ok(), Some(1));
    /// ```
    pub fn cell_increment(&mut self) -> Result<usize, BrainfuckVMError> {
        self.cells[self.head].wrapping_increment();
        Ok(self.pc + 1)
    }

    /// Decrement the current data cell (wraps on overflow). Returns the next
    /// program counter.
    ///
    /// # Example
    ///
    /// ```
    /// # use bft_interp::BrainfuckVM;
    /// # use bft_types::BrainfuckProg;
    /// let prog = BrainfuckProg::new("fake/path.bf", "<>[[[]-]+],.");
    /// let mut bfvm: BrainfuckVM<u8> = BrainfuckVM::new(&prog, 0, false);
    /// assert_eq!(bfvm.cell_decrement().ok(), Some(1));
    /// ```
    pub fn cell_decrement(&mut self) -> Result<usize, BrainfuckVMError> {
        self.cells[self.head].wrapping_decrement();
        Ok(self.pc + 1)
    }

    /// Read into the current cell, from some reader. Returns the next program
    /// counter, or error if the read fails.
    ///
    /// # Example
    ///
    /// ```
    /// # use bft_interp::BrainfuckVM;
    /// # use bft_types::BrainfuckProg;
    /// # use std::io;
    /// let prog = BrainfuckProg::new("fake/path.bf", "<>[[[]-]+],.");
    /// let mut bfvm: BrainfuckVM<u8> = BrainfuckVM::new(&prog, 0, false);
    /// let mut reader = io::Cursor::new(vec![42]);
    /// assert!(bfvm.cell_read(&mut reader).is_ok());
    /// ```
    pub fn cell_read(&mut self, reader: &mut impl io::Read) -> Result<usize, BrainfuckVMError> {
        let mut buffer = [0];
        // We can't try? reader.read(), because we don't know how to convert
        // from io::Error to BrainfuckVMError::IOError. Maybe we will learn in a
        // later lesson...
        match reader.read(&mut buffer) {
            Ok(_) => {
                self.cells[self.head].load_from_u8(buffer[0]);
                Ok(self.pc + 1)
            }
            Err(e) => Err(BrainfuckVMError::IOError(self.current_instr(), e)),
        }
    }

    /// Write from the current cell, to some writer. Returns the next program
    /// counter, or error if the write fails.
    ///
    /// # Example
    ///
    /// ```
    /// # use bft_interp::BrainfuckVM;
    /// # use bft_types::BrainfuckProg;
    /// # use std::io;
    /// let prog = BrainfuckProg::new("fake/path.bf", "<>[[[]-]+],.");
    /// let mut bfvm: BrainfuckVM<u8> = BrainfuckVM::new(&prog, 0, false);
    /// let mut buff = io::Cursor::new(vec![42]);
    /// assert!(bfvm.cell_write(&mut buff).is_ok());
    /// assert_eq!(buff.into_inner()[0], 0);
    /// ```
    pub fn cell_write(&mut self, writer: &mut impl io::Write) -> Result<usize, BrainfuckVMError> {
        let buffer = [self.cells[self.head].as_u8()];
        match writer.write(&buffer) {
            Ok(_) => Ok(self.pc + 1),
            Err(e) => Err(BrainfuckVMError::IOError(self.current_instr(), e)),
        }
    }

    /// Start a while-loop. Returns the next program counter (loop-body) if data
    /// at cell is non-zero, otherwise returns the program counter after the
    /// matching right-bracket.
    ///
    /// # Example
    ///
    /// ```
    /// # use bft_interp::BrainfuckVM;
    /// # use bft_types::BrainfuckProg;
    /// # use std::io;
    /// let prog = BrainfuckProg::new("fake/path.bf", "[>]>");
    /// let mut bfvm: BrainfuckVM<u8> = BrainfuckVM::new(&prog, 0, false);
    /// let rbracket_pc = bfvm.while_start();
    /// assert_eq!(rbracket_pc.ok(), Some(3));
    /// ```
    pub fn while_start(&self) -> Result<usize, BrainfuckVMError> {
        let loop_cond = self.cells[self.head].as_u8() != 0;
        if loop_cond {
            Ok(self.pc + 1)
        } else {
            let pc = self.matching_rbracket(self.pc)?;
            Ok(pc + 1)
        }
    }

    /// End a while-loop body. Returns an unconditional branch to the matching
    /// left-bracket.
    pub fn while_end(&self) -> Result<usize, BrainfuckVMError> {
        self.matching_lbracket(self.pc)
    }

    /// From the provided left-bracket, search for the next matching right-bracket
    /// and return its pc.  Returns an error if no matching bracket is found.
    fn matching_rbracket(&self, pc_lbracket: usize) -> Result<usize, BrainfuckVMError> {
        let instrs = self.program.instrs();
        let pc_last = instrs.len() - 1;
        let mut pc = pc_lbracket;

        while pc < pc_last {
            pc += 1;
            match *instrs[pc].instr() {
                BrainfuckInstrRaw::WhileStart => pc = self.matching_rbracket(pc)?,
                BrainfuckInstrRaw::WhileEnd => return Ok(pc),
                _ => (),
            };
        }

        Err(BrainfuckVMError::UnmatchedBracket(self.current_instr()))
    }

    /// From the provided right-bracket, search for the next matching left-bracket
    /// and return its pc.  Returns an error if no matching bracket is found.
    fn matching_lbracket(&self, pc_rbracket: usize) -> Result<usize, BrainfuckVMError> {
        let instrs = self.program.instrs();
        let pc_first = 0;
        let mut pc = pc_rbracket;

        while pc > pc_first {
            pc -= 1;
            match *instrs[pc].instr() {
                BrainfuckInstrRaw::WhileEnd => pc = self.matching_lbracket(pc)?,
                BrainfuckInstrRaw::WhileStart => return Ok(pc),
                _ => (),
            }
        }

        Err(BrainfuckVMError::UnmatchedBracket(self.current_instr()))
    }

    /// Return the current instruction using the program-counter
    fn current_instr(&self) -> BrainfuckInstr {
        self.program.instrs()[self.pc]
    }
}

#[cfg(test)]
mod tests {
    use super::BrainfuckProg;
    use super::BrainfuckVM;
    use std::io;

    const FKPATH: &str = "fake/path.bf";

    #[test]
    fn test_brainfuckvm_init() {
        let prog = BrainfuckProg::new(FKPATH, "<>[[[]-]+],.");
        let bfvm: BrainfuckVM<u8> = BrainfuckVM::new(&prog, 0, false);
        assert_eq!(bfvm.cells.len(), 30_000);

        for num_cells in 1..11 {
            let bfvm: BrainfuckVM<u8> = BrainfuckVM::new(&prog, num_cells, false);
            assert_eq!(bfvm.cells.len(), num_cells);
        }
    }

    #[test]
    fn test_brainfuckvm_move_head_left() {
        let prog = BrainfuckProg::new(FKPATH, "<>[[[]-]+],.");
        let mut bfvm: BrainfuckVM<u8> = BrainfuckVM::new(&prog, 0, false);
        assert!(bfvm.move_head_right().is_ok());
        assert!(bfvm.move_head_left().is_ok());
    }

    #[test]
    fn test_brainfuckvm_move_head_left_before_zero() {
        let prog = BrainfuckProg::new(FKPATH, "<>[[[]-]+],.");
        let mut bfvm: BrainfuckVM<u8> = BrainfuckVM::new(&prog, 0, false);
        assert!(bfvm.move_head_right().is_ok());
        assert!(bfvm.move_head_left().is_ok());
        assert!(bfvm.move_head_left().is_err());
    }

    #[test]
    fn test_brainfuckvm_move_head_right() {
        let prog = BrainfuckProg::new(FKPATH, "<>[[[]-]+],.");
        let mut bfvm: BrainfuckVM<u8> = BrainfuckVM::new(&prog, 2, false);
        assert!(bfvm.move_head_right().is_ok());
    }

    #[test]
    fn test_brainfuckvm_move_head_right_after_max_not_growable() {
        let prog = BrainfuckProg::new(FKPATH, "<>[[[]-]+],.");
        let mut bfvm: BrainfuckVM<u8> = BrainfuckVM::new(&prog, 2, false);
        assert!(bfvm.move_head_right().is_ok());
        assert!(bfvm.move_head_right().is_err());
    }

    #[test]
    fn test_brainfuckvm_move_head_right_after_max_growable() {
        let prog = BrainfuckProg::new(FKPATH, "<>[[[]-]+],.");
        let mut bfvm: BrainfuckVM<u8> = BrainfuckVM::new(&prog, 2, true);
        for _ in 1..9001 {
            assert!(bfvm.move_head_right().is_ok());
        }
    }

    #[test]
    fn test_brainfuckvm_cell_increment() {
        let prog = BrainfuckProg::new(FKPATH, "<>[[[]-]+],.");
        let num_cells = 123;
        let mut bfvm: BrainfuckVM<u8> = BrainfuckVM::new(&prog, num_cells, false);

        // We're going to test incrementing every cell
        for cell_increment in 0..num_cells {
            // Check and increment, until we overflow
            for i in 0..=u8::MAX {
                // Check the value of every cell
                for cell_check in 0..num_cells {
                    if cell_check == cell_increment {
                        assert_eq!(bfvm.cells[cell_check], i);
                    } else {
                        assert_eq!(bfvm.cells[cell_check], 0);
                    }
                }
                assert!(bfvm.cell_increment().is_ok());
            }
            // Now we expect the overflow and every cell should be 0
            for cell_check in 0..num_cells {
                assert_eq!(bfvm.cells[cell_check], 0);
            }

            if cell_increment < num_cells - 1 {
                assert!(bfvm.move_head_right().is_ok());
            }
        }
    }

    #[test]
    fn test_brainfuckvm_cell_decrement() {
        let prog = BrainfuckProg::new(FKPATH, "<>[[[]-]+],.");
        let num_cells = 123;
        let mut bfvm: BrainfuckVM<u8> = BrainfuckVM::new(&prog, num_cells, false);

        // We're going to test decrementing every cell
        for cell_decrement in 0..num_cells {
            // Check and decrement, until we overflow
            for i in 0..=u8::MAX {
                assert!(bfvm.cell_decrement().is_ok());
                // Check the value of every cell.
                // We should have already underflowed.
                for cell_check in 0..num_cells {
                    if cell_check == cell_decrement {
                        assert_eq!(bfvm.cells[cell_check], u8::MAX - i);
                    } else {
                        assert_eq!(bfvm.cells[cell_check], 0);
                    }
                }
            }

            if cell_decrement < num_cells - 1 {
                assert!(bfvm.move_head_right().is_ok());
            }
        }
    }

    #[test]
    fn test_cell_read_u8() {
        let prog = BrainfuckProg::new(FKPATH, "<>[[[]-]+],.");
        let num_cells = 123;
        let mut bfvm: BrainfuckVM<u8> = BrainfuckVM::new(&prog, num_cells, false);

        // Check every cell is zero
        for cell_check in 0..num_cells {
            assert_eq!(bfvm.cells[cell_check], 0);
        }

        let val = 42;
        let mut buff = io::Cursor::new(vec![val, 0]);
        assert!(bfvm.cell_read(&mut buff).is_ok());

        // Now check the first cell is `val`, and every other cell is zero
        assert_eq!(bfvm.cells[0], val);
        for cell_check in 1..num_cells {
            assert_eq!(bfvm.cells[cell_check], 0);
        }
    }

    #[test]
    fn test_cell_write_u8() {
        let prog = BrainfuckProg::new(FKPATH, "<>[[[]-]+],.");
        let num_cells = 123;
        let mut bfvm: BrainfuckVM<u8> = BrainfuckVM::new(&prog, num_cells, false);

        // Set the expected value, which is to be read
        let val = 123;
        bfvm.cells[0] = val;

        // Check values can be read
        let mut buff = io::Cursor::new(vec![0, 1]);
        assert!(bfvm.cell_write(&mut buff).is_ok());

        // Check it was written
        let r = buff.get_ref();
        assert_eq!(r[0], val);
    }

    #[test]
    fn test_while_start() {
        let prog = BrainfuckProg::new("fake/path.bf", "[>]>[>[>]>]");
        let mut bfvm: BrainfuckVM<u8> = BrainfuckVM::new(&prog, 0, false);

        bfvm.pc = 0;
        let pc_after_rbracket = bfvm.while_start();
        assert_eq!(pc_after_rbracket.ok(), Some(3));

        bfvm.pc = 4;
        let pc_after_rbracket = bfvm.while_start();
        assert_eq!(pc_after_rbracket.ok(), Some(11));

        bfvm.pc = 6;
        let pc_after_rbracket = bfvm.while_start();
        assert_eq!(pc_after_rbracket.ok(), Some(9));
    }

    #[test]
    fn test_while_end() {
        let prog = BrainfuckProg::new("fake/path.bf", "[>]>[>[>]>]");
        let mut bfvm: BrainfuckVM<u8> = BrainfuckVM::new(&prog, 0, false);

        bfvm.pc = 2;
        let lbracket_pc = bfvm.while_end();
        assert_eq!(lbracket_pc.ok(), Some(0));

        bfvm.pc = 8;
        let lbracket_pc = bfvm.while_end();
        assert_eq!(lbracket_pc.ok(), Some(6));

        bfvm.pc = 10;
        let lbracket_pc = bfvm.while_end();
        assert_eq!(lbracket_pc.ok(), Some(4));
    }
}
