//! Brainfuck interpreter types
//!
//! This crate contains all the data types necessary for the Brainfuck
//! interpreter project.

use std::fmt;
use std::path::{Path, PathBuf};

/// Represents the eight raw Brainfuck instructions.
#[derive(Debug, PartialEq, Copy, Clone)]
pub enum BrainfuckInstrRaw {
    Plus,
    Minus,
    LessThan,
    GreaterThan,
    LeftBracket,
    RightBracket,
    Comma,
    Fullstop,
}

impl BrainfuckInstrRaw {
    /// Returns a BrainfuckInstrRaw from the given character.
    fn from_byte(c: u8) -> Option<BrainfuckInstrRaw> {
        match c {
            b'+' => Some(BrainfuckInstrRaw::Plus),
            b'-' => Some(BrainfuckInstrRaw::Minus),
            b'<' => Some(BrainfuckInstrRaw::LessThan),
            b'>' => Some(BrainfuckInstrRaw::GreaterThan),
            b'[' => Some(BrainfuckInstrRaw::LeftBracket),
            b']' => Some(BrainfuckInstrRaw::RightBracket),
            b',' => Some(BrainfuckInstrRaw::Comma),
            b'.' => Some(BrainfuckInstrRaw::Fullstop),
            _ => None,
        }
    }
}

/// Represents the raw Brainfuck instruction and where it is in the file.
#[derive(Debug, Copy, Clone)]
pub struct BrainfuckInstr {
    instr: BrainfuckInstrRaw,
    line: usize,
    column: usize,
}

impl BrainfuckInstr {
    /// Returns a vector of BrainfuckInstr's, parsed from the given String.
    ///
    /// # Example
    /// ```
    /// # use bft_types::{BrainfuckInstr, BrainfuckInstrRaw};
    /// let bf = BrainfuckInstr::from_string("<>".to_string());
    ///
    /// assert_eq!(bf[0].line1(), 1);
    /// assert_eq!(bf[0].column(), 0);
    ///
    /// assert_eq!(bf[1].line1(), 1);
    /// assert_eq!(bf[1].column(), 1);
    /// ```
    pub fn from_string(s: String) -> Vec<Self> {
        let mut instrs: Vec<BrainfuckInstr> = Vec::new();

        for (l, pline) in s.lines().enumerate() {
            for (c, pbyte) in pline.bytes().enumerate() {
                if let Some(iraw) = BrainfuckInstrRaw::from_byte(pbyte) {
                    instrs.push(BrainfuckInstr {
                        instr: iraw,
                        line: l,
                        column: c,
                    });
                }
            }
        }

        instrs
    }

    /// Returns the Brainfuck instruction line number, starting at 1
    pub fn line1(&self) -> usize {
        self.line + 1
    }

    /// Returns the Brainfuck instruction column
    pub fn column(&self) -> usize {
        self.column
    }

    /// Returns a borrow of the raw Brainfuck instruction.
    pub fn instr(&self) -> &BrainfuckInstrRaw {
        &self.instr
    }
}

impl fmt::Display for BrainfuckInstr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let text = match self.instr {
            BrainfuckInstrRaw::Plus => "Increment byte at data pointer",
            BrainfuckInstrRaw::Minus => "Decrement byte at data pointer",
            BrainfuckInstrRaw::LessThan => "Decrement data pointer",
            BrainfuckInstrRaw::GreaterThan => "Increment data pointer",
            BrainfuckInstrRaw::LeftBracket => "Start looping",
            BrainfuckInstrRaw::RightBracket => "End looping",
            BrainfuckInstrRaw::Comma => "Input byte at the data pointer",
            BrainfuckInstrRaw::Fullstop => "Output byte at data pointer",
        };
        write!(f, "{}", text)
    }
}

/// Represents an entire Brainfuck program: a Path and a series of instructions.
#[derive(Debug)]
pub struct BrainfuckProg {
    path: PathBuf,
    instrs: Vec<BrainfuckInstr>,
}

impl BrainfuckProg {
    pub fn new<P: AsRef<Path>>(path: P, content: String) -> Self {
        Self {
            path: path.as_ref().to_path_buf(),
            instrs: BrainfuckInstr::from_string(content),
        }
    }

    /// Returns a new instance of BrainfuckProg, parsed from the file located at
    /// the given Path-like reference.
    ///
    /// # Example
    /// ```no_run
    /// # use bft_types::BrainfuckProg;
    /// # use std::path::Path;
    /// let bf = BrainfuckProg::from_file(Path::new("path/to/prog.bf"));
    /// ```
    pub fn from_file<P: AsRef<Path>>(path: P) -> Result<Self, Box<dyn std::error::Error>> {
        let content = std::fs::read_to_string(&path)?;
        Ok(Self::new(path, content))
    }

    /// Returns a reference to the BrainfuckProg's path.
    pub fn path(&self) -> &PathBuf {
        &self.path
    }

    /// Returns a reference to the BrainfuckProg's instructions.
    pub fn instrs(&self) -> &[BrainfuckInstr] {
        &self.instrs[..]
    }

    /// Checks the program and returns the Result.
    pub fn check(&self) -> Result<(), String> {
        self.check_brackets()
    }

    /// Checks the left and right brackets and returns the Result.
    fn check_brackets(&self) -> Result<(), String> {
        let mut left_brackets: Vec<&BrainfuckInstr> = Vec::new();

        // Collect left brackets and pop when we find matching right brackets.
        for bf_instr in &self.instrs {
            if bf_instr.instr == BrainfuckInstrRaw::LeftBracket {
                left_brackets.push(&bf_instr);
            } else if bf_instr.instr == BrainfuckInstrRaw::RightBracket {
                match left_brackets.pop() {
                    Some(_) => (),
                    None => return Err(self.error_msg(bf_instr, "Unmatched ]".to_string())),
                };
            }
        }

        // Error if there are remaining unmatched left_brackets
        match left_brackets.iter().last() {
            Some(v) => Err(self.error_msg(v, "Unmatched [".to_string())),
            None => Ok(()),
        }
    }

    /// Returns a nicely formatted error message.
    fn error_msg(&self, instr: &BrainfuckInstr, msg: String) -> String {
        let path_str = self.path().to_string_lossy().into_owned();
        format!("{}:{}:{}: {}", path_str, instr.line1(), instr.column(), msg)
    }
}

#[cfg(test)]
mod tests {
    use super::{BrainfuckInstrRaw, BrainfuckProg};
    use std::path::Path;

    // Store the line and column
    struct Position {
        line: usize,
        column: usize,
    }

    // Some default sequence, which we can test against.
    const CORRECT_INSTRS: [BrainfuckInstrRaw; 8] = [
        BrainfuckInstrRaw::LessThan,
        BrainfuckInstrRaw::GreaterThan,
        BrainfuckInstrRaw::LeftBracket,
        BrainfuckInstrRaw::RightBracket,
        BrainfuckInstrRaw::Minus,
        BrainfuckInstrRaw::Plus,
        BrainfuckInstrRaw::Comma,
        BrainfuckInstrRaw::Fullstop,
    ];

    #[test]
    fn test_program() {
        let fake_path = "path/to/file.bf";
        let another_path = "path/to/somewhere/else.bf";

        // Construct
        let b = BrainfuckProg::new(fake_path, "<>[]-+,.".to_string());

        // Check the path is stored correctly
        assert_eq!(Path::new(fake_path), b.path.as_path());
        assert_ne!(Path::new(another_path), b.path.as_path());

        // Check the program
        let p = b.instrs();

        for (i, cinstr) in CORRECT_INSTRS.iter().enumerate() {
            assert_eq!(p[i].instr, *cinstr);
            assert_eq!(p[i].line1(), 1);
            assert_eq!(p[i].column(), i);
        }

        // Check the program backwards (verify BrainfuckInstrRaw PartialEq)
        for (i, cinstr) in CORRECT_INSTRS.iter().rev().enumerate() {
            assert_ne!(p[i].instr, *cinstr);
        }
    }

    #[test]
    fn test_program_with_comments() {
        let prog_str = "this < is > a [ valid ]\n\
            brainfuck - program +\n\
            these , are . comments"
            .to_string();
        let correct_pos = [
            Position { line: 0, column: 5 },
            Position {
                line: 0,
                column: 10,
            },
            Position {
                line: 0,
                column: 14,
            },
            Position {
                line: 0,
                column: 22,
            },
            Position {
                line: 1,
                column: 10,
            },
            Position {
                line: 1,
                column: 20,
            },
            Position { line: 2, column: 6 },
            Position {
                line: 2,
                column: 12,
            },
        ];
        let b = BrainfuckProg::new("path/to/file.bf", prog_str);

        // Check the program
        let p = b.instrs();
        for (i, cinstr) in CORRECT_INSTRS.iter().enumerate() {
            assert_eq!(p[i].instr, *cinstr);
            assert_eq!(p[i].line1(), correct_pos[i].line + 1);
            assert_eq!(p[i].column(), correct_pos[i].column);
        }
    }

    #[test]
    fn test_program_with_matched_brackets() {
        let fake_path = "path/to/file.bf";
        let b = BrainfuckProg::new(fake_path, "<>[[[]-]+],.".to_string());
        b.check().unwrap();
    }

    #[test]
    #[should_panic]
    fn test_program_with_unmatched_brackets() {
        let fake_path = "path/to/file.bf";
        let b1 = BrainfuckProg::new(fake_path, "<>[[]-+,.".to_string());
        b1.check().unwrap();
        let b2 = BrainfuckProg::new(fake_path, "<>[[]]]-+,.".to_string());
        b2.check().unwrap();
    }

    #[test]
    #[should_panic]
    fn test_bad_path() {
        BrainfuckProg::from_file("/path/to/file.bf").unwrap();
    }
}
