use std::fmt;
use std::path::{Path, PathBuf};

/// Represents the eight raw Brainfuck instructions.
#[derive(Debug, PartialEq)]
enum BrainfuckInstrRaw {
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
#[derive(Debug)]
struct BrainfuckInstr {
    instr: BrainfuckInstrRaw,
    line: usize,
    column: usize,
}

impl BrainfuckInstr {
    fn from_string(s: String) -> Vec<Self> {
        let mut program: Vec<BrainfuckInstr> = Vec::new();

        for (l, pline) in s.lines().enumerate() {
            for (c, pbyte) in pline.bytes().enumerate() {
                if let Some(iraw) = BrainfuckInstrRaw::from_byte(pbyte) {
                    program.push(BrainfuckInstr {
                        instr: iraw,
                        line: l,
                        column: c,
                    });
                }
            }
        }

        program
    }

    /// Returns the line number, starting at 1
    fn line1(&self) -> usize {
        self.line + 1
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
    program: Vec<BrainfuckInstr>,
}

impl BrainfuckProg {
    pub fn new<P: AsRef<Path>>(path: P, content: String) -> Self {
        Self {
            path: path.as_ref().to_path_buf(),
            program: BrainfuckInstr::from_string(content),
        }
    }

    pub fn from_file<P: AsRef<Path>>(path: P) -> Result<Self, Box<dyn std::error::Error>> {
        let content = std::fs::read_to_string(&path)?;
        Ok(Self::new(path, content))
    }

    fn path(&self) -> &PathBuf {
        &self.path
    }

    fn program(&self) -> &[BrainfuckInstr] {
        &self.program[..]
    }
}

#[cfg(test)]
mod tests {
    use super::{BrainfuckInstrRaw, BrainfuckProg};
    use std::path::Path;

    #[test]
    fn test_valid_program() {
        let fake_path = "path/to/file.bf";
        let another_path = "path/to/somewhere/else.bf";

        // Construct
        let b = BrainfuckProg::new(fake_path, "<>[]-+,.".to_string());

        // Check the path is stored correctly
        assert_eq!(Path::new(fake_path), b.path.as_path());
        assert_ne!(Path::new(another_path), b.path.as_path());

        // Check the program
        let p = b.program();
        assert_eq!(p[0].instr, BrainfuckInstrRaw::LessThan);
        assert_eq!(p[1].instr, BrainfuckInstrRaw::GreaterThan);
        assert_eq!(p[2].instr, BrainfuckInstrRaw::LeftBracket);
        assert_eq!(p[3].instr, BrainfuckInstrRaw::RightBracket);
        assert_eq!(p[4].instr, BrainfuckInstrRaw::Minus);
        assert_eq!(p[5].instr, BrainfuckInstrRaw::Plus);
        assert_eq!(p[6].instr, BrainfuckInstrRaw::Comma);
        assert_eq!(p[7].instr, BrainfuckInstrRaw::Fullstop);

        // Check the program backwards (verify BrainfuckInstrRaw PartialEq)
        assert_ne!(p[7].instr, BrainfuckInstrRaw::LessThan);
        assert_ne!(p[6].instr, BrainfuckInstrRaw::GreaterThan);
        assert_ne!(p[5].instr, BrainfuckInstrRaw::LeftBracket);
        assert_ne!(p[4].instr, BrainfuckInstrRaw::RightBracket);
        assert_ne!(p[3].instr, BrainfuckInstrRaw::Minus);
        assert_ne!(p[2].instr, BrainfuckInstrRaw::Plus);
        assert_ne!(p[1].instr, BrainfuckInstrRaw::Comma);
        assert_ne!(p[0].instr, BrainfuckInstrRaw::Fullstop);
    }

    #[test]
    fn test_invalid_program() {
        BrainfuckProg::new("path/to/file.bf", "<>[]-+,.".to_string());
    }

    #[test]
    #[should_panic]
    fn test_bad_path() {
        BrainfuckProg::from_file("/path/to/file.bf").unwrap();
    }
}
