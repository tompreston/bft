use std::fmt;
use std::io;
use std::path::Path;

#[derive(Debug)]
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

        return program;
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

#[derive(Debug)]
pub struct BrainfuckProg {
    // TODO I don't know how to handle this
    path: &Path,
    program: Vec<BrainfuckInstr>,
}

impl BrainfuckProg {
    fn new<P: AsRef<Path>>(path: P, content: String) -> Self {
        Self {
            path: path.as_ref(),
            program: BrainfuckInstr::from_string(content),
        }
    }

    fn from_file<P: AsRef<Path>>(path: P) -> io::Result<Self> {
        let content = std::fs::read_to_string(path).expect("Failed to read_to_string");
        Ok(Self::new(path, content))
    }

    // TODO getters for private members
}

#[cfg(test)]
mod tests {}
