//! A Brainfuck Interpreter written in Rust!

#![deny(missing_docs)]

use bft_interp::BrainfuckVm;
use bft_types::BrainfuckProg;
use std::error::Error;
use std::io;
use std::ops::Drop;

mod cli;
use cli::{BrainfuckOpt, StructOpt};

/// Proxy writer which ensures the last byte written is a new-line.
struct TidyWriter<T> {
    writer: T,

    /// Keep track of the last byte.
    last_u8: u8,
}

impl<T> io::Write for TidyWriter<T>
where
    T: io::Write,
{
    /// Proxy write command which tracks the last byte.
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        if let Some(l) = buf.last() {
            self.last_u8 = *l;
        }
        self.writer.write(buf)
    }

    /// Proxy flush command.
    fn flush(&mut self) -> io::Result<()> {
        self.writer.flush()
    }
}

impl<T> Drop for TidyWriter<T> {
    /// When the TidyWriter is dropped, ensure there is a new line.
    fn drop(&mut self) {
        if self.last_u8 != b"\n"[0] {
            println!()
        }
    }
}

/// Run the Brainfuck Interpreter.
fn run_bft(opt: BrainfuckOpt) -> Result<(), Box<dyn Error>> {
    let num_cells = opt.cells.unwrap_or_default();
    let bf_prog = BrainfuckProg::from_file(opt.file)?;
    bf_prog.check()?;

    let mut bf_vm: BrainfuckVm<u8> = BrainfuckVm::new(&bf_prog, num_cells, opt.extensible);
    let twriter = TidyWriter {
        writer: io::stdout(),
        last_u8: 0,
    };
    bf_vm.interpret(io::stdin(), twriter)?;
    Ok(())
}

/// Parse the arguments, run the program and return sensible errors.
fn main() {
    let opt = BrainfuckOpt::from_args();
    std::process::exit(match run_bft(opt) {
        Ok(_) => 0,
        Err(err) => {
            eprintln!("bft: error: {}", err);
            1
        }
    });
}
