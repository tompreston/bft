use bft_interp::BrainfuckVM;
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
        match buf.last() {
            Some(l) => self.last_u8 = *l,
            None => (),
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

fn run_bft(opt: BrainfuckOpt) -> Result<(), Box<dyn Error>> {
    let num_cells = match opt.cells {
        Some(n) => n,
        None => 0,
    };
    let bf_prog = BrainfuckProg::from_file(opt.file)?;
    bf_prog.check()?;

    let mut bf_vm: BrainfuckVM<u8> = BrainfuckVM::new(&bf_prog, num_cells, opt.extensible);
    let twriter = TidyWriter {
        writer: io::stdout(),
        last_u8: 0,
    };
    bf_vm.interpret(io::stdin(), twriter)?;
    Ok(())
}

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
