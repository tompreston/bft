//! The bft interpreter command line interface (CLI).
use std::path::PathBuf;
pub use structopt::StructOpt;

/// Returns Ok() if string is a non-zero number.
fn is_num_positive(s: String) -> Result<(), String> {
    let n: usize = s.parse().map_err(|_| "Not a number".to_string())?;
    if n == 0 {
        return Err("Not positive".to_string());
    }
    Ok(())
}

/// Options for the bft program
#[derive(StructOpt, Debug)]
#[structopt(
    name = "Brainfuck Interpreter",
    about = "A Brainfuck interpreter written in Rust!"
)]
pub struct BrainfuckOpt {
    /// Set the number of cells in the BrainfuckVm.
    #[structopt(short, long, validator = is_num_positive)]
    pub cells: Option<usize>,

    /// Turns on the BrainfuckVm auto-extending tape.
    #[structopt(short, long)]
    pub extensible: bool,

    /// Path to Brainfuck program file.
    #[structopt(parse(from_os_str))]
    pub file: PathBuf,
}
