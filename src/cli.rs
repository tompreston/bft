use std::path::PathBuf;
pub use structopt::StructOpt;

/// Returns Ok() if string is a non-zero number.
fn is_num_positive(s: String) -> Result<(), String> {
    let n: usize = match s.parse() {
        Ok(v) => v,
        Err(_) => return Err("Not a number".to_string()),
    };
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
    /// Set the number of cells in the BrainfuckVM.
    #[structopt(short, long, validator = is_num_positive)]
    pub cells: Option<usize>,

    /// Turns on the BrainfuckVM auto-extending tape.
    #[structopt(short, long)]
    pub extensible: bool,

    /// Path to Brainfuck program file.
    #[structopt(parse(from_os_str))]
    pub file: PathBuf,
}
