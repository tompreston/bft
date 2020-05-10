use bft_interp::BrainfuckVM;
use bft_types::BrainfuckProg;
use std::error::Error;

mod cli;
use cli::{BrainfuckOpt, StructOpt};

fn run_bft(opt: BrainfuckOpt) -> Result<(), Box<dyn Error>> {
    let num_cells = match opt.cells {
        Some(n) => n,
        None => 0,
    };
    let bf_prog = BrainfuckProg::from_file(opt.file)?;
    bf_prog.check()?;

    let bf_vm: BrainfuckVM<u8> = BrainfuckVM::new(&bf_prog, num_cells, opt.extensible);
    bf_vm.run_program();
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
