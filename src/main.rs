use bft_interp::BrainfuckVM;
use bft_types::BrainfuckProg;
use std::error::Error;

mod cli;
use cli::{BrainfuckOpt, StructOpt};

fn main() -> Result<(), Box<dyn Error>> {
    let opt = BrainfuckOpt::from_args();

    let num_cells = match opt.cells {
        Some(n) => n,
        None => 0,
    };
    let bf_vm: BrainfuckVM<u8> = BrainfuckVM::new(num_cells, opt.extensible);

    let bf_prog = BrainfuckProg::from_file(opt.file)?;
    bf_prog.check()?;
    bf_vm.run_prog(&bf_prog);
    Ok(())
}
