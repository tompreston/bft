use bft_interp::BrainfuckVM;
use bft_types::BrainfuckProg;
use std::error::Error;

fn main() -> Result<(), Box<dyn Error>> {
    let fname = std::env::args().nth(1).ok_or("Expected filename")?;
    let bf_prog = BrainfuckProg::from_file(fname)?;
    let bf_vm: BrainfuckVM<u8> = BrainfuckVM::new(0, false);
    println!("{:?}", bf_prog);
    println!("{:?}", bf_vm);
    Ok(())
}
