use std::default::Default;

struct BrainfuckVM<T> {
    // TODO maybe we want to use std::cell::Cell
    cells: Vec<T>,
    cur_cell: usize,
    is_growable: bool,
}

impl<T> BrainfuckVM<T> {
    fn new(num_cells: usize, is_growable: bool) -> Self {
        let n = if num_cells == 0 { 30_000 } else { num_cells };

        // TODO figure this out
        //let c: Vec<T> = vec![Default::default(); n];
        let mut cells: Vec<T> = Vec::new();
        for i in 0..n {
            cells.push(0); // waaaa, how do I know the default val of a gerneic
        }

        BrainfuckVM {
            cells: c,
            cur_cell: 0,
            is_growable: is_growable,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::BrainfuckVM;

    #[test]
    fn test_brainfuckvm_init() {
        for num_cells in 0..10 {
            let bfvm: BrainfuckVM<u8> = BrainfuckVM::new(num_cells, false);
            assert_eq!(bfvm.cells.len(), num_cells);
        }
    }
}
