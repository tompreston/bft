use std::default::Default;

#[derive(Debug)]
pub struct BrainfuckVM<T> {
    // TODO maybe we want to use std::cell::Cell
    cells: Vec<T>,
    cur_cell: usize,
    is_growable: bool,
}

impl<T> BrainfuckVM<T>
where
    T: Clone,
    T: Default,
{
    pub fn new(num_cells: usize, is_growable: bool) -> Self {
        let n = if num_cells == 0 { 30_000 } else { num_cells };
        let c: Vec<T> = vec![T::default(); n];
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
        let bfvm: BrainfuckVM<u8> = BrainfuckVM::new(0, false);
        assert_eq!(bfvm.cells.len(), 30_000);

        for num_cells in 1..11 {
            let bfvm: BrainfuckVM<u8> = BrainfuckVM::new(num_cells, false);
            assert_eq!(bfvm.cells.len(), num_cells);
        }
    }
}
