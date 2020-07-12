#[derive(Clone, Copy, PartialEq, Hash)]
pub struct Board {
    board: u64,
    // tiles: [u8; 16],
}

impl Board {
    pub fn transpose(&self) -> Board {
        // https://github.com/nneonneo/2048-ai
        let x = self.board;
        let a1 = x & 0xF0F00F0FF0F00F0F;
        let a2 = x & 0x0000F0F00000F0F0;
        let a3 = x & 0x0F0F00000F0F0000;
        let a = a1 | (a2 << 12) | (a3 >> 12);
        let b1 = a & 0xFF00FF0000FF00FF;
        let b2 = a & 0x00FF00FF00000000;
        let b3 = a & 0x00000000FF00FF00;
        Board { board: b1 | (b2 >> 24) | (b3 << 24) }
    }

    pub fn count_empty(&self) -> usize {
        // https://github.com/nneonneo/2048-ai
        let mut x = self.board;
        if x == 0 { return 16; }
        x |= (x >> 2) & 0x3333333333333333;
        x |= x >> 1;
        x = !x & 0x1111111111111111;
        // At this point each nibble is:
        //  0 if the original nibble was non-zero
        //  1 if the original nibble was zero
        // Next sum them all
        x += x >> 32;
        x += x >> 16;
        x += x >> 8;
        x += x >> 4;
        // Since the board is non-empty, the answer is at most 15,
        // so overflow is not a problem.
        (x & 0xf) as usize
    }
}

fn row_to_col(row: u16) -> u64 {
    let row = row as u64;
    (row | (row << 12) | (row << 24) | (row << 36)) & 0x000F000F000F000F
}

fn reverse_row(row: u16) -> u16 {
    (row >> 12) | ((row >> 4) & 0x00F0) | ((row << 4) & 0x0F00) | (row << 12)
}

pub struct BoardTable {
    gravity1: [u16; 0x10000],
    gravity2: [u16; 0x10000],
    gravity3: [u64; 0x10000],
    gravity4: [u64; 0x10000],
}

impl BoardTable {
    pub fn new() -> Self {
        let mut g1 = [0; 0x10000];
        let mut g2 = [0; 0x10000];
        let mut g3 = [0; 0x10000];
        let mut g4 = [0; 0x10000];
        for idx in 0..0x10000usize {
            let row = idx as u16;
            let a = (row & 0xF) as u8;
            let b = ((row >> 4) & 0xF) as u8;
            let c = ((row >> 8) & 0xF) as u8;
            let d = (row >> 12) as u8;
            let (a, b, c, d) = gravity4(a, b, c, d);
            let result = (a as u16) | ((b as u16) << 4) | ((c as u16) << 8) | ((d as u16) << 12);
            let rev_result = reverse_row(result);
            let rev_row = reverse_row(row);
            let rev_idx = rev_row as usize;
            g1[idx] = row ^ result;
            g2[rev_idx] = rev_row ^ rev_result;
            g3[idx] = row_to_col(row) ^ row_to_col(result);
            g4[rev_idx] = row_to_col(rev_row) ^ row_to_col(rev_result);
        }
        Self { gravity1: g1, gravity2: g2, gravity3: g3, gravity4: g4 }
    }

    fn gravity1(&self, board: Board) -> Board {
        let mut x = board.board;
        x ^= (self.gravity1[((x >> (0 * 16)) & 0xFFFF) as usize] as u64) << (0 * 16);
        x ^= (self.gravity1[((x >> (1 * 16)) & 0xFFFF) as usize] as u64) << (1 * 16);
        x ^= (self.gravity1[((x >> (2 * 16)) & 0xFFFF) as usize] as u64) << (2 * 16);
        x ^= (self.gravity1[((x >> (3 * 16)) & 0xFFFF) as usize] as u64) << (3 * 16);
        Board { board: x }
    }

    fn gravity2(&self, board: Board) -> Board {
        let mut x = board.board;
        x ^= (self.gravity2[((x >> (0 * 16)) & 0xFFFF) as usize] as u64) << (0 * 16);
        x ^= (self.gravity2[((x >> (1 * 16)) & 0xFFFF) as usize] as u64) << (1 * 16);
        x ^= (self.gravity2[((x >> (2 * 16)) & 0xFFFF) as usize] as u64) << (2 * 16);
        x ^= (self.gravity2[((x >> (3 * 16)) & 0xFFFF) as usize] as u64) << (3 * 16);
        Board { board: x }
    }

    fn gravity3(&self, board: Board) -> Board {
        let mut x = board.board;
        let t = board.transpose().board;
        x ^= self.gravity3[((t >> (0 * 16)) & 0xFFFF) as usize] << (0 * 4);
        x ^= self.gravity3[((t >> (1 * 16)) & 0xFFFF) as usize] << (1 * 4);
        x ^= self.gravity3[((t >> (2 * 16)) & 0xFFFF) as usize] << (2 * 4);
        x ^= self.gravity3[((t >> (3 * 16)) & 0xFFFF) as usize] << (3 * 4);
        Board { board: x }
    }

    fn gravity4(&self, board: Board) -> Board {
        let mut x = board.board;
        let t = board.transpose().board;
        x ^= self.gravity4[((t >> (0 * 16)) & 0xFFFF) as usize] << (0 * 4);
        x ^= self.gravity4[((t >> (1 * 16)) & 0xFFFF) as usize] << (1 * 4);
        x ^= self.gravity4[((t >> (2 * 16)) & 0xFFFF) as usize] << (2 * 4);
        x ^= self.gravity4[((t >> (3 * 16)) & 0xFFFF) as usize] << (3 * 4);
        Board { board: x }
    }
}

fn gravity2(a: u8, b: u8) -> (u8, u8) {
    if a == 0 {
        (b, 0)
    } else if a == b {
        (a + 1, 0)
    } else {
        (a, b)
    }
}

fn gravity3(a: u8, b: u8, c: u8) -> (u8, u8, u8) {
    if a == 0 {
        let (b, c) = gravity2(b, c);
        (b, c, 0)
    } else if a == b {
        (a + 1, c, 0)
    } else if b == 0 && a == c {
        (a + 1, 0, 0)
    } else {
        let (b, c) = gravity2(b, c);
        (a, b, c)
    }
}

fn gravity4(a: u8, b: u8, c: u8, d: u8) -> (u8, u8, u8, u8) {
    if a == 0 {
        let (b, c, d) = gravity3(b, c, d);
        (b, c, d, 0)
    } else if a == b {
        let (c, d) = gravity2(c, d);
        (a + 1, c, d, 0)
    } else if b == 0 && a == c {
        (a + 1, d, 0, 0)
    } else if b == 0 && c == 0 && a == d {
        (a + 1, 0, 0, 0)
    } else {
        let (b, c, d) = gravity3(b, c, d);
        (a, b, c, d)
    }
}

pub struct BoardTiles(u64);

#[derive(Clone, Copy)]
pub struct BoardTilesIterator(u64, usize);

impl BoardTiles {
    pub fn iter(&self) -> BoardTilesIterator {
        BoardTilesIterator(self.0, 0)
    }

    pub fn as_array(&self) -> [u8; 16] {
        let x = self.0;
        [
            (x >> (0 * 4)) as u8 & 0xf,
            (x >> (1 * 4)) as u8 & 0xf,
            (x >> (2 * 4)) as u8 & 0xf,
            (x >> (3 * 4)) as u8 & 0xf,
            (x >> (4 * 4)) as u8 & 0xf,
            (x >> (5 * 4)) as u8 & 0xf,
            (x >> (6 * 4)) as u8 & 0xf,
            (x >> (7 * 4)) as u8 & 0xf,
            (x >> (8 * 4)) as u8 & 0xf,
            (x >> (9 * 4)) as u8 & 0xf,
            (x >> (10 * 4)) as u8 & 0xf,
            (x >> (11 * 4)) as u8 & 0xf,
            (x >> (12 * 4)) as u8 & 0xf,
            (x >> (13 * 4)) as u8 & 0xf,
            (x >> (14 * 4)) as u8 & 0xf,
            (x >> (15 * 4)) as u8 & 0xf,
        ]
    }
}

impl Iterator for BoardTilesIterator {
    type Item = u8;

    fn next(&mut self) -> Option<Self::Item> {
        if self.1 < 16 {
            let v = (self.0 & 0xf) as u8;
            self.0 >>= 4;
            self.1 += 1;
            Some(v)
        } else {
            None
        }
    }
}

impl Board {
    pub fn new() -> Self {
        Self { board: 0 }
    }

    pub fn from_array(tiles: [u8; 16]) -> Self {
        Self { board:
            (tiles[0] as u64) << (0 * 4) |
            (tiles[1] as u64) << (1 * 4) |
            (tiles[2] as u64) << (2 * 4) |
            (tiles[3] as u64) << (3 * 4) |
            (tiles[4] as u64) << (4 * 4) |
            (tiles[5] as u64) << (5 * 4) |
            (tiles[6] as u64) << (6 * 4) |
            (tiles[7] as u64) << (7 * 4) |
            (tiles[8] as u64) << (8 * 4) |
            (tiles[9] as u64) << (9 * 4) |
            (tiles[10] as u64) << (10 * 4) |
            (tiles[11] as u64) << (11 * 4) |
            (tiles[12] as u64) << (12 * 4) |
            (tiles[13] as u64) << (13 * 4) |
            (tiles[14] as u64) << (14 * 4) |
            (tiles[15] as u64) << (15 * 4)
        }
    }

    pub fn tiles(&self) -> BoardTiles {
        BoardTiles(self.board)
    }

    pub fn iter_moves(self) -> BoardMoves {
        BoardMoves { board: self, i: 0 }
    }

    pub fn iter_moves_table(self, t: &BoardTable) -> BoardMovesTable {
        // assert_eq!(BoardMovesTable { board: self, i: 0, t }.collect::<Vec<_>>(), self.iter_moves().collect::<Vec<_>>());
        BoardMovesTable { board: self, i: 0, t }
    }

    pub fn iter_growth(&self) -> impl Iterator<Item=BoardGrowth> + '_ {
        self.tiles().iter().enumerate().filter_map(move |(i, v)| if v != 0 { None } else { Some(BoardGrowth{ board: *self, i: i as u8 }) })
    }

    fn gravity1(self) -> Self {
        let [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p] = self.tiles().as_array();
        let (a, b, c, d) = gravity4(a, b, c, d);
        let (e, f, g, h) = gravity4(e, f, g, h);
        let (i, j, k, l) = gravity4(i, j, k, l);
        let (m, n, o, p) = gravity4(m, n, o, p);
        Board::from_array(
            [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p]
        )
    }

    fn gravity2(self) -> Self {
        let [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p] = self.tiles().as_array();
        let (d, c, b, a) = gravity4(d, c, b, a);
        let (h, g, f, e) = gravity4(h, g, f, e);
        let (l, k, j, i) = gravity4(l, k, j, i);
        let (p, o, n, m) = gravity4(p, o, n, m);
        Board::from_array(
            [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p]
        )
    }

    fn gravity3(self) -> Self {
        let [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p] = self.tiles().as_array();
        let (a, e, i, m) = gravity4(a, e, i, m);
        let (b, f, j, n) = gravity4(b, f, j, n);
        let (c, g, k, o) = gravity4(c, g, k, o);
        let (d, h, l, p) = gravity4(d, h, l, p);
        Board::from_array(
            [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p]
        )
    }

    fn gravity4(self) -> Self {
        let [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p] = self.tiles().as_array();
        let (m, i, e, a) = gravity4(m, i, e, a);
        let (n, j, f, b) = gravity4(n, j, f, b);
        let (o, k, g, c) = gravity4(o, k, g, c);
        let (p, l, h, d) = gravity4(p, l, h, d);
        Board::from_array(
            [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p]
        )
    }
}

pub struct BoardMoves {
    board: Board,
    i: u8,
}

impl Iterator for BoardMoves {
    type Item = Board;

    fn next(&mut self) -> Option<Board> {
        if self.i == 0 {
            self.i += 1;
            let b = self.board.gravity1();
            if self.board != b {
                return Some(b);
            }
        }
        if self.i == 1 {
            self.i += 1;
            let b = self.board.gravity2();
            if self.board != b {
                return Some(b);
            }
        }
        if self.i == 2 {
            self.i += 1;
            let b = self.board.gravity3();
            if self.board != b {
                return Some(b);
            }
        }
        if self.i == 3 {
            self.i += 1;
            let b = self.board.gravity4();
            if self.board != b {
                return Some(b);
            }
        }
        None
    }
}

pub struct BoardMovesTable<'a> {
    board: Board,
    i: u8,
    t: &'a BoardTable,
}

impl<'a> Iterator for BoardMovesTable<'a> {
    type Item = Board;

    fn next(&mut self) -> Option<Board> {
        if self.i == 0 {
            self.i += 1;
            let b = self.t.gravity1(self.board);
            if self.board != b {
                return Some(b);
            }
        }
        if self.i == 1 {
            self.i += 1;
            let b = self.t.gravity2(self.board);
            if self.board != b {
                return Some(b);
            }
        }
        if self.i == 2 {
            self.i += 1;
            let b = self.t.gravity3(self.board);
            if self.board != b {
                return Some(b);
            }
        }
        if self.i == 3 {
            self.i += 1;
            let b = self.t.gravity4(self.board);
            if self.board != b {
                return Some(b);
            }
        }
        None
    }
}

pub struct BoardGrowth {
    board: Board,
    i: u8,
}

impl BoardGrowth {
    pub fn set(&self, v: u8) -> Board {
        let mut b = self.board.board;
        b |= (v as u64) << (4 * self.i);
        Board { board: b }
    }
}

impl std::fmt::Display for Board {
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
        for (i, v) in self.tiles().iter().enumerate() {
            if v == 0 {
                write!(fmt, "     ")?;
            } else {
                write!(fmt, "{:^5}", 1 << v)?;
            }
            if i < 15 && i % 4 == 3 {
                write!(fmt, "\n\n")?;
            }
        }
        Ok(())
    }
}

impl std::fmt::Debug for Board {
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(fmt, "Board::from_array({:?})", self.tiles().as_array())
    }
}
