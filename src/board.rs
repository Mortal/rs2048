#[derive(Debug, Clone, Copy, PartialEq, Hash)]
pub struct Board {
    board: u64,
    // tiles: [u8; 16],
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
