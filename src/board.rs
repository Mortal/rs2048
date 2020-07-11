#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Board {
    tiles: [u8; 16],
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

impl Board {
    pub fn new() -> Self {
        Self { tiles: [0; 16] }
    }

    pub fn tiles(&self) -> [u8; 16] {
        self.tiles
    }

    pub fn iter_moves(self) -> BoardMoves {
        BoardMoves { board: self, i: 0 }
    }

    pub fn iter_growth(self) -> BoardGrowthIterator {
        BoardGrowthIterator { board: self, i: 0 }
    }

    fn gravity1(self) -> Self {
        let [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p] = self.tiles;
        let (a, b, c, d) = gravity4(a, b, c, d);
        let (e, f, g, h) = gravity4(e, f, g, h);
        let (i, j, k, l) = gravity4(i, j, k, l);
        let (m, n, o, p) = gravity4(m, n, o, p);
        Board {
            tiles: [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p],
        }
    }

    fn gravity2(self) -> Self {
        let [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p] = self.tiles;
        let (d, c, b, a) = gravity4(d, c, b, a);
        let (h, g, f, e) = gravity4(h, g, f, e);
        let (l, k, j, i) = gravity4(l, k, j, i);
        let (p, o, n, m) = gravity4(p, o, n, m);
        Board {
            tiles: [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p],
        }
    }

    fn gravity3(self) -> Self {
        let [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p] = self.tiles;
        let (a, e, i, m) = gravity4(a, e, i, m);
        let (b, f, j, n) = gravity4(b, f, j, n);
        let (c, g, k, o) = gravity4(c, g, k, o);
        let (d, h, l, p) = gravity4(d, h, l, p);
        Board {
            tiles: [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p],
        }
    }

    fn gravity4(self) -> Self {
        let [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p] = self.tiles;
        let (m, i, e, a) = gravity4(m, i, e, a);
        let (n, j, f, b) = gravity4(n, j, f, b);
        let (o, k, g, c) = gravity4(o, k, g, c);
        let (p, l, h, d) = gravity4(p, l, h, d);
        Board {
            tiles: [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p],
        }
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

pub struct BoardGrowthIterator {
    board: Board,
    i: u8,
}

pub struct BoardGrowth {
    board: Board,
    i: u8,
}

impl BoardGrowth {
    pub fn set(&self, v: u8) -> Board {
        let mut b = self.board;
        b.tiles[self.i as usize] = v;
        b
    }
}

impl Iterator for BoardGrowthIterator {
    type Item = BoardGrowth;

    fn next(&mut self) -> Option<Self::Item> {
        while self.i < 16 && self.board.tiles[self.i as usize] != 0 {
            self.i += 1;
        }
        if self.i == 16 {
            None
        } else {
            let res = BoardGrowth {
                board: self.board,
                i: self.i,
            };
            self.i += 1;
            Some(res)
        }
    }
}

impl std::fmt::Display for Board {
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
        let [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p] = self.tiles;
        write!(fmt, "{:^5}{:^5}{:^5}{:^5}\n\n{:^5}{:^5}{:^5}{:^5}\n\n{:^5}{:^5}{:^5}{:^5}\n\n{:^5}{:^5}{:^5}{:^5}", 1 << a, 1 << b, 1 << c, 1 << d, 1 << e, 1 << f, 1 << g, 1 << h, 1 << i, 1 << j, 1 << k, 1 << l, 1 << m, 1 << n, 1 << o, 1 << p)
    }
}
