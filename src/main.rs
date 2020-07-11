use rand::seq::IteratorRandom;
use rand::Rng;

mod board;
use crate::board::Board;

fn tree_search_dfs<F: Fn(Board) -> f64>(b: Board, depth: usize, f: &F) -> f64 {
    if depth == 0 {
        return f(b);
    }
    let mut s = 0.0;
    let mut n = 0.0;
    for ms in b.iter_growth() {
        for (w, m) in [(9.0, ms.set(1)), (1.0, ms.set(2))].iter() {
            let mut b = 0f64;
            for s in m.iter_moves() {
                b = b.max(tree_search_dfs(s, depth - 1, f));
            }
            s += w * b;
            n += w;
        }
    }
    if n == 0.0 {
        0f64
    } else {
        s / n
    }
}

struct TreeSearchNode {
    board: Board,
    children: Option<Vec<(f64, Vec<TreeSearchNode>)>>,
}

impl TreeSearchNode {
    fn new(board: Board) -> Self {
        TreeSearchNode {
            board,
            children: None,
        }
    }

    fn max_weight_leaf(&mut self) -> Option<(f64, &mut TreeSearchNode)> {
        match self.children {
            None => Some((0.0, self)),
            Some(ref mut children) => children
                .iter_mut()
                .filter_map(|(w, v)| {
                    match v
                        .iter_mut()
                        .filter_map(|n| n.max_weight_leaf())
                        .max_by(|a, b| {
                            if a.0 < b.0 {
                                std::cmp::Ordering::Less
                            } else {
                                std::cmp::Ordering::Greater
                            }
                        }) {
                        None => None,
                        Some((a, b)) => Some((*w + a, b)),
                    }
                })
                .max_by(|a, b| {
                    if a.0 < b.0 {
                        std::cmp::Ordering::Less
                    } else {
                        std::cmp::Ordering::Greater
                    }
                }),
        }
    }

    fn find_heavy_leaf(&mut self, threshold: f64) -> (usize, Option<&mut TreeSearchNode>) {
        match self.children {
            None => (1, if threshold <= 0.0 { Some(self) } else { None }),
            Some(ref mut children) => {
                let mut count = 0;
                for (w, v) in children.iter_mut() {
                    for n in v.iter_mut() {
                        let (c, res) = n.find_heavy_leaf(threshold - *w);
                        count += c;
                        if let Some(r) = res {
                            return (count, Some(r));
                        }
                    }
                }
                (count, None)
            }
        }
    }

    fn expand(&mut self) {
        assert!(self.children.is_none());
        let mut children = vec![];
        let growth = self.board.iter_growth().collect::<Vec<_>>();
        let log_n = (growth.len() as f64).ln();
        for ms in growth {
            for (w, m) in [(0.9f64.ln(), ms.set(1)), (0.1f64.ln(), ms.set(2))].iter() {
                let mut c = vec![];
                for s in m.iter_moves() {
                    c.push(TreeSearchNode {
                        board: s,
                        children: None,
                    });
                }
                children.push((w - log_n, c));
            }
        }
        self.children = Some(children);
    }

    fn evaluate<F: FnMut(Board, f64) -> f64>(&self, f: &mut F, w: f64) -> f64 {
        match self.children {
            None => f(self.board, w.exp()),
            Some(ref children) => {
                let mut s = 0.0;
                for (v, c) in children.iter() {
                    s += c
                        .iter()
                        .map(|a| a.evaluate(f, w + v))
                        .max_by(|a, b| {
                            if a < b {
                                std::cmp::Ordering::Less
                            } else {
                                std::cmp::Ordering::Greater
                            }
                        })
                        .unwrap_or(0.0);
                }
                s
            }
        }
    }
}

fn tree_search<F: Fn(usize, Board) -> f64>(
    b: Board,
    max_count: usize,
    min_weight: f64,
    f: &F,
) -> f64 {
    let mut s = TreeSearchNode::new(b);
    let log_min_weight = min_weight.ln();
    let count = loop {
        let (c, n) = s.find_heavy_leaf(log_min_weight);
        if c > max_count {
            break c;
        }
        if let Some(x) = n {
            // println!("Found a heavy leaf after looking at {} leaves", c);
            x.expand();
        } else {
            break c;
        }
    };
    let mut actual_count = 0;
    let r = s.evaluate(
        &mut |b, w| {
            // println!("Evaluate a leaf with weight {}", w);
            actual_count += 1;
            f(count, b) * w
        },
        0.0,
    );
    r
}

fn board_value(board: Board) -> f64 {
    let [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p] = board.tiles();

    fn v(a: u8, b: u8, c: u8, d: u8) -> isize {
        [a.cmp(&b), b.cmp(&c), c.cmp(&d)]
            .iter()
            .map(|v| match v {
                std::cmp::Ordering::Less => -1,
                std::cmp::Ordering::Equal => 0,
                std::cmp::Ordering::Greater => 1,
            })
            .sum()
    }
    1000.0
        + board.tiles().iter().filter(|v| **v == 0).count() as f64
        + ((v(a, b, c, d) + v(e, f, g, h) + v(i, j, k, l) + v(m, n, o, p)).abs()
            + (v(a, e, i, m) + v(b, f, j, n) + v(c, g, k, o) + v(d, h, l, p)).abs())
            as f64
    //2.0f64.powi(*b.tiles().iter().max().unwrap() as i32)
}

fn play<F: FnMut(Board) -> f64>(f: &mut F) {
    let mut rng = rand::thread_rng();
    let mut board = Board::new()
        .iter_growth()
        .choose(&mut rng)
        .unwrap()
        .set(if rng.gen_range(0, 10) < 9 { 1 } else { 2 });
    let mut i = 0;
    let mut known_value = None;
    loop {
        println!(
            "Board {} (naive={} expected={}):\n{}\n",
            i,
            board_value(board),
            known_value.unwrap_or(-1.0),
            board
        );
        let mut it = board.iter_moves();
        let mut best = match it.next() {
            None => {
                println!("No moves!");
                break;
            }
            Some(m) => m,
        };
        let mut best_value = None;
        for m in it {
            let w = best_value.get_or_insert_with(|| f(best));
            let v = f(m);
            if v > *w {
                best = m;
                best_value = Some(v);
            }
        }
        board = best
            .iter_growth()
            .choose(&mut rng)
            .unwrap()
            .set(if rng.gen_range(0, 10) < 9 { 1 } else { 2 });
        known_value = best_value;
        i += 1;
    }
}

fn main() {
    play(&mut |b| {
        tree_search(b, 10000, 0.1, &|c, b| {
            tree_search_dfs(
                b,
                if c < 50 {
                    4
                } else if c < 1000 {
                    2
                } else if c < 10000 {
                    1
                } else {
                    0
                },
                &board_value,
            )
        })
    });
}
