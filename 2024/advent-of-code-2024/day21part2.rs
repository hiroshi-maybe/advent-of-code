#![allow(unused_macros, unused_imports)]
use std::cmp::*;
use std::collections::*;

// $ cp-batch day21part2 | diff day21part2.out -
// $ cargo run --bin day21part2

///
/// 12/29/2024
///
/// 14:08-14:19 AC
///

const MOVES: [(isize, isize, usize); 4] = [(1, 0, 4), (0, 1, 5), (-1, 0, 1), (0, -1, 3)];
const POS_A: usize = 2;
const DIR_KEYS: [[char; 3]; 2] = [['#', '^', 'A'], ['<', 'v', '>']];
const NUM_KEYS: [[char; 3]; 4] = [
    ['7', '8', '9'],
    ['4', '5', '6'],
    ['1', '2', '3'],
    ['#', '0', 'A'],
];

fn solve() -> usize {
    let mut res = 0;
    loop {
        let s = readln_str();
        let s = s.trim_end();
        if s.is_empty() {
            break;
        }

        let seq = prepend_a(s.chars().collect_vec());
        let mut code = 0;
        for &c in &seq {
            let d = (c as u8).wrapping_sub(b'0' as u8);
            if d < 10 {
                code = code * 10 + d as usize;
            }
        }

        let len = shortest_sequence(s);

        dbgln!(seq, len, code);

        res += len * code;
    }

    res
}

fn shortest_sequence(s: &str) -> usize {
    let seq = prepend_a(s.chars().collect_vec());
    let mut memo = vec![vec![vec![None; 6]; 6]; 25];

    seq.windows(2)
        .map(|cs| {
            let cur = cs[0];
            let dest: char = cs[1];

            let st = find_key(cur, &NUM_KEYS);
            let dest = find_key(dest, &NUM_KEYS);

            cost_for_numeric(st, dest, &mut memo)
        })
        .sum::<usize>()
}

fn cost_for_numeric(
    st: (usize, usize),
    dest: (usize, usize),
    memo: &mut Vec<Vec<Vec<Option<usize>>>>,
) -> usize {
    let inf = usize::MAX / 10;
    let mut dist = vec![vec![vec![vec![inf; 6]; 6]; NUM_KEYS[0].len()]; NUM_KEYS.len()];
    let mut res = vec![inf; 6];
    let mut q: BinaryHeap<(Reverse<usize>, (usize, usize), usize)> = BinaryHeap::new();
    q.push((Reverse(0), st, POS_A));
    while let Some((Reverse(d), (i, j), prev)) = q.pop() {
        if i == dest.0 && j == dest.1 {
            let w = cost0(prev, POS_A, 24, memo);
            res[prev].setmin(d + w);
            continue;
        }
        for mo in MOVES {
            let ii = i.wrapping_add_signed(mo.0);
            let jj = j.wrapping_add_signed(mo.1);

            if ii < NUM_KEYS.len() && jj < NUM_KEYS[0].len() && NUM_KEYS[ii][jj] != '#' {
                let w = cost0(prev, mo.2, 24, memo);
                // dbgln!(
                //     NUM_KEYS[i][j],
                //     NUM_KEYS[ii][jj],
                //     to_key(prev),
                //     to_key(mo.2),
                //     w
                // );
                if dist[ii][jj][prev][mo.2].setmin(d + w) {
                    // dbgln!(NUM_KEYS[ii][jj], d + w, dir_key(prev), dir_key(mo.2));
                    q.push((Reverse(d + w), (ii, jj), mo.2));
                }
            }
        }
    }
    let res = res.iter().copied().min().unwrap();
    // dbgln!(NUM_KEYS[st.0][st.1], NUM_KEYS[dest.0][dest.1], res);
    res
}

// fn dir_key(pos: usize) -> char {
//     DIR_KEYS[pos / 3][pos % 3]
// }

fn cost0(
    start: usize,
    destination: usize,
    depth: usize,
    memo: &mut Vec<Vec<Vec<Option<usize>>>>,
) -> usize {
    if let Some(res) = memo[depth][start][destination] {
        return res;
    }

    if depth == 0 {
        let res = cost1(start, destination);
        memo[depth][start][destination] = Some(res);
        return res;
    }

    let m = DIR_KEYS[0].len();
    let st = (start / m, start % m);
    let dest = (destination / m, destination % m);
    let inf = usize::MAX / 10;
    let mut dist = vec![vec![vec![vec![inf; 6]; 6]; m]; DIR_KEYS.len()];
    let mut res = vec![inf; 6];
    let mut q = BinaryHeap::new();
    q.push((Reverse(0), st, POS_A));
    while let Some((Reverse(d), (i, j), prev)) = q.pop() {
        if i == dest.0 && j == dest.1 {
            let w = cost0(prev, POS_A, depth - 1, memo);
            res[prev].setmin(d + w);
            continue;
        }
        for mo in MOVES {
            let ii = i.wrapping_add_signed(mo.0);
            let jj = j.wrapping_add_signed(mo.1);

            if ii < DIR_KEYS.len() && jj < DIR_KEYS[0].len() && DIR_KEYS[ii][jj] != '#' {
                let w = cost0(prev, mo.2, depth - 1, memo);
                // dbgln!(to_key(prev), to_key(mo.2), w);
                if dist[ii][jj][prev][mo.2].setmin(d + w) {
                    q.push((Reverse(d + w), (ii, jj), mo.2));
                }
            }
        }
    }
    let res = res.iter().copied().min().unwrap();
    // dbgln!(DIR_KEYS[st.0][st.1], DIR_KEYS[dest.0][dest.1], res);

    memo[depth][start][destination] = Some(res);
    res
}

fn cost1(start: usize, dest: usize) -> usize {
    let m = DIR_KEYS[0].len();
    let di = (start / m).abs_diff(dest / m);
    let dj = (start % m).abs_diff(dest % m);
    di + dj + 1
}

fn to_key(p: usize) -> char {
    let m = DIR_KEYS[0].len();
    DIR_KEYS[p / m][p % m]
}

fn prepend_a(seq: Vec<char>) -> Vec<char> {
    let mut res = vec!['A'];
    for c in seq {
        res.push(c);
    }
    res
}

fn find_key(c: char, keys: &[[char; 3]; 4]) -> (usize, usize) {
    let mut res = None;
    for i in 0..keys.len() {
        for j in 0..keys[i].len() {
            if keys[i][j] == c {
                res = Some((i, j));
            }
        }
    }
    res.unwrap()
}

fn main() {
    setup_out!(put, puts);

    let res = solve();
    puts!("{}", res);
}

use crate::cplib::io::*;
use crate::cplib::minmax::*;
use crate::cplib::vec::*;
// region: cplib
#[rustfmt::skip]
#[allow(dead_code)]
pub mod cplib {
pub mod io {
	macro_rules! _with_dollar_sign { ($($body:tt)*) => { macro_rules! __with_dollar_sign { $($body)* } __with_dollar_sign!($); }}
	macro_rules! setup_out {
		($fn:ident,$fn_s:ident) => {
			use std::io::Write;
			let out = std::io::stdout();
			let mut out = ::std::io::BufWriter::new(out.lock());
				_with_dollar_sign! { ($d:tt) => {
				macro_rules! $fn { ($d($format:tt)*) => { let _ = write!(out,$d($format)*); } }
				macro_rules! $fn_s { ($d($format:tt)*) => { let _ = writeln!(out,$d($format)*); } }
			}}
		};
	}
	macro_rules! _epr { ($v:expr $(,)?) => {eprint!("{} = {:?}, ", stringify!($v), $v)}; }
	macro_rules! dbgln { ($($val:expr),*) => {{ eprint!("[{}:{}] ", file!(), line!()); ($(_epr!($val)),*); eprintln!(); }}; }
	pub fn readln_str() -> String {
		let mut line = String::new();
		::std::io::stdin().read_line(&mut line).unwrap_or_else(|e| panic!("{}", e));
		line
	}
	macro_rules! _read {
		($it:ident; [char]) => { _read!($it; String).chars().collect::<Vec<_>>() };
		($it:ident; [u8]) => { Vec::from(_read!($it; String).into_bytes()) };
		($it:ident; usize1) => { $it.next().unwrap_or_else(|| panic!("input mismatch")).parse::<usize>().unwrap_or_else(|e| panic!("{}", e)) - 1 };
		($it:ident; [usize1]) => { $it.map(|s| s.parse::<usize>().unwrap_or_else(|e| panic!("{}", e)) - 1).collect::<Vec<_>>() };
		($it:ident; [$t:ty]) => { $it.map(|s| s.parse::<$t>().unwrap_or_else(|e| panic!("{}", e))).collect::<Vec<_>>() };
		($it:ident; $t:ty) => { $it.next().unwrap_or_else(|| panic!("input mismatch")).parse::<$t>().unwrap_or_else(|e| panic!("{}", e)) };
		($it:ident; $($t:tt),+) => { ($(_read!($it; $t)),*) };
	}
	macro_rules! readlns {
		($($t:tt),*; $n:expr) => {{ let stdin = ::std::io::stdin();
			::std::io::BufRead::lines(stdin.lock()).take($n).map(|line| {
				let line = line.unwrap(); #[allow(unused_mut)]let mut it = line.split_whitespace(); _read!(it; $($t),*)
			}).collect::<Vec<_>>()
		}};
	}
	macro_rules! readln {
		($($t:tt),*) => {{ let line = cplib::io::readln_str(); #[allow(unused_mut)]let mut it = line.split_whitespace(); _read!(it; $($t),*) }};
	}
	pub(crate) use {readlns, readln, setup_out, dbgln, _with_dollar_sign, _epr, _read};
}
pub mod minmax {
	pub trait SetMinMax {
		fn setmin(&mut self, other: Self) -> bool;
		fn setmax(&mut self, other: Self) -> bool;
	}
	macro_rules! _set { ($self:ident, $cmp:tt, $other:ident) => {{
			let update = $other $cmp *$self;
			if update { *$self = $other; }
			update
	}}; }
	impl<T> SetMinMax for T where T: PartialOrd {
		fn setmin(&mut self, other: T) -> bool { _set!(self, <, other) }
		fn setmax(&mut self, other: T) -> bool { _set!(self, >, other) }
	}
}
pub mod vec {
	pub trait CollectVec: Iterator { fn collect_vec(self) -> Vec<Self::Item> where Self: Sized { self.collect() } }
	impl<T> CollectVec for T where T: Iterator {}
	macro_rules! vvec {
		($v:expr; $n:expr) => { Vec::from(vec![$v; $n]) };
		($v:expr; $n:expr $(; $ns:expr)+) => { Vec::from(vec![vvec![$v $(; $ns)*]; $n]) };
	}
	pub(crate) use vvec;
}
}
// endregion: cplib
