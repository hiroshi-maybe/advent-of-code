#![allow(unused_macros, unused_imports)]
use std::cmp::*;
use std::collections::*;

// $ cp-batch day12part2 | diff day12part2.out -
// $ cargo run --bin day12part2

///
/// 12/23/2024
///
/// 11:50-12:35 AC
///

// vert x2, hor x2
const MOVES: [(isize, isize); 4] = [(1, 0), (-1, 0), (0, 1), (0, -1)];

fn solve() -> usize {
    let n = 140;
    // let n = 10;
    let mut a = vec![];
    for _ in 0..n {
        let b = readln!([char]);
        a.push(b);
    }
    let m = a[0].len();

    let mut viz = vec![vec![false; m]; n];
    let mut res = 0;
    for i in 0..n {
        for j in 0..m {
            let ans = dfs(i, j, n, m, &a, &mut viz);
            // dbgln!(a[i][j], ans.0, ans.1);
            res += ans.0 * ans.1;
        }
    }
    res
}

fn dfs(
    i: usize,
    j: usize,
    n: usize,
    m: usize,
    a: &Vec<Vec<char>>,
    viz: &mut Vec<Vec<bool>>,
) -> (usize, usize) {
    if viz[i][j] {
        return (0, 0);
    }
    viz[i][j] = true;

    let (mut side, mut area) = (0, 1);
    for k in 0..MOVES.len() {
        let mo = MOVES[k];

        if is_border(i, j, mo, n, m, a) {
            let adj = if k < 2 {
                (i, j.wrapping_add_signed(-1))
            } else {
                (i.wrapping_add_signed(-1), j)
            };

            if adj.0 < n
                && adj.1 < m
                && a[i][j] == a[adj.0][adj.1]
                && is_border(adj.0, adj.1, mo, n, m, a)
            {
                continue;
            }
            // dbgln!(i, j, adj);
            side += 1;
        } else {
            let ii = i.wrapping_add_signed(mo.0);
            let jj = j.wrapping_add_signed(mo.1);
            let (p, a) = dfs(ii, jj, n, m, a, viz);
            side += p;
            area += a;
        }
    }

    (side, area)
}

fn is_border(
    i: usize,
    j: usize,
    mo: (isize, isize),
    n: usize,
    m: usize,
    a: &Vec<Vec<char>>,
) -> bool {
    let ii = i.wrapping_add_signed(mo.0);
    let jj = j.wrapping_add_signed(mo.1);
    if ii < n && jj < m {
        a[i][j] != a[ii][jj]
    } else {
        true
    }
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
