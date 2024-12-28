#![allow(unused_macros, unused_imports)]
use std::cmp::*;
use std::collections::*;
use std::i64;

// $ cp-batch day16part1 | diff day16part1.out -
// $ cargo run --bin day16part1

///
/// 12/28/2024
///
/// 13:00-13:49 AC
///

// vert x2, hor x2
const MOVES: [(isize, isize); 4] = [(1, 0), (0, 1), (-1, 0), (0, -1)];

fn solve() -> i64 {
    let mut a = vec![];
    let (mut si, mut sj) = (0, 0);
    let (mut di, mut dj) = (0, 0);
    loop {
        let s = readln_str();
        let s = s.trim_end();
        if s.is_empty() {
            break;
        }

        let cs = s.chars().collect_vec();
        if let Some(jj) = cs.iter().position(|&c| c == 'S') {
            si = a.len();
            sj = jj;
        }
        if let Some(jj) = cs.iter().position(|&c| c == 'E') {
            di = a.len();
            dj = jj;
        }

        a.push(cs);
    }

    let n = a.len();
    let m = a[0].len();

    let inf = i64::MAX;
    let mut dist = vec![vec![vec![inf; 4]; m]; n];

    let mut q = BinaryHeap::new();
    q.push((Reverse(0), (si, sj), 1));
    dist[si][sj][1] = 0;

    while let Some((Reverse(score), (i, j), dir)) = q.pop() {
        // dbgln!(score, i, j, dir);
        let mo = MOVES[dir];
        let ii = i.wrapping_add_signed(mo.0);
        let jj = j.wrapping_add_signed(mo.1);

        if a[ii][jj] != '#' && score + 1 < dist[ii][jj][dir] {
            dist[ii][jj][dir] = score + 1;
            q.push((Reverse(score + 1), (ii, jj), dir));
        }

        for delta in [-1isize, 1] {
            let dir2 = ((dir + MOVES.len()).wrapping_add_signed(delta)) % MOVES.len();
            if score + 1000 < dist[i][j][dir2] {
                dist[i][j][dir2] = score + 1000;
                q.push((Reverse(score + 1000), (i, j), dir2));
            }
        }
    }

    *dist[di][dj].iter().min().unwrap()
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
