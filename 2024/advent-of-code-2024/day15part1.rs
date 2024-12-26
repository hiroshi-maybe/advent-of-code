#![allow(unused_macros, unused_imports)]
use std::cmp::*;
use std::collections::*;
use std::ops::Index;

// $ cp-batch day15part1 | diff day15part1.out -
// $ cargo run --bin day15part1

///
/// 12/26/2024
///
/// 14:22-15:16 AC
///

fn solve() -> usize {
    let mut a = vec![];
    let mut moves = vec![];
    let (mut i, mut j) = (0, 0);
    let mut empty_ln_cnt = 0;
    while empty_ln_cnt < 2 {
        let s = readln_str();
        let s = s.trim_end();
        if s.len() == 0 {
            empty_ln_cnt += 1;
            continue;
        }

        let mut b = s.chars().collect_vec();
        if b[0] == '#' {
            if let Some(jj) = b.iter().position(|&c| c == '@') {
                i = a.len();
                j = jj;
                b[jj] = '.';
            }
            a.push(b);
        } else {
            moves.append(&mut b);
        }
    }
    let n = a.len();
    let m = a[0].len();

    for mv_c in moves {
        dbgln!(mv_c);

        let mo = match mv_c {
            '<' => (0isize, -1isize),
            '>' => (0, 1),
            '^' => (-1, 0),
            'v' => (1, 0),
            _ => unreachable!(),
        };

        let (mut ii, mut jj) = mv(i, j, mo);
        match a[ii][jj] {
            '.' => {
                i = ii;
                j = jj;
            }
            '#' => {}
            'O' => {
                let (org_ii, org_jj) = (ii, jj);
                while a[ii][jj] == 'O' {
                    (ii, jj) = mv(ii, jj, mo);
                }
                match a[ii][jj] {
                    '#' => {}
                    '.' => {
                        (i, j) = (org_ii, org_jj);
                        while (ii, jj) != (i, j) {
                            // dbgln!(ii, jj, i, j);
                            a[ii][jj] = 'O';
                            (ii, jj) = mv(ii, jj, (-mo.0, -mo.1));
                        }
                    }
                    _ => unreachable!(),
                }
            }
            _ => unreachable!(),
        }
        a[i][j] = '.';

        /*
        for ii in 0..n {
            for jj in 0..m {
                print!("{}", if ii == i && jj == j { '@' } else { a[ii][jj] });
            }
            println!();
        } */
    }

    let mut res = 0;
    for i in 0..n {
        for j in 0..m {
            if a[i][j] == 'O' {
                res += i * 100 + j;
            }
        }
    }
    res
}

fn mv(i: usize, j: usize, m: (isize, isize)) -> (usize, usize) {
    (i.wrapping_add_signed(m.0), j.wrapping_add_signed(m.1))
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
