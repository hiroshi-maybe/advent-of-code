#![allow(unused_macros, unused_imports)]
use std::cmp::*;
use std::collections::*;

// $ cp-batch day22part2 | diff day22part2.out -
// $ cargo run --bin day22part2

///
/// 12/29/2024
///
/// 14:31-15:02 AC
///

fn solve() -> usize {
    let mut dp2 = vec![vec![vec![vec![0; 20]; 20]; 20]; 20];
    loop {
        let s = readln_str();
        let s = s.trim_end();
        if s.is_empty() {
            break;
        }

        let mut n = s.parse::<usize>().unwrap();
        let mut vals = vec![n % 10];
        for _ in 0..2000 {
            n = f(n);
            vals.push(n % 10);
        }
        assert_eq!(vals.len(), 2001);

        let mut dp = vec![vec![vec![vec![0; 20]; 20]; 20]; 20];
        for w in vals.windows(5) {
            let price = w[4];
            // assert!(price < 10);
            let difs = w.windows(2).map(|vs| vs[1] + 10 - vs[0]).collect_vec();
            // assert_eq!(difs.len(), 4);
            if dp[difs[0]][difs[1]][difs[2]][difs[3]] == 0 {
                dp[difs[0]][difs[1]][difs[2]][difs[3]] = price;
            }
        }
        for i in 0..20 {
            for j in 0..20 {
                for k in 0..20 {
                    for l in 0..20 {
                        dp2[i][j][k][l] += dp[i][j][k][l];
                    }
                }
            }
        }
    }

    let mut res = 0;
    for i in 0..20 {
        for j in 0..20 {
            for k in 0..20 {
                for l in 0..20 {
                    res.setmax(dp2[i][j][k][l]);
                }
            }
        }
    }
    res
}

fn f(x: usize) -> usize {
    let x = mix(x * 64, x);
    let x = prune(x);

    let x = mix(x, x / 32);
    let x = prune(x);

    let x = mix(x, x * 2048);
    prune(x)
}

fn mix(x: usize, y: usize) -> usize {
    x ^ y
}

fn prune(x: usize) -> usize {
    x % 16777216
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
