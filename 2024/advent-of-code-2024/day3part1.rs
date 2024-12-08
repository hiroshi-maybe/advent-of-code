#![allow(unused_macros, unused_imports)]
use std::cmp::*;
use std::collections::*;

// $ cp-batch day3part1 | diff day3part1.out -
// $ cargo run --bin day3part1

///
/// 12/7/2024
///
/// 16:52-18:19 AC
///
#[derive(Debug)]
enum State {
    Mul(usize),
    Num1,
    Comma,
    Num2,
    Close,
}
const MULS: [char; 4] = ['m', 'u', 'l', '('];
fn solve(s: String) -> i64 {
    let s = s.chars().collect::<Vec<_>>();
    let n = s.len();
    let mut i = 0;
    let (mut num1, mut num2) = (0, 0);
    let mut res = 0;
    let mut st = State::Mul(0);

    let mut cnt = 0;

    while i < n {
        // println!("{}, {:?}", s[i], st);
        match st {
            State::Mul(j) => {
                if s[i] == MULS[j] {
                    if j == MULS.len() - 1 {
                        st = State::Num1;
                    } else {
                        st = State::Mul(j + 1)
                    }
                } else {
                    st = State::Mul(0);
                }
            }
            State::Num1 => {
                if let Some(d) = s[i].to_digit(10) {
                    num1 = 10 * num1 + d as i64;
                } else if s[i] == ',' {
                    st = State::Comma;
                    continue;
                } else {
                    st = State::Mul(0);
                    num1 = 0;
                }
            }
            State::Comma => {
                assert_eq!(s[i], ',');
                st = State::Num2;
            }
            State::Num2 => {
                if let Some(d) = s[i].to_digit(10) {
                    num2 = 10 * num2 + d as i64;
                } else if s[i] == ')' {
                    st = State::Close;
                    continue;
                } else {
                    st = State::Mul(0);
                    num1 = 0;
                    num2 = 0;
                }
            }
            State::Close => {
                // println!("---- {num1} * {num2}");
                res += num1 * num2;
                num1 = 0;
                num2 = 0;
                st = State::Mul(0);

                cnt += 1;
            }
        }
        i += 1;
    }
    // println!("{res} ({cnt})");

    res
}

fn main() {
    setup_out!(put, puts);

    let mut res = 0;
    for _ in 0..6 {
        let s = readln_str();
        res += solve(s);
    }

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
