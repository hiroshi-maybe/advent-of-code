#![allow(unused_macros, unused_imports)]
use std::cmp::*;
use std::collections::*;

// $ cp-batch day17part1 | diff day17part1.out -
// $ cargo run --bin day17part1

///
/// 12/28/2024
///
/// 14:18-15:19 AC
///

#[derive(Debug)]
struct Op {
    op_code: usize,
    operand: usize,
}

fn solve() -> String {
    let mut ra = 0;
    let mut rb = 0;
    let mut rc = 0;
    let mut prog = vec![];
    let mut empty_str_cnt = 0;
    loop {
        let s = readln_str();
        let s = s.trim_end();
        if s.starts_with("Register A: ") {
            let s = s.trim_start_matches("Register A: ");
            ra = s.parse::<usize>().unwrap();
            continue;
        }

        if s.starts_with("Register B: ") {
            let s = s.trim_start_matches("Register B: ");
            rb = s.parse::<usize>().unwrap();
            continue;
        }

        if s.starts_with("Register C: ") {
            let s = s.trim_start_matches("Register C: ");
            rc = s.parse::<usize>().unwrap();
            continue;
        }

        if s.is_empty() {
            empty_str_cnt += 1;
        }

        if empty_str_cnt == 2 {
            break;
        }

        if s.starts_with("Program: ") {
            let s = s.trim_start_matches("Program: ");
            let ds = s.split(',').collect_vec();
            let p = ds.iter().map(|d| d.parse::<usize>().unwrap()).collect_vec();

            for i in 0..p.len() / 2 {
                prog.push(Op {
                    op_code: p[2 * i],
                    operand: p[2 * i + 1],
                });
            }

            continue;
        }
    }

    let mut ip = 0;
    let mut res = vec![];
    while ip < prog.len() {
        let op = &prog[ip];
        // dbgln!(ip, op, ra, rb, rc);
        let combo_operand = |x: usize| -> usize {
            match x {
                0..=3 => x,
                4 => ra,
                5 => rb,
                6 => rc,
                _ => unreachable!(),
            }
        };
        let adv = |operand: usize| -> usize {
            let pow = combo_operand(operand);
            if pow >= 64 {
                0
            } else {
                ra / (1 << pow)
            }
        };
        match op.op_code {
            0 => {
                ra = adv(op.operand);
            }
            1 => {
                rb = rb ^ op.operand;
            }
            2 => {
                rb = combo_operand(op.operand) % 8;
            }
            3 => {
                if ra != 0 {
                    ip = op.operand / 2;
                    continue;
                }
            }
            4 => {
                rb = rb ^ rc;
            }
            5 => {
                res.push(combo_operand(op.operand) % 8);
            }
            6 => {
                rb = adv(op.operand);
            }
            7 => {
                rc = adv(op.operand);
            }
            _ => unreachable!(),
        }

        ip += 1;
    }

    res.iter().map(|x| x.to_string()).collect_vec().join(",")
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