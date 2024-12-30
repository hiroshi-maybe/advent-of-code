#![allow(unused_macros, unused_imports)]
use std::cmp::*;
use std::collections::*;

// $ cp-batch day24part1 | diff day24part1.out -
// $ cargo run --bin day24part1

///
/// 12/29/2024
///
/// 16:17-17:33 AC
///

fn solve() -> usize {
    let mut vals = HashMap::new();
    let mut empty_line_num = 0;
    let mut edges = HashMap::new();
    let mut exp = HashMap::new();
    let mut ind = HashMap::new();
    loop {
        let s = readln_str();
        let s = s.trim_end();
        if s.is_empty() {
            empty_line_num += 1;
            if empty_line_num == 2 {
                break;
            }
            continue;
        }

        if empty_line_num == 0 {
            let val = s.split(": ").collect_vec();
            vals.insert(val[0].to_string(), val[1].parse::<usize>().unwrap());
            continue;
        }

        let opstr = s.split(" -> ").collect_vec();
        let input = opstr[0].split(' ').collect_vec();
        let i1 = input[0].to_string();
        let i2 = input[2].to_string();
        let op = input[1].to_string();
        let o = opstr[1].to_string();

        let e = edges.entry(i1.clone()).or_insert(vec![]);
        e.push(o.clone());
        let e = edges.entry(i2.clone()).or_insert(vec![]);
        e.push(o.clone());

        assert!(exp
            .insert(o.clone(), (op, i1.clone(), i2.clone()))
            .is_none());
        assert!(ind.insert(o.clone(), 2).is_none());
    }

    let mut q = VecDeque::new();
    for k in vals.keys() {
        q.push_back(k.to_string());
    }

    while let Some(name) = q.pop_front() {
        let Some(edges) = edges.get(&name) else {
            continue;
        };

        for v in edges {
            ind.entry(v.to_string()).and_modify(|e| *e -= 1);
            // dbgln!(v, ind[v]);
            if ind[v] == 0 {
                let e = &exp[v];
                // dbgln!(e, v);
                let i1 = vals[&e.1];
                let i2 = vals[&e.2];
                vals.insert(v.to_string(), operation(&e.0, i1, i2));
                q.push_back(v.to_string());
            }
        }
    }

    let mut zs = vals
        .iter()
        .filter(|(k, _)| k.starts_with("z"))
        .collect_vec();
    zs.sort_unstable();
    // dbgln!(zs);

    let mut res = 0;
    for (_, &b) in zs.iter().rev() {
        res <<= 1;
        res |= b;
    }

    res
}

fn operation(op: &str, i1: usize, i2: usize) -> usize {
    match op {
        "AND" => i1 & i2,
        "OR" => i1 | i2,
        "XOR" => i1 ^ i2,
        _ => unreachable!(),
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
