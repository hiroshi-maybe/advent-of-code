#![allow(unused_macros, unused_imports)]
use std::cmp::*;
use std::collections::*;

// $ cp-batch day5part2 | diff day5part2.out -
// $ cargo run --bin day5part2

///
/// 12/17/2024
///
/// 22:11-
///

fn solve() -> i64 {
    // let n = 28;
    let n = 1371;
    let mut ind = HashMap::new();
    let mut g = HashMap::new();
    let mut ord = HashMap::new();

    let mut res = 0;
    let mut is_query = false;
    for _ in 0..n {
        let s = readln_str();
        let s = s.trim_end();
        // dbgln!(s);
        if s.is_empty() {
            is_query = true;

            let mut q = VecDeque::new();
            let mut sorted = vec![];

            for (&k, &v) in &ind {
                if v == 0 {
                    q.push_back(k);
                    sorted.push(k);
                }
            }
            dbgln!(ind);
            assert!(!q.is_empty());

            while let Some(u) = q.pop_front() {
                sorted.push(u);
                for &v in g.get(&u).unwrap_or(&vec![]) {
                    let e = ind.get_mut(&v).unwrap();
                    *e -= 1;
                    if *e == 0 {
                        q.push_back(v);
                    }
                }
            }

            // assert!(ind.is_empty());
            dbgln!(sorted);
            for i in 0..sorted.len() {
                ord.insert(sorted[i], i);
            }
            dbgln!(ord);

            continue;
        }

        if is_query {
            let a = s
                .split(',')
                .map(|n| n.parse::<i64>().unwrap())
                .collect_vec();

            for x in &a {
                if !ord.contains_key(x) {
                    dbgln!(a);
                    dbgln!(x);
                }
            }

            let mut b = a.clone();
            b.sort_by_key(|n| ord[n]);

            if a != b {
                dbgln!(a);
                dbgln!(b);
                res += b[b.len() / 2];
            }
        } else {
            let p = s
                .split('|')
                .map(|n| n.parse::<i64>().unwrap())
                .collect_vec();

            ind.entry(p[0]).or_insert(0);
            let e = ind.entry(p[1]).or_insert(0);
            *e += 1;

            let e = g.entry(p[0]).or_insert(vec![]);
            e.push(p[1]);
        }
    }

    res
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
