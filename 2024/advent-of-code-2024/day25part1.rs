#![allow(unused_macros, unused_imports)]
use std::cmp::*;
use std::collections::*;

// $ cp-batch day25part1 | diff day25part1.out -
// $ cargo run --bin day25part1

///
/// 12/29/2024
///
/// 21:13-22:13 AC
///

fn solve() -> usize {
    let mut keys = vec![];
    let mut locks = vec![];
    let mut cur: Vec<Vec<char>> = vec![];

    loop {
        let mut s = String::new();
        match std::io::stdin().read_line(&mut s) {
            Ok(_) => {}
            Err(_) => break,
        }

        let s = s.trim_end();
        if s.is_empty() {
            if cur.is_empty() {
                break;
            }

            let pat = (0..cur[0].len())
                .map(|j| {
                    (0..cur.len())
                        .map(|i| if cur[i][j] == '#' { 1 } else { 0 })
                        .sum::<i64>()
                        - 1
                })
                .collect_vec();
            if cur[0][0] == '.' {
                keys.push(pat);
            } else {
                locks.push(pat);
            }
            cur = vec![];

            continue;
        }

        cur.push(s.chars().collect_vec());
    }

    // let offset = keys.len();
    // let mut g: Vec<Vec<usize>> = vec![vec![]; offset + locks.len()];
    let mut res = 0;
    for i in 0..keys.len() {
        for j in 0..locks.len() {
            if keys[i].iter().zip(locks[j].iter()).all(|(a, b)| a + b <= 5) {
                // let jj = j + offset;
                // g[i].push(jj);
                // g[jj].push(i);
                res += 1;
            }
        }
    }

    dbgln!(keys.len(), locks.len());
    res
}

// region: max_bipartite_matching

#[allow(dead_code)]
mod max_bipartite_matching {
    fn dfs(
        u: usize,
        g: &Vec<Vec<usize>>,
        viz: &mut Vec<bool>,
        matched: &mut Vec<Option<usize>>,
    ) -> bool {
        viz[u] = true;
        for &v in &g[u] {
            if match matched[v] {
                None => true,
                Some(w) => !viz[w] && dfs(w, g, viz, matched),
            } {
                matched[v] = Some(u);
                matched[u] = Some(v);
                return true;
            }
        }
        false
    }
    pub fn max_bipartite_matching(g: &Vec<Vec<usize>>) -> usize {
        let n = g.len();
        let mut res = 0;
        let mut matched = vec![None; n];
        for u in 0..n {
            if matched[u].is_none() {
                let mut viz = vec![false; n];
                if dfs(u, &g, &mut viz, &mut matched) {
                    res += 1;
                }
            }
        }
        res
    }
}
pub use max_bipartite_matching::max_bipartite_matching;

// endregion: max_bipartite_matching

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
