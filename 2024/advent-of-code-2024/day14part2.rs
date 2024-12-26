#![allow(unused_macros, unused_imports)]
use std::cmp::*;
use std::collections::*;

// $ cp-batch day14part2 | diff day14part2.out -
// $ cargo run --bin day14part2

///
/// 12/23/2024
///
/// 24:09-24:23 pause
///
/// 12/26/2024
///
/// 14:20 AC
///

fn solve() {
    let (n, m) = (103, 101);

    let mut ps = vec![];
    let mut vs = vec![];

    loop {
        let s = readln_str();
        let s = s.trim_end();
        let s = s.split_whitespace().collect_vec();
        if s.len() != 2 {
            break;
        }
        let ps_s = s[0].trim_start_matches("p=");
        let vs_s = s[1].trim_start_matches("v=");

        let pos = ps_s
            .split(',')
            .map(|s| s.parse::<isize>().unwrap())
            .collect_vec();
        let vel = vs_s
            .split(',')
            .map(|s| s.parse::<isize>().unwrap())
            .collect_vec();

        ps.push((pos[1], pos[0]));
        vs.push((vel[1], vel[0]));
    }

    for x in 0..8258 {
        let mut cnt = vec![vec![0; m]; n];
        for i in 0..ps.len() {
            let new_pos = sim(ps[i].0, ps[i].1, n as isize, m as isize, vs[i]);
            ps[i] = new_pos;
            cnt[new_pos.0 as usize][new_pos.1 as usize] += 1;
        }

        if find_pattern(&cnt, n, m) {
            println!("--------------------------------------------------------------------------------------------------------{}", x+1);
            for i in 0..n {
                for j in 0..m {
                    print!("{}", if cnt[i][j] == 0 { ' ' } else { '#' });
                }
                println!();
            }
        }
    }
}

fn find_pattern(cnt: &Vec<Vec<usize>>, n: usize, m: usize) -> bool {
    for i in 0..n {
        let mut consecutive_cnt = 0;
        for j in 0..m {
            if cnt[i][j] > 0 {
                consecutive_cnt += 1;
            } else {
                consecutive_cnt = 0;
            }

            if consecutive_cnt == 10 {
                return true;
            }
        }
    }
    false
}

fn sim(mut i: isize, mut j: isize, n: isize, m: isize, mov: (isize, isize)) -> (isize, isize) {
    for _ in 0..1 {
        i = (i + n + mov.0) % n;
        j = (j + m + mov.1) % m;

        assert!(i >= 0);
        assert!(j >= 0);
    }
    (i, j)
}

fn main() {
    setup_out!(put, puts);

    solve();
    // let res = solve();
    // puts!("{}", res);
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
