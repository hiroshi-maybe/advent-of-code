#![allow(unused_macros, unused_imports)]
use std::cmp::*;
use std::collections::*;

// $ cp-batch day24part2 | diff day24part2.out -
// $ cargo run --bin day24part2

///
/// 12/29/2024
///
/// 19:46-21:05 AC
///

/*

Note:

x00: 1
x01: 0
x02: 1
x03: 1
x04: 0
x05: 0
..
x14: 0

y00: 1
y01: 0
y02: 0
y03: 1
y04: 1
y05: 0
..
y14: 0

x00 XOR y00 -> z00 1
x00 AND y00 -> jfw 0 (c00)

y01 XOR x01 -> gnj 0
jfw XOR gnj -> z01 0

x01 AND y01 -> ntt 0
gnj AND jfw -> spq 0

--

y14 XOR x14 -> dfb
dfb XOR bfn -> hbk * (bfn = c14)
sjr OR tck -> z14 *

wjj OR scs -> bfn
bfn AND dfb -> sjr
y14 AND x14 -> tck

--

y23 XOR x23 -> rpg
dvw XOR rpg -> dbb

x23 AND y23 -> gcb
dvw AND rpg -> z23

--

x34 XOR y34 -> tfn *
mqf XOR cvh -> z34

cht OR mkv -> mqf
tfn OR trj -> cqv
y34 AND x34 -> cvh *
mqf AND cvh -> trj

--

x18 XOR y18 -> grp
grp XOR fgr -> kvn *

fgr AND grp -> ffb
y18 AND x18 -> z18 *

*/

#[derive(Clone)]
struct Gate {
    op: String,
    in1: String,
    in2: String,
    out: String,
}

fn solve() -> String {
    let mut vals = HashMap::new();
    let mut empty_line_num = 0;

    let mut gates = vec![];
    let swaps = vec![(6, 187), (35, 55), (180, 155), (84, 138)];
    let mut res = vec![];

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
            let k = val[0].to_string();
            let v = val[1].parse::<usize>().unwrap();
            // use rand::prelude::*;
            // let v = random::<usize>() % 2;
            vals.insert(k, v);
            continue;
        }

        let opstr = s.split(" -> ").collect_vec();
        let input = opstr[0].split(' ').collect_vec();
        let in1 = input[0].to_string();
        let in2 = input[2].to_string();
        let op = input[1].to_string();
        let out = opstr[1].to_string();

        let gate = Gate { op, in1, in2, out };
        gates.push(gate);
    }

    let mut edges = HashMap::new();
    let mut exp = HashMap::new();
    let mut ind = HashMap::new();

    for (i, j) in swaps {
        let out1 = gates[i].out.clone();
        let out2 = gates[j].out.clone();
        if let Some(g2) = gates.get_mut(j) {
            g2.out = out1.clone();
        }
        if let Some(g1) = gates.get_mut(i) {
            g1.out = out2.clone();
        }
        res.push(out1.clone());
        res.push(out2.clone());
    }

    for g in &gates {
        let op = &g.op;
        let in1 = &g.in1;
        let in2 = &g.in2;
        let out = &g.out;

        let e = edges.entry(in1.clone()).or_insert(vec![]);
        e.push(out.clone());
        let e = edges.entry(in2.clone()).or_insert(vec![]);
        e.push(out.clone());

        assert!(exp
            .insert(out.clone(), (op, in1.clone(), in2.clone()))
            .is_none());
        assert!(ind.insert(out.clone(), 2).is_none());
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
    dbgln!(zs.len());

    let mut carry = 0;
    for i in 0..zs.len() {
        let mut s = i.to_string();
        if s.len() == 1 {
            s = "0".to_string() + &s;
        }
        let xkey = "x".to_string() + &s;
        let ykey = "y".to_string() + &s;
        let x = vals.get(&xkey).unwrap_or(&0);
        let y = vals.get(&ykey).unwrap_or(&0);
        let new_carry = (x & y) | (x & carry) | (carry & y);
        let expected_z = x ^ y ^ carry;
        println!(
            "{i}, {} + {} + {} = {} (vs {}) (carry={}) {}",
            x,
            y,
            carry,
            expected_z,
            zs[i].1,
            new_carry,
            if expected_z == *zs[i].1 { "" } else { "NG" }
        );
        carry = new_carry;
    }
    // dbgln!(vals);

    res.sort_unstable();
    res.join(",")
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
