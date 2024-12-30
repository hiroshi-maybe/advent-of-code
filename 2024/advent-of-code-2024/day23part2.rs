#![allow(unused_macros, unused_imports)]
use std::cmp::*;
use std::collections::hash_map::Entry::{Occupied, Vacant};
use std::collections::*;
use std::collections::{BTreeSet, HashMap};

// $ cp-batch day23part2 | diff day23part2.out -
// $ cargo run --bin day23part2

///
/// 12/29/2024
///
/// 15:39-16:13 AC
///

// https://stackoverflow.com/questions/60835260/why-do-i-obtain-different-results-for-the-bron-kerbosch-algorithm-when-switching
type Nodes = HashSet<usize>;
type Graph = HashMap<usize, Nodes>;
type Record = (usize, usize);

fn init_nodes(records: &[Record]) -> Graph {
    let mut nodes: Graph = Graph::with_capacity(records.len());
    for r in records.iter() {
        let n: &mut Nodes = match nodes.entry(r.0) {
            Vacant(entry) => entry.insert(Nodes::new()),
            Occupied(entry) => entry.into_mut(),
        };
        n.insert(r.1);
        let n: &mut Nodes = match nodes.entry(r.1) {
            Vacant(entry) => entry.insert(Nodes::new()),
            Occupied(entry) => entry.into_mut(),
        };
        n.insert(r.0);
    }
    nodes.shrink_to_fit();
    nodes
}

fn bron1(graph: &Graph, r: Nodes, mut p: Nodes, mut x: Nodes, cliques: &mut Vec<Nodes>) {
    if p.is_empty() && x.is_empty() {
        cliques.push(r);
    } else if !p.is_empty() {
        let nodes = p.iter().cloned().collect::<Nodes>();
        nodes.iter().for_each(|node| {
            let neighbours: &Nodes = graph.get(node).unwrap();
            let mut to_add: Nodes = Nodes::new();
            to_add.insert(*node);
            bron1(
                graph,
                r.union(&to_add).cloned().collect(),
                p.intersection(&neighbours).cloned().collect(),
                x.intersection(&neighbours).cloned().collect(),
                cliques,
            );
            p.remove(node);
            x.insert(*node);
        });
    }
}

fn display_cliques(cliques: &[Nodes]) {
    let max = (&cliques[0]).len();
    let mut count = 0;
    for (idx, cl) in cliques.iter().enumerate() {
        if cl.len() != max {
            count = idx;
            break;
        }
    }
    println!(
        "Found {} cliques of {} nodes on a total of {} cliques",
        count,
        max,
        cliques.len()
    )
}

fn max_clique(cliques: &[Nodes]) -> HashSet<usize> {
    cliques.iter().max_by_key(|cl| cl.len()).unwrap().clone()
}

fn solve() -> String {
    let mut es = vec![];
    loop {
        let s = readln_str();
        let s = s.trim_end();
        if s.is_empty() {
            break;
        }

        let vs = s.split('-').collect_vec();
        // println!("{} {}", vs[0], vs[1]);
        es.push((vs[0].to_string(), vs[1].to_string()));
    }
    let mut vset = HashSet::new();
    for i in 0..es.len() {
        vset.insert(es[i].0.clone());
        vset.insert(es[i].1.clone());
    }
    let n = vset.len();
    dbgln!(n);
    let mut vs = HashMap::new();
    let mut vnames = vec![];
    for (id, v) in vset.iter().enumerate() {
        // println!("{v}");
        vs.insert(v, id);
        vnames.push(v);
    }
    let records = es
        .iter()
        .map(|(n1, n2)| (*vs.get(n1).unwrap(), *vs.get(n2).unwrap()))
        .collect_vec();

    let nodes = init_nodes(&records);
    let r: Nodes = nodes.keys().copied().collect();
    let mut cliques: Vec<Nodes> = Vec::new();
    bron1(&nodes, Nodes::new(), r, Nodes::new(), &mut cliques);
    cliques.sort_unstable_by(|a, b| a.len().cmp(&b.len()).reverse());
    let max_cliq = max_clique(&cliques);

    let mut names = max_cliq.iter().map(|&u| vnames[u].clone()).collect_vec();
    names.sort();
    names.join(",")
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
