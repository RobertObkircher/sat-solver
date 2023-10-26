use std::{env, fs, process};

use sat_solver::dimacs::parse_dimacs_cnf;
use sat_solver::solver::{sat, Satisfiable};
use sat_solver::statistics::Statistics;

fn main() {
    let args = env::args().collect::<Vec<_>>();
    if args.len() != 2 {
        eprintln!("Usage: {} <dimacs.cnf>", args[0]);
        process::exit(1);
    }
    let contents = fs::read_to_string(&args[1]).unwrap_or_else(|e| {
        eprintln!("Could not read file: {e}");
        process::exit(1);
    });

    let mut stats = Statistics::default();
    let formula = parse_dimacs_cnf(&contents, &mut stats).unwrap_or_else(|e| {
        eprintln!("Parse error: {}", e);
        process::exit(1);
    });
    let result = sat(formula);
    match result {
        Satisfiable::Yes => { println!("SAT"); }
        Satisfiable::No => { println!("UNSAT"); }
    }
    eprintln!("{stats:?}");
}
