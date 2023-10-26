#![cfg(test)]

use std::fs;

use crate::dimacs::parse_dimacs_cnf;
use crate::formula::Literal;
use crate::solver::{sat, Satisfiable};
use crate::statistics::Statistics;

const SAT_CNF: &str = "c Satisfiable example
p cnf 3 2
1 0
-1 2 3 0
";

const UNSAT_CNF: &str = "c Unsatisfiable example
p cnf 2 4
1 0
-1 0
2 0
-2 0
";


#[test]
fn parse_sat() {
    let mut stats = Statistics::default();
    let result = parse_dimacs_cnf(SAT_CNF, &mut stats).unwrap();
    assert!(result.comments.contains("Satisfiable"));
    let clauses = result.clauses().collect::<Vec<&[Literal]>>();
    assert_eq!(clauses.len(), 2);
    assert_eq!(clauses[0], [Literal::try_from(1).unwrap()]);
    assert_eq!(clauses[1], [Literal::try_from(-1).unwrap(), Literal::try_from(2).unwrap(), Literal::try_from(3).unwrap()]);

    let result = sat(result, &mut stats);
    assert_eq!(result, Satisfiable::Yes);
    eprintln!("{stats:?}");
}

#[test]
fn parse_unsat() {
    let mut stats = Statistics::default();
    let result = parse_dimacs_cnf(UNSAT_CNF, &mut stats).unwrap();
    assert!(result.comments.contains("Unsatisfiable"));
    let clauses = result.clauses().collect::<Vec<&[Literal]>>();
    assert_eq!(clauses.len(), 4);
    assert_eq!(clauses[0], [Literal::try_from(1).unwrap()]);
    assert_eq!(clauses[1], [Literal::try_from(-1).unwrap()]);
    assert_eq!(clauses[2], [Literal::try_from(2).unwrap()]);
    assert_eq!(clauses[3], [Literal::try_from(-2).unwrap()]);

    let result = sat(result, &mut stats);
    assert_eq!(result, Satisfiable::No);
    eprintln!("{stats:?}");
}

const SLIDES_CNF: &str = "c Slides example
p cnf 11 6
10 -1 9 11 0
10 -4 11 0
10 -2 -3 11 0
-4 5 10 0
-4 6 11 0
-5 -6 0
";

#[test]
fn slides_sat() {
    let mut stats = Statistics::default();
    let result = parse_dimacs_cnf(SLIDES_CNF, &mut stats).unwrap();
    assert!(result.comments.contains("Slides"));
    let clauses = result.clauses().collect::<Vec<&[Literal]>>();
    assert_eq!(clauses.len(), 6);

    let result = sat(result, &mut stats);
    assert_eq!(result, Satisfiable::Yes);
    eprintln!("{stats:?}");
}

#[test]
fn uf50_218() {
    let mut stats = Statistics::default();
    fs::read_dir("inputs/uf50-218").unwrap().for_each(|x| {
        let entry = x.unwrap();
        println!("{}", entry.file_name().to_string_lossy());

        let contents = fs::read_to_string(entry.path()).unwrap();
        let result = parse_dimacs_cnf(&contents, &mut stats).unwrap();
        let result = sat(result, &mut stats);
        assert_eq!(result, Satisfiable::Yes);
    });
    eprintln!("{stats:?}");
}

#[test]
fn uuf50_218() {
    let mut stats = Statistics::default();
    fs::read_dir("inputs/uuf50-218").unwrap().for_each(|x| {
        let entry = x.unwrap();
        println!("{}", entry.file_name().to_string_lossy());

        let contents = fs::read_to_string(entry.path()).unwrap();
        let result = parse_dimacs_cnf(&contents, &mut stats).unwrap();
        let result = sat(result, &mut stats);
        assert_eq!(result, Satisfiable::No);
    });
    eprintln!("{stats:?}");
}

const ELIMINATE_X_OR_NOT_X: &str = "c Elimination
p cnf 2 2
1 2 -1 0
-2 1 2 0
";

#[test]
fn eliminate_x_or_not_x() {
    let mut stats = Statistics::default();
    let result = parse_dimacs_cnf(ELIMINATE_X_OR_NOT_X, &mut stats).unwrap();
    assert_eq!(stats.eliminated_x_or_not_x_clauses, 2);
    assert_eq!(result.clauses.len(), 0);
    assert_eq!(result.literals.len(), 0);
    eprintln!("{stats:?}");
}

const ELIMINATE_X_OR_X: &str = "c Elimination
p cnf 2 2
1 2 1 0
2 1 2 0
";

#[test]
fn eliminate_x_or_x() {
    let mut stats = Statistics::default();
    let result = parse_dimacs_cnf(ELIMINATE_X_OR_X, &mut stats).unwrap();
    assert_eq!(stats.eliminated_x_or_x_literals, 2);
    assert_eq!(result.literals.len(), 4);
    eprintln!("{stats:?}");
}