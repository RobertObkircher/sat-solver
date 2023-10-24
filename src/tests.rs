#![cfg(test)]

use std::fs;

use crate::dimacs::parse_dimacs_cnf;
use crate::formula::Literal;
use crate::solver::{sat, Satisfiable};

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
    let result = parse_dimacs_cnf(SAT_CNF).unwrap();
    assert!(result.comments.contains("Satisfiable"));
    let clauses = result.clauses().collect::<Vec<&[Literal]>>();
    assert_eq!(clauses.len(), 2);
    assert_eq!(clauses[0], [Literal::try_from(1).unwrap()]);
    assert_eq!(clauses[1], [Literal::try_from(-1).unwrap(), Literal::try_from(2).unwrap(), Literal::try_from(3).unwrap()]);

    let result = sat(result);
    assert_eq!(result, Satisfiable::Yes);
}

#[test]
fn parse_unsat() {
    let result = parse_dimacs_cnf(UNSAT_CNF).unwrap();
    assert!(result.comments.contains("Unsatisfiable"));
    let clauses = result.clauses().collect::<Vec<&[Literal]>>();
    assert_eq!(clauses.len(), 4);
    assert_eq!(clauses[0], [Literal::try_from(1).unwrap()]);
    assert_eq!(clauses[1], [Literal::try_from(-1).unwrap()]);
    assert_eq!(clauses[2], [Literal::try_from(2).unwrap()]);
    assert_eq!(clauses[3], [Literal::try_from(-2).unwrap()]);

    let result = sat(result);
    assert_eq!(result, Satisfiable::No);
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
    let result = parse_dimacs_cnf(SLIDES_CNF).unwrap();
    assert!(result.comments.contains("Slides"));
    let clauses = result.clauses().collect::<Vec<&[Literal]>>();
    assert_eq!(clauses.len(), 6);

    let result = sat(result);
    assert_eq!(result, Satisfiable::Yes);
}

#[test]
fn uf50_218() {
    fs::read_dir("inputs/uf50-218").unwrap().for_each(|x| {
        let entry = x.unwrap();
        println!("{}", entry.file_name().to_string_lossy());

        let contents = std::fs::read_to_string(entry.path()).unwrap();
        // TODO figure out why the files from a website end with '%' and '0' as the last two lines.
        let source = if let Some((start, _)) = contents.rsplit_once('%') {
            start
        } else {
            &contents
        };
        let result = parse_dimacs_cnf(&source).unwrap();
        let result = sat(result);
        assert_eq!(result, Satisfiable::Yes);
    });
}

#[test]
fn uuf50_218() {
    fs::read_dir("inputs/uuf50-218").unwrap().for_each(|x| {
        let entry = x.unwrap();
        println!("{}", entry.file_name().to_string_lossy());

        let contents = std::fs::read_to_string(entry.path()).unwrap();
        // TODO figure out why the files from a website end with '%' and '0' as the last two lines.
        let source = if let Some((start, _)) = contents.rsplit_once('%') {
            start
        } else {
            &contents
        };
        let result = parse_dimacs_cnf(&source).unwrap();
        let result = sat(result);
        assert_eq!(result, Satisfiable::No);
    });
}