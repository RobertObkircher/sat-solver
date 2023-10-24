#![cfg(test)]

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
