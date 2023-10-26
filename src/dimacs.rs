use std::num::NonZeroI32;
use std::time::Instant;

use crate::formula::{CnfFormula, Literal};
use crate::simp::simplify_new_clause;
use crate::statistics::Statistics;

pub fn parse_dimacs_cnf(source: &str, stats: &mut Statistics) -> Result<CnfFormula, String> {
    let start_instant = Instant::now();

    let mut lines = source.lines().enumerate();
    let mut comments = Vec::new();

    let mut variables_and_clauses = None;

    // find header
    while let Some((i, line)) = lines.next() {
        if let Some(comment) = line.strip_prefix('c') {
            comments.push(comment);
        } else if let Some(header) = line.strip_prefix('p') {
            if let Some(rest) = header.strip_prefix(" cnf ") {
                let mut split = rest.split_ascii_whitespace();
                match (split.next().map(str::parse::<i32>), split.next().map(str::parse::<usize>), split.next()) {
                    (Some(Ok(variables)), Some(Ok(clauses)), None) if variables >= 0 => {
                        variables_and_clauses = Some((variables, clauses));
                        break;
                    }
                    _ => {
                        return Err(format!("Line {}: Could not parse number of variables and clauses after 'p cnf ' in line '{line}'", i + 1));
                    }
                }
            } else {
                return Err(format!("Line {}: Only 'p cnf ' headers are supported, but got '{line}'", i + 1));
            }
        } else {
            return Err(format!("Line {}: Expected to find header starting with 'p', but got '{line}'", i + 1));
        }
    }

    let (n_variables, n_clauses) = if let Some(x) = variables_and_clauses {
        x
    } else {
        return Err("Could not find header starting with 'p'".to_string());
    };

    let mut start = 0;
    let mut literals = Vec::new();
    let mut clauses = Vec::with_capacity(n_clauses);
    let mut parsed_clauses = 0;

    // parse literals
    for (i, line) in lines {
        if let Some(comment) = line.strip_prefix('c') {
            comments.push(comment);
        } else {
            for number in line.split(' ')
                .filter(|it| !it.is_empty())
                .map(str::parse) {
                let nr: i32 = number.map_err(|e| format!("Line {}: Could not parse number: {e}", i + 1))?;
                if let Ok(nr) = NonZeroI32::try_from(nr) {
                    if nr.get().abs() > n_variables {
                        return Err(format!("Line {}: Variable '{}' is larger than indicated in the header", i + 1, nr.get()));
                    }
                    literals.push(Literal::try_from(nr.get()).unwrap());
                } else {
                    parsed_clauses += 1;
                    // PERFORMANCE: sorting and checking tautological neighbours took parsing of
                    // 1000 instances, 50 variables, 218 clauses, 3-sat from 30 to 41 milliseconds.
                    simplify_new_clause(start, &mut literals, stats);
                    if literals.len() > start {
                        clauses.push(literals.len());
                        start = literals.len();
                    }
                }
            }
        }
    }

    stats.parse_duration += start_instant.elapsed();

    if parsed_clauses != n_clauses {
        Err(format!("Parsed {} clauses but expected {n_clauses} from the header", clauses.len()))
    } else {
        Ok(CnfFormula {
            comments: comments.join("\n"),
            variable_count: n_variables as usize,
            literals,
            clauses,
        })
    }
}