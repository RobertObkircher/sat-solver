use std::num::NonZeroI32;

use crate::formula::{CnfFormula, Literal};

pub fn parse_dimacs_cnf(source: &str) -> Result<CnfFormula, String> {
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

    let mut literals = Vec::new();
    let mut clauses = Vec::with_capacity(n_clauses);

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
                    clauses.push(literals.len());
                }
            }
        }
    }

    if clauses.len() != n_clauses {
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