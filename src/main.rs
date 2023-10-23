use std::num::{NonZeroI32, TryFromIntError};

fn main() {
    println!("Hello, world!");
}

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

#[cfg(test)]
mod tests {
    use crate::{Literal, parse_dimacs_cnf, SAT_CNF};

    #[test]
    fn parse_sat() {
        let result = parse_dimacs_cnf(SAT_CNF).unwrap();
        assert!(result.comments.contains("Satisfiable"));
        let clauses = result.clauses().collect::<Vec<&[Literal]>>();
        assert_eq!(clauses.len(), 2);
        assert_eq!(clauses[0], [Literal::try_from(1).unwrap()]);
        assert_eq!(clauses[1], [Literal::try_from(-1).unwrap(), Literal::try_from(-2).unwrap(), Literal::try_from(3).unwrap()]);
    }

    fn parse_unsat() {
        let result = parse_dimacs_cnf(SAT_CNF).unwrap();
        assert!(result.comments.contains("Unsatisfiable"));
        let clauses = result.clauses().collect::<Vec<&[Literal]>>();
        assert_eq!(clauses.len(), 2);
        assert_eq!(clauses[0], [Literal::try_from(1).unwrap()]);
        assert_eq!(clauses[1], [Literal::try_from(-1).unwrap()]);
        assert_eq!(clauses[2], [Literal::try_from(2).unwrap()]);
        assert_eq!(clauses[3], [Literal::try_from(-2).unwrap()]);
    }
}

fn parse_dimacs_cnf(source: &str) -> Result<CnfFormula, String> {
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
                    literals.push(Literal(nr));
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
            literals,
            clauses,
        })
    }
}

struct CnfFormula {
    comments: String,
    literals: Vec<Literal>,
    clauses: Vec<usize>,
}

impl CnfFormula {
    fn get_clause(&self, index: usize) -> &[Literal] {
        let start = if index > 0 { self.clauses[index - 1] } else { 0 };
        let end = self.clauses[index];
        return &self.literals[start..end];
    }
}

impl CnfFormula {
    pub fn clauses(&self) -> impl Iterator<Item=&[Literal]> {
        (0..self.clauses.len()).map(|c| self.get_clause(c))
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
enum Satisfiable {
    Yes,
    No,
}

fn sat() -> Satisfiable {
    loop {
        if let Some(_assignment) = decide() {
            while BCP() == Conflict::Yes {
                if !resolve_conflict() {
                    return Satisfiable::No;
                }
            }
        } else {
            return Satisfiable::Yes;
        }
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
struct Variable(NonZeroI32);

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
struct Literal(NonZeroI32);

impl TryFrom<i32> for Literal {
    type Error = TryFromIntError;

    fn try_from(value: i32) -> Result<Self, Self::Error> {
        value.try_into().map(Literal)
    }
}

/// Choose next variable and value. Return `None` if all variables are assigned.
fn decide() -> Option<Literal> {
    None
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
enum Conflict {
    Yes,
    No,
}

/// Apply repeatedly the unit rule. Return false if a conflict is reached
fn BCP() -> Conflict {
    Conflict::No
}

/// Backtrack until no conflict occurs any more. Return false, if this is impossible
fn resolve_conflict() -> bool {
    false
}
