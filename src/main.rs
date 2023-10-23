use std::num::{NonZeroI32, TryFromIntError};
use std::ops::{Index, IndexMut};

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
    use crate::{Literal, parse_dimacs_cnf, sat, SAT_CNF, Satisfiable, UNSAT_CNF};

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
            variable_count: n_variables as usize,
            literals,
            clauses,
        })
    }
}

struct CnfFormula {
    comments: String,
    variable_count: usize,
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

fn sat(mut formula: CnfFormula) -> Satisfiable {
    let mut assignment = Assignment::new(formula.variable_count);
    let mut implications = ImplicationGraph { nodes: vec![] };
    let mut level = 0;

    loop {
        if let Some(literal) = decide(&assignment) {
            level += 1;
            assignment[literal.variable()] = Some(literal.value());
            implications.nodes.push(ImplicationNode {
                literal,
                level,
                antecedent: Antecedent::Decision,
                predecessor: 0, // self
            });

            while boolean_constraint_propagation(&formula, level, &mut assignment, &mut implications) == Conflict::Yes {
                if !resolve_conflict(&mut formula, &mut assignment, &mut implications, &mut level) {
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

impl Variable {
    pub fn index(self) -> usize {
        self.0.get().abs() as usize
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
struct Literal(NonZeroI32);

impl Literal {
    pub fn negated(self) -> Literal {
        Literal(-self.0)
    }

    pub fn variable(self) -> Variable {
        Variable(self.0.abs())
    }

    pub fn value(self) -> bool {
        self.0.is_positive()
    }
}

impl TryFrom<i32> for Literal {
    type Error = TryFromIntError;

    fn try_from(value: i32) -> Result<Self, Self::Error> {
        value.try_into().map(Literal)
    }
}

/// Choose next variable and value. Return `None` if all variables are assigned.
fn decide(x: &Assignment) -> Option<Literal> {
    for (i, value) in x.values.iter().enumerate() {
        if i == 0 { continue; }
        if value.is_none() {
            return Some(Literal::try_from(i32::try_from(i).unwrap()).unwrap());
        }
    }
    None
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
enum Conflict {
    Yes,
    No,
}

/// A labeled directed acyclic graph G = (V, E), where:
/// - each node has a label l@d for a literal l
/// - E = {(v_i, v_j)}, directed to v_j, labeled with Antecedent(v_j)
/// - In case G is a conflict graph, it also contains a single conflict
//    node with incoming edges labeled with clause c.
struct ImplicationGraph {
    nodes: Vec<ImplicationNode>,
}

struct ImplicationNode {
    literal: Literal,
    level: usize,
    // Could this be moved into Antecedent::Decision()?
    antecedent: Antecedent,
    predecessor: usize,
}

enum Antecedent {
    Decision,
    Clause(usize),
}

struct Assignment {
    values: Vec<Option<bool>>,
}

impl Assignment {
    pub fn new(count: usize) -> Self {
        Self {
            values: vec![None; count + 1],
        }
    }
}

/// Under a (partial) assignment, a clause can be
enum ClauseStatus {
    /// at least one of its literals is assigned to true,
    Satisfied,
    /// all its literals are assigned to false
    Unsatisfied,
    /// all but one of its literals are assigned to false
    Unit(Literal),
    /// otherwise
    Unresolved,
}

impl Assignment {
    pub fn evaluate_clause(&self, clause: &[Literal]) -> ClauseStatus {
        let mut unsat = 0;
        let mut unit = None;
        for &l in clause {
            match self[l.variable()] {
                Some(b) => {
                    if b == l.0.is_positive() {
                        return ClauseStatus::Satisfied;
                    } else {
                        unsat += 1;
                    }
                }
                None => {
                    unit = Some(l)
                }
            }
        }

        if clause.len() == unsat {
            ClauseStatus::Unsatisfied
        } else if clause.len() == unsat + 1 {
            ClauseStatus::Unit(unit.unwrap())
        } else {
            ClauseStatus::Unresolved
        }
    }
}

impl Index<Variable> for Assignment {
    type Output = Option<bool>;

    fn index(&self, index: Variable) -> &Self::Output {
        &self.values[index.index()]
    }
}

impl IndexMut<Variable> for Assignment {
    fn index_mut(&mut self, index: Variable) -> &mut Self::Output {
        &mut self.values[index.index()]
    }
}

/// Propagate consequences (implications) of a decision through the formula,
/// thereby changing the status of clauses. The implication graph
/// is used to keep track of the changes.
///
/// Apply repeatedly the unit rule. Return false if a conflict is reached
fn boolean_constraint_propagation(formula: &CnfFormula, level: usize, assignment: &mut Assignment, implications: &mut ImplicationGraph) -> Conflict {
    'outer: loop {
        // check conflicts
        for c in formula.clauses() {
            if let ClauseStatus::Unsatisfied = assignment.evaluate_clause(c) {
                return Conflict::Yes;
            }
        }
        // propagate
        for (clause_index, c) in formula.clauses().enumerate() {
            match assignment.evaluate_clause(c) {
                ClauseStatus::Satisfied => {}
                ClauseStatus::Unsatisfied => {
                    unreachable!()
                }
                ClauseStatus::Unit(literal) => {
                    assignment[literal.variable()] = Some(literal.value());
                    implications.nodes.push(ImplicationNode {
                        literal,
                        level,
                        antecedent: Antecedent::Clause(clause_index),
                        predecessor: 0,
                    });
                    continue 'outer;
                }
                ClauseStatus::Unresolved => {}
            }
        }
        break Conflict::No;
    }
}

/// Backtrack until no conflict occurs any more. Return false, if this is impossible
fn resolve_conflict(formula: &mut CnfFormula, assignment: &mut Assignment, implications: &mut ImplicationGraph, level: &mut usize) -> bool {
    while let Some(last) = implications.nodes.pop() {
        assignment[last.literal.variable()] = None;
        *level = last.level;
        match last.antecedent {
            Antecedent::Decision => {
                formula.literals.push(last.literal.negated());
                for node in implications.nodes.iter().rev() {
                    formula.literals.push(node.literal.negated());
                }
                formula.clauses.push(formula.literals.len());
                return true;
            }
            Antecedent::Clause(_) => {}
        }
    }
    false
}
