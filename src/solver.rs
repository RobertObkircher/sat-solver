use std::ops::{Index, IndexMut};

use crate::formula::{CnfFormula, Literal, Variable};

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum Satisfiable {
    Yes,
    No,
}


pub fn sat(mut formula: CnfFormula) -> Satisfiable {
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
                    if b == l.value() {
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
