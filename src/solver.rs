use std::ops::{Index, IndexMut};

use crate::formula::{CnfFormula, Literal, Variable};

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum Satisfiable {
    Yes,
    No,
}


pub fn sat(mut formula: CnfFormula) -> Satisfiable {
    let mut implications = ImplicationGraph::new(formula.variable_count);
    // 0 = uninitialized
    // 1 = "forced" decisions
    // 2 = first real decision
    let mut level = 1;

    // make "forced" decisions
    let mut change = true;
    while change {
        change = false;
        for c in formula.clauses() {
            match implications.assignment.evaluate_clause(c) {
                ClauseStatus::Satisfied => {}
                ClauseStatus::Unsatisfied => {
                    return Satisfiable::No;
                }
                ClauseStatus::Unit(literal) => {
                    implications.add_decision(literal, level);
                    change = true;
                }
                ClauseStatus::Unresolved => {}
            }
        }
    }
    level += 1;

    loop {
        if let Some(literal) = decide(&implications.assignment) {
            level += 1;
            implications.add_decision(literal, level);

            while let Conflict::Yes(conflict_clause) = boolean_constraint_propagation(&formula, level, &mut implications) {
                if !resolve_conflict(conflict_clause, &mut formula, &mut implications, &mut level) {
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
    Yes(usize),
    No,
}

/// A labeled directed acyclic graph G = (V, E), where:
/// - each node has a label l@d for a literal l
/// - E = {(v_i, v_j)}, directed to v_j, labeled with Antecedent(v_j)
/// - In case G is a conflict graph, it also contains a single conflict
//    node with incoming edges labeled with clause c.
struct ImplicationGraph {
    assignment: Assignment,
    nodes: Vec<ImplicationNode>,
}

impl ImplicationGraph {
    fn new(variable_count: usize) -> Self {
        Self {
            assignment: Assignment::new(variable_count),
            nodes: (0..(variable_count + 1)).map(|_| ImplicationNode {
                level: 0,
                antecedent: Antecedent::Decision,
            }).collect(),
        }
    }

    pub fn add_decision(&mut self, literal: Literal, level: usize) {
        self.assignment[literal.variable()] = Some(literal.value());
        self.nodes[literal.variable().index()] = ImplicationNode {
            level,
            antecedent: Antecedent::Decision,
        };
    }

    pub fn last_assigned_literal(&self, clause: &[Literal]) -> Option<(usize, Literal)> {
        // TODO debug assert that we didn't filter anything larger
        clause.iter().cloned().enumerate()
            .filter(|(_, l)| self.nodes[l.variable().index()].antecedent.is_clause())
            .max_by_key(|(_, l)| self.nodes[l.variable().index()].level)
    }


    /// 2nd highest dl in cl
    pub fn clause_asserting_level(&self, clause: &[Literal]) -> Option<usize> {
        let mut max = 0;
        let mut second = 0;

        for l in clause.iter() {
            let level = self.nodes[l.variable().index()].level;
            if level > max {
                second = max;
                max = level;
            } else if level > second {
                second = level;
            }
        }
        if max != second { Some(second) } else { None }
    }
}

struct ImplicationNode {
    level: usize,
    antecedent: Antecedent,
}

enum Antecedent {
    Decision,
    /// The actual edges are the other literals in the clause.
    Clause(usize),
}

impl Antecedent {
    pub fn is_clause(&self) -> bool {
        match self {
            Antecedent::Decision => false,
            Antecedent::Clause(_) => true,
        }
    }
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
fn boolean_constraint_propagation(formula: &CnfFormula, level: usize, implications: &mut ImplicationGraph) -> Conflict {
    'outer: loop {
        // check conflicts
        for (index, c) in formula.clauses().enumerate() {
            if let ClauseStatus::Unsatisfied = implications.assignment.evaluate_clause(c) {
                return Conflict::Yes(index);
            }
        }
        // propagate
        for (clause_index, c) in formula.clauses().enumerate() {
            match implications.assignment.evaluate_clause(c) {
                ClauseStatus::Satisfied => {}
                ClauseStatus::Unsatisfied => {
                    unreachable!()
                }
                ClauseStatus::Unit(literal) => {
                    implications.assignment[literal.variable()] = Some(literal.value());
                    implications.nodes[literal.variable().index()] = ImplicationNode {
                        level,
                        antecedent: Antecedent::Clause(clause_index),
                    };
                    continue 'outer;
                }
                ClauseStatus::Unresolved => {}
            }
        }
        break Conflict::No;
    }
}

/// Backtrack until no conflict occurs any more. Return false, if this is impossible
fn resolve_conflict(conflict_clause: usize, formula: &mut CnfFormula, implications: &mut ImplicationGraph, level: &mut usize) -> bool {
    let result = analyze_conflict(conflict_clause, implications, formula, level);
    if result {
        // TODO find a smarter way to do this (either during analyze_conflict or on maybe check level on each read
        for (i, node) in implications.nodes.iter().enumerate() {
            if node.level > *level {
                implications.assignment.values[i] = None;
            }
        }
        #[cfg(debug_assertions)]
        {
            implications.nodes.iter_mut()
                .filter(|it| it.level > *level)
                .for_each(|it| it.level = 0);
        }
    }
    result
}

/// Output: BT level and new conflict clause
fn analyze_conflict(conflict_clause: usize, implications: &ImplicationGraph, formula: &mut CnfFormula, level: &mut usize) -> bool {
    if *level == 1 {
        return false;
    }

    let mut cl = formula.get_clause(conflict_clause).to_vec();
    while !is_asserting(&cl, implications, *level) {
        let (i, lit) = implications.last_assigned_literal(&cl).unwrap();
        let var = lit.variable();
        debug_assert_eq!(implications.nodes[var.index()].level, *level);
        let ante = match &implications.nodes[var.index()].antecedent {
            Antecedent::Decision => unreachable!(),
            Antecedent::Clause(i) => *i,
        };
        // cl := Resolve(cl, ante, var)
        let removed = cl.swap_remove(i);
        debug_assert_eq!(lit, removed);
        for &l in formula.get_clause(ante) {
            if l.variable() != var {
                if cl.iter().position(|&it| it == l).is_none() {
                    cl.push(l);
                }
                debug_assert!(cl.iter().position(|&it| it == l.negated()).is_none());
            }
        }
    }

    if let Some(l) =  implications.clause_asserting_level(&cl) {
        *level = l;
    } else {
        return false; // TODO not sure about this but it fixes unsatisfiable tests
    }

    // add-clause-to-databse
    for l in cl {
        formula.literals.push(l);
    }
    formula.clauses.push(formula.literals.len());

    return true;
}

/// An asserting clause (AC) is a conflict clause with a single literal from the current decision level.
fn is_asserting(clause: &[Literal], implications: &ImplicationGraph, level: usize) -> bool {
    let mut found = false;
    for l in clause {
        if implications.nodes[l.variable().index()].level == level {
            if found {
                return false;
            }
            found = true;
        }
    }
    found
}

