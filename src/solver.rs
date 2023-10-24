use crate::formula::{CnfFormula, Literal};

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

    // VSIDS: Variable State Independent Decaying Sum
    let mut vsids = vec![0u8; formula.variable_count + 1];

    // make "forced" decisions
    let mut change = true;
    while change {
        change = false;
        for c in formula.clauses() {
            match implications.evaluate_clause(c) {
                ClauseStatus::Satisfied => {}
                ClauseStatus::Unsatisfied => {
                    return Satisfiable::No;
                }
                ClauseStatus::Unit(literal) => {
                    implications.add_node(literal, level, Antecedent::Decision);
                    change = true;
                }
                ClauseStatus::Unresolved => {}
            }
        }
    }

    loop {
        if let Some(literal) = decide(&implications, &vsids) {
            level += 1;
            implications.add_node(literal, level, Antecedent::Decision);

            while let Conflict::Yes(conflict_clause) = boolean_constraint_propagation(&formula, level, &mut implications) {
                for l in formula.get_clause(conflict_clause) {
                    if vsids[l.variable().index()] == 255 {
                        // TODO does it matter that this isn't entirely fair?
                        vsids.iter_mut().for_each(|it| *it /= 2);
                    }
                    vsids[l.variable().index()] += 1;
                }
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
fn decide(x: &ImplicationGraph, vsids: &[u8]) -> Option<Literal> {
    x.values.iter().enumerate()
        .skip(1)
        .filter(|(_, value)| value.is_none())
        .max_by_key(|(i, _)| vsids[*i])
        .map(|(i, _)| Literal::try_from(i32::try_from(i).unwrap()).unwrap())
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
    // TODO pack two into one byte?
    values: Vec<Option<bool>>,
    nodes: Vec<ImplicationNode>,
}

impl ImplicationGraph {
    fn new(variable_count: usize) -> Self {
        Self {
            values: vec![None; variable_count + 1],
            nodes: (0..(variable_count + 1)).map(|_| ImplicationNode {
                level: 0,
                antecedent: Antecedent::Decision,
            }).collect(),
        }
    }

    pub fn add_node(&mut self, literal: Literal, level: usize, antecedent: Antecedent) {
        let index = literal.variable().index();
        debug_assert!(self.values[index].is_none());
        self.values[index] = Some(literal.value());
        self.nodes[index] = ImplicationNode {
            level,
            antecedent,
        };
    }

    /// Returns the index and the literal with the highest decision level.
    /// Decision nodes are ignored, because the caller only resolves against the
    /// others to make the clause asserting asserting on the current decision level.
    pub fn last_assigned_literal(&self, clause: &[Literal]) -> Option<(usize, Literal)> {
        debug_assert!(clause.iter().all(|l| self.values[l.variable().index()].is_some()));
        clause.iter().cloned().enumerate()
            .filter(|(_, l)| self.nodes[l.variable().index()].antecedent.is_clause())
            .max_by_key(|(_, l)| self.nodes[l.variable().index()].level)
    }


    /// 2nd highest dl in an asserting clause
    pub fn clause_asserting_level(&self, clause: &[Literal]) -> usize {
        debug_assert!(!clause.is_empty(), "Expected asserting clause which must have at least one literal");

        if clause.len() == 1 {
            debug_assert!(self.values[clause[0].variable().index()].is_some());
            return 1;
        }

        let mut max = 0;
        let mut second = 0;

        for l in clause.iter() {
            debug_assert!(self.values[l.variable().index()].is_some());
            let level = self.nodes[l.variable().index()].level;
            if level > max {
                second = max;
                max = level;
            } else if level > second {
                second = level;
            }
        }

        debug_assert!(second > 0, "Asserting clauses have exactly one literal at the current level, so there must be another one at this point.");
        second
    }

    pub fn evaluate_clause(&self, clause: &[Literal]) -> ClauseStatus {
        let mut unsat = 0;
        let mut unit = None;
        for &l in clause {
            match self.values[l.variable().index()] {
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

/// Propagate consequences (implications) of a decision through the formula,
/// thereby changing the status of clauses. The implication graph
/// is used to keep track of the changes.
///
/// Apply repeatedly the unit rule. Return false if a conflict is reached
fn boolean_constraint_propagation(formula: &CnfFormula, level: usize, implications: &mut ImplicationGraph) -> Conflict {
    'outer: loop {
        // check conflicts
        for (index, c) in formula.clauses().enumerate() {
            if let ClauseStatus::Unsatisfied = implications.evaluate_clause(c) {
                return Conflict::Yes(index);
            }
        }
        // propagate
        for (clause_index, c) in formula.clauses().enumerate() {
            match implications.evaluate_clause(c) {
                ClauseStatus::Satisfied => {}
                ClauseStatus::Unsatisfied => {
                    unreachable!()
                }
                ClauseStatus::Unit(literal) => {
                    implications.add_node(literal, level, Antecedent::Clause(clause_index));
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
                implications.values[i] = None;
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
    debug_assert!(*level != 0);
    if *level <= 1 {
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

    *level = implications.clause_asserting_level(&cl);

    // add-clause-to-database
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

