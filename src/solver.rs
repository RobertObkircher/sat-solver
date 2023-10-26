use crate::formula::{CnfFormula, Literal};
use crate::statistics::Statistics;

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum Satisfiable {
    Yes,
    No,
}


pub fn sat(mut formula: CnfFormula, stats: &mut Statistics) -> Satisfiable {
    let mut implications = ImplicationGraph::new(formula.variable_count);
    // 0 = uninitialized
    // 1 = "forced" initial decisions
    // 2 = first real decision
    let mut level = 1u32; // u32 is enough because there at most one level per variable

    let mut pure_literals = vec![None; formula.variable_count + 1];

    // make initial decisions
    if let Conflict::Yes(_) = boolean_constraint_propagation(&formula, level, &mut implications, stats, &mut pure_literals) {
        return Satisfiable::No;
    }

    // VSIDS: Variable State Independent Decaying Sum
    let mut vsids = vec![0u8; formula.variable_count + 1];

    let mut conflicts = 0;
    loop {
        if let Some(literal) = decide(&implications, &vsids) {
            level += 1;
            implications.add_node(literal, level, Antecedent::Decision);

            while let Conflict::Yes(conflict_clause) = boolean_constraint_propagation(&formula, level, &mut implications, stats, &mut pure_literals) {
                for l in formula.get_clause(conflict_clause) {
                    if vsids[l.variable().index()] == 255 {
                        // TODO does it matter that this isn't entirely fair?
                        vsids.iter_mut().for_each(|it| *it /= 2);
                    }
                    vsids[l.variable().index()] += 1;
                }
                let from_level = level;
                if !analyze_conflict(conflict_clause, &mut implications, &mut formula, &mut level) {
                    return Satisfiable::No;
                }
                conflicts += 1;
                // TODO tune restart policy, guarantee different decision after restart
                // restart for every power of two
                // This reduced time for 100 p cnf 150  645 instances from 266 to 103 seconds
                if conflicts & (conflicts - 1) == 0 {
                    level = 1;
                }
                implications.backtrack(from_level, level);
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

/// The data is essentially `Map<Variable, (Sign, Level, Antecedent)>`
/// but it is split into two arrays for possibly better caching.
///
/// The edges are from the other variables in the `Antecedent`.
struct ImplicationGraph {
    // TODO pack two into one byte?
    values: Vec<Option<bool>>,
    nodes: Vec<ImplicationNode>,
    /// Stores the variables for backtracking. The sign indicates
    /// whether a decision was made, so backtracking doesn't have
    /// to fetch the level from the `node` array.
    ///
    /// On "p cnf 50  218" this only gave a minor improvement over
    /// simple iteration through all nodes.
    backtrack_stack: Vec<Literal>,
}

impl ImplicationGraph {
    fn new(variable_count: usize) -> Self {
        Self {
            values: vec![None; variable_count + 1],
            nodes: (0..(variable_count + 1)).map(|_| ImplicationNode {
                level: 0,
                from_clause: false,
                clause: 0,
            }).collect(),
            backtrack_stack: Vec::with_capacity(variable_count),
        }
    }

    pub fn add_node(&mut self, literal: Literal, level: u32, antecedent: Antecedent) {
        let index = literal.variable().index();
        debug_assert!(self.values[index].is_none());
        self.values[index] = Some(literal.value());
        self.nodes[index] = if let Antecedent::Clause(clause) = antecedent {
            ImplicationNode {
                level,
                from_clause: true,
                clause,
            }
        } else {
            ImplicationNode {
                level,
                from_clause: false,
                clause: 0,
            }
        };
        self.backtrack_stack.push(literal.variable().literal(matches!(antecedent, Antecedent::Decision)));
    }

    /// Returns the index and the literal with the highest decision level.
    /// Decision nodes are ignored, because the caller only resolves against the
    /// others to make the clause asserting asserting on the current decision level.
    pub fn last_assigned_literal(&self, clause: &[Literal]) -> Option<(usize, Literal)> {
        debug_assert!(clause.iter().all(|l| self.values[l.variable().index()].is_some()));
        clause.iter().cloned().enumerate()
            .filter(|(_, l)| self.nodes[l.variable().index()].from_clause)
            .max_by_key(|(_, l)| self.nodes[l.variable().index()].level)
    }


    /// 2nd highest dl in an asserting clause
    pub fn clause_asserting_level(&self, clause: &[Literal]) -> u32 {
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

    pub fn backtrack(&mut self, mut from: u32, to: u32) {
        while from > to {
            let next = self.backtrack_stack.pop().unwrap();
            debug_assert_eq!(self.nodes[next.variable().index()].level, from);
            if next.value() {
                from -= 1;
            }
            self.values[next.variable().index()] = None;
            #[cfg(debug_assertions)]
            {
                self.nodes[next.variable().index()].level = 0;
            }
        }
    }
}

const _: [u8; 16] = [0; std::mem::size_of::<ImplicationNode>()];

/// Memory optimization:
/// For some reason the size is 24 bytes if `ImplicationNode` contains `Antecedent`.
/// Reducing it to 16 with `usize`+`bool` initially made runtime worse
/// (103 -> 107 seconds on 100*`p cnf 150  645`) but adding repr(C) improved it to 101 s.
#[repr(C)]
struct ImplicationNode {
    level: u32,
    from_clause: bool,
    clause: usize,
}

#[derive(Debug, Copy, Clone)]
enum Antecedent {
    Decision,
    /// The actual edges are the other literals in the clause.
    Clause(usize),
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
fn boolean_constraint_propagation(formula: &CnfFormula, level: u32, implications: &mut ImplicationGraph, stats: &mut Statistics, pure_literals: &mut Vec<Option<Option<bool>>>) -> Conflict {
    let mut break_after_index = 0;
    // NOTE: Previously we eagerly checked all clauses for conflicts before any unit propagation.
    //       This version is much faster (4x on p cnf 50  218), despite potentially causing multiple conflicts.
    //       Visiting them in reverse order, to immediately try learned clauses after backtracking,
    //       also made small instances faster, but it slightly slowed down p cnf 150  645.
    // TODO: although not covered in the course, something like 2-watched literals could make this even faster
    pure_literals.fill(None);
    loop {
        for (index, c) in formula.clauses().enumerate().rev() {
            match implications.evaluate_clause(c) {
                ClauseStatus::Satisfied => {}
                ClauseStatus::Unsatisfied => {
                    return Conflict::Yes(index);
                }
                ClauseStatus::Unit(literal) => {
                    implications.add_node(literal, level, Antecedent::Clause(index));
                    break_after_index = index;
                    pure_literals.fill(None);
                    continue;
                }
                ClauseStatus::Unresolved => {
                    for &l in c {
                        let new = match pure_literals[l.variable().index()] {
                            None => Some(Some(l.value())),
                            Some(s) => Some(s.clone().filter(|&it| it == l.value())),
                        };
                        pure_literals[l.variable().index()] = new;
                    }
                }
            }
            if break_after_index == index {
                for (i, s) in pure_literals.iter().enumerate() {
                    if let Some(Some(sign)) = s {
                        let var = i as i32;
                        let lit = Literal::try_from(if *sign { var } else { -var }).unwrap();
                        if implications.values[lit.variable().index()].is_none() {
                            stats.pure_literals += 1;
                            implications.add_node(lit, level, Antecedent::Decision);
                            let ugly_hack = implications.backtrack_stack.pop().unwrap().negated();
                            implications.backtrack_stack.push( ugly_hack);
                        }
                    }
                }

                return Conflict::No;
            }
        }
    }
}

/// Output: BT level and new conflict clause
fn analyze_conflict(conflict_clause: usize, implications: &ImplicationGraph, formula: &mut CnfFormula, level: &mut u32) -> bool {
    debug_assert!(*level != 0);
    if *level <= 1 {
        return false;
    }

    let mut cl = formula.get_clause(conflict_clause).to_vec();
    while !is_asserting(&cl, implications, *level) {
        let (i, lit) = implications.last_assigned_literal(&cl).unwrap();
        let var = lit.variable();
        debug_assert_eq!(implications.nodes[var.index()].level, *level);
        debug_assert!(implications.nodes[var.index()].from_clause);
        let ante = implications.nodes[var.index()].clause;
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
fn is_asserting(clause: &[Literal], implications: &ImplicationGraph, level: u32) -> bool {
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

