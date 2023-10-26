use crate::formula::Literal;
use crate::statistics::Statistics;

pub fn simplify_new_clause(start: usize, literals: &mut Vec<Literal>, stats: &mut Statistics) {
    literals[start..].sort_by_key(|it| it.variable().index());

    let mut i = start + 0;
    let mut j = start + 1;
    while j < literals.len() {
        if literals[i] == literals[j] {
            // found duplicate
            stats.eliminated_x_or_x_literals += 1;
            j += 1;
        } else if literals[i] == literals[j].negated() {
            // found tautology
            stats.eliminated_x_or_not_x_clauses += 1;
            literals.truncate(start);
            return;
        } else {
            i += 1;
            literals[i] = literals[j];
            j += 1;
        }
    }
    literals.truncate(i + 1);
}
