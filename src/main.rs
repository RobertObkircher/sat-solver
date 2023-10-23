fn main() {
    println!("Hello, world!");
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
enum Satisfiable {
    Yes,
    No,
}
fn sat() -> Satisfiable {
    loop {
        if let Some(assignment) = decide() {
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

struct Variable;
struct Value;

/// Choose next variable and value. Return `None` if all variables are assigned.
fn decide() -> Option<(Variable, Value)> {
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
