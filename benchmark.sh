cargo build --release

echo "Uniform Random-3-SAT: 50 variables, 218 clauses - 1000 instances, all SAT"
hyperfine --warmup 1 'for f in inputs/uf50-218/*.cnf2; do target/release/sat-solver "$f"; done' 'for f in inputs/uf50-218/*.cnf2; do minisat -verb=0 "$f"; done; exit 0';
echo "Uniform Random-3-SAT: 50 variables, 218 clauses - 1000 instances, all UNSAT"
hyperfine --warmup 1 'for f in inputs/uuf50-218/*.cnf2; do target/release/sat-solver "$f"; done' 'for f in inputs/uuf50-218/*.cnf2; do minisat -verb=0 "$f"; done; exit 0';
echo "Uniform Random-3-SAT: 150 variables, 645 clauses - 100 instances, all SAT"
hyperfine --min-runs 3 'for f in inputs/uf150-645/*.cnf2; do target/release/sat-solver "$f"; done' 'for f in inputs/uf150-645/*.cnf2; do minisat -verb=0 "$f"; done; exit 0';
echo "Uniform Random-3-SAT: 150 variables, 645 clauses - 100 instances, all UNSAT"
hyperfine --min-runs 3 'for f in inputs/uuf150-645/*.cnf2; do target/release/sat-solver "$f"; done' 'for f in inputs/uuf150-645/*.cnf2; do minisat -verb=0 "$f"; done; exit 0';

