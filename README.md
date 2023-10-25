# sat-solver

A simple SAT solver based on the lecture slides from `185.A93 Formal Methods in Computer Science` at TU Wien.

# benchmark

- The files were from https://www.cs.ubc.ca/~hoos/SATLIB/benchm.html, but 
for some reason they had `%`, `0`, and a bunch of newlines at the end, 
which I removed with `for f in *.cnf; do head -n -3 "$f" > "${f}2"; done; rm *.cnf`.
- 1000 instances, 50 variables, 218 clauses
- WARNING: each run only takes ~5 milliseconds, so the measured time might be mostly startup overhead
- The performance seems to be somewhat similar to `minisat`

1000 instances, 50 variables, 218 clauses, all SAT
```
robert@robert-7590:~/dev/sat-solver$ hyperfine 'for f in inputs/uf50-218/*.cnf2; do target/release/sat-solver "$f"; done' 'for f in inputs/uf50-218/*.cnf2; do minisat -verb=0 "$f"; done; exit 0'
Benchmark 1: for f in inputs/uf50-218/*.cnf2; do target/release/sat-solver "$f"; done
  Time (mean ± σ):      4.707 s ±  0.741 s    [User: 3.399 s, System: 1.288 s]
  Range (min … max):    3.620 s …  5.644 s    10 runs
 
Benchmark 2: for f in inputs/uf50-218/*.cnf2; do minisat -verb=0 "$f"; done; exit 0
  Time (mean ± σ):      4.740 s ±  1.321 s    [User: 2.530 s, System: 2.185 s]
  Range (min … max):    3.240 s …  6.853 s    10 runs
 
Summary
  for f in inputs/uf50-218/*.cnf2; do target/release/sat-solver "$f"; done ran
    1.01 ± 0.32 times faster than for f in inputs/uf50-218/*.cnf2; do minisat -verb=0 "$f"; done; exit 0
```

1000 instances, 50 variables, 218 clauses, all UNSAT
```
robert@robert-7590:~/dev/sat-solver$ hyperfine 'for f in inputs/uuf50-218/*.cnf2; do target/release/sat-solver "$f"; done' 'for f in inputs/uuf50-218/*.cnf2; do minisat -verb=0 "$f"; done; exit 0'
Benchmark 1: for f in inputs/uuf50-218/*.cnf2; do target/release/sat-solver "$f"; done
  Time (mean ± σ):      4.464 s ±  0.462 s    [User: 3.691 s, System: 0.750 s]
  Range (min … max):    3.668 s …  5.108 s    10 runs
 
Benchmark 2: for f in inputs/uuf50-218/*.cnf2; do minisat -verb=0 "$f"; done; exit 0
  Time (mean ± σ):      4.409 s ±  0.587 s    [User: 2.511 s, System: 1.872 s]
  Range (min … max):    3.783 s …  5.338 s    10 runs
 
Summary
  for f in inputs/uuf50-218/*.cnf2; do minisat -verb=0 "$f"; done; exit 0 ran
    1.01 ± 0.17 times faster than for f in inputs/uuf50-218/*.cnf2; do target/release/sat-solver "$f"; done
```