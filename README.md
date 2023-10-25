# sat-solver

A simple SAT solver based on the lecture `185.A93 Formal Methods in Computer Science` at TU Wien.

# benchmark

- The input files were from https://www.cs.ubc.ca/~hoos/SATLIB/benchm.html, but 
for some reason they had `%`, `0`, and a newline at the end, 
which I removed with `for f in *.cnf; do head -n -3 "$f" > "${f}2"; done; rm *.cnf`.
- script: `./benchmark.sh`
- On small instances, the performance is similar to `minisat`, but on larger ones we are much slower:

Uniform Random-3-SAT: 50 variables, 218 clauses - 1000 instances, all SAT
```
Benchmark 1: for f in inputs/uf50-218/*.cnf2; do target/release/sat-solver "$f"; done
  Time (mean ± σ):      3.823 s ±  0.458 s    [User: 2.744 s, System: 1.056 s]
  Range (min … max):    3.040 s …  4.528 s    10 runs
 
Benchmark 2: for f in inputs/uf50-218/*.cnf2; do minisat -verb=0 "$f"; done; exit 0
  Time (mean ± σ):      4.643 s ±  1.227 s    [User: 2.557 s, System: 2.061 s]
  Range (min … max):    3.324 s …  7.241 s    10 runs
 
Summary
  for f in inputs/uf50-218/*.cnf2; do target/release/sat-solver "$f"; done ran
    1.21 ± 0.35 times faster than for f in inputs/uf50-218/*.cnf2; do minisat -verb=0 "$f"; done; exit 0
```
Uniform Random-3-SAT: 50 variables, 218 clauses - 1000 instances, all UNSAT
```
Benchmark 1: for f in inputs/uuf50-218/*.cnf2; do target/release/sat-solver "$f"; done
  Time (mean ± σ):      5.227 s ±  0.745 s    [User: 4.140 s, System: 1.067 s]
  Range (min … max):    4.160 s …  6.787 s    10 runs
 
Benchmark 2: for f in inputs/uuf50-218/*.cnf2; do minisat -verb=0 "$f"; done; exit 0
  Time (mean ± σ):      4.466 s ±  0.751 s    [User: 2.520 s, System: 1.921 s]
  Range (min … max):    3.442 s …  5.747 s    10 runs
 
Summary
  for f in inputs/uuf50-218/*.cnf2; do minisat -verb=0 "$f"; done; exit 0 ran
    1.17 ± 0.26 times faster than for f in inputs/uuf50-218/*.cnf2; do target/release/sat-solver "$f"; done
```
Uniform Random-3-SAT: 150 variables, 645 clauses - 100 instances, all SAT
```
Benchmark 1: for f in inputs/uf150-645/*.cnf2; do target/release/sat-solver "$f"; done
  Time (mean ± σ):     100.024 s ±  0.086 s    [User: 99.883 s, System: 0.133 s]
  Range (min … max):   99.928 s … 100.094 s    3 runs
 
Benchmark 2: for f in inputs/uf150-645/*.cnf2; do minisat -verb=0 "$f"; done; exit 0
  Time (mean ± σ):      1.198 s ±  0.002 s    [User: 1.001 s, System: 0.195 s]
  Range (min … max):    1.196 s …  1.200 s    3 runs
 
Summary
  for f in inputs/uf150-645/*.cnf2; do minisat -verb=0 "$f"; done; exit 0 ran
   83.47 ± 0.17 times faster than for f in inputs/uf150-645/*.cnf2; do target/release/sat-solver "$f"; done
```
Uniform Random-3-SAT: 150 variables, 645 clauses - 100 instances, all UNSAT
```
Benchmark 1: for f in inputs/uuf150-645/*.cnf2; do target/release/sat-solver "$f"; done
  Time (mean ± σ):     377.046 s ±  0.161 s    [User: 376.811 s, System: 0.208 s]
  Range (min … max):   376.868 s … 377.183 s    3 runs
 
Benchmark 2: for f in inputs/uuf150-645/*.cnf2; do minisat -verb=0 "$f"; done; exit 0
  Time (mean ± σ):      2.574 s ±  0.005 s    [User: 2.354 s, System: 0.217 s]
  Range (min … max):    2.570 s …  2.580 s    3 runs
 
Summary
  for f in inputs/uuf150-645/*.cnf2; do minisat -verb=0 "$f"; done; exit 0 ran
  146.49 ± 0.31 times faster than for f in inputs/uuf150-645/*.cnf2; do target/release/sat-solver "$f"; done
```
