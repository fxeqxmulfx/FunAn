# Functional Analysis in Lean 4

Formalization of exercises from **R.A. Bashmakov & I.S. Galimov, "Functional Analysis: Assignments for 3rd-year students"** (Bashkir State University, Ufa, 2007) using Lean 4 and Mathlib.

## Status

**128 / 128** proof tasks formalized (all `sorry`-free).

## Structure

Each section corresponds to a chapter of the textbook:

| # | Topic | Tasks |
|---|-------|-------|
| 1 | Algebra of Sets | 6 |
| 2 | Measure & Measurable Sets | 8 |
| 3 | Measurable Functions | 12 |
| 4 | Lebesgue Integral | 4 |
| 5 | Bounded Variation & Riemann-Stieltjes Integral | 7 |
| 6 | Topological Spaces | 2 |
| 7 | Metric Spaces | 4 |
| 8 | Complete Metric Spaces | 5 |
| 9 | Separable Metric Spaces | 11 |
| 10 | Contraction Mapping Principle | 6 |
| 11 | Normed Spaces | 13 |
| 12 | Hilbert Spaces | 13 |
| 13 | Linear Continuous Functionals | 1 |
| 14 | Linear Continuous Operators | 3 |
| 15 | Inverse Operators | 5 |
| 17 | Hahn-Banach, Strong & Weak Convergence | 6 |
| 18 | Adjoint Operators | 3 |
| 19 | Operator Convergence | 5 |
| 20 | Compact Sets | 5 |
| 21 | Compact Operators | 11 |

Proof files are in `FunAn/SectionNN_Topic/TaskMM.lean`. The full task list with status is in [TODO_prove_tasks.md](TODO_prove_tasks.md).

## Building

```bash
lake build
```

Requires Lean 4 and Mathlib.
