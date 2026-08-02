# Lean 4 formalization — peaceable queens on even toroidal boards

[![Lean](https://github.com/jphme/math-problems/actions/workflows/lean.yml/badge.svg)](https://github.com/jphme/math-problems/actions/workflows/lean.yml)

Companion formalization for *Peaceable queens on even toroidal boards*
(`../paper/peace_even_torus.tex`), written at the request of an OEIS editor
reviewing the A279405 contribution.  Two deliverables:

1. **`FORMAL_PROOF.md`** — the proof of Theorem 1 (`t(2q) = H(2q)`) rewritten
   as a dependency-ordered sequence of formal statements, each tagged by
   formalization status, with exact specifications of the finite certified
   objects the upper bound rests on.
2. **`PeaceableQueens/`** — a Lean 4 / Mathlib development, building with
   **zero `sorry`**, formalizing the lower-bound half of the theorem in full
   generality plus complete small instances of the theorem itself.

## What is formalized

| Result | Lean name | File |
|---|---|---|
| Board, attacks, peaceability, `t n` (A279405), `H q` (= paper's `H(2q)`) | `Cell`, `SharesLine`, `IsPeaceable`, `HasPeaceable`, `t`, `H` | `Defs.lean` |
| `m ≤ t n ↔ HasPeaceable n m` | `le_t_iff` | `Defs.lean` |
| Line-colouring equivalence (paper Lemma 2): queens are eliminated | `hasPeaceable_iff_lineSets` | `LineColouring.lean` |
| `t n = lineMax n` — `t` becomes finitely computable | `t_eq_lineMax` | `LineColouring.lean` |
| Parity-separated construction (paper Prop. 4) | `parity construction lemmas` | `LowerBound.lean` |
| **Lower bound, all q: `H q ≤ t (2*q)`** | `H_le_t` | `LowerBound.lean` |
| `H` values of paper Table 1 (`H(2)…H(40)`), matching all published even terms of A279405 | `H_one` … `H_twenty` | `Values.lean` |
| **Complete Theorem 1 instances, upper bound included:** `t 2 = H 1`, `t 4 = H 2` | `t_two`, `t_four` | `Values.lean` |
| Reduction of Theorem 1 to the upper-bound statement | `evenTorusTheorem_of_upperBound` | `Main.lean` |

The general upper bound `t(2q) ≤ H(2q)` (paper Sections 3–6: 42-equation
moment relaxation, two exact rational branch certificates, algebraic finish
for `q ≥ 130`, exact cut-envelope ladder for `q ≤ 129`) is **not** formalized.
`FORMAL_PROOF.md` states it as precise finite statements against which a
verified certificate checker could be written; `Main.lean` isolates it as the
single hypothesis `UpperBoundStatement` from which Theorem 1 follows.

## Building

```
elan self update            # or install elan first
cd lean
lake exe cache get          # fetch Mathlib build cache
lake build                  # builds everything; no sorries
```

Pinned toolchain: `leanprover/lean4:v4.32.2`, Mathlib `v4.32.2`.

The same build runs in CI on every change to a Lean file
([`.github/workflows/lean.yml`](../../.github/workflows/lean.yml), via
[`leanprover/lean-action`](https://github.com/leanprover/lean-action)); the
badge above reports the result on `main`.

## Trusted base

All lemmas are checked by the Lean kernel. The exhaustive evaluations in
`Values.lean` (`H` values; `lineMax` for `n = 2, 4`) use `native_decide`,
i.e. Lean's compiled evaluator — the standard mechanism for verified
computation, with a slightly larger trusted base (the `Lean.ofReduceBool`
mechanism, reported per-declaration by `#print axioms`) than kernel-only
proofs. Everything else uses only the standard axioms (`propext`,
`Classical.choice`, `Quot.sound`); see the `#print axioms` commands at the
end of `Values.lean`. The same decision for `n = 6` (`t 6 = H 3`,
2²⁴ colourings) is possible in principle but was not kept: it exceeded a
15-minute wall-time budget.
