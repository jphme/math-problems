import PeaceableQueens.UpperBound.FiniteLattice

/-!
# Sparse eight-coordinate cut evaluation

`SparseCut8.ofCut` computes the nonzero linear and bilinear term lists once.
Its evaluator then visits only retained terms for each point.  This is a
sparse representation; its equality theorem keeps `Cut.eval` as
the proof-facing definition.
-/

namespace PeaceableQueens.UpperBound.SparseCutEval

open FiniteLattice

abbrev LinearTerm := Fin 8 × Int
abbrev BilinearTerm := (Fin 8 × Fin 8) × Int

def sparseLinearTerms (cut : Cut 8) : List LinearTerm :=
  (List.ofFn (fun i : Fin 8 => (i, cut.linear i))).filter
    (fun term => decide (term.2 ≠ 0))

def sparseBilinearTerms (cut : Cut 8) : List BilinearTerm :=
  (List.ofFn (fun i : Fin 8 =>
    List.ofFn (fun j : Fin 8 => ((i, j), cut.bilinear i j)))).flatten.filter
      (fun term => decide (term.2 ≠ 0))

/-- A cut whose active coefficient locations have already been materialized. -/
structure SparseCut8 where
  constant : Int
  linearTerms : List LinearTerm
  bilinearTerms : List BilinearTerm

def SparseCut8.ofCut (cut : Cut 8) : SparseCut8 :=
  { constant := cut.constant
    linearTerms := sparseLinearTerms cut
    bilinearTerms := sparseBilinearTerms cut }

@[inline] def SparseCut8.eval (cut : SparseCut8) (q : Nat) (x : Point 8) : Int :=
  cut.constant * (q : Int) * (q : Int) +
    (cut.linearTerms.map fun term => term.2 * ((q : Int) * x term.1)).sum +
      (cut.bilinearTerms.map fun term =>
        term.2 * (x term.1.1 * x term.1.2)).sum

private theorem filter_zero_sum {α : Type*} (l : List α) (p : α → Bool)
    (f : α → Int) (hz : ∀ a, p a = false → f a = 0) :
    ((l.filter p).map f).sum = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      cases hp : p a with
      | false => simp [hp, hz a hp, ih]
      | true => simp [hp, ih]

private theorem sparseLinearTerms_eval_eq (cut : Cut 8) (q : Nat) (x : Point 8) :
    ((sparseLinearTerms cut).map (fun term => term.2 * ((q : Int) * x term.1))).sum =
      ∑ i, cut.linear i * ((q : Int) * x i) := by
  unfold sparseLinearTerms
  rw [filter_zero_sum]
  · simp only [List.map_ofFn, Fin.sum_ofFn, Function.comp_apply]
  · intro term hzero
    simp only [decide_eq_false_iff_not, not_not] at hzero
    simp [hzero]

private theorem sparseBilinearTerms_eval_eq (cut : Cut 8) (x : Point 8) :
    ((sparseBilinearTerms cut).map (fun term =>
      term.2 * (x term.1.1 * x term.1.2))).sum =
      ∑ i, ∑ j, cut.bilinear i j * (x i * x j) := by
  unfold sparseBilinearTerms
  rw [filter_zero_sum]
  · simp only [List.map_flatten, List.sum_flatten, List.map_map,
      List.map_ofFn, Fin.sum_ofFn, Function.comp_apply]
  · intro term hzero
    simp only [decide_eq_false_iff_not, not_not] at hzero
    simp [hzero]

/-- Sparse evaluation is exactly the established cut polynomial. -/
theorem SparseCut8.eval_ofCut_eq (cut : Cut 8) (q : Nat) (x : Point 8) :
    (SparseCut8.ofCut cut).eval q x = cut.eval q x := by
  simp only [SparseCut8.eval, SparseCut8.ofCut, sparseLinearTerms_eval_eq,
    sparseBilinearTerms_eval_eq, Cut.eval]

#print axioms SparseCut8.eval_ofCut_eq

end PeaceableQueens.UpperBound.SparseCutEval
