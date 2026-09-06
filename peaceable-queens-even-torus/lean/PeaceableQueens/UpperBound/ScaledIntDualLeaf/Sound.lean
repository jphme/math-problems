import PeaceableQueens.UpperBound.ScaledIntDualLeaf.BoundScale
namespace PeaceableQueens.UpperBound.ScaledIntDualLeaf
open LPModel DualLeaf
set_option maxRecDepth 100000
set_option maxHeartbeats 0
lemma checkAt_implies_accepted (n d : Int) (b : Box) (c : Certificate)
    (h : checkAt n d b c = true) : AcceptedAt n d b c := by
  unfold checkAt at h
  have split {u v : Bool} (huv : (u && v) = true) : u = true ∧ v = true :=
    Eq.mp (Bool.and_eq_true u v) huv
  rcases split h with ⟨h6, hbound⟩
  rcases split h6 with ⟨h5, hc⟩
  rcases split h5 with ⟨h4, hp⟩
  rcases split h4 with ⟨h3, ht⟩
  rcases split h3 with ⟨h2, hmu⟩
  rcases split h2 with ⟨h1, hdS⟩
  have hs := h1
  refine ⟨of_decide_eq_true hs, of_decide_eq_true hdS, ?_, of_decide_eq_true ht, ?_,
    of_decide_eq_true hc, of_decide_eq_true hbound⟩
  · intro e he
    exact of_decide_eq_true (List.all_eq_true.mp hmu e he)
  · intro a
    apply of_decide_eq_true
    exact List.all_eq_true.mp hp _ (List.mem_ofFn.mpr ⟨a, rfl⟩)

theorem scaled_checkAt_to_sparse_checkAt (n d : Int) (b : Box) (c : Certificate)
    (hcheck : checkAt n d b c = true) :
    SparseListDualLeaf.checkAt ((n:ℚ)/d) b.profileLo b.profileHi (toSparse b c) = true := by
  have ha := checkAt_implies_accepted n d b c hcheck
  rcases ha with ⟨hS, hd, hmu, ht, hp, hc, hth⟩
  change decide (SparseListDualLeaf.AcceptedAt ((n:ℚ)/d) b.profileLo b.profileHi (toSparse b c)) = true
  apply decide_eq_true
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro e
    have hem : (toSparse b c).mu.get e ∈ (toSparse b c).mu :=
      List.get_mem _ _
    have hem' : (toSparse b c).mu.get e ∈
        c.mu.map (fun q => (q.1, (q.2 : ℚ) / b.S)) := by
      simpa [toSparse] using hem
    rcases List.mem_map.mp hem' with ⟨q, hq, heq⟩
    rw [← heq]
    exact div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hmu q hq)
      (by exact_mod_cast (le_of_lt hS))
  · have hz : (residual2 b c tVar : ℚ) / (b.S*b.S) = 0 := by simp [ht]
    rw [residual2_div b c tVar (ne_of_gt hS)] at hz
    exact hz
  · intro a
    rw [← residual1_div_p b c a (ne_of_gt hS)]
    exact div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hp a)
      (by exact_mod_cast (le_of_lt hS))
  · change (c.claimed : ℚ) / (b.S*b.S*b.S) =
      SparseListDualLeaf.recomputedBound b.profileLo b.profileHi (toSparse b c)
    rw [← recomputedBoundNum_scale b c hS, ← hc]
  · simp [toSparse]
    have hs3 : (0:ℚ) < b.S*b.S*b.S := by positivity
    have hdq : (0:ℚ) < d := by exact_mod_cast hd
    rw [div_le_div_iff₀ hs3 hdq]
    have hthq : ((c.claimed*d : Int) : ℚ) ≤ ((n*b.S*b.S*b.S : Int) : ℚ) := by
      exact_mod_cast hth
    simpa [mul_assoc] using hthq

theorem scaled_checkAt_sound {n d : Int} {b : Box} {c : Certificate}
    {z : LPVector} (hz : LeafFeasible b.profileLo b.profileHi z)
    (hcheck : checkAt n d b c = true) : z tVar ≤ (n : ℚ) / d := by
  exact SparseListDualLeaf.checkAt_sound hz
    (scaled_checkAt_to_sparse_checkAt n d b c hcheck)

#print axioms checkAt_implies_accepted
#print axioms recomputedBoundNum_scale
#print axioms scaled_checkAt_to_sparse_checkAt
#print axioms scaled_checkAt_sound
end PeaceableQueens.UpperBound.ScaledIntDualLeaf
