import PeaceableQueens.Defs

/-!
# Reusable finite counting and board equivalences

These interfaces transport predicates, army sizes and peaceability along
explicit bijections. They are shared by the parity-block and symmetry proofs.
-/

namespace PeaceableQueens

theorem card_filter_of_bijective {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq β] (f : α → β) (hf : Function.Bijective f)
    (P : β → Prop) [DecidablePred P] :
    (Finset.univ.filter fun x => P (f x)).card = (Finset.univ.filter P).card := by
  classical
  have himage : (Finset.univ.filter fun x => P (f x)).image f =
      Finset.univ.filter P := by
    ext y
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      obtain ⟨x, rfl⟩ := hf.surjective y
      exact ⟨x, hy, rfl⟩
  rw [← himage, Finset.card_image_of_injective _ hf.injective]

/-- A board equivalence preserves the four-line attack relation. -/
structure BoardEquiv (n : ℕ) extends Cell n ≃ Cell n where
  sharesLine_iff : ∀ p q, SharesLine (toEquiv p) (toEquiv q) ↔ SharesLine p q

/-- Translating the torus preserves each of its four line families. -/
def BoardEquiv.translation {n : ℕ} (d : Cell n) : BoardEquiv n where
  toFun p := (p.1 + d.1, p.2 + d.2)
  invFun p := (p.1 - d.1, p.2 - d.2)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp
  sharesLine_iff p q := by
    change SharesLine (p.1 + d.1, p.2 + d.2) (q.1 + d.1, q.2 + d.2) ↔ SharesLine p q
    simp only [SharesLine]
    constructor <;> rintro (h | h | h | h)
    all_goals first
      | exact Or.inl (by linear_combination h)
      | exact Or.inr (Or.inl (by linear_combination h))
      | exact Or.inr (Or.inr (Or.inl (by linear_combination h)))
      | exact Or.inr (Or.inr (Or.inr (by linear_combination h)))

theorem BoardEquiv.isPeaceable_image {n : ℕ} (e : BoardEquiv n)
    {B W : Finset (Cell n)} (h : IsPeaceable B W) :
    IsPeaceable (B.image e.toEquiv) (W.image e.toEquiv) := by
  rintro _ hb _ hw hline
  obtain ⟨b, hbB, rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨w, hwW, rfl⟩ := Finset.mem_image.mp hw
  exact h b hbB w hwW ((e.sharesLine_iff b w).mp hline)

theorem BoardEquiv.card_image {n : ℕ} (e : BoardEquiv n) (B : Finset (Cell n)) :
    (B.image e.toEquiv).card = B.card :=
  Finset.card_image_of_injective _ e.toEquiv.injective

end PeaceableQueens
