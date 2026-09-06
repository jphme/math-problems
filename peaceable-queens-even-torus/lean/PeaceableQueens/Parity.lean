import PeaceableQueens.Defs

/-! Shared parity labels, fibres and counting for both bounds of the even theorem. -/

namespace PeaceableQueens.Parity

/-- The canonical reduction modulo two on the even torus. -/
def parityMap (q : ℕ) : ZMod (2 * q) →+* ZMod 2 :=
  ZMod.castHom ⟨q, rfl⟩ (ZMod 2)

/-- A parity-labelled natural index; bounded versions give finite fibres. -/
def labelNat (q i j : ℕ) : ZMod (2 * q) := ((2 * j + i : ℕ) : ZMod (2 * q))

lemma parityMap_labelNat (q i j : ℕ) : parityMap q (labelNat q i j) = (i : ZMod 2) := by
  rw [labelNat, parityMap, map_natCast, Nat.cast_add, Nat.cast_mul,
    ZMod.natCast_self, zero_mul, zero_add]

lemma labelNat_inj {q i j k : ℕ} (hi : i ≤ 1) (hj : j < q) (hk : k < q)
    (h : labelNat q i j = labelNat q i k) : j = k := by
  have hv := congrArg ZMod.val h
  rw [labelNat, labelNat, ZMod.val_cast_of_lt (by omega),
    ZMod.val_cast_of_lt (by omega)] at hv
  omega

/-- The `j`-th label in parity class `p`, for `j < q`. -/
def parityLabel (q : ℕ) (p : Fin 2) (j : Fin q) : ZMod (2 * q) :=
  ((2 * j.val + p.val : ℕ) : ZMod (2 * q))

/-- The finite set of all labels represented by this parity parameterization. -/
def parityLabels (q : ℕ) (p : Fin 2) : Finset (ZMod (2 * q)) :=
  Finset.univ.image (parityLabel q p)

/-- The parity fibre, as a subset of all even-torus labels. -/
def parityClass (q : ℕ) [NeZero (2 * q)] (p : Fin 2) : Finset (ZMod (2 * q)) :=
  Finset.univ.filter fun x => parityMap q x = (p.val : ZMod 2)

lemma parityMap_label (q : ℕ) (p : Fin 2) (j : Fin q) :
    parityMap q (parityLabel q p j) = (p.val : ZMod 2) :=
  parityMap_labelNat q p.val j.val

lemma parityLabel_injective (q : ℕ) (p : Fin 2) :
    Function.Injective (parityLabel q p) := by
  intro j k h
  exact Fin.ext (labelNat_inj (by omega) j.isLt k.isLt h)

lemma card_parityLabels (q : ℕ) (p : Fin 2) :
    (parityLabels q p).card = q := by
  unfold parityLabels
  rw [Finset.card_image_of_injOn]
  · simp
  · intro j hj k hk h
    exact parityLabel_injective q p h

lemma parityMap_val (q : ℕ) [NeZero (2 * q)] (x : ZMod (2 * q)) :
    parityMap q x = (x.val : ZMod 2) := by
  rw [← ZMod.natCast_zmod_val x]
  simp [parityMap]

lemma parityLabels_eq_class (q : ℕ) [NeZero (2 * q)] (p : Fin 2) :
    parityLabels q p = parityClass q p := by
  ext x
  constructor
  · intro hx
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hx
    simp only [parityClass, Finset.mem_filter, Finset.mem_univ, true_and]
    exact parityMap_label q p j
  · intro hx
    have hxpar : parityMap q x = (p.val : ZMod 2) :=
      (Finset.mem_filter.mp hx).2
    let xv : ℕ := ZMod.val x
    have hxvlt : xv < 2 * q := by
      dsimp [xv]
      exact ZMod.val_lt x
    let pv : ℕ := Fin.val p
    have hmod : ((xv : ℕ) : ZMod 2) = ((pv : ℕ) : ZMod 2) := by
      rw [← parityMap_val q x]
      exact hxpar
    have hv := congrArg ZMod.val hmod
    have hpvlt : pv < 2 := by exact p.isLt
    have hpmod : pv % 2 = pv := Nat.mod_eq_of_lt hpvlt
    have hxveq : xv = x.val := rfl
    have hdecomp : 2 * (xv / 2) + pv = xv := by
      have hv' : xv % 2 = pv % 2 := by simpa using hv
      omega
    let j : Fin q := ⟨xv / 2, by omega⟩
    have hxeq : x = parityLabel q p j := by
      calc
        x = ((xv : ℕ) : ZMod (2 * q)) := by
          rw [show xv = x.val from rfl]
          exact (ZMod.natCast_zmod_val x).symm
        _ = ((2 * (xv / 2) + pv : ℕ) : ZMod (2 * q)) := by rw [hdecomp]
        _ = parityLabel q p j := by
          simp [parityLabel, pv, j]
    rw [hxeq]
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩

/-- Every parity class on the `2q` torus has exactly `q` labels. -/
theorem card_parityClass (q : ℕ) [NeZero (2 * q)] (p : Fin 2) :
    (parityClass q p).card = q := by
  rw [← parityLabels_eq_class q p]
  exact card_parityLabels q p

/-- The index of a label in its parity fibre. -/
def parityIndex (q : ℕ) [NeZero q] (x : ZMod (2 * q)) : Fin q :=
  ⟨x.val / 2, by
    have hx := ZMod.val_lt x
    have hq := Nat.pos_of_ne_zero (NeZero.ne q)
    omega⟩

lemma parityLabel_index (q : ℕ) [NeZero q] (p : Fin 2) (x : ZMod (2 * q))
    (hx : parityMap q x = (p.val : ZMod 2)) :
    parityLabel q p (parityIndex q x) = x := by
  let xv : ℕ := ZMod.val x
  let pv : ℕ := Fin.val p
  have hxvlt : xv < 2 * q := by
    dsimp [xv]
    exact ZMod.val_lt x
  have hmod : ((xv : ℕ) : ZMod 2) = ((pv : ℕ) : ZMod 2) := by
    rw [← parityMap_val q x]
    exact hx
  have hv := congrArg ZMod.val hmod
  have hpvlt : pv < 2 := by exact p.isLt
  have hpmod : pv % 2 = pv := Nat.mod_eq_of_lt hpvlt
  have hdecomp : 2 * (xv / 2) + pv = xv := by
    have hv' : xv % 2 = pv % 2 := by simpa using hv
    omega
  change ((2 * (xv / 2) + pv : ℕ) : ZMod (2 * q)) = x
  calc
    ((2 * (xv / 2) + pv : ℕ) : ZMod (2 * q)) = ((xv : ℕ) : ZMod (2 * q)) := by
      rw [hdecomp]
    _ = x := ZMod.natCast_zmod_val x

/-- Parameters whose parity-`p` label belongs to a selected set. -/
def selectedParityLabels (q : ℕ) (p : Fin 2) (S : Finset (ZMod (2 * q))) :
    Finset (Fin q) := Finset.univ.filter fun u => parityLabel q p u ∈ S

lemma selectedParityLabels_image (q : ℕ) [NeZero (2 * q)] (p : Fin 2)
    (S : Finset (ZMod (2 * q))) :
    (selectedParityLabels q p S).image (parityLabel q p) =
      S.filter fun x => parityMap q x = (p.val : ZMod 2) := by
  ext x
  simp only [Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨u, hu, rfl⟩
    have huS : parityLabel q p u ∈ S := by
      simpa [selectedParityLabels] using hu
    exact ⟨huS, parityMap_label q p u⟩
  · rintro ⟨hxS, hxpar⟩
    have hxclass : x ∈ parityClass q p := by simp [parityClass, hxpar]
    rw [← parityLabels_eq_class] at hxclass
    obtain ⟨u, -, hu⟩ := Finset.mem_image.mp hxclass
    refine ⟨u, ?_, hu⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [hu]
    exact hxS

lemma card_selectedParityLabels (q : ℕ) [NeZero (2 * q)] (p : Fin 2)
    (S : Finset (ZMod (2 * q))) :
    (selectedParityLabels q p S).card =
      (S.filter fun x => parityMap q x = (p.val : ZMod 2)).card := by
  rw [← selectedParityLabels_image]
  rw [Finset.card_image_of_injOn]
  intro x _ y _ h
  exact parityLabel_injective q p h

/-- The canonical equivalence between indices and an actual parity fibre. -/
def parityEquiv (q : ℕ) [NeZero q] (p : Fin 2) :
    Fin q ≃ {x : ZMod (2 * q) // parityMap q x = (p.val : ZMod 2)} where
  toFun j := ⟨parityLabel q p j, parityMap_label q p j⟩
  invFun x := parityIndex q x.val
  left_inv j := parityLabel_injective q p (parityLabel_index q p _ (parityMap_label q p j))
  right_inv x := Subtype.ext (parityLabel_index q p x.val x.property)

private lemma card_filter_compl_eq_sub_card_filter
    {α : Type} [Fintype α] [DecidableEq α]
    (s : Finset α) (P : α → Prop) [DecidablePred P]
    (hsub : s.filter P ⊆ Finset.univ.filter P)
    (huniv : (Finset.univ.filter P).card = q) :
    (sᶜ.filter P).card = q - (s.filter P).card := by
  have hset : sᶜ.filter P = (Finset.univ.filter P) \ (s.filter P) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_compl, Finset.mem_univ, true_and,
      Finset.mem_sdiff]
    tauto
  rw [hset, Finset.card_sdiff_of_subset hsub, huniv]

lemma parity_filter_subset_class (q : ℕ) [NeZero (2 * q)]
    (s : Finset (ZMod (2 * q))) (p : Fin 2) :
    s.filter (fun x => parityMap q x = (p.val : ZMod 2)) ⊆ parityClass q p := by
  intro x hx
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩

lemma card_parity_filter_compl (q : ℕ) [NeZero (2 * q)]
    (s : Finset (ZMod (2 * q))) (p : Fin 2) :
    (sᶜ.filter (fun x => parityMap q x = (p.val : ZMod 2))).card =
      q - (s.filter (fun x => parityMap q x = (p.val : ZMod 2))).card := by
  apply card_filter_compl_eq_sub_card_filter s
    (fun x => parityMap q x = (p.val : ZMod 2))
    (parity_filter_subset_class q s p)
  exact card_parityClass q p

end PeaceableQueens.Parity
