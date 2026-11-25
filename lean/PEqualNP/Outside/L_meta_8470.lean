import PEqualNP.Defs

-- Finite incidence geometry and a rectangle-cover cardinality bound.
namespace PEqualNP.Outside.L_meta_8470

abbrev Inc (p l : Fin 21) : Prop :=
  (l.val + 21 - p.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)

def incidences : Finset (Fin 21 × Fin 21) :=
  Finset.univ.filter fun e => Inc e.1 e.2

def commonLines (p q : Fin 21) : Finset (Fin 21) :=
  Finset.univ.filter fun l => Inc p l ∧ Inc q l

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16000 in
lemma incidence_count : incidences.card = 105 := by
  decide +kernel

-- This checks only the 21 by 21 table of common-neighbor sets, rather than
-- enumerating four independent vertices.
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16000 in
lemma commonLines_card_le_one : ∀ p q : Fin 21, p ≠ q → (commonLines p q).card ≤ 1 := by
  decide +kernel

lemma rectangle_has_singleton_side (A B : Finset (Fin 21))
    (hrect : ∀ p ∈ A, ∀ l ∈ B, Inc p l) : A.card ≤ 1 ∨ B.card ≤ 1 := by
  by_cases hA : A.card ≤ 1
  · exact Or.inl hA
  · obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp (by omega : 1 < A.card)
    have hsub : B ⊆ commonLines p q := by
      intro l hl
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ l, hrect p hp l hl, hrect q hq l hl⟩
    exact Or.inr ((Finset.card_le_card hsub).trans (commonLines_card_le_one p q hpq))

lemma rectangle_card_le_weight (A B : Finset (Fin 21))
    (hA : A.Nonempty) (hB : B.Nonempty)
    (hrect : ∀ p ∈ A, ∀ l ∈ B, Inc p l) :
    (A ×ˢ B).card ≤ A.card + B.card - 1 := by
  have ha : 0 < A.card := Finset.card_pos.mpr hA
  have hb : 0 < B.card := Finset.card_pos.mpr hB
  rw [Finset.card_product]
  rcases rectangle_has_singleton_side A B hrect with h | h
  · have he : A.card = 1 := by omega
    rw [he, Nat.one_mul]
    omega
  · have he : B.card = 1 := by omega
    rw [he, Nat.mul_one]
    omega

theorem cover_cost_ge_105 (F : Finset (Finset (Fin 21) × Finset (Fin 21)))
    (hrect : ∀ p ∈ F, p.1.Nonempty ∧ p.2.Nonempty ∧
      ∀ u ∈ p.1, ∀ v ∈ p.2, Inc u v)
    (hcover : ∀ u v : Fin 21, Inc u v → ∃ p ∈ F, u ∈ p.1 ∧ v ∈ p.2) :
    105 ≤ F.sum (fun p => p.1.card + p.2.card - 1) := by
  have hsub : incidences ⊆ F.biUnion (fun p => p.1 ×ˢ p.2) := by
    intro e he
    obtain ⟨p, hp, hu, hv⟩ := hcover e.1 e.2 (Finset.mem_filter.mp he).2
    exact Finset.mem_biUnion.mpr ⟨p, hp, Finset.mem_product.mpr ⟨hu, hv⟩⟩
  calc
    105 = incidences.card := incidence_count.symm
    _ ≤ (F.biUnion (fun p => p.1 ×ˢ p.2)).card := Finset.card_le_card hsub
    _ ≤ F.sum (fun p => (p.1 ×ˢ p.2).card) := Finset.card_biUnion_le
    _ ≤ F.sum (fun p => p.1.card + p.2.card - 1) := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hA, hB, hI⟩ := hrect p hp
      exact rectangle_card_le_weight p.1 p.2 hA hB hI

end PEqualNP.Outside.L_meta_8470

theorem PEqualNP.Outside.L_meta_8470 : ∀ (x1 : Finset (Finset (Fin (21 : ℕ)) × Finset (Fin (21 : ℕ)))), (∀ x2 ∈ x1, x2.1.Nonempty ∧ x2.2.Nonempty ∧ ∀ x4 ∈ x2.1, ∀ x6 ∈ x2.2, (↑x6 + (21 : ℕ) - ↑x4) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) → (∀ (x3 x4 : Fin (21 : ℕ)), (↑x4 + (21 : ℕ) - ↑x3) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)] → ∃ x6 ∈ x1, x3 ∈ x6.1 ∧ x4 ∈ x6.2) → (105 : ℕ) ≤ ∑ x4 ∈ x1, (x4.1.card + x4.2.card - (1 : ℕ)) := by
  exact PEqualNP.Outside.L_meta_8470.cover_cost_ge_105
