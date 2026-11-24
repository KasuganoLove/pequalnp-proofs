import Mathlib.Data.Finset.Card
import PEqualNP.Defs

namespace Pnp3321Contexts

/-!
Research partial for L-meta-3321.  A safe line context for two pure-point OR
factors is one for which every assignment satisfying both factors already has
an incident active point on that line.  This is a local semantic condition;
it is not a normalization of arbitrary shared circuit wires.
-/

def SafeLine {N : ℕ} (I : Fin N → Fin N → Prop)
    (S T : Finset (Fin N)) (l : Fin N) : Prop :=
  ∀ x : Fin N → Bool,
    (∃ s ∈ S, x s = true) → (∃ t ∈ T, x t = true) →
    ∃ p : Fin N, I p l ∧ x p = true

theorem safeLine_iff_pairwise {N : ℕ} (I : Fin N → Fin N → Prop)
    (S T : Finset (Fin N)) (l : Fin N) :
    SafeLine I S T l ↔ ∀ s ∈ S, ∀ t ∈ T, I s l ∨ I t l := by
  classical
  constructor
  · intro h s hs t ht
    obtain ⟨p, hp, hpx⟩ := h (fun p => decide (p = s ∨ p = t))
      ⟨s, hs, by simp⟩ ⟨t, ht, by simp⟩
    rcases of_decide_eq_true hpx with rfl | rfl
    · exact Or.inl hp
    · exact Or.inr hp
  · intro h x hs ht
    obtain ⟨s, hs, hxs⟩ := hs
    obtain ⟨t, ht, hxt⟩ := ht
    rcases h s hs t ht with hsI | htI
    · exact ⟨s, hsI, hxs⟩
    · exact ⟨t, htI, hxt⟩

theorem safeLine_iff_side {N : ℕ} (I : Fin N → Fin N → Prop)
    (S T : Finset (Fin N)) (l : Fin N) :
    SafeLine I S T l ↔
      (∀ s ∈ S, I s l) ∨ (∀ t ∈ T, I t l) := by
  classical
  rw [safeLine_iff_pairwise]
  constructor
  · intro h
    by_cases hs : ∀ s ∈ S, I s l
    · exact Or.inl hs
    · right
      push_neg at hs
      obtain ⟨s, hs, hsI⟩ := hs
      intro t ht
      exact (h s hs t ht).resolve_left hsI
  · rintro (hs | ht) s hs' t ht'
    · exact Or.inl (hs s hs')
    · exact Or.inr (ht t ht')

noncomputable def fullLines {N : ℕ} (I : Fin N → Fin N → Prop)
    (S : Finset (Fin N)) : Finset (Fin N) := by
  classical
  exact Finset.univ.filter (fun l => ∀ s ∈ S, I s l)

noncomputable def safeLines {N : ℕ} (I : Fin N → Fin N → Prop)
    (S T : Finset (Fin N)) : Finset (Fin N) := by
  classical
  exact Finset.univ.filter (SafeLine I S T)

theorem safeLines_eq_union {N : ℕ} (I : Fin N → Fin N → Prop)
    (S T : Finset (Fin N)) :
    safeLines I S T = fullLines I S ∪ fullLines I T := by
  classical
  ext l
  simp [safeLines, fullLines, safeLine_iff_side]

theorem fullLines_card_le_one {N : ℕ} (I : Fin N → Fin N → Prop)
    (noFour : ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l'))
    (S : Finset (Fin N)) (hS : 2 ≤ S.card) :
    (fullLines I S).card ≤ 1 := by
  classical
  obtain ⟨s, hs, t, ht, hst⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
  apply Finset.card_le_one.mpr
  intro l hl m hm
  have hl' : ∀ p ∈ S, I p l := (Finset.mem_filter.mp hl).2
  have hm' : ∀ p ∈ S, I p m := (Finset.mem_filter.mp hm).2
  by_contra hlm
  exact noFour s t l m hst hlm ⟨hl' s hs, hm' s hs, hl' t ht, hm' t ht⟩

/-- A product of two pure-point ORs, each using at least two distinct points,
has at most two individually sound line contexts in a C4-free incidence. -/
theorem safeLines_card_le_two {N : ℕ} (I : Fin N → Fin N → Prop)
    (noFour : ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l'))
    (S T : Finset (Fin N)) (hS : 2 ≤ S.card) (hT : 2 ≤ T.card) :
    (safeLines I S T).card ≤ 2 := by
  classical
  rw [safeLines_eq_union]
  calc
    (fullLines I S ∪ fullLines I T).card ≤
        (fullLines I S).card + (fullLines I T).card := Finset.card_union_le _ _
    _ ≤ 1 + 1 := Nat.add_le_add
      (fullLines_card_le_one I noFour S hS) (fullLines_card_le_one I noFour T hT)
    _ = 2 := rfl

/-- Two common points improve the local bound to one safe line context. -/
theorem safeLines_card_le_one_of_inter {N : ℕ} (I : Fin N → Fin N → Prop)
    (noFour : ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l'))
    (S T : Finset (Fin N)) (hST : 2 ≤ (S ∩ T).card) :
    (safeLines I S T).card ≤ 1 := by
  classical
  have hsub : safeLines I S T ⊆ fullLines I (S ∩ T) := by
    intro l hl
    have hp := (safeLine_iff_pairwise I S T l).mp (Finset.mem_filter.mp hl).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro p hmem
    obtain ⟨hs, ht⟩ := Finset.mem_inter.mp hmem
    exact (hp p hs p ht).elim id id
  exact (Finset.card_le_card hsub).trans (fullLines_card_le_one I noFour (S ∩ T) hST)

end Pnp3321Contexts
