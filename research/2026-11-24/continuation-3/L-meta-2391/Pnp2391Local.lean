import Mathlib.Data.Finset.Card
import PEqualNP.Defs

namespace Pnp2391Local

/-!
Research partial for L-meta-2391, extending the locally checked L-meta-3321 context lemma.  A safe line context for two pure-point OR
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
      push Not at hs
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

/-! A local semantic rewrite.  The gate-count claim still requires realizing
the rewiring in the root circuit model; it is not asserted here. -/

noncomputable def pointOr {N : ℕ} (S : Finset (Fin N)) (x : Fin N → Bool) : Bool := by
  classical
  exact decide (∃ p ∈ S, x p = true)

noncomputable def incidenceFun {N : ℕ} (I : Fin N → Fin N → Prop)
    (x y : Fin N → Bool) : Bool := by
  classical
  exact decide (∃ p l : Fin N, I p l ∧ x p = true ∧ y l = true)

theorem pointOr_one_hot {N : ℕ} (S : Finset (Fin N)) (p : Fin N) :
    pointOr S (fun q => decide (q = p)) = decide (p ∈ S) := by
  classical
  simp [pointOr]

/-- On an incident pair input, a pure-point product sees only the singleton
point coordinate.  Its active points are exactly the intersection. -/
theorem product_one_hot {N : ℕ} (S T : Finset (Fin N)) (p : Fin N) :
    (pointOr S (fun q => decide (q = p)) && pointOr T (fun q => decide (q = p))) =
      decide (p ∈ S ∩ T) := by
  classical
  rw [pointOr_one_hot, pointOr_one_hot]
  simp

theorem product_one_hot_empty {N : ℕ} (S T : Finset (Fin N))
    (empty : S ∩ T = ∅) (p : Fin N) :
    (pointOr S (fun q => decide (q = p)) && pointOr T (fun q => decide (q = p))) =
      false := by
  rw [product_one_hot, empty]
  simp

theorem product_one_hot_singleton {N : ℕ} (S T : Finset (Fin N)) (p : Fin N)
    (single : S ∩ T = {p}) (q : Fin N) :
    (pointOr S (fun r => decide (r = q)) && pointOr T (fun r => decide (r = q))) =
      decide (q = p) := by
  rw [product_one_hot, single]
  simp

theorem common_input_implies_product {N : ℕ} (S T : Finset (Fin N))
    (p : Fin N) (common : p ∈ S ∩ T) (x : Fin N → Bool) (active : x p = true) :
    (pointOr S x && pointOr T x) = true := by
  classical
  simp only [Bool.and_eq_true]
  obtain ⟨hs, ht⟩ := Finset.mem_inter.mp common
  exact ⟨decide_eq_true ⟨p, hs, active⟩, decide_eq_true ⟨p, ht, active⟩⟩

noncomputable def selectedFactor {N : ℕ} (I : Fin N → Fin N → Prop)
    (S T : Finset (Fin N)) (l : Fin N) : Finset (Fin N) := by
  classical
  exact if ∀ s ∈ S, I s l then S else T

theorem selectedFactor_incident {N : ℕ} (I : Fin N → Fin N → Prop)
    (S T : Finset (Fin N)) (l : Fin N) (safe : SafeLine I S T l) :
    ∀ p ∈ selectedFactor I S T l, I p l := by
  classical
  have h := (safeLine_iff_side I S T l).mp safe
  unfold selectedFactor
  split_ifs with hs
  · exact hs
  · exact h.resolve_left hs

theorem old_reader_implies_new {N : ℕ} (I : Fin N → Fin N → Prop)
    (S T : Finset (Fin N)) (l : Fin N) (x y : Fin N → Bool) :
    ((pointOr S x && pointOr T x) && y l) = true →
      (pointOr (selectedFactor I S T l) x && y l) = true := by
  classical
  simp only [Bool.and_eq_true]
  intro h
  refine ⟨?_, h.2⟩
  unfold selectedFactor
  split_ifs
  · exact h.1.1
  · exact h.1.2

theorem new_reader_implies_incidence {N : ℕ} (I : Fin N → Fin N → Prop)
    (S T : Finset (Fin N)) (l : Fin N) (safe : SafeLine I S T l)
    (x y : Fin N → Bool) :
    (pointOr (selectedFactor I S T l) x && y l) = true →
      incidenceFun I x y = true := by
  classical
  intro h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hpoint, hline⟩ := h
  obtain ⟨p, hp, hx⟩ := of_decide_eq_true hpoint
  apply decide_eq_true
  exact ⟨p, l, selectedFactor_incident I S T l safe p hp, hx, hline⟩

/-- Increasing intermediate signals only on already-positive inputs preserves
any monotone continuation that originally computed the target. -/
theorem monotone_context_rewrite {α : Type} (old new : α → Bool)
    (target : Bool) (context : (α → Bool) → Bool)
    (mono : ∀ u v : α → Bool, (∀ i, u i = true → v i = true) →
      context u = true → context v = true)
    (increase : ∀ i, old i = true → new i = true)
    (sound : ∀ i, new i = true → target = true)
    (correct : context old = target) : context new = target := by
  cases ht : target with
  | false =>
    have eq : new = old := by
      funext i
      cases hn : new i with
      | false =>
        cases ho : old i with
        | false => rfl
        | true => have h := increase i ho; rw [hn] at h; cases h
      | true => have h := sound i hn; rw [ht] at h; cases h
    rw [eq, correct]
    exact ht
  | true =>
    exact mono old new increase (correct.trans ht)

/-- Each line reader can choose its own incident pure-point factor.  The
continuation may share reader outputs arbitrarily, provided it is monotone. -/
theorem safe_reader_context_rewrite {N : ℕ} {α : Type}
    (I : Fin N → Fin N → Prop) (S T : Finset (Fin N))
    (line : α → Fin N) (safe : ∀ i, SafeLine I S T (line i))
    (x y : Fin N → Bool) (context : (α → Bool) → Bool)
    (mono : ∀ u v : α → Bool, (∀ i, u i = true → v i = true) →
      context u = true → context v = true)
    (correct : context (fun i => (pointOr S x && pointOr T x) && y (line i)) =
      incidenceFun I x y) :
    context (fun i => pointOr (selectedFactor I S T (line i)) x && y (line i)) =
      incidenceFun I x y := by
  apply monotone_context_rewrite _ _ _ context mono
  · exact fun i => old_reader_implies_new I S T (line i) x y
  · exact fun i => new_reader_implies_incidence I S T (line i) (safe i) x y
  · exact correct

def plane3Inc (p l : Fin 13) : Prop :=
  p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9

instance : DecidableRel plane3Inc := fun p l => inferInstanceAs
  (Decidable (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9))

theorem plane3_no_four : ∀ p p' l l' : Fin 13, p ≠ p' → l ≠ l' →
    ¬ (plane3Inc p l ∧ plane3Inc p l' ∧ plane3Inc p' l ∧ plane3Inc p' l') := by
  decide +kernel

theorem plane3_safe_contexts (S T : Finset (Fin 13))
    (hS : 2 ≤ S.card) (hT : 2 ≤ T.card) :
    (safeLines plane3Inc S T).card ≤ 2 :=
  safeLines_card_le_two plane3Inc plane3_no_four S T hS hT

theorem plane3_common_pair_context (S T : Finset (Fin 13))
    (hST : 2 ≤ (S ∩ T).card) :
    (safeLines plane3Inc S T).card ≤ 1 :=
  safeLines_card_le_one_of_inter plane3Inc plane3_no_four S T hST

end Pnp2391Local

