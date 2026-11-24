import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace Pnp3321Local

def PointHit {N : ℕ} (S : Finset (Fin N)) (z : Fin (N + N) → Bool) : Prop :=
  ∃ p ∈ S, z (Fin.castAdd N p) = true

def EdgeTrue {N : ℕ} (I : Fin N → Fin N → Prop) (z : Fin (N + N) → Bool) : Prop :=
  ∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true

def witness {N : ℕ} (s t l : Fin N) : Fin (N + N) → Bool :=
  Fin.append (fun p => decide (p = s ∨ p = t)) (fun k => decide (k = l))

theorem witness_points {N : ℕ} (s t l p : Fin N) :
    witness s t l (Fin.castAdd N p) = decide (p = s ∨ p = t) := by
  exact Fin.append_left _ _ p

theorem witness_line {N : ℕ} (s t l k : Fin N) :
    witness s t l (Fin.natAdd N k) = decide (k = l) := by
  exact Fin.append_right _ _ k

theorem witness_edge_iff {N : ℕ} (I : Fin N → Fin N → Prop) (s t l : Fin N) :
    EdgeTrue I (witness s t l) ↔ I s l ∨ I t l := by
  constructor
  · rintro ⟨p,k,hI,hp,hk⟩
    have hpk : p = s ∨ p = t := by simpa only [witness_points, decide_eq_true_eq] using hp
    have hkl : k = l := by simpa only [witness_line, decide_eq_true_eq] using hk
    subst k
    rcases hpk with rfl | rfl
    · exact Or.inl hI
    · exact Or.inr hI
  · rintro (h | h)
    · exact ⟨s,l,h,by rw [witness_points]; simp,by rw [witness_line]; simp⟩
    · exact ⟨t,l,h,by rw [witness_points]; simp,by rw [witness_line]; simp⟩

theorem product_forces_pairwise {N : ℕ} (I : Fin N → Fin N → Prop)
    (S T : Finset (Fin N)) (l : Fin N)
    (h : ∀ z, PointHit S z → PointHit T z →
      z (Fin.natAdd N l) = true → EdgeTrue I z) :
    ∀ s ∈ S, ∀ t ∈ T, I s l ∨ I t l := by
  intro s hs t ht
  apply (witness_edge_iff I s t l).mp
  exact h (witness s t l) ⟨s,hs,by rw [witness_points]; simp⟩
    ⟨t,ht,by rw [witness_points]; simp⟩ (by rw [witness_line]; simp)

theorem pairwise_forces_product {N : ℕ} (I : Fin N → Fin N → Prop)
    (S T : Finset (Fin N)) (l : Fin N)
    (h : ∀ s ∈ S, ∀ t ∈ T, I s l ∨ I t l) :
    ∀ z, PointHit S z → PointHit T z →
      z (Fin.natAdd N l) = true → EdgeTrue I z := by
  rintro z ⟨s,hs,hzs⟩ ⟨t,ht,hzt⟩ hzl
  rcases h s hs t ht with hsI | htI
  · exact ⟨s,l,hsI,hzs,hzl⟩
  · exact ⟨t,l,htI,hzt,hzl⟩

theorem violating_input {N : ℕ} (I : Fin N → Fin N → Prop)
    (S T : Finset (Fin N)) (s t l : Fin N)
    (hs : s ∈ S) (ht : t ∈ T) (hsl : ¬ I s l) (htl : ¬ I t l) :
    ∃ z, PointHit S z ∧ PointHit T z ∧
      z (Fin.natAdd N l) = true ∧ ¬ EdgeTrue I z := by
  refine ⟨witness s t l,⟨s,hs,by rw [witness_points]; simp⟩,
    ⟨t,ht,by rw [witness_points]; simp⟩,by rw [witness_line]; simp,?_⟩
  rw [witness_edge_iff]
  exact not_or.mpr ⟨hsl,htl⟩

theorem circuit_wire_bridge {N : ℕ} (I : Fin N → Fin N → Prop)
    (C : Circuit) (w : ℕ) (S T : Finset (Fin N)) (l : Fin N)
    (hsignal : ∀ z : Fin (N + N) → Bool,
      (C.wires (List.ofFn z)).getD w false = true ↔ PointHit S z ∧ PointHit T z)
    (hforces : ∀ z : Fin (N + N) → Bool,
      (C.wires (List.ofFn z)).getD w false = true →
      z (Fin.natAdd N l) = true → circuitFun (N + N) C z = true)
    (hcorrect : ∀ z : Fin (N + N) → Bool,
      circuitFun (N + N) C z = true ↔ EdgeTrue I z) :
    ∀ s ∈ S, ∀ t ∈ T, I s l ∨ I t l := by
  apply product_forces_pairwise I S T l
  intro z hs ht hl
  exact (hcorrect z).mp (hforces z ((hsignal z).mpr ⟨hs,ht⟩) hl)

def pointSingleton {N : ℕ} (p : Fin N) : Fin (N + N) → Bool :=
  Fin.append (fun q => decide (q = p)) (fun _ => false)

def lineSingleton {N : ℕ} (l : Fin N) : Fin (N + N) → Bool :=
  Fin.append (fun _ => false) (fun k => decide (k = l))

theorem point_hit_singleton {N : ℕ} (S : Finset (Fin N)) (p : Fin N) :
    PointHit S (pointSingleton p) ↔ p ∈ S := by
  simp [PointHit, pointSingleton]

theorem point_hit_line_singleton {N : ℕ} (S : Finset (Fin N)) (l : Fin N) :
    ¬ PointHit S (lineSingleton l) := by
  simp [PointHit, lineSingleton]

theorem product_singleton_iff {N : ℕ} (S T : Finset (Fin N)) (p : Fin N) :
    (PointHit S (pointSingleton p) ∧ PointHit T (pointSingleton p)) ↔ p ∈ S ∩ T := by
  simp [point_hit_singleton]

def sharpRelation (p l : Fin 3) : Prop :=
  (l = 0 ∧ (p = 0 ∨ p = 1)) ∨ (l = 1 ∧ (p = 0 ∨ p = 2))

instance : DecidableRel sharpRelation := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

def sharpS : Finset (Fin 3) := {0,1}
def sharpT : Finset (Fin 3) := {0,2}

theorem sharp_c4_free :
    ∀ p p' l l' : Fin 3, p ≠ p' → l ≠ l' →
      ¬ (sharpRelation p l ∧ sharpRelation p l' ∧ sharpRelation p' l ∧ sharpRelation p' l') := by
  decide +kernel

theorem sharp_safe_lines :
    ((Finset.univ : Finset (Fin 3)).filter
      (fun l => ∀ s ∈ sharpS, ∀ t ∈ sharpT, sharpRelation s l ∨ sharpRelation t l)).card = 2 := by
  decide +kernel

def sharpCircuit : Circuit :=
  ⟨[⟨GateOp.or,[0,1]⟩,⟨GateOp.or,[0,2]⟩,⟨GateOp.and,[6,7]⟩],8⟩

theorem sharp_circuit_semantics :
    ∀ z : Fin 6 → Bool,
      sharpCircuit.eval (List.ofFn z) = ((z 0 || z 1) && (z 0 || z 2)) := by
  decide +kernel

theorem sharp_singleton_true :
    sharpCircuit.eval (List.ofFn (pointSingleton (0 : Fin 3))) = true := by
  decide +kernel

theorem sharp_monotone : Monotone2 sharpCircuit := by
  intro g hg
  simp [sharpCircuit] at hg
  rcases hg with rfl | rfl | rfl <;> simp

theorem sharp_readsBack : NestedCover.ReadsBack 6 sharpCircuit := by
  intro j hj i hi
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by simp [sharpCircuit] at hj; omega
  rcases hj' with rfl | rfl | rfl <;>
    simp [NestedCover.gateAt, sharpCircuit] at hi <;>
    rcases hi with rfl | rfl <;> omega

end Pnp3321Local
