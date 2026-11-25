import PEqualNP.Outside.L_meta_4101
import Pnp1031OwnershipFinite

/-!
Conditional finite-test cost bounds.  These compose the finite-test equivalence
from `Pnp1031OwnershipFinite` with the existing clean-circuit count and the
order-three plane facts from upstream `L_meta_4101` (Apache-2.0).

The hypothesis that every AND gate rejects the negative family is essential.
Output rejection alone is not a substitute for that hypothesis.
-/

namespace Pnp2343CleanCost

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
  Pnp1031OwnershipFinite

theorem exact_of_finite_tests {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit)
    (hmono : Monotone2 C) (htests : RejectsNonedgePairs G C)
    (hsingle : ∀ u : Fin n, C.eval (List.ofFn (pairInput u u)) = false)
    (haccept : ∀ u v : Fin n, G.Adj u v →
      C.eval (List.ofFn (pairInput u v)) = true) :
    ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔ EdgeTrue G x := by
  intro x
  constructor
  · intro hv
    by_contra hfree
    have hwire : Wire.val C.gates C.output x = true := hv
    obtain ⟨u, _, hu⟩ := edgefree_wire_witness G C hmono htests x hfree C.output hwire
    have hone : C.eval (List.ofFn (pairInput u u)) = true :=
      hu _ (by simp [pairInput])
    rw [hsingle u] at hone
    contradiction
  · rintro ⟨u, v, huv, hxu, hxv⟩
    apply Wire.val_mono C.gates hmono (pairInput u v) x ?_ C.output (haccept u v huv)
    intro w hw
    simp only [pairInput, decide_eq_true_eq] at hw
    rcases hw with rfl | rfl
    · exact hxu
    · exact hxv

theorem cover_budget_of_finite_tests {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj]
    (hfour : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (C : Circuit) (hmono : Monotone2 C) (htests : RejectsNonedgePairs G C)
    (hsingle : ∀ u : Fin n, C.eval (List.ofFn (pairInput u u)) = false)
    (haccept : ∀ u v : Fin n, G.Adj u v →
      C.eval (List.ofFn (pairInput u v)) = true) :
    ∃ T : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) ∧
      G.edgeFinset.card + T.card ≤ C.size + 1 := by
  classical
  have hcorrect := exact_of_finite_tests G C hmono htests hsingle haccept
  have hsound := finite_tests_imply_all_and_sound G C hmono htests
  apply PEqualNP.Outside.L_meta_4101_aux.CleanCount.pairCleanBound n G hfour
    C.gates C.output hmono
  · intro x
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq, EdgeTrue] using hcorrect x
  · intro i x _ hand hv
    exact hsound i.val (C.gates.get i) (by simp [List.get_eq_getElem]) hand x hv

theorem plane_bound_of_finite_tests (C : Circuit) (hmono : Monotone2 C)
    (htests : RejectsNonedgePairs PEqualNP.Outside.L_meta_4101_aux.Plane.G C)
    (hsingle : ∀ u : Fin 26, C.eval (List.ofFn (pairInput u u)) = false)
    (haccept : ∀ u v : Fin 26, PEqualNP.Outside.L_meta_4101_aux.Plane.G.Adj u v →
      C.eval (List.ofFn (pairInput u v)) = true) :
    64 ≤ C.size := by
  classical
  obtain ⟨T, hT, hbudget⟩ := cover_budget_of_finite_tests
    PEqualNP.Outside.L_meta_4101_aux.Plane.G PEqualNP.Outside.L_meta_4101_aux.Plane.G_c4
    C hmono htests hsingle haccept
  have hcover := PEqualNP.Outside.L_meta_4101_aux.Plane.cover13 T hT
  have hedges := PEqualNP.Outside.L_meta_4101_aux.Plane.G_edges inferInstance
  omega

/-- Monotonicity transfers rejection of a covering negative family to the
zero and nonedge-pair tests for every AND gate. -/
theorem finite_tests_of_negative_family {n : ℕ} (G : SimpleGraph (Fin n))
    (C : Circuit) (hmono : Monotone2 C) (Neg : (Fin n → Bool) → Prop)
    (hex : ∃ z, Neg z)
    (hcover : ∀ u v : Fin n, ¬ G.Adj u v →
      ∃ z, Neg z ∧ ∀ i, pairInput u v i = true → z i = true)
    (hreject : ∀ j g, C.gates[j]? = some g → g.op = GateOp.and →
      ∀ z, Neg z → gateVal n C j z = false) :
    RejectsNonedgePairs G C := by
  intro j g hj hg
  constructor
  · obtain ⟨z, hz⟩ := hex
    cases hv : gateVal n C j (fun _ => false) with
    | false => rfl
    | true =>
      have htrue : gateVal n C j z = true :=
        Wire.val_mono C.gates hmono (fun _ => false) z
          (by intro i hi; contradiction) (n + j) hv
      rw [hreject j g hj hg z hz] at htrue
      contradiction
  · intro u v huv
    obtain ⟨z, hz, hle⟩ := hcover u v huv
    cases hv : gateVal n C j (pairInput u v) with
    | false => rfl
    | true =>
      have htrue : gateVal n C j z = true :=
        Wire.val_mono C.gates hmono (pairInput u v) z hle (n + j) hv
      rw [hreject j g hj hg z hz] at htrue
      contradiction

/-- Diagonal nonedge coverage gives output rejection on every singleton. -/
theorem singletons_false_of_negative_family {n : ℕ} (G : SimpleGraph (Fin n))
    (C : Circuit) (hmono : Monotone2 C) (Neg : (Fin n → Bool) → Prop)
    (hcover : ∀ u v : Fin n, ¬ G.Adj u v →
      ∃ z, Neg z ∧ ∀ i, pairInput u v i = true → z i = true)
    (hreject : ∀ z, Neg z → C.eval (List.ofFn z) = false) :
    ∀ u : Fin n, C.eval (List.ofFn (pairInput u u)) = false := by
  intro u
  obtain ⟨z, hz, hle⟩ := hcover u u (G.loopless.irrefl u)
  cases hv : C.eval (List.ofFn (pairInput u u)) with
  | false => rfl
  | true =>
    have htrue : C.eval (List.ofFn z) = true :=
      Wire.val_mono C.gates hmono (pairInput u u) z hle C.output hv
    rw [hreject z hz] at htrue
    contradiction

/-- For the order-three plane, a covering negative family and AND-gate
rejection reduce the existing 64-gate bound to finite positive/negative tests.
No circuit minimality or extra wire-order condition is needed. -/
theorem plane_bound_of_negative_family (C : Circuit) (hmono : Monotone2 C)
    (Neg : (Fin 26 → Bool) → Prop)
    (hcover : ∀ u v : Fin 26,
      ¬ PEqualNP.Outside.L_meta_4101_aux.Plane.G.Adj u v →
      ∃ z, Neg z ∧ ∀ i, pairInput u v i = true → z i = true)
    (haccept : ∀ u v : Fin 26, PEqualNP.Outside.L_meta_4101_aux.Plane.G.Adj u v →
      C.eval (List.ofFn (pairInput u v)) = true)
    (hreject : ∀ z, Neg z → C.eval (List.ofFn z) = false)
    (handreject : ∀ j g, C.gates[j]? = some g → g.op = GateOp.and →
      ∀ z, Neg z → gateVal 26 C j z = false) :
    64 ≤ C.size := by
  have hex : ∃ z, Neg z := by
    obtain ⟨z, hz, _⟩ := hcover 0 0
      (PEqualNP.Outside.L_meta_4101_aux.Plane.G.loopless.irrefl 0)
    exact ⟨z, hz⟩
  exact plane_bound_of_finite_tests C hmono
    (finite_tests_of_negative_family _ C hmono Neg hex hcover handreject)
    (singletons_false_of_negative_family _ C hmono Neg hcover hreject) haccept

end Pnp2343CleanCost
