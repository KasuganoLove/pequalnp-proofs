import Pnp2343FreeOr

/-!
An explicit necessary shape for a counterexample to L-meta-2343. This combines
the sample-preserving minimal normalization and erasure lemmas with the
conditional clean-AND lower bound. It is not a proof that the shape is impossible.
-/

namespace Pnp2343CounterexampleShape

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.Pnp2343Pruning Pnp2343FreeOr

theorem small_normal_shape (C : Circuit) (s : List ℕ)
    (hs : s.length ≤ 2) (hm : Monotone2 C)
    (hr : ∀ i : Fin C.gates.length, ∀ w ∈ (C.gates.get i).inputs, w < 27 + i.val)
    (hfit : Fits (positive s) (negative s) C) (hsmall : C.size < 63) :
    ∃ D : Circuit, LeastSamples 27 (positive s) (negative s) D ∧
      PEqualNP.TopForm.IsAO2 27 D ∧ D.size ≤ C.size ∧
      ∃ r a b : ℕ, r < D.gates.length ∧ (gateAt D r).op = GateOp.and ∧
        (gateAt D r).inputs = [a,b] ∧ a ≠ b ∧
        ∃ Q11 Q10 Q01 : Quad,
          Q11 ≠ Q10 ∧ Q11 ≠ Q01 ∧ Q10 ≠ Q01 ∧
          (val D (negative s Q11) a = true ∧ val D (negative s Q11) b = true) ∧
          (val D (negative s Q10) a = true ∧ val D (negative s Q10) b = false) ∧
          (val D (negative s Q01) a = false ∧ val D (negative s Q01) b = true) := by
  obtain ⟨D,hmin,hAO,hsize,hbinary⟩ := free_or_normal_form C s hm hr hfit
  have hDsmall : D.size < 63 := lt_of_le_of_lt hsize hsmall
  obtain ⟨r,hrD,hop,Q11,hfire⟩ := small_has_firing_and D s hs hmin.1 hmin.2.2.1 hDsmall
  obtain ⟨a,b,hins,hab⟩ := hbinary r hrD
  have hv := (val_and (negative_length s Q11) hrD hop).1 hfire
  have ha11 : val D (negative s Q11) a = true := (hv a (by simp [hins])).2
  have hb11 : val D (negative s Q11) b = true := (hv b (by simp [hins])).2
  obtain ⟨⟨Q10,ha10,hb10⟩,⟨Q01,hb01,ha01⟩⟩ :=
    and_negative_incomparable 27 (positive s) (negative s)
      (positive_length s) (negative_length s) D hmin r a b hrD hop hins
  have hne1 : Q11 ≠ Q10 := by
    intro h
    rw [h,hb10] at hb11
    cases hb11
  have hne2 : Q11 ≠ Q01 := by
    intro h
    rw [h,ha01] at ha11
    cases ha11
  have hne3 : Q10 ≠ Q01 := by
    intro h
    rw [h,ha01] at ha10
    cases ha10
  exact ⟨D,hmin,hAO,hsize,r,a,b,hrD,hop,hins,hab,
    Q11,Q10,Q01,hne1,hne2,hne3,⟨ha11,hb11⟩,⟨ha10,hb10⟩,⟨ha01,hb01⟩⟩

end Pnp2343CounterexampleShape
