import Pnp2343Pruning

namespace PEqualNP.Outside.Pnp2343Pruning

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

/-- The finite-sample sandwich also allows the false wire beyond the end. -/
lemma bypass_samples_false_valid {α β : Type} (n : ℕ)
    (positive : α → List Bool) (negative : β → List Bool)
    (hpLen : ∀ p, (positive p).length = n) (hnLen : ∀ q, (negative q).length = n)
    (C : Circuit) (hM : Monotone2 C) (hF : Fits positive negative C)
    (r i : ℕ) (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
    (hp : ∀ p, val C (positive p) (n + r) = true → val C (positive p) i = true)
    (hn : ∀ q, val C (negative q) i = true → val C (negative q) (n + r) = true) :
    Fits positive negative (bypass n C r i) := by
  constructor
  · intro p
    exact bypass_eval_rel (R := fun a b => a = true → b = true) (fun _ => id) opMono_imp
      (hpLen p) (mono_ops hM) hr hi (hp p) (hF.1 p)
  · intro q
    cases he : (bypass n C r i).eval (negative q) with
    | false => rfl
    | true =>
      have hc := bypass_eval_rel (R := fun a b => b = true → a = true) (fun _ => id) opMono_reverse
        (hnLen q) (mono_ops hM) hr hi (hn q) he
      rw [hF.2 q] at hc
      cases hc

/-- Every gate of a minimum sample separator fires on a positive sample.
Deleting an unproductive gate through the false wire need not preserve ReadsBack;
constant propagation then restores binary, earlier-wire form without adding gates. -/
theorem least_gate_positive {α β : Type} (n : ℕ)
    (positive : α → List Bool) (negative : β → List Bool)
    (hpLen : ∀ p, (positive p).length = n) (hnLen : ∀ q, (negative q).length = n)
    (p0 : α) (q0 : β) (C : Circuit) (hmin : LeastSamples n positive negative C)
    (r : ℕ) (hr : r < C.gates.length) :
    ∃ p, val C (positive p) (n + r) = true := by
  by_contra hnone
  let i := n + C.gates.length
  let B := bypass n C r i
  have hBM : Monotone2 B := bypass_mono hmin.1
  have hBF : Fits positive negative B := by
    apply bypass_samples_false_valid n positive negative hpLen hnLen C hmin.1 hmin.2.2.1
      r i hr (Or.inr (by rfl))
    · intro p hp
      exact False.elim (hnone ⟨p,hp⟩)
    · intro q hq
      rw [val_ge (hnLen q) (show n + C.gates.length ≤ i from le_refl _)] at hq
      cases hq
  obtain ⟨D,hD,hDB,hsize⟩ := Normalize.normalize_nonconstant n B hBM (circuitFun n B) rfl
    (sample_nonconstant n positive negative hpLen hnLen p0 q0 B hBF)
  have hDM : Monotone2 D := by
    intro g hg
    exact ⟨hD.1 g hg,(hD.2.2 g hg).le⟩
  have hDF : Fits positive negative D := by
    constructor
    · intro p
      rw [eval_of_funEq hDB _ (hpLen p)]
      exact hBF.1 p
    · intro q
      rw [eval_of_funEq hDB _ (hnLen q)]
      exact hBF.2 q
  have hleast := hmin.2.2.2 D hDM hD.2.1 hDF
  have hBS : B.size = C.size - 1 := bypass_length n C r i
  have hpos : 0 < C.size := by change 0 < C.gates.length; omega
  omega

/-- Two raw inputs of an AND that survives in a minimum separator must occur
simultaneously in a positive sample. This holds even for deeply nested gates. -/
theorem least_and_raw_cooccurs {α β : Type} (n : ℕ)
    (positive : α → List Bool) (negative : β → List Bool)
    (hpLen : ∀ p, (positive p).length = n) (hnLen : ∀ q, (negative q).length = n)
    (p0 : α) (q0 : β) (C : Circuit) (hmin : LeastSamples n positive negative C)
    (r a b : ℕ) (hr : r < C.gates.length) (ha : a < n) (hb : b < n)
    (hop : (gateAt C r).op = GateOp.and) (hins : (gateAt C r).inputs = [a,b]) :
    ∃ p, (positive p).getD a false = true ∧ (positive p).getD b false = true := by
  obtain ⟨p,hp⟩ := least_gate_positive n positive negative hpLen hnLen p0 q0 C hmin r hr
  have hv := (val_and (hpLen p) hr hop).mp hp
  refine ⟨p,?_,?_⟩
  · have h := (hv a (by simp [hins])).2
    rwa [val_input (hpLen p) ha] at h
  · have h := (hv b (by simp [hins])).2
    rwa [val_input (hpLen p) hb] at h

end PEqualNP.Outside.Pnp2343Pruning
