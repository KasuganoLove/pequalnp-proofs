import Mathlib.Data.Finset.Card
import PEqualNP.Defs

namespace Pnp2391Wmax

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

/-! A structural restriction on safe raw-input partners of a gate.  The
monotonicity premise is explicit; no local soundness is inferred from the
circuit's output correctness. -/

-- The elementary pair-input calculation follows the checked L_meta_1876 proof.
theorem graphFun_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u v : Fin n) : graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    simp only [pairInput, decide_eq_true_eq] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.irrefl hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.irrefl hab).elim
  · intro h
    exact ⟨u, v, h, by simp [pairInput], by simp [pairInput]⟩

theorem wmax_adj_singleton {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (j : ℕ)
    (mono : ∀ x y : Fin n → Bool, (∀ i, x i = true → y i = true) →
      gateVal n C j x = true → gateVal n C j y = true)
    (p : Fin n) (hp : gateVal n C j (fun i => decide (i = p)) = true)
    (w : Fin n) (hw : w ∈ wmax G C j) : G.Adj p w := by
  have hpair : gateVal n C j (pairInput p w) = true := by
    apply mono _ _ _ hp
    intro i hi
    have : i = p := of_decide_eq_true hi
    subst i
    simp [pairInput]
  have hs := (Finset.mem_filter.mp hw).2
  exact (graphFun_pair G p w).mp (hs (pairInput p w) hpair (by simp [pairInput]))

/-- A gate true on two distinct singleton inputs has at most one safe
raw-input AND partner in a graph with no four-cycle. -/
theorem wmax_card_le_one {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (noFour : NoFourCycle G) (C : Circuit) (j : ℕ)
    (mono : ∀ x y : Fin n → Bool, (∀ i, x i = true → y i = true) →
      gateVal n C j x = true → gateVal n C j y = true)
    (p q : Fin n) (distinct : p ≠ q)
    (hp : gateVal n C j (fun i => decide (i = p)) = true)
    (hq : gateVal n C j (fun i => decide (i = q)) = true) :
    (wmax G C j).card ≤ 1 := by
  have sub : wmax G C j ⊆ Finset.univ.filter (fun w => G.Adj p w ∧ G.Adj q w) := by
    intro w hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      wmax_adj_singleton G C j mono p hp w hw,
      wmax_adj_singleton G C j mono q hq w hw⟩
  exact (Finset.card_le_card sub).trans (noFour p q distinct)

end Pnp2391Wmax
