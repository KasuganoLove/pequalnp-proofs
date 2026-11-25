import Pnp4201Graph
import Pnp4201CleanOrCount
import Pnp4201CleanBudgetTopForm
import Pnp4201CleanNormalize

/-!
Composition for the exact clean-circuit child L-meta-8323 of the L-meta-4201 cut.
All normalizations here preserve the assumed AND cleanliness and never increase
OR count. This proves a conditional clean-circuit lower bound, not an existence
claim for a clean replacement of an arbitrary circuit.
The exact final statement is copied from the public L-meta-8323 record.
-/

namespace PEqualNP.Outside.Pnp4201CleanCase

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.Outside.Pnp4201Graph PEqualNP.Outside.Pnp4201OrBudget
open PEqualNP.Outside.Pnp4201CleanBudgetTopForm PEqualNP.Outside.Pnp4201CleanOrCount
open PEqualNP.Outside.Pnp4201CleanNormalize

lemma clean_ao2_lower_bound (C : Circuit) (hAO : IsAO2 42 C)
    (hf : circuitFun 42 C = graphFun pg4 ∅)
    (hclean : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → BelowF pg4 C j) :
    104 ≤ C.gates.countP
      (fun g => GateOp.casesOn g.op false true false (fun _ => false) false) := by
  have hG : pg4.edgeFinset.Nonempty := Finset.card_pos.mp (by rw [edgeFinset_card]; decide)
  obtain ⟨D, hDA, hDF, _, hDO, hDC, hDT⟩ :=
    exists_clean_top_form_with_or_budget 42 pg4 hG C hAO hf
      ((clean_iff_all_and_below 42 pg4 C).mpr hclean)
  have hb := clean_top_or_bound 42 pg4 D hDA noFourCycle hDF hDT
    ((clean_iff_all_and_below 42 pg4 D).mp hDC)
  change orderedEdges.card ≤ _ at hb
  rw [orderedEdges_card] at hb
  rw [orCount_eq_public D, orCount_eq_public C] at hDO
  omega

lemma clean_monotone_lower_bound (C : Circuit) (hM : Monotone2 C)
    (hf : circuitFun 42 C = graphFun pg4 ∅)
    (hclean : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → BelowF pg4 C j) :
    104 ≤ C.gates.countP
      (fun g => GateOp.casesOn g.op false true false (fun _ => false) false) := by
  have hC : Clean 42 (graphFun pg4 ∅) C := (clean_iff_all_and_below 42 pg4 C).mpr hclean
  obtain ⟨D, hDA, hDF, _, hDB, hDC⟩ :=
    normalize_nonconstant_clean_budgets 42 C hM (graphFun pg4 ∅) hf nonconstant hC
  have hDC' : Clean 42 (graphFun pg4 ∅) D := hDC
  have hb := clean_ao2_lower_bound D hDA hDF ((clean_iff_all_and_below 42 pg4 D).mp hDC')
  have hDO : orCount D ≤ orCount C := hDB isOr
  rw [orCount_eq_public D, orCount_eq_public C] at hDO
  exact hb.trans hDO

theorem exact_8323 : have x1 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x1 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x2 : Fin (42 : ℕ) → Bool), x1.eval (List.ofFn x2) = Bool.true ↔ ∃ (x3 : Fin (42 : ℕ)) (x4 : Fin (42 : ℕ)), (↑x3 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x4 ∧ (↑x4 + (21 : ℕ) - ↑x3) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x2 x3 = Bool.true ∧ x2 x4 = Bool.true; have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x3]? = Option.some x4 → x4.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x7 : Fin (42 : ℕ) → Bool), (x2.wires (List.ofFn x7)).getD ((42 : ℕ) + x3) Bool.false = Bool.true → x2.eval (List.ofFn x7) = Bool.true; have x3 : PEqualNP.CircuitLowerBounds.Circuit → ℕ := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => List.countP (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.casesOn x4.op Bool.false Bool.true Bool.false (fun (x5 : ℕ) => Bool.false) Bool.false) x3.gates; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → x1 x4 → x2 x4 → (104 : ℕ) ≤ x3 x4 := by
  dsimp only
  intro C hM hF hSafe
  have hf : circuitFun 42 C = graphFun pg4 ∅ := (computes_iff C).mp hF
  apply clean_monotone_lower_bound C hM hf
  intro j hj hop x hx
  have hg : C.gates[j]? = some (gateAt C j) := by
    rw [PEqualNP.Outside.L_meta_2235.s2231_gateAt_eq C j hj]
    simp [hj]
  have hout := hSafe j (gateAt C j) hg hop x hx
  change circuitFun 42 C x = true at hout
  rwa [hf] at hout

end PEqualNP.Outside.Pnp4201CleanCase
