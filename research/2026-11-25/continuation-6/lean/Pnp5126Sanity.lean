import PEqualNP.Defs

/-!
Four-variable scope check for L-meta-5126, model A proposed and independently
enumerated by the session's remote-status audit.  Variables a,b,c,d are 0,1,2,3.

The circuit computes a(c+d), has exactly two dirty AND gates, rejects every
singleton at both of them, is in TopForm, and has no dead gate.  Its second
dirty gate computes ac+ad+bc, which is not a product of two disjoint sums of
variables.  A two-gate competitor shows this six-gate circuit is NOT least.
Thus this is a scope counterexample after dropping leastness, not a
counterexample to L-meta-5126.  Every finite check uses `decide +kernel`.
-/

namespace Pnp5126Sanity

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

def G : SimpleGraph (Fin 4) := edgeGraph 4 [(0,2),(0,3)]

instance : DecidableRel G.Adj :=
  inferInstanceAs (DecidableRel (edgeGraph 4 [(0,2),(0,3)]).Adj)

def C : Circuit :=
  ⟨[⟨GateOp.or, [0,1]⟩,       -- wire 4: a+b
    ⟨GateOp.or, [2,3]⟩,       -- wire 5: c+d
    ⟨GateOp.and, [4,5]⟩,      -- wire 6: H=(a+b)(c+d)
    ⟨GateOp.or, [0,2]⟩,       -- wire 7: a+c
    ⟨GateOp.and, [6,7]⟩,      -- wire 8: J=H(a+c)=ac+ad+bc
    ⟨GateOp.and, [0,8]⟩], 9⟩ -- wire 9: aJ=a(c+d)

def competitor : Circuit :=
  ⟨[⟨GateOp.or, [2,3]⟩, ⟨GateOp.and, [0,4]⟩], 5⟩

theorem graph_bipartite :
    ∀ u v : Fin 4, G.Adj u v → decide (u = 0) ≠ decide (v = 0) := by
  decide +kernel

theorem graph_no_four_cycle : NoFourCycle G := by
  decide +kernel

theorem circuit_ao2 : IsAO2 4 C := by
  decide +kernel

theorem circuit_correct_pointwise :
    ∀ x : Fin 4 → Bool, circuitFun 4 C x = graphFun G ∅ x := by
  decide +kernel

theorem circuit_correct : circuitFun 4 C = graphFun G ∅ :=
  funext circuit_correct_pointwise

theorem circuit_top_form : TopForm G C := by
  decide +kernel

theorem circuit_junk : junk G C = {2,4} := by
  decide +kernel

theorem circuit_junk_count : (junk G C).card = 2 := by
  decide +kernel

theorem junk_unit_off :
    ∀ k ∈ junk G C, ∀ v : Fin 4,
      gateVal 4 C k (PEqualNP.SplitCount.unitInput v) = false := by
  decide +kernel

theorem all_gates_live :
    ∀ k < C.gates.length, PEqualNP.Core.InOutputCone 4 C k := by
  decide +kernel

theorem first_dirty_in_second : InCone 4 C 2 4 := by
  decide +kernel

theorem second_dirty_value :
    ∀ x : Fin 4 → Bool, gateVal 4 C 4 x =
      ((x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2)) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem second_dirty_not_rectangle :
    ¬ ∃ A B : Finset (Fin 4), Disjoint A B ∧
      ∀ x : Fin 4 → Bool, gateVal 4 C 4 x =
        (decide (∃ a ∈ A, x a = true) && decide (∃ b ∈ B, x b = true)) := by
  decide +kernel

theorem competitor_ao2 : IsAO2 4 competitor := by
  decide +kernel

theorem competitor_correct_pointwise :
    ∀ x : Fin 4 → Bool, circuitFun 4 competitor x = graphFun G ∅ x := by
  decide +kernel

theorem competitor_correct : circuitFun 4 competitor = graphFun G ∅ :=
  funext competitor_correct_pointwise

theorem circuit_size : C.size = 6 := by
  decide +kernel

theorem competitor_size : competitor.size = 2 := by
  decide +kernel

theorem circuit_not_least : ¬ IsLeastAO G C := by
  intro h
  have hle := h.2.2 competitor competitor_ao2 competitor_correct
  have hnot : ¬ C.size ≤ competitor.size := by decide +kernel
  exact hnot hle

end Pnp5126Sanity
