import PEqualNP.Outside.L_meta_4101
import PEqualNP.Outside.L_meta_4320
import PEqualNP.Outside.L_meta_1906
import PEqualNP.Outside.L_meta_1600

-- Research bridge for L-meta-1031, using already checked upstream results.
-- This is not an official submission file: its outside imports would need inlining.
-- The remaining existence of a minimum circuit passing the finite tests is explicit.
-- Attribution: L4101.CleanCount supplies the cover budget, L4320 the clean builder,
-- L1906 the ownership normalization, and L1600 the star conclusion.

namespace Pnp1031OwnershipBridge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

def EdgeCorrect {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) : Prop :=
  ∀ x : Fin n → Bool, C.eval (List.ofFn x) =
    decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)

-- Repeated endpoints include every singleton input; only nonedges need testing.
def RejectsNonedgePairs {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) : Prop :=
  ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → g.op = GateOp.and →
    gateVal n C j (fun _ => false) = false ∧
    ∀ u v : Fin n, ¬ G.Adj u v → gateVal n C j (pairInput u v) = false

def AllAndSound {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) : Prop :=
  ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → g.op = GateOp.and →
    ∀ x : Fin n → Bool, gateVal n C j x = true →
      ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true

def NonemptyStarOwnership {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) : Prop :=
  ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
    ∃ c : Fin n,
      (∃ u v : Fin n, G.Adj u v ∧ Owns n C j u v) ∧
      ∀ u v : Fin n, G.Adj u v → Owns n C j u v → u = c ∨ v = c

lemma correct_eq_graph {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (h : EdgeCorrect G C) : circuitFun n C = graphFun G ∅ := by
  funext x
  change C.eval (List.ofFn x) = graphFun G ∅ x
  rw [h x]
  simp [graphFun]

lemma finite_tests_sound {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit}
    (h : RejectsNonedgePairs G C) (j : ℕ) (g : Gate)
    (hg : C.gates[j]? = some g) (hand : g.op = GateOp.and)
    (x : Fin n → Bool)
    (hx : x = (fun _ => false) ∨ ∃ u v : Fin n, x = pairInput u v)
    (hv : gateVal n C j x = true) :
    ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true := by
  classical
  rcases hx with rfl | ⟨u, v, rfl⟩
  · rw [(h j g hg hand).1] at hv
    contradiction
  · by_cases huv : G.Adj u v
    · exact ⟨u, v, huv, by simp [pairInput], by simp [pairInput]⟩
    · rw [(h j g hg hand).2 u v huv] at hv
      contradiction

-- This count-and-rebuild proof gives a no-larger globally sound replacement.
-- The separate finite-test equivalence also establishes soundness of the original gates.
theorem clean_replacement {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hc4 : ∀ a b c d : Fin n, G.Adj a b → G.Adj b c → G.Adj c d →
      G.Adj d a → a = c ∨ b = d)
    (C : Circuit) (hmono : Monotone2 C) (hcorrect : EdgeCorrect G C)
    (htests : RejectsNonedgePairs G C) :
    ∃ D : Circuit, Monotone2 D ∧ D.size ≤ C.size ∧ EdgeCorrect G D ∧
      AllAndSound G D := by
  have hfour : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a) := by
    intro a b c d hac hbd ⟨hab, hbc, hcd, hda⟩
    exact (hc4 a b c d hab hbc hcd hda).elim hac hbd
  have hsmall : ∀ (i : Fin C.gates.length) (x : Fin n → Bool),
      (x = (fun _ => false) ∨ (∃ u : Fin n, x = fun z => decide (z = u)) ∨
        (∃ u v : Fin n, x = fun z => decide (z = u ∨ z = v))) →
      (C.gates.get i).op = GateOp.and →
      ((⟨C.gates, 0⟩ : Circuit).wires (List.ofFn x)).getD (n + i.val) false = true →
      ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true := by
    intro i x hx hand hv
    apply finite_tests_sound htests i.val C.gates[i.val]
      (List.getElem?_eq_getElem i.isLt) hand x _ hv
    rcases hx with h | ⟨u, h⟩ | ⟨u, v, h⟩
    · exact Or.inl h
    · refine Or.inr ⟨u, u, ?_⟩
      rw [h]
      funext z
      simp [pairInput]
    · exact Or.inr ⟨u, v, h⟩
  obtain ⟨T, hcover, hbudget⟩ :=
    PEqualNP.Outside.L_meta_4101_aux.CleanCount.pairCleanBound n G hfour
      C.gates C.output hmono hcorrect hsmall
  obtain ⟨D, hD, hDcorrect, hDsize, hDsound⟩ :=
    PEqualNP.Outside.L_meta_4320 n G T hcover
  refine ⟨D, hD, ?_, hDcorrect, hDsound⟩
  change G.edgeFinset.card + T.card ≤ C.size + 1 at hbudget
  omega

theorem minimum_star_of_finite_tests {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj]
    (htri : ∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (hc4 : ∀ a b c d : Fin n, G.Adj a b → G.Adj b c → G.Adj c d →
      G.Adj d a → a = c ∨ b = d)
    (C : Circuit) (hmin : IsMinimalMonoCircuit n C)
    (hcorrect : EdgeCorrect G C) (htests : RejectsNonedgePairs G C) :
    ∃ D : Circuit, IsMinimalMonoCircuit n D ∧ EdgeCorrect G D ∧
      D.size = C.size ∧ AllAndSound G D ∧ NonemptyStarOwnership G D := by
  obtain ⟨D0, hD0, hD0size, hD0correct, hD0sound⟩ :=
    clean_replacement G hc4 C hmin.1 hcorrect htests
  have hD0min : ∀ E : Circuit, Monotone2 E → EdgeCorrect G E → D0.size ≤ E.size := by
    intro E hE hEc
    apply hD0size.trans
    exact hmin.2 E hE ((correct_eq_graph hEc).trans (correct_eq_graph hcorrect).symm)
  obtain ⟨D, hD, hDsize, hDcorrect, hDall⟩ :=
    PEqualNP.Outside.L_meta_1906 n G D0 htri hc4 hD0 hD0correct hD0min hD0sound
  have hsize : D.size = C.size := le_antisymm (hDsize.trans hD0size)
    (hmin.2 D hD ((correct_eq_graph hDcorrect).trans (correct_eq_graph hcorrect).symm))
  have hDmin : IsMinimalMonoCircuit n D := by
    refine ⟨hD, ?_⟩
    intro E hE hEc
    rw [hsize]
    apply hmin.2 E hE
    exact hEc.trans ((correct_eq_graph hDcorrect).trans (correct_eq_graph hcorrect).symm)
  refine ⟨D, hDmin, hDcorrect, hsize, ?_, ?_⟩
  · intro j g hg hand
    exact (hDall j g hg hand).1
  · intro j hj hand
    have hgat : gateAt D j = D.gates[j] := List.getD_eq_getElem _ _ hj
    have hop : D.gates[j].op = GateOp.and := by rwa [hgat] at hand
    obtain ⟨hclean, howned⟩ := hDall j D.gates[j] (List.getElem?_eq_getElem hj) hop
    have hbelow : ∀ x : Fin n → Bool, gateVal n D j x = true → graphFun G ∅ x = true := by
      intro x hx
      simpa [graphFun] using hclean x hx
    have hfour : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
        ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a) := by
      intro a b c d hac hbd ⟨hab, hbc, hcd, hda⟩
      exact (hc4 a b c d hab hbc hcd hda).elim hac hbd
    rcases PEqualNP.Outside.L_meta_1600 n G hfour D hD j hj hand hbelow with hnone | ⟨c, hc⟩
    · obtain ⟨u, v, hadj, hown⟩ := howned
      exact False.elim (hnone u v hadj hown)
    · exact ⟨c, howned, hc⟩

-- The missing assertion for the general task is the existence of C passing these tests.
-- This corollary keeps that assertion as an explicit premise.
theorem existence_bridge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (htri : ∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (hc4 : ∀ a b c d : Fin n, G.Adj a b → G.Adj b c → G.Adj c d →
      G.Adj d a → a = c ∨ b = d)
    (h : ∃ C : Circuit, IsMinimalMonoCircuit n C ∧ EdgeCorrect G C ∧
      RejectsNonedgePairs G C) :
    ∃ D : Circuit, IsMinimalMonoCircuit n D ∧ EdgeCorrect G D ∧
      AllAndSound G D ∧ NonemptyStarOwnership G D := by
  obtain ⟨C, hmin, hc, ht⟩ := h
  obtain ⟨D, hm, he, _, hs, ho⟩ := minimum_star_of_finite_tests G htri hc4 C hmin hc ht
  exact ⟨D, hm, he, hs, ho⟩

end Pnp1031OwnershipBridge
