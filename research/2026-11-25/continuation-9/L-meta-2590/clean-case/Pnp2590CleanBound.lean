import Pnp2590Graph
import Pnp4201CleanOrCount
import Pnp4201CleanBudgetTopForm
import Pnp4201CleanNormalize

/-!
Clean-circuit Petersen lower bound for research on held L-meta-2590.
The generic cover construction is adapted from L_meta_2235.s2231 (Apache-2.0),
using the newly proved clean-TopForm edge witnesses instead of a read-once
restriction. All normalization here preserves an explicit initial cleanliness
premise. The unrestricted L-meta-2590 statement is not asserted by this file.
-/

namespace PEqualNP.Outside.Pnp2590CleanBound

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_2235
open PEqualNP.Outside.Pnp4201CleanOrCount PEqualNP.Outside.Pnp4201OrBudget
open PEqualNP.Outside.Pnp4201CleanBudgetTopForm PEqualNP.Outside.Pnp4201CleanNormalize
open PEqualNP.Outside.Pnp2590Graph

def andCount (C : Circuit) : ℕ := C.gates.countP
  (fun g => GateOp.casesOn g.op true false false (fun _ => false) false)

open Classical in
lemma and_indices_eq_count (C : Circuit) :
    ((Finset.range C.gates.length).filter fun i => (gateAt C i).op = GateOp.and).card =
      andCount C := by
  classical
  have hmap : (List.range C.gates.length).map (gateAt C) = C.gates := by
    apply List.ext_getElem
    · simp
    · intro i hi hi'
      rw [List.getElem_map, List.getElem_range]
      exact s2231_gateAt_eq C i hi'
  have hc : ((Finset.range C.gates.length).filter fun i => (gateAt C i).op = GateOp.and).card =
      ((List.range C.gates.length).map (gateAt C)).countP (fun g => decide (g.op = GateOp.and)) := by
    simpa only [List.countP_map, Function.comp_def, List.toFinset_range] using
      (List.Nodup.card_eq_countP (P := fun i => (gateAt C i).op = GateOp.and)
        (List.nodup_range (n := C.gates.length)))
  rw [hmap] at hc
  rw [hc]
  unfold andCount
  congr 1
  funext g
  cases g.op <;> simp

lemma and_or_count_le_size (C : Circuit) : andCount C + orCount C ≤ C.size := by
  rcases C with ⟨gs, out⟩
  change gs.countP (fun g => GateOp.casesOn g.op true false false (fun _ => false) false) +
    gs.countP (fun g => isOr g.op) ≤ gs.length
  induction gs with
  | nil => simp
  | cons g gs ih =>
    simp only [List.countP_cons, List.length_cons]
    cases g.op <;> simp_all [isOr] <;> omega

/-- A clean TopForm C4-free circuit yields a vertex cover with at most one
vertex per actual AND gate, without a read-once assumption. -/
theorem clean_top_cover (n : ℕ) (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (h4 : NoFourCycle H)
    (hf : circuitFun n C = graphFun H ∅) (htop : TopForm H C)
    (hclean : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → BelowF H C j) :
    ∃ T : Finset (Fin n), T.card ≤ andCount C ∧
      ∀ e ∈ (Finset.univ.filter (fun e : Fin n × Fin n => e.1 < e.2 ∧ H.Adj e.1 e.2)),
        e.1 ∈ T ∨ e.2 ∈ T := by
  classical
  have h1 : ∀ a : Fin n, circuitFun n C (fun k => decide (k = a)) = false := by
    intro a
    rw [hf]
    exact graph_unit_false n H a
  have h2 : ∀ a b : Fin n, a ≠ b → ¬ H.Adj a b →
      circuitFun n C (fun k => decide (k = a ∨ k = b)) = false := by
    intro a b _ hab
    rw [hf]
    exact graph_pair_false n H a b hab
  let F : Finset ℕ := (Finset.range C.gates.length).filter fun j => (gateAt C j).op = GateOp.and
  refine ⟨F.biUnion (s2231_cen n C), ?_, ?_⟩
  · calc
      (F.biUnion (s2231_cen n C)).card ≤ F.sum (fun i => (s2231_cen n C i).card) :=
        Finset.card_biUnion_le
      _ ≤ F.sum (fun _ => 1) := Finset.sum_le_sum (fun i _ => s2231_cen_card n C i)
      _ = F.card := by simp
      _ = andCount C := and_indices_eq_count C
  · intro e he
    have heG := (Finset.mem_filter.mp he).2.2
    have htrue : circuitFun n C (pairInput e.1 e.2) = true := by
      rw [hf]
      apply Bool.or_eq_true_iff.mpr
      right
      exact decide_eq_true ⟨e.1, e.2, heG, by simp [pairInput], by simp [pairInput]⟩
    obtain ⟨i, hi, hop, hreach, hs⟩ :=
      clean_top_edge_witness n H C hAO h4 h1 h2 htop hclean e.1 e.2 htrue
    have hiF : i ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, hop⟩
    obtain ⟨_, _, hcard⟩ := s2231_part1 n H C h4 hAO h1 h2 i hi hop hreach
    by_cases c0 : (side (n := n) C i 0).card ≤ 1
    · have hc : s2231_cen n C i = side (n := n) C i 0 := by
        unfold s2231_cen
        rw [ite_eq_left c0]
      rcases hs with ⟨h, _⟩ | ⟨h, _⟩
      · exact Or.inl (Finset.mem_biUnion.mpr ⟨i, hiF, by rwa [hc]⟩)
      · exact Or.inr (Finset.mem_biUnion.mpr ⟨i, hiF, by rwa [hc]⟩)
    · have c1 : (side (n := n) C i 1).card ≤ 1 := hcard.resolve_left c0
      have hc : s2231_cen n C i = side (n := n) C i 1 := by
        unfold s2231_cen
        rw [ite_eq_right c0, ite_eq_left c1]
      rcases hs with ⟨_, h⟩ | ⟨_, h⟩
      · exact Or.inr (Finset.mem_biUnion.mpr ⟨i, hiF, by rwa [hc]⟩)
      · exact Or.inl (Finset.mem_biUnion.mpr ⟨i, hiF, by rwa [hc]⟩)

theorem top_and_ge_six (C : Circuit) (hAO : IsAO2 10 C)
    (hf : circuitFun 10 C = graphFun G ∅) (htop : TopForm G C)
    (hclean : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → BelowF G C j) :
    6 ≤ andCount C := by
  obtain ⟨T, hcard, hcover⟩ := clean_top_cover 10 G C hAO noFourCycle hf htop hclean
  exact (cover_ge_six T hcover).trans hcard

theorem top_or_ge_fourteen (C : Circuit) (hAO : IsAO2 10 C)
    (hf : circuitFun 10 C = graphFun G ∅) (htop : TopForm G C)
    (hclean : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → BelowF G C j) :
    14 ≤ orCount C := by
  have h := clean_top_or_bound 10 G C hAO noFourCycle hf htop hclean
  change orderedEdges.card ≤ _ at h
  rw [edge_count] at h
  rw [orCount_eq_public]
  omega

theorem top_size_ge_twenty (C : Circuit) (hAO : IsAO2 10 C)
    (hf : circuitFun 10 C = graphFun G ∅) (htop : TopForm G C)
    (hclean : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → BelowF G C j) :
    20 ≤ C.size := by
  have ha := top_and_ge_six C hAO hf htop hclean
  have ho := top_or_ge_fourteen C hAO hf htop hclean
  have hs := and_or_count_le_size C
  omega

theorem clean_monotone_normal_form (C : Circuit) (hM : Monotone2 C)
    (hf : circuitFun 10 C = target)
    (hclean : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → BelowF G C j) :
    ∃ D : Circuit, IsAO2 10 D ∧ circuitFun 10 D = graphFun G ∅ ∧
      D.size ≤ C.size ∧ orCount D ≤ orCount C ∧
      (∀ j < D.gates.length, (gateAt D j).op = GateOp.and → BelowF G D j) ∧ TopForm G D := by
  have hfg : circuitFun 10 C = graphFun G ∅ := hf.trans target_eq_graphFun
  have hnc : ∃ x y, graphFun G ∅ x ≠ graphFun G ∅ y := by
    simpa only [target_eq_graphFun] using target_nonconstant
  have hC : Clean 10 (graphFun G ∅) C := (clean_iff_all_and_below 10 G C).mpr hclean
  obtain ⟨A, hAA, hAF, hAS, hAB, hAC⟩ :=
    normalize_nonconstant_clean_budgets 10 C hM (graphFun G ∅) hfg hnc hC
  obtain ⟨D, hDA, hDF, hDS, hDO, hDC, hDT⟩ :=
    exists_clean_top_form_with_or_budget 10 G nonempty_edges A hAA hAF hAC
  have hAO : orCount A ≤ orCount C := hAB isOr
  exact ⟨D, hDA, hDF, hDS.trans hAS, hDO.trans hAO,
    (clean_iff_all_and_below 10 G D).mp hDC, hDT⟩

/-- Full clean Monotone2 case, including empty/unary gates and malformed reads. -/
theorem clean_size_ge_twenty (C : Circuit) (hM : Monotone2 C)
    (hf : circuitFun 10 C = target)
    (hclean : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → BelowF G C j) :
    20 ≤ C.size := by
  obtain ⟨D, hDA, hDF, hDS, _, hDC, hDT⟩ := clean_monotone_normal_form C hM hf hclean
  exact (top_size_ge_twenty D hDA hDF hDT hDC).trans hDS

theorem clean_or_ge_fourteen (C : Circuit) (hM : Monotone2 C)
    (hf : circuitFun 10 C = target)
    (hclean : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → BelowF G C j) :
    14 ≤ orCount C := by
  obtain ⟨D, hDA, hDF, _, hDO, hDC, hDT⟩ := clean_monotone_normal_form C hM hf hclean
  exact (top_or_ge_fourteen D hDA hDF hDT hDC).trans hDO

/-- Any counterexample to held L2590 must contain an AND true on a target-negative input. -/
theorem small_correct_has_dirty_and (C : Circuit) (hM : Monotone2 C) (hs : C.size ≤ 19)
    (hf : circuitFun 10 C = target) :
    ∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧
      ∃ x : Fin 10 → Bool, gateVal 10 C j x = true ∧ target x = false := by
  classical
  by_contra hn
  have hc : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → BelowF G C j := by
    intro j hj hop x hx
    cases htx : target x with
    | false => exact False.elim (hn ⟨j,hj,hop,x,hx,htx⟩)
    | true => rw [← target_eq_graphFun]; exact htx
  have h20 := clean_size_ge_twenty C hM hf hc
  omega

end PEqualNP.Outside.Pnp2590CleanBound
