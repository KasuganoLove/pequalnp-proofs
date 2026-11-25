import PEqualNP.Outside.L_meta_2235
import PEqualNP.Outside.L_meta_1501

/-!
Research for L-meta-4201 / conditional clean-circuit child L-meta-8323.
The counting construction is adapted from upstream L_meta_2235.core (Apache-2.0),
which combines L_meta_2231, L_meta_2233 and L_meta_2234. Its final count is sharpened
here to count only OR gates. No total-size minimality is assumed.
Wire/cone semantics are reused from upstream L_meta_1501 (Apache-2.0); none of
its least-circuit conclusions is used. This file does not assert that arbitrary
correct circuits admit a clean replacement.
-/

namespace PEqualNP.Outside.Pnp4201CleanOrCount

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.CleanedNonEdge PEqualNP.TopForm
open PEqualNP.Outside.L_meta_2235

lemma disjoint_or_count (C : Circuit) (A B : Set ℕ)
    (hA : A ⊆ {i | i < C.gates.length ∧ (gateAt C i).op = GateOp.or})
    (hB : B ⊆ {i | i < C.gates.length ∧ (gateAt C i).op = GateOp.or})
    (hd : ∀ i ∈ A, i ∉ B) :
    A.ncard + B.ncard ≤ Set.ncard {i | i < C.gates.length ∧ (gateAt C i).op = GateOp.or} := by
  have hfin : Set.Finite {i | i < C.gates.length ∧ (gateAt C i).op = GateOp.or} :=
    (Set.finite_lt_nat C.gates.length).subset (fun _ hi => hi.1)
  have hdis : Disjoint A B := Set.disjoint_left.mpr hd
  rw [← Set.ncard_union_eq hdis (hfin.subset hA) (hfin.subset hB)]
  exact Set.ncard_le_ncard (Set.union_subset hA hB) hfin

theorem or_count_core (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (E : Finset (Fin n × Fin n))
    (hlt : ∀ e ∈ E, e.1 < e.2)
    (h30 : ∀ e ∈ E, ∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧
      OrReaches n C C.output j ∧
      ((e.1 ∈ side (n := n) C j 0 ∧ e.2 ∈ side (n := n) C j 1) ∨
        (e.2 ∈ side (n := n) C j 0 ∧ e.1 ∈ side (n := n) C j 1)))
    (h31a : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → OrReaches n C C.output j →
      (∀ w : Fin n, w ∈ side (n := n) C j 0 → w ∉ side (n := n) C j 1) ∧
      (∀ u : Fin n, u ∈ side (n := n) C j 0 → ∀ v : Fin n, v ∈ side (n := n) C j 1 → G.Adj u v) ∧
      ((side (n := n) C j 0).card ≤ 1 ∨ (side (n := n) C j 1).card ≤ 1))
    (h33 : ∀ F : Finset ℕ, (∀ j ∈ F, j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧
        OrReaches n C C.output j) →
      F.card ≤ Set.ncard {i : ℕ | i < C.gates.length ∧ (gateAt C i).op = GateOp.or ∧
        OrReaches n C C.output i} + 1)
    (h34 : ∀ (F : Finset ℕ) (ctr : ℕ → Fin n) (lf : ℕ → ℕ),
      (∀ j ∈ F, ∀ b : Fin n, b ∈ orIn n C (lf j) → G.Adj (ctr j) b) →
      (∀ i < C.gates.length, (gateAt C i).op = GateOp.or → 2 ≤ (orIn n C (n + i)).card →
        (∃ j1 ∈ F, OrReaches n C (lf j1) i) → ¬ OrReaches n C C.output i) ∧
      ∑ c : Fin n, (Finset.univ.filter (fun b2 : Fin n =>
        ∃ j2 ∈ F, ctr j2 = c ∧ b2 ∈ orIn n C (lf j2))).card ≤
        Set.ncard {i2 : ℕ | i2 < C.gates.length ∧ (gateAt C i2).op = GateOp.or ∧
          2 ≤ (orIn n C (n + i2)).card ∧ ∃ j3 ∈ F, OrReaches n C (lf j3) i2} + F.card) :
    E.card ≤ Set.ncard {i : ℕ | i < C.gates.length ∧ (gateAt C i).op = GateOp.or} + 1 := by
  classical
  by_cases hE : E = ∅
  · subst hE
    simp
  obtain ⟨e0, he0⟩ := Finset.nonempty_iff_ne_empty.mpr hE
  obtain ⟨F, hF⟩ : ∃ F : Finset ℕ, ∀ j, j ∈ F ↔ (j < C.gates.length ∧
      (gateAt C j).op = GateOp.and ∧ OrReaches n C C.output j ∧
      (side (n := n) C j 0).Nonempty ∧ (side (n := n) C j 1).Nonempty) :=
    ⟨(Finset.range C.gates.length).filter (fun j => (gateAt C j).op = GateOp.and ∧
      OrReaches n C C.output j ∧
      (side (n := n) C j 0).Nonempty ∧ (side (n := n) C j 1).Nonempty),
      fun j => by rw [Finset.mem_filter, Finset.mem_range]⟩
  have hper : ∀ j : ℕ, ∃ (c : Fin n) (l : ℕ), j ∈ F →
      (∀ b : Fin n, b ∈ orIn n C l → G.Adj c b) ∧
      (∀ u : Fin n, u ∈ side (n := n) C j 0 → ∀ v : Fin n, v ∈ side (n := n) C j 1 →
        (c = u ∧ v ∈ orIn n C l) ∨ (c = v ∧ u ∈ orIn n C l)) := by
    intro j
    by_cases hj : j ∈ F
    · obtain ⟨hjl, hand, hor, hn0, hn1⟩ := (hF j).mp hj
      obtain ⟨hdis, hadj, hcard⟩ := h31a j hjl hand hor
      rcases hcard with hc | hc
      · obtain ⟨c, hc0⟩ := hn0
        refine ⟨c, opnd C j 1, fun _ => ⟨?_, ?_⟩⟩
        · intro b hb
          exact hadj c hc0 b hb
        · intro u hu v hv
          exact Or.inl ⟨Finset.card_le_one.mp hc c hc0 u hu, hv⟩
      · obtain ⟨c, hc1⟩ := hn1
        refine ⟨c, opnd C j 0, fun _ => ⟨?_, ?_⟩⟩
        · intro b hb
          exact (hadj b hb c hc1).symm
        · intro u hu v hv
          exact Or.inr ⟨Finset.card_le_one.mp hc c hc1 v hv, hu⟩
    · exact ⟨e0.1, 0, fun h => absurd h hj⟩
  choose ctr lf hcl using hper
  have hw : ∀ e ∈ E, ∃ i ∈ F, i < C.gates.length ∧
      (gateAt C i).op = GateOp.and ∧ OrReaches n C C.output i ∧
      ((e.1 ∈ side (n := n) C i 0 ∧ e.2 ∈ side (n := n) C i 1) ∨
        (e.2 ∈ side (n := n) C i 0 ∧ e.1 ∈ side (n := n) C i 1)) := by
    intro e he
    obtain ⟨j, hjl, hand, hor, hs⟩ := h30 e he
    refine ⟨j, (hF j).mpr ⟨hjl, hand, hor, ?_, ?_⟩, hjl, hand, hor, hs⟩
    · rcases hs with hs | hs
      · exact ⟨e.1, hs.1⟩
      · exact ⟨e.2, hs.1⟩
    · rcases hs with hs | hs
      · exact ⟨e.2, hs.2⟩
      · exact ⟨e.1, hs.2⟩
  have hFand : ∀ j ∈ F, j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧
      OrReaches n C C.output j := by
    intro j hj
    obtain ⟨ha, hb, hc, _⟩ := (hF j).mp hj
    exact ⟨ha, hb, hc⟩
  have h3 := h33 F hFand
  obtain ⟨h4a, h4b⟩ := h34 F ctr lf (fun j hj => (hcl j hj).1)
  have hEsum := le_trans (sum_card_ge E (fun c => Finset.univ.filter (fun b2 : Fin n =>
      ∃ j2 ∈ F, ctr j2 = c ∧ b2 ∈ orIn n C (lf j2))) hlt (by
    intro e he
    obtain ⟨j, hjF, _, _, _, hs⟩ := hw e he
    rcases hs with hs | hs
    · rcases (hcl j hjF).2 e.1 hs.1 e.2 hs.2 with h | h
      · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, hjF, h.1, h.2⟩)
      · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, hjF, h.1, h.2⟩)
    · rcases (hcl j hjF).2 e.2 hs.1 e.1 hs.2 with h | h
      · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, hjF, h.1, h.2⟩)
      · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, hjF, h.1, h.2⟩))) h4b
  have hcount := disjoint_or_count C
    {i : ℕ | i < C.gates.length ∧ (gateAt C i).op = GateOp.or ∧ OrReaches n C C.output i}
    {i : ℕ | i < C.gates.length ∧ (gateAt C i).op = GateOp.or ∧
      2 ≤ (orIn n C (n + i)).card ∧ ∃ j ∈ F, OrReaches n C (lf j) i}
    (fun _ hi => ⟨hi.1, hi.2.1⟩) (fun _ hi => ⟨hi.1, hi.2.1⟩)
    (fun i hi hiB => h4a i hi.1 hi.2.1 hiB.2.2.1 hiB.2.2.2 hi.2.2)
  omega

/-- OR-only version of the L2235 counting core, with its structural edge witnesses explicit. -/
theorem or_bound_of_edge_witness (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (E : Finset (Fin n × Fin n))
    (h4 : NoFourCycle G) (hAO : IsAO2 n C)
    (h1 : ∀ a : Fin n, circuitFun n C (fun k => decide (k = a)) = false)
    (h2 : ∀ a b : Fin n, a ≠ b → ¬ G.Adj a b →
      circuitFun n C (fun k => decide (k = a ∨ k = b)) = false)
    (hlt : ∀ e ∈ E, e.1 < e.2)
    (hedge : ∀ e ∈ E, ∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧
      OrReaches n C C.output j ∧
      ((e.1 ∈ side (n := n) C j 0 ∧ e.2 ∈ side (n := n) C j 1) ∨
        (e.2 ∈ side (n := n) C j 0 ∧ e.1 ∈ side (n := n) C j 1))) :
    E.card ≤ Set.ncard {i : ℕ | i < C.gates.length ∧ (gateAt C i).op = GateOp.or} + 1 := by
  exact or_count_core n G C E hlt hedge (s2231 n G C h4 hAO h1 h2).1
    (fun F => s2233 n C F hAO) (fun F ctr lf => s2234 n G C F ctr lf h4 hAO h1)


open PEqualNP.EdgeOwnership PEqualNP.Outside.L_meta_1501

/-- Every true wire has a true raw input in its OR support, or a true AND in its OR closure. -/
lemma fire_trace (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (x : Fin n → Bool) :
    ∀ w : ℕ, wv n C x w = true →
      (∃ u ∈ orIn n C w, x u = true) ∨
      ∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧
        OrReaches n C w j ∧ gateVal n C j x = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hwn : w < n
    · left
      refine ⟨⟨w, hwn⟩, (s2234_qmem_orIn n C w _).mpr (Or.inl rfl), ?_⟩
      simpa only [wv_input n C x w hwn] using hw
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < C.gates.length := by
        have hl := out_lt n { C with output := n + j } x hw
        simpa using (show j < C.gates.length by simpa using hl)
      have haob := aob (ao2_of n C hAO)
      rcases (haob j hj).1 with hop | hop
      · exact Or.inr ⟨j, hj, hop, s2234_qreach_self n C j hj, hw⟩
      · rw [wv_rec n C x haob j hj, hop] at hw
        simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq] at hw
        obtain ⟨r, hr, hv⟩ := hw
        have hrlt := (haob j hj).2 r hr
        rcases ih r hrlt hv with ⟨u, hu, hxu⟩ | ⟨k, hk, hka, hkr, hkv⟩
        · exact Or.inl ⟨u, s2230_orIn_up n C j r u hj hop hr hrlt hu, hxu⟩
        · exact Or.inr ⟨k, hk, hka, s2230_orReaches_step n C j r k hj hop hr hrlt hkr, hkv⟩

lemma or_reach_cone (n : ℕ) (C : Circuit) (g : ℕ) :
    ∀ j : ℕ, j < C.gates.length → OrReaches n C (n + j) g → g = j ∨ InCone n C g j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj hr
    rcases (s2234_qreach_iff n C j g hj).mp hr with heq | ⟨_, w, hw, hwlt, hwr⟩
    · exact Or.inl heq
    · have hwn : n ≤ w := hwr.1
      have hk : w - n < j := by omega
      have he : n + (w - n) = w := by omega
      have hki := ih (w - n) hk (by omega) (by rwa [he])
      right
      apply (inCone_iff n C g j).mpr
      exact ⟨hj, w - n, hk, by rwa [he], hki⟩

lemma or_reach_into_input (n : ℕ) (C : Circuit) (j w g : ℕ)
    (hj : j < C.gates.length) (hw : w ∈ (gateAt C j).inputs) (hwlt : w < n + j)
    (hr : OrReaches n C w g) : InCone n C g j := by
  have hwn : n ≤ w := hr.1
  have hk : w - n < j := by omega
  have he : n + (w - n) = w := by omega
  exact (inCone_iff n C g j).mpr ⟨hj, w - n, hk, by rwa [he],
    or_reach_cone n C g (w - n) (by omega) (by rwa [he])⟩

/-- Clean TopForm makes every firing operand of an AND originate in a raw OR support. -/
lemma clean_top_operand (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (htop : TopForm G C)
    (hclean : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → BelowF G C j)
    (j : ℕ) (hj : j < C.gates.length) (hja : (gateAt C j).op = GateOp.and)
    (w : ℕ) (hw : w ∈ (gateAt C j).inputs) (x : Fin n → Bool)
    (hv : wv n C x w = true) : ∃ u ∈ orIn n C w, x u = true := by
  rcases fire_trace n C hAO x w hv with h | ⟨k, hk, hka, hr, _⟩
  · exact h
  · exact False.elim (htop k hk j hj hka (hclean k hk hka) hja
      (or_reach_into_input n C j w k hj hw (hAO.2.1 j hj w hw) hr))

/-- The edge-witness premise needed by the OR count follows directly from clean TopForm. -/
theorem clean_top_edge_witness (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (h4 : NoFourCycle G)
    (h1 : ∀ a : Fin n, circuitFun n C (fun k => decide (k = a)) = false)
    (h2 : ∀ a b : Fin n, a ≠ b → ¬ G.Adj a b →
      circuitFun n C (fun k => decide (k = a ∨ k = b)) = false)
    (htop : TopForm G C)
    (hclean : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → BelowF G C j)
    (a b : Fin n) (hout : circuitFun n C (pairInput a b) = true) :
    ∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧ OrReaches n C C.output j ∧
      ((a ∈ side (n := n) C j 0 ∧ b ∈ side (n := n) C j 1) ∨
        (b ∈ side (n := n) C j 0 ∧ a ∈ side (n := n) C j 1)) := by
  rcases fire_trace n C hAO (pairInput a b) C.output hout with
    ⟨u, hu, _⟩ | ⟨j, hj, hja, hreach, hjval⟩
  · have hon := s2234_qval_orIn n C C.output u hu
    have hoff := h1 u
    change circuitFun n C (fun k => decide (k = u)) = true at hon
    rw [hoff] at hon
    cases hon
  · have hgm : gateAt C j ∈ C.gates := gateAt_mem C j hj
    obtain ⟨r, s, hrs⟩ := List.length_eq_two.mp (hAO.2.2 _ hgm)
    have hr : r ∈ (gateAt C j).inputs := by rw [hrs]; simp
    have hs : s ∈ (gateAt C j).inputs := by rw [hrs]; simp
    have hrval : wv n C (pairInput a b) r = true ∧ wv n C (pairInput a b) s = true := by
      change wv n C (pairInput a b) (n + j) = true at hjval
      rw [wv_rec n C _ (aob (ao2_of n C hAO)) j hj, hja, hrs] at hjval
      simpa [GateOp.eval] using hjval
    obtain ⟨u, hu, hxu⟩ := clean_top_operand n G C hAO htop hclean j hj hja r hr _ hrval.1
    obtain ⟨v, hv, hxv⟩ := clean_top_operand n G C hAO htop hclean j hj hja s hs _ hrval.2
    have e0 : opnd C j 0 = r := by simp [opnd, hrs]
    have e1 : opnd C j 1 = s := by simp [opnd, hrs]
    have hu0 : u ∈ side (n := n) C j 0 := by simpa only [side, e0] using hu
    have hv1 : v ∈ side (n := n) C j 1 := by simpa only [side, e1] using hv
    have huv : u ≠ v := by
      intro he
      subst v
      exact (s2231 n G C h4 hAO h1 h2).1 j hj hja hreach |>.1 u hu0 hv1
    have hua : u = a ∨ u = b := by simpa only [pairInput, decide_eq_true_eq] using hxu
    have hva : v = a ∨ v = b := by simpa only [pairInput, decide_eq_true_eq] using hxv
    refine ⟨j, hj, hja, hreach, ?_⟩
    rcases hua with rfl | rfl <;> rcases hva with rfl | rfl
    · exact False.elim (huv rfl)
    · exact Or.inl ⟨hu0, hv1⟩
    · exact Or.inr ⟨hu0, hv1⟩
    · exact False.elim (huv rfl)


lemma graph_unit_false (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a : Fin n) : graphFun G ∅ (fun k => decide (k = a)) = false := by
  simp [graphFun]

lemma graph_pair_false (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a b : Fin n) (hab : ¬ G.Adj a b) : graphFun G ∅ (pairInput a b) = false := by
  have hn : ¬ ∃ u v : Fin n, G.Adj u v ∧ pairInput a b u = true ∧ pairInput a b v = true := by
    rintro ⟨u, v, huv, hu, hv⟩
    have hu' : u = a ∨ u = b := by simpa only [pairInput, decide_eq_true_eq] using hu
    have hv' : v = a ∨ v = b := by simpa only [pairInput, decide_eq_true_eq] using hv
    rcases hu' with rfl | rfl <;> rcases hv' with rfl | rfl
    · exact G.irrefl huv
    · exact hab huv
    · exact hab huv.symm
    · exact G.irrefl huv
  simp [graphFun, hn]

lemma or_indices_eq_countP (C : Circuit) :
    Set.ncard {i : ℕ | i < C.gates.length ∧ (gateAt C i).op = GateOp.or} =
      C.gates.countP (fun g => GateOp.casesOn g.op false true false (fun _ => false) false) := by
  classical
  have hS : {i : ℕ | i < C.gates.length ∧ (gateAt C i).op = GateOp.or} =
      (↑((Finset.range C.gates.length).filter fun i => (gateAt C i).op = GateOp.or) : Set ℕ) := by
    ext i
    simp
  rw [hS, Set.ncard_coe_finset]
  have hmap : (List.range C.gates.length).map (gateAt C) = C.gates := by
    apply List.ext_getElem
    · simp
    · intro i hi hi'
      rw [List.getElem_map, List.getElem_range]
      exact s2231_gateAt_eq C i hi'
  have hc : ((Finset.range C.gates.length).filter fun i => (gateAt C i).op = GateOp.or).card =
      ((List.range C.gates.length).map (gateAt C)).countP (fun g => decide (g.op = GateOp.or)) := by
    simpa only [List.countP_map, Function.comp_def, List.toFinset_range] using
      (List.Nodup.card_eq_countP (P := fun i => (gateAt C i).op = GateOp.or)
        (List.nodup_range (n := C.gates.length)))
  rw [hmap] at hc
  rw [hc]
  congr 1
  funext g
  cases g.op <;> simp

/-- In a C4-free graph, an exact clean TopForm AO2 circuit has at least |E|-1 OR gates.
There is no total-size or OR-budget minimality premise. -/
theorem clean_top_or_bound (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (h4 : NoFourCycle G)
    (hf : circuitFun n C = graphFun G ∅) (htop : TopForm G C)
    (hclean : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → BelowF G C j) :
    (Finset.univ.filter (fun e : Fin n × Fin n => e.1 < e.2 ∧ G.Adj e.1 e.2)).card ≤
      C.gates.countP (fun g => GateOp.casesOn g.op false true false (fun _ => false) false) + 1 := by
  have h1 : ∀ a : Fin n, circuitFun n C (fun k => decide (k = a)) = false := by
    intro a
    rw [hf]
    exact graph_unit_false n G a
  have h2 : ∀ a b : Fin n, a ≠ b → ¬ G.Adj a b →
      circuitFun n C (fun k => decide (k = a ∨ k = b)) = false := by
    intro a b _ hab
    rw [hf]
    exact graph_pair_false n G a b hab
  have hcount := or_bound_of_edge_witness n G C
    (Finset.univ.filter (fun e : Fin n × Fin n => e.1 < e.2 ∧ G.Adj e.1 e.2))
    h4 hAO h1 h2 (fun e he => (Finset.mem_filter.mp he).2.1) (by
      intro e he
      apply clean_top_edge_witness n G C hAO h4 h1 h2 htop hclean e.1 e.2
      rw [hf]
      apply Bool.or_eq_true_iff.mpr
      right
      exact decide_eq_true ⟨e.1, e.2, (Finset.mem_filter.mp he).2.2,
        by simp [pairInput], by simp [pairInput]⟩)
  rwa [or_indices_eq_countP] at hcount

end PEqualNP.Outside.Pnp4201CleanOrCount
