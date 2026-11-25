import Pnp4201OrBudget
import PEqualNP.Outside.L_meta_1501

/-
OR-budget version of the TopForm normalization in upstream L_meta_1501.
The wire/cone/junk machinery and the reader proof construction are reused with
attribution. The new ingredient is exact V1/V2 operation accounting, allowing
total-size minimization only among circuits within the same OR budget.
TopForm excludes clean AND ancestors of AND gates; it does not make all ANDs clean.
-/

namespace PEqualNP.Outside.Pnp4201BudgetTopForm

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.Outside.L_meta_1501
open PEqualNP.Outside.Pnp4201OrBudget

theorem opCount_of_same_ops (p : GateOp → Bool) (C D : Circuit)
    (hlen : C.gates.length = D.gates.length)
    (hops : ∀ k, k < C.gates.length → (gateAt C k).op = (gateAt D k).op) :
    opCount p C = opCount p D := by
  have hm : C.gates.map Gate.op = D.gates.map Gate.op := by
    apply List.ext_getElem
    · simpa using hlen
    · intro k hk hk'
      simp only [List.length_map] at hk hk'
      simp only [List.getElem_map]
      rw [← Pnp2343Pruning.gateAt_eq hk, ← Pnp2343Pruning.gateAt_eq hk']
      exact hops k hk
  have h := congrArg (List.countP p) hm
  simpa only [List.countP_map, Function.comp_def, opCount] using h

theorem V1_opCount (p : GateOp → Bool) (n : ℕ) (C : Circuit) (r b : ℕ)
    (hr : r < C.gates.length) :
    opCount p (V1 n C r b) + (if p (gateAt C r).op then 1 else 0) = opCount p C := by
  have he : opCount p (V1 n C r b) = opCount p (Pnp2343Pruning.bypass n C r b) := by
    apply opCount_of_same_ops
    · rw [V1_len, Pnp2343Pruning.bypass_length]
    · intro k hk
      rw [V1_len] at hk
      rw [V1_gate n C r b k hk, Pnp2343Pruning.gateAt_bypass hk]
      simp only [rho]
      split_ifs <;> rfl
  rw [he]
  exact bypass_opCount p n C r b hr

theorem V1_orCount_le (n : ℕ) (C : Circuit) (r b : ℕ)
    (hr : r < C.gates.length) : orCount (V1 n C r b) ≤ orCount C := by
  have h := V1_opCount isOr n C r b hr
  change opCount isOr (V1 n C r b) ≤ opCount isOr C
  omega

theorem V2_ops (n : ℕ) (C : Circuit) (r b i : ℕ) (hr : r < C.gates.length) :
    (V2 n C r b i).gates.map Gate.op = (V1 n C r b).gates.map Gate.op ++ [GateOp.or] := by
  apply List.ext_getElem
  · simp only [List.length_map, List.length_append, List.length_singleton, V1_len, V2_len]
    omega
  · intro k hk hk'
    have hkC : k < C.gates.length := by simpa only [List.length_map, V2_len] using hk
    by_cases hk0 : k < C.gates.length - 1
    · rw [List.getElem_append_left (by simp only [List.length_map, V1_len]; exact hk0)]
      simp only [List.getElem_map]
      rw [← Pnp2343Pruning.gateAt_eq (by rw [V2_len]; exact hkC),
        ← Pnp2343Pruning.gateAt_eq (by rw [V1_len]; exact hk0),
        V2_gate n C r b i k hk0, V1_gate n C r b k hk0]
    · have hk0' : k = C.gates.length - 1 := by omega
      subst k
      rw [List.getElem_append_right (by simp only [List.length_map, V1_len]; exact le_rfl)]
      simp only [List.length_map, V1_len, Nat.sub_self, List.getElem_cons_zero, List.getElem_map]
      rw [← Pnp2343Pruning.gateAt_eq (by rw [V2_len]; omega), V2_top n C r b i (by omega)]

theorem V2_opCount (p : GateOp → Bool) (n : ℕ) (C : Circuit) (r b i : ℕ)
    (hr : r < C.gates.length) :
    opCount p (V2 n C r b i) + (if p (gateAt C r).op then 1 else 0) =
      opCount p C + (if p GateOp.or then 1 else 0) := by
  have hv := congrArg (List.countP p) (V2_ops n C r b i hr)
  simp only [List.countP_append, List.countP_map, Function.comp_def,
    List.countP_cons, List.countP_nil, zero_add] at hv
  have hd := V1_opCount p n C r b hr
  change opCount p (V2 n C r b i) = opCount p (V1 n C r b) +
    (if p GateOp.or then 1 else 0) at hv
  omega

theorem V2_orCount (n : ℕ) (C : Circuit) (r b i : ℕ)
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    orCount (V2 n C r b i) = orCount C := by
  have h := V2_opCount isOr n C r b i hr
  rw [hop] at h
  exact Nat.add_right_cancel h

def BudgetLeast (n : ℕ) (C : Circuit) : Prop :=
  AO2 n C ∧ ∀ D : Circuit, AO2 n D →
    (∀ x, wv n D x D.output = wv n C x C.output) → orCount D ≤ orCount C →
    C.gates.length ≤ D.gates.length

lemma budget_reader_or (n : ℕ) (C : Circuit) (hL : BudgetLeast n C) (hout : C.output < n + C.gates.length)
    (i r : ℕ) (hr : r < C.gates.length)
    (hbel : ∀ x, wv n C x (n + i) = true → wv n C x C.output = true)
    (hin : n + i ∈ (gateAt C r).inputs) :
    (gateAt C r).op = GateOp.or ∧ ∃ c, c ≠ n + i ∧ c < n + r ∧
      ((gateAt C r).inputs = [n + i, c] ∨ (gateAt C r).inputs = [c, n + i]) := by
  obtain ⟨hop, ⟨a, c0, hab⟩, hlt⟩ := hL.1 r hr
  have hir : n + i < n + r := hlt _ hin
  have hin' : n + i = a ∨ n + i = c0 := by rw [hab] at hin; simpa using hin
  by_contra hcon
  have key : ∀ x, wv n C x (n + i) = false → wv n C x (n + r) = false := by
    intro x hx
    rw [wv_rec n C x (aob hL.1) r hr, hab]
    rcases hop with hop | hop
    · rw [hop, eval_and_pair]
      rcases hin' with h | h
      · rw [← h, hx]; rfl
      · rw [← h, hx]; simp
    · rw [hop, eval_or_pair]
      have ha : a = n + i := by
        by_contra hne
        apply hcon
        refine ⟨hop, a, hne, hlt a (by rw [hab]; simp), ?_⟩
        rcases hin' with h | h
        · exact absurd h.symm hne
        · right; rw [hab, h]
      have hc : c0 = n + i := by
        by_contra hne
        apply hcon
        refine ⟨hop, c0, hne, hlt c0 (by rw [hab]; simp), ?_⟩
        left; rw [hab, ha]
      rw [ha, hc, hx]; rfl
  have hfun : ∀ x, wv n (V1 n C r (n + i)) x (V1 n C r (n + i)).output = wv n C x C.output :=
    fun x => V1_fun n C r (n + i) x hL.1 hr hir hout (hbel x) (key x)
  have hle := hL.2 _ (V1_AO2 n C r (n + i) hL.1 hr hir) hfun (V1_orCount_le n C r (n + i) hr)
  rw [V1_len] at hle
  omega

lemma budget_reader_unique (n : ℕ) (C : Circuit) (hL : BudgetLeast n C)
    (hout : C.output < n + C.gates.length) (i r1 r2 : ℕ) (h12 : r1 < r2)
    (hr2 : r2 < C.gates.length)
    (hbel : ∀ x, wv n C x (n + i) = true → wv n C x C.output = true)
    (hin1 : n + i ∈ (gateAt C r1).inputs) (hin2 : n + i ∈ (gateAt C r2).inputs) : False := by
  have hr1 : r1 < C.gates.length := by omega
  obtain ⟨hop1, c1, hc1, hc1lt, hi1⟩ := budget_reader_or n C hL hout i r1 hr1 hbel hin1
  obtain ⟨hop2, c2, hc2, hc2lt, hi2⟩ := budget_reader_or n C hL hout i r2 hr2 hbel hin2
  have hir1 : i < r1 := by have := (hL.1 r1 hr1).2.2 _ hin1; omega
  have hir2 : i < r2 := by omega
  have k2 : ∀ x, wv n C x (n + i) = false → wv n C x (n + r2) = wv n C x c2 := by
    intro x hx
    rw [wv_rec n C x (aob hL.1) r2 hr2, hop2]
    rcases hi2 with h | h
    · rw [h, eval_or_pair, hx]; rfl
    · rw [h, eval_or_pair, hx]; simp
  have k1 : ∀ x, wv n C x (n + i) = false → wv n C x (n + r1) = wv n C x c1 := by
    intro x hx
    rw [wv_rec n C x (aob hL.1) r1 hr1, hop1]
    rcases hi1 with h | h
    · rw [h, eval_or_pair, hx]; rfl
    · rw [h, eval_or_pair, hx]; simp
  have hD : AO2 n (V2 n C r2 c2 i) := V2_AO2 n C r2 c2 i hL.1 hr2 hc2lt hir2 hout
  have hDlen := V2_len n C r2 c2 i
  have hDfun : ∀ x, wv n (V2 n C r2 c2 i) x (V2 n C r2 c2 i).output = wv n C x C.output :=
    fun x => V2_out n C r2 c2 i x hL.1 hr2 hc2lt hir2 hout (hbel x) (k2 x)
  have hDout : (V2 n C r2 c2 i).output = n + ((V2 n C r2 c2 i).gates.length - 1) := by
    rw [hDlen]
    show n + C.gates.length - 1 = n + (C.gates.length - 1)
    omega
  have hDtop : gateAt (V2 n C r2 c2 i) ((V2 n C r2 c2 i).gates.length - 1) =
      ⟨GateOp.or, [tau n r2 c2 C.output, n + i]⟩ := by
    rw [hDlen]
    exact V2_top n C r2 c2 i (by omega)
  have h0 : ∀ x, wv n (V2 n C r2 c2 i) x (n + i) = false →
      wv n (V2 n C r2 c2 i) x (n + r1) = wv n (V2 n C r2 c2 i) x c1 := by
    intro x hx
    rw [V2_low n C r2 c2 i x hL.1 hr2 hc2lt hir2 hout (n + i) (by omega)] at hx
    rw [V2_low n C r2 c2 i x hL.1 hr2 hc2lt hir2 hout (n + r1) (by omega),
      V2_low n C r2 c2 i x hL.1 hr2 hc2lt hir2 hout c1 (by omega)]
    exact k1 x hx
  have hEfun : ∀ x, wv n (V1 n (V2 n C r2 c2 i) r1 c1) x (V1 n (V2 n C r2 c2 i) r1 c1).output =
      wv n C x C.output := fun x =>
    (V1_fun_top n (V2 n C r2 c2 i) r1 c1 i (tau n r2 c2 C.output) x hD (by rw [hDlen]; omega)
      hc1lt hir1 hDout hDtop (h0 x)).trans (hDfun x)
  have hle := hL.2 _ (V1_AO2 n (V2 n C r2 c2 i) r1 c1 hD (by rw [hDlen]; omega) hc1lt) hEfun
    ((V1_orCount_le n (V2 n C r2 c2 i) r1 c1 (by rw [hDlen]; omega)).trans
      (le_of_eq (V2_orCount n C r2 c2 i hr2 hop2)))
  rw [V1_len, hDlen] at hle
  omega

lemma budget_step3_core (n : ℕ) (C : Circuit) (hL : BudgetLeast n C) (hout : C.output < n + C.gates.length)
    (i j : ℕ) (hbel : ∀ x, wv n C x (n + i) = true → wv n C x C.output = true)
    (hcone : InCone n C i j) :
    ∃ r c, r < C.gates.length ∧ i < r ∧ c < n + r ∧ c ≠ n + i ∧ c ∈ (gateAt C r).inputs ∧
      (gateAt C r).op = GateOp.or ∧
      (∀ k, k < C.gates.length → n + i ∈ (gateAt C k).inputs → k = r) ∧
      (∀ x, wv n C x (n + i) = false → wv n C x (n + r) = wv n C x c) := by
  obtain ⟨r, hr, hir, hrin, _⟩ := inCone_reader n C i j hcone
  obtain ⟨hop, c, hc, hclt, hi⟩ := budget_reader_or n C hL hout i r hr hbel hrin
  refine ⟨r, c, hr, hir, hclt, hc, ?_, hop, ?_, ?_⟩
  · rcases hi with h | h <;> rw [h] <;> simp
  · intro k hk hkin
    rcases Nat.lt_trichotomy k r with h | h | h
    · exact (budget_reader_unique n C hL hout i k r h hr hbel hkin hrin).elim
    · exact h
    · exact (budget_reader_unique n C hL hout i r k h hk hbel hrin hkin).elim
  · intro x hx
    rw [wv_rec n C x (aob hL.1) r hr, hop]
    rcases hi with h | h
    · rw [h, eval_or_pair, hx]; rfl
    · rw [h, eval_or_pair, hx]; simp

lemma budget_least_of_same (n : ℕ) (C D : Circuit) (hL : BudgetLeast n C) (hD : AO2 n D)
    (hfun : ∀ x, wv n D x D.output = wv n C x C.output)
    (hlen : D.gates.length = C.gates.length) (hcount : orCount D = orCount C) : BudgetLeast n D :=
  ⟨hD, fun E hE hEf hEc => by
    rw [hlen]
    exact hL.2 E hE (fun x => (hEf x).trans (hfun x)) (hEc.trans hcount.le)⟩

lemma budget_step3_struct (n : ℕ) (C : Circuit) (F : (Fin n → Bool) → Bool) (hL : BudgetLeast n C)
    (hF : ∀ x, wv n C x C.output = F x) (hout : C.output < n + C.gates.length)
    (i j : ℕ) (hbel : ∀ x, wv n C x (n + i) = true → F x = true)
    (hcone : InCone n C i j) :
    ∃ (C' : Circuit) (r : ℕ), r < C.gates.length ∧ i < r ∧ BudgetLeast n C' ∧
      (∀ x, wv n C' x C'.output = F x) ∧ C'.gates.length = C.gates.length ∧
      (∀ k', k' < C.gates.length - 1 → (gateAt C' k').op = (gateAt C (rho r k')).op) ∧
      (gateAt C' (C.gates.length - 1)).op = GateOp.or ∧ (gateAt C r).op = GateOp.or ∧
      (∀ k', k' < C.gates.length - 1 →
        ((∀ x, wv n C' x (n + k') = true → F x = true) ↔
          (∀ x, wv n C x (n + rho r k') = true → F x = true))) ∧
      (∀ a' b', b' < C.gates.length - 1 → InCone n C' a' b' →
        InCone n C (rho r a') (rho r b')) ∧
      (∀ j', j' < C.gates.length - 1 → ¬ InCone n C' i j') ∧ orCount C' = orCount C := by
  have hbel' : ∀ x, wv n C x (n + i) = true → wv n C x C.output = true :=
    fun x h => by rw [hF]; exact hbel x h
  obtain ⟨r, c, hr, hir, hclt, hci, hcin, hop, huniq, h0⟩ :=
    budget_step3_core n C hL hout i j hbel' hcone
  have hD := V2_AO2 n C r c i hL.1 hr hclt hir hout
  have hfun : ∀ x, wv n (V2 n C r c i) x (V2 n C r c i).output = wv n C x C.output :=
    fun x => V2_out n C r c i x hL.1 hr hclt hir hout (hbel' x) (h0 x)
  refine ⟨V2 n C r c i, r, hr, hir, budget_least_of_same n C _ hL hD hfun (V2_len n C r c i)
      (V2_orCount n C r c i hr hop),
    fun x => (hfun x).trans (hF x), V2_len n C r c i, ?_, ?_, hop, ?_, ?_, ?_, ?_⟩
  · intro k' hk'
    rw [V2_gate n C r c i k' hk']
  · rw [V2_top n C r c i (by omega)]
  · intro k' hk'
    exact V2_below n C r c i F hL.1 hr hclt hir hout hbel h0 k' hk'
  · intro a' b' hb' h
    exact V2_cone n C r c i hL.1 hr hclt hcin a' b' hb' h
  · exact V2_no_cone n C r c i hr hir hci huniq
  · exact V2_orCount n C r c i hr hop

open Classical in
lemma budget_main_ind (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : G.edgeFinset.Nonempty) :
    ∀ k : ℕ, ∀ C : Circuit, BudgetLeast n C →
      (∀ x, wv n C x C.output = graphFun G ∅ x) →
      ((Finset.range C.gates.length ×ˢ Finset.range C.gates.length).filter
        (fun p : ℕ × ℕ => (gateAt C p.1).op = GateOp.and ∧
          (gateAt C p.2).op = GateOp.and ∧ InCone n C p.1 p.2)).card = k →
      ∃ C' : Circuit, BudgetLeast n C' ∧
        (∀ x, wv n C' x C'.output = graphFun G ∅ x) ∧ C'.size = C.size ∧
        orCount C' = orCount C ∧
        (PEqualNP.TopForm.junk G C').card = (PEqualNP.TopForm.junk G C).card ∧
        PEqualNP.TopForm.TopForm G C' := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro C hC hF hk
    by_cases htop : PEqualNP.TopForm.TopForm G C
    · exact ⟨C, hC, hF, rfl, rfl, rfl, htop⟩
    · have hex : ∃ i j, i < C.gates.length ∧ j < C.gates.length ∧
          (gateAt C i).op = GateOp.and ∧ PEqualNP.TopForm.BelowF G C i ∧
          (gateAt C j).op = GateOp.and ∧ InCone n C i j := by
        by_contra hne
        apply htop
        intro i hi j hj h1 h2 h3 h4
        exact hne ⟨i, j, hi, hj, h1, h2, h3, h4⟩
      obtain ⟨i, j, hi, hj, hopi, hbi, hopj, hcone⟩ := hex
      obtain ⟨x1, hx1⟩ := exists_true n G hG
      have hout : C.output < n + C.gates.length := out_lt n C x1 (by rw [hF]; exact hx1)
      obtain ⟨C', r, hr, hir, hL', hF', hlen, hops, htop', hopr, hbelow, hcn, hno, hcount⟩ :=
        budget_step3_struct n C (graphFun G ∅) hC hF hout i j hbi hcone
      have hlt := pairs_lt n C C' r i j hr hir hlen hops htop' hcn hno hopi hopj hcone
      rw [hk] at hlt
      obtain ⟨C'', h1, h2, h3, h4, h5, h6⟩ := ih _ hlt C' hL' hF' rfl
      refine ⟨C'', h1, h2, h3.trans hlen, h4.trans hcount, h5.trans ?_, h6⟩
      refine junk_eq n C C' (graphFun G ∅) r hr hlen hops htop' hopr hbelow _ _ ?_ ?_
      · intro j
        exact mem_junk n G C j
      · intro j
        exact mem_junk n G C' j

theorem budget_top_form (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : G.edgeFinset.Nonempty) (C : Circuit) (hC : BudgetLeast n C)
    (hF : circuitFun n C = graphFun G ∅) :
    ∃ D : Circuit, BudgetLeast n D ∧ circuitFun n D = graphFun G ∅ ∧
      D.size = C.size ∧ orCount D = orCount C ∧
      (PEqualNP.TopForm.junk G D).card = (PEqualNP.TopForm.junk G C).card ∧
      PEqualNP.TopForm.TopForm G D := by
  obtain ⟨D, hD, hDf, hs, ho, hj, ht⟩ :=
    budget_main_ind n G hG _ C hC (fun x => congrFun hF x) rfl
  exact ⟨D, hD, funext hDf, hs, ho, hj, ht⟩

theorem budgetLeast_of_leastBudget (n : ℕ) (f : (Fin n → Bool) → Bool)
    (K : ℕ) (C : Circuit) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (hmin : LeastBudget n f isOr K C) : BudgetLeast n C := by
  refine ⟨ao2_of n C hAO, ?_⟩
  intro D hD hDf hcount
  have hAO' := ao2_to n D hD
  have hM : Monotone2 D := fun g hg => ⟨hAO'.1 g hg, (hAO'.2.2 g hg).le⟩
  have hF : circuitFun n D = f := by
    funext x
    exact (hDf x).trans (congrFun hmin.2.1 x)
  exact hmin.2.2.2 D hM hF (hcount.trans hmin.2.2.1)

theorem exists_top_form_with_or_budget (n : ℕ) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hG : G.edgeFinset.Nonempty) (C : Circuit)
    (hM : Monotone2 C) (hF : circuitFun n C = graphFun G ∅) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧ circuitFun n D = graphFun G ∅ ∧
      D.size ≤ C.size ∧ orCount D ≤ orCount C ∧ BudgetLeast n D ∧
      PEqualNP.TopForm.TopForm G D := by
  have hnc : ∃ x y : Fin n → Bool, graphFun G ∅ x ≠ graphFun G ∅ y := by
    obtain ⟨x, hx⟩ := exists_true n G hG
    refine ⟨x, fun _ => false, ?_⟩
    rw [hx]
    simp [graphFun]
  obtain ⟨B, hBA, hBmin, hBC⟩ := least_budget_normal_form n (graphFun G ∅)
    isOr (orCount C) C hM hF le_rfl hnc
  have hBL := budgetLeast_of_leastBudget n (graphFun G ∅) (orCount C) B hBA hBmin
  obtain ⟨D, hDL, hDF, hDS, hDO, _, hDT⟩ := budget_top_form n G hG B hBL hBmin.2.1
  exact ⟨D, ao2_to n D hDL.1, hDF, hDS.le.trans hBC,
    hDO.le.trans hBmin.2.2.1, hDL, hDT⟩

end PEqualNP.Outside.Pnp4201BudgetTopForm
