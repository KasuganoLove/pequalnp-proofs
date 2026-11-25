import Pnp4201BudgetTopForm

/-
Clean-class OR-budget TopForm normalization for L-meta-4201 / L-meta-8323.
This imports the checked operation accounting and the upstream L_meta_1501
wire/cone machinery. The minimum is restricted to circuits whose AND gates
reject the same target-negative inputs. The restriction is explicitly proved
for every comparison circuit; unrestricted minimum-size cleanliness is not used.
-/

namespace PEqualNP.Outside.Pnp4201CleanBudgetTopForm

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.Outside.L_meta_1501
open PEqualNP.Outside.Pnp4201OrBudget PEqualNP.Outside.Pnp4201BudgetTopForm

def Clean (n : ℕ) (F : (Fin n → Bool) → Bool) (C : Circuit) : Prop :=
  ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
    ∀ x, F x = false → wv n C x (n + k) = false

def CleanLeast (n : ℕ) (F : (Fin n → Bool) → Bool) (C : Circuit) : Prop :=
  AO2 n C ∧ Clean n F C ∧ ∀ D : Circuit, AO2 n D →
    (∀ x, wv n D x D.output = wv n C x C.output) → orCount D ≤ orCount C →
    Clean n F D → C.gates.length ≤ D.gates.length

lemma below_off (n : ℕ) (C : Circuit) (F : (Fin n → Bool) → Bool)
    (hF : ∀ x, wv n C x C.output = F x) (i : ℕ)
    (hbel : ∀ x, wv n C x (n + i) = true → wv n C x C.output = true) :
    ∀ x, F x = false → wv n C x (n + i) = false := by
  intro x hx
  cases hi : wv n C x (n + i) with
  | false => rfl
  | true =>
    have hbad := hbel x hi
    rw [hF, hx] at hbad
    cases hbad

lemma V1_clean (n : ℕ) (C : Circuit) (F : (Fin n → Bool) → Bool)
    (r b : ℕ) (hC : AO2 n C) (hClean : Clean n F C)
    (hr : r < C.gates.length) (hb : b < n + r)
    (h0 : ∀ x, F x = false → wv n C x (n + r) = wv n C x b) :
    Clean n F (V1 n C r b) := by
  intro k hk hop x hx
  rw [V1_len] at hk
  have hkC := rho_lt r k C.gates.length hr hk
  have htr := transfer_eq n C (V1 n C r b) r b x (aob hC)
    (aob (V1_AO2 n C r b hC hr hb)) hr hb (by rw [V1_len]) (V1_red n C r b)
    (n + rho r k) (by omega) (fun _ => h0 x hx)
  rw [tau_rho] at htr
  rw [← htr]
  apply hClean (rho r k) hkC ?_ x hx
  rw [V1_gate n C r b k hk] at hop
  exact hop

lemma V2_clean (n : ℕ) (C : Circuit) (F : (Fin n → Bool) → Bool)
    (r b i : ℕ) (hC : AO2 n C) (hClean : Clean n F C)
    (hr : r < C.gates.length) (hb : b < n + r) (hi : i < r)
    (hout : C.output < n + C.gates.length)
    (h0 : ∀ x, F x = false → wv n C x (n + r) = wv n C x b) :
    Clean n F (V2 n C r b i) := by
  intro k hk hop x hx
  rw [V2_len] at hk
  by_cases hk0 : k < C.gates.length - 1
  · rw [V2_gateval n C r b i x hC hr hb hi hout (h0 x hx) k hk0]
    apply hClean (rho r k) (rho_lt r k _ hr hk0) ?_ x hx
    rw [V2_gate n C r b i k hk0] at hop
    exact hop
  · have he : k = C.gates.length - 1 := by omega
    rw [he, V2_top n C r b i (by omega)] at hop
    cases hop

lemma clean_reader_or (n : ℕ) (C : Circuit) (F : (Fin n → Bool) → Bool)
    (hF : ∀ x, wv n C x C.output = F x) (hL : CleanLeast n F C) (hout : C.output < n + C.gates.length)
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
  have hsafe : Clean n F (V1 n C r (n + i)) :=
    V1_clean n C F r (n + i) hL.1 hL.2.1 hr hir (fun x hx => by
      have hi0 := below_off n C F hF i hbel x hx
      rw [key x hi0, hi0])
  have hle := hL.2.2 _ (V1_AO2 n C r (n + i) hL.1 hr hir) hfun (V1_orCount_le n C r (n + i) hr) hsafe
  rw [V1_len] at hle
  omega

lemma clean_reader_unique (n : ℕ) (C : Circuit) (F : (Fin n → Bool) → Bool)
    (hF : ∀ x, wv n C x C.output = F x) (hL : CleanLeast n F C)
    (hout : C.output < n + C.gates.length) (i r1 r2 : ℕ) (h12 : r1 < r2)
    (hr2 : r2 < C.gates.length)
    (hbel : ∀ x, wv n C x (n + i) = true → wv n C x C.output = true)
    (hin1 : n + i ∈ (gateAt C r1).inputs) (hin2 : n + i ∈ (gateAt C r2).inputs) : False := by
  have hr1 : r1 < C.gates.length := by omega
  obtain ⟨hop1, c1, hc1, hc1lt, hi1⟩ := clean_reader_or n C F hF hL hout i r1 hr1 hbel hin1
  obtain ⟨hop2, c2, hc2, hc2lt, hi2⟩ := clean_reader_or n C F hF hL hout i r2 hr2 hbel hin2
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
  have hDclean := V2_clean n C F r2 c2 i hL.1 hL.2.1 hr2 hc2lt hir2 hout
    (fun x hx => k2 x (below_off n C F hF i hbel x hx))
  have hEclean : Clean n F (V1 n (V2 n C r2 c2 i) r1 c1) :=
    V1_clean n (V2 n C r2 c2 i) F r1 c1 hD hDclean (by rw [hDlen]; omega)
      hc1lt (fun x hx => h0 x (by
        rw [V2_low n C r2 c2 i x hL.1 hr2 hc2lt hir2 hout (n + i) (by omega)]
        exact below_off n C F hF i hbel x hx))
  have hle := hL.2.2 _ (V1_AO2 n (V2 n C r2 c2 i) r1 c1 hD (by rw [hDlen]; omega) hc1lt) hEfun
    ((V1_orCount_le n (V2 n C r2 c2 i) r1 c1 (by rw [hDlen]; omega)).trans
      (le_of_eq (V2_orCount n C r2 c2 i hr2 hop2))) hEclean
  rw [V1_len, hDlen] at hle
  omega

lemma clean_step3_core (n : ℕ) (C : Circuit) (F : (Fin n → Bool) → Bool)
    (hF : ∀ x, wv n C x C.output = F x) (hL : CleanLeast n F C) (hout : C.output < n + C.gates.length)
    (i j : ℕ) (hbel : ∀ x, wv n C x (n + i) = true → wv n C x C.output = true)
    (hcone : InCone n C i j) :
    ∃ r c, r < C.gates.length ∧ i < r ∧ c < n + r ∧ c ≠ n + i ∧ c ∈ (gateAt C r).inputs ∧
      (gateAt C r).op = GateOp.or ∧
      (∀ k, k < C.gates.length → n + i ∈ (gateAt C k).inputs → k = r) ∧
      (∀ x, wv n C x (n + i) = false → wv n C x (n + r) = wv n C x c) := by
  obtain ⟨r, hr, hir, hrin, _⟩ := inCone_reader n C i j hcone
  obtain ⟨hop, c, hc, hclt, hi⟩ := clean_reader_or n C F hF hL hout i r hr hbel hrin
  refine ⟨r, c, hr, hir, hclt, hc, ?_, hop, ?_, ?_⟩
  · rcases hi with h | h <;> rw [h] <;> simp
  · intro k hk hkin
    rcases Nat.lt_trichotomy k r with h | h | h
    · exact (clean_reader_unique n C F hF hL hout i k r h hr hbel hkin hrin).elim
    · exact h
    · exact (clean_reader_unique n C F hF hL hout i r k h hk hbel hrin hkin).elim
  · intro x hx
    rw [wv_rec n C x (aob hL.1) r hr, hop]
    rcases hi with h | h
    · rw [h, eval_or_pair, hx]; rfl
    · rw [h, eval_or_pair, hx]; simp

lemma clean_least_of_same (n : ℕ) (F : (Fin n → Bool) → Bool) (C D : Circuit)
    (hL : CleanLeast n F C) (hD : AO2 n D) (hClean : Clean n F D)
    (hfun : ∀ x, wv n D x D.output = wv n C x C.output)
    (hlen : D.gates.length = C.gates.length) (hcount : orCount D = orCount C) : CleanLeast n F D :=
  ⟨hD, hClean, fun E hE hEf hEc hEclean => by
    rw [hlen]
    exact hL.2.2 E hE (fun x => (hEf x).trans (hfun x)) (hEc.trans hcount.le) hEclean⟩

lemma clean_step3_struct (n : ℕ) (C : Circuit) (F : (Fin n → Bool) → Bool) (hL : CleanLeast n F C)
    (hF : ∀ x, wv n C x C.output = F x) (hout : C.output < n + C.gates.length)
    (i j : ℕ) (hbel : ∀ x, wv n C x (n + i) = true → F x = true)
    (hcone : InCone n C i j) :
    ∃ (C' : Circuit) (r : ℕ), r < C.gates.length ∧ i < r ∧ CleanLeast n F C' ∧
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
    clean_step3_core n C F hF hL hout i j hbel' hcone
  have hD := V2_AO2 n C r c i hL.1 hr hclt hir hout
  have hfun : ∀ x, wv n (V2 n C r c i) x (V2 n C r c i).output = wv n C x C.output :=
    fun x => V2_out n C r c i x hL.1 hr hclt hir hout (hbel' x) (h0 x)
  have hDclean := V2_clean n C F r c i hL.1 hL.2.1 hr hclt hir hout
    (fun x hx => h0 x (below_off n C F hF i hbel' x hx))
  refine ⟨V2 n C r c i, r, hr, hir, clean_least_of_same n F C _ hL hD hDclean hfun (V2_len n C r c i)
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
lemma clean_main_ind (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : G.edgeFinset.Nonempty) :
    ∀ k : ℕ, ∀ C : Circuit, CleanLeast n (graphFun G ∅) C →
      (∀ x, wv n C x C.output = graphFun G ∅ x) →
      ((Finset.range C.gates.length ×ˢ Finset.range C.gates.length).filter
        (fun p : ℕ × ℕ => (gateAt C p.1).op = GateOp.and ∧
          (gateAt C p.2).op = GateOp.and ∧ InCone n C p.1 p.2)).card = k →
      ∃ C' : Circuit, CleanLeast n (graphFun G ∅) C' ∧
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
        clean_step3_struct n C (graphFun G ∅) hC hF hout i j hbi hcone
      have hlt := pairs_lt n C C' r i j hr hir hlen hops htop' hcn hno hopi hopj hcone
      rw [hk] at hlt
      obtain ⟨C'', h1, h2, h3, h4, h5, h6⟩ := ih _ hlt C' hL' hF' rfl
      refine ⟨C'', h1, h2, h3.trans hlen, h4.trans hcount, h5.trans ?_, h6⟩
      refine junk_eq n C C' (graphFun G ∅) r hr hlen hops htop' hopr hbelow _ _ ?_ ?_
      · intro j
        exact mem_junk n G C j
      · intro j
        exact mem_junk n G C' j

theorem clean_top_form (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : G.edgeFinset.Nonempty) (C : Circuit) (hC : CleanLeast n (graphFun G ∅) C)
    (hF : circuitFun n C = graphFun G ∅) :
    ∃ D : Circuit, CleanLeast n (graphFun G ∅) D ∧ circuitFun n D = graphFun G ∅ ∧
      D.size = C.size ∧ orCount D = orCount C ∧
      (PEqualNP.TopForm.junk G D).card = (PEqualNP.TopForm.junk G C).card ∧
      PEqualNP.TopForm.TopForm G D := by
  obtain ⟨D, hD, hDf, hs, ho, hj, ht⟩ :=
    clean_main_ind n G hG _ C hC (fun x => congrFun hF x) rfl
  exact ⟨D, hD, funext hDf, hs, ho, hj, ht⟩

theorem exists_clean_minimum (n : ℕ) (F : (Fin n → Bool) → Bool) (C : Circuit)
    (hAO : AO2 n C) (hClean : Clean n F C) (hF : circuitFun n C = F) :
    ∃ B : Circuit, CleanLeast n F B ∧ circuitFun n B = F ∧
      B.size ≤ C.size ∧ orCount B ≤ orCount C := by
  classical
  let A (k : ℕ) : Prop := ∃ B : Circuit,
    AO2 n B ∧ Clean n F B ∧ circuitFun n B = F ∧ orCount B ≤ orCount C ∧ B.size = k
  have hex : ∃ k, A k := ⟨C.size, C, hAO, hClean, hF, le_rfl, rfl⟩
  obtain ⟨B, hBA, hBClean, hBF, hBO, hBS⟩ := Nat.find_spec hex
  refine ⟨B, ⟨hBA, hBClean, ?_⟩, hBF, ?_, hBO⟩
  · intro D hD hDf hDO hDClean
    have hDF : circuitFun n D = F := funext fun x => (hDf x).trans (congrFun hBF x)
    change B.size ≤ D.size
    rw [hBS]
    exact Nat.find_min' hex ⟨D, hD, hDClean, hDF, hDO.trans hBO, rfl⟩
  · rw [hBS]
    exact Nat.find_min' hex ⟨C, hAO, hClean, hF, le_rfl, rfl⟩

theorem exists_clean_top_form_with_or_budget (n : ℕ) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hG : G.edgeFinset.Nonempty) (C : Circuit)
    (hAO : PEqualNP.TopForm.IsAO2 n C) (hF : circuitFun n C = graphFun G ∅)
    (hClean : Clean n (graphFun G ∅) C) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧ circuitFun n D = graphFun G ∅ ∧
      D.size ≤ C.size ∧ orCount D ≤ orCount C ∧ Clean n (graphFun G ∅) D ∧
      PEqualNP.TopForm.TopForm G D := by
  obtain ⟨B, hBL, hBF, hBS, hBO⟩ :=
    exists_clean_minimum n (graphFun G ∅) C (ao2_of n C hAO) hClean hF
  obtain ⟨D, hDL, hDF, hDS, hDO, _, hDT⟩ := clean_top_form n G hG B hBL hBF
  exact ⟨D, ao2_to n D hDL.1, hDF, hDS.le.trans hBS, hDO.le.trans hBO, hDL.2.1, hDT⟩

theorem clean_iff_all_and_below (n : ℕ) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) :
    Clean n (graphFun G ∅) C ↔
      ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → PEqualNP.TopForm.BelowF G C k := by
  constructor
  · intro h k hk hop x hx
    cases hf : graphFun G ∅ x with
    | true => rfl
    | false =>
      have hz := h k hk hop x hf
      change wv n C x (n + k) = true at hx
      rw [hz] at hx
      cases hx
  · intro h k hk hop x hx
    cases hv : wv n C x (n + k) with
    | false => rfl
    | true =>
      have hf := h k hk hop x hv
      rw [hx] at hf
      cases hf

end PEqualNP.Outside.Pnp4201CleanBudgetTopForm
