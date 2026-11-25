import PEqualNP.Outside.L_meta_1501

/-!
Research bridge for L-meta-5126. The normalization construction and induction
are reused from upstream L_meta_1501. The added invariant is rejection, by every
AND gate, of an arbitrary specified family of graph-negative inputs. This does
not prove the two-junk impossibility statement.
-/

namespace Pnp5126TopForm

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.Outside.L_meta_1501

def AndOffOn (n : ℕ) (C : Circuit) (Test : (Fin n → Bool) → Prop) : Prop :=
  ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
    ∀ x, Test x → wv n C x (n+k) = false

lemma step3_struct_tests (n : ℕ) (C : Circuit) (F : (Fin n → Bool) → Bool)
    (Test : (Fin n → Bool) → Prop) (hTest : ∀ x, Test x → F x = false)
    (hOff : AndOffOn n C Test) (hL : Least n C)
    (hF : ∀ x, wv n C x C.output = F x) (hout : C.output < n + C.gates.length)
    (i j : ℕ) (hbel : ∀ x, wv n C x (n+i) = true → F x = true)
    (hcone : InCone n C i j) :
    ∃ (C' : Circuit) (r : ℕ), r < C.gates.length ∧ i < r ∧ Least n C' ∧
      (∀ x, wv n C' x C'.output = F x) ∧ C'.gates.length = C.gates.length ∧
      (∀ k', k' < C.gates.length - 1 → (gateAt C' k').op = (gateAt C (rho r k')).op) ∧
      (gateAt C' (C.gates.length - 1)).op = GateOp.or ∧ (gateAt C r).op = GateOp.or ∧
      (∀ k', k' < C.gates.length - 1 →
        ((∀ x, wv n C' x (n+k') = true → F x = true) ↔
          (∀ x, wv n C x (n+rho r k') = true → F x = true))) ∧
      (∀ a' b', b' < C.gates.length - 1 → InCone n C' a' b' →
        InCone n C (rho r a') (rho r b')) ∧
      (∀ j', j' < C.gates.length - 1 → ¬ InCone n C' i j') ∧
      AndOffOn n C' Test := by
  have hbel' : ∀ x, wv n C x (n+i) = true → wv n C x C.output = true :=
    fun x h => by rw [hF]; exact hbel x h
  obtain ⟨r,c,hr,hir,hclt,hci,hcin,hop,huniq,h0⟩ :=
    step3_core n C hL hout i j hbel' hcone
  have hD := V2_AO2 n C r c i hL.1 hr hclt hir hout
  have hfun : ∀ x, wv n (V2 n C r c i) x (V2 n C r c i).output = wv n C x C.output :=
    fun x => V2_out n C r c i x hL.1 hr hclt hir hout (hbel' x) (h0 x)
  refine ⟨V2 n C r c i,r,hr,hir,least_of_same n C _ hL hD hfun (V2_len n C r c i),
    fun x => (hfun x).trans (hF x), V2_len n C r c i, ?_, ?_, hop, ?_, ?_, ?_, ?_⟩
  · intro k' hk'
    rw [V2_gate n C r c i k' hk']
  · rw [V2_top n C r c i (by omega)]
  · intro k' hk'
    exact V2_below n C r c i F hL.1 hr hclt hir hout hbel h0 k' hk'
  · intro a' b' hb' h
    exact V2_cone n C r c i hL.1 hr hclt hcin a' b' hb' h
  · exact V2_no_cone n C r c i hr hir hci huniq
  · intro k hk hkand x hx
    rw [V2_len] at hk
    by_cases hkl : k < C.gates.length - 1
    · have hi0 : wv n C x (n+i) = false := by
        cases he : wv n C x (n+i)
        · rfl
        · have hf := hbel x he
          rw [hTest x hx] at hf
          cases hf
      rw [V2_gateval n C r c i x hL.1 hr hclt hir hout (h0 x hi0) k hkl]
      apply hOff (rho r k) (rho_lt r k _ hr hkl) ?_ x hx
      rw [V2_gate n C r c i k hkl] at hkand
      exact hkand
    · have he : k = C.gates.length - 1 := by omega
      rw [he, V2_top n C r c i (by omega)] at hkand
      cases hkand

open Classical in
lemma main_ind_tests (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : G.edgeFinset.Nonempty) (Test : (Fin n → Bool) → Prop)
    (hTest : ∀ x, Test x → graphFun G ∅ x = false) :
    ∀ k : ℕ, ∀ C : Circuit, PEqualNP.TopForm.IsLeastAO G C →
      ((Finset.range C.gates.length ×ˢ Finset.range C.gates.length).filter
        (fun p : ℕ × ℕ => (gateAt C p.1).op = GateOp.and ∧
          (gateAt C p.2).op = GateOp.and ∧ InCone n C p.1 p.2)).card = k →
      AndOffOn n C Test →
      ∃ C' : Circuit, PEqualNP.TopForm.IsLeastAO G C' ∧ C'.size = C.size ∧
        (PEqualNP.TopForm.junk G C').card = (PEqualNP.TopForm.junk G C).card ∧
        PEqualNP.TopForm.TopForm G C' ∧ AndOffOn n C' Test := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro C hC hk hOff
    by_cases htop : PEqualNP.TopForm.TopForm G C
    · exact ⟨C,hC,rfl,rfl,htop,hOff⟩
    · have hex : ∃ i j, i < C.gates.length ∧ j < C.gates.length ∧
          (gateAt C i).op = GateOp.and ∧ PEqualNP.TopForm.BelowF G C i ∧
          (gateAt C j).op = GateOp.and ∧ InCone n C i j := by
        by_contra hne
        apply htop
        intro i hi j hj h1 h2 h3 h4
        exact hne ⟨i,j,hi,hj,h1,h2,h3,h4⟩
      obtain ⟨i,j,hi,hj,hopi,hbi,hopj,hcone⟩ := hex
      obtain ⟨hL,hF⟩ := least_glue n G C hC
      obtain ⟨x1,hx1⟩ := exists_true n G hG
      have hout : C.output < n + C.gates.length := out_lt n C x1 (by rw [hF]; exact hx1)
      obtain ⟨C',r,hr,hir,hL',hF',hlen,hops,htop',hopr,hbelow,hcn,hno,hOff'⟩ :=
        step3_struct_tests n C (graphFun G ∅) Test hTest hOff hL hF hout i j hbi hcone
      have hlt := pairs_lt n C C' r i j hr hir hlen hops htop' hcn hno hopi hopj hcone
      rw [hk] at hlt
      obtain ⟨C'',h1,h2,h3,h4,h5⟩ :=
        ih _ hlt C' (least_glue' n G C' hL' hF') rfl hOff'
      refine ⟨C'',h1,h2.trans hlen,h3.trans ?_,h4,h5⟩
      refine junk_eq n C C' (graphFun G ∅) r hr hlen hops htop' hopr hbelow _ _ ?_ ?_
      · intro k
        exact mem_junk n G C k
      · intro k
        exact mem_junk n G C' k

theorem exists_top_form_preserving_tests (n : ℕ) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hG : G.edgeFinset.Nonempty)
    (hC : PEqualNP.TopForm.IsLeastAO G C) (Test : (Fin n → Bool) → Prop)
    (hTest : ∀ x, Test x → graphFun G ∅ x = false) (hOff : AndOffOn n C Test) :
    ∃ C' : Circuit, PEqualNP.TopForm.IsLeastAO G C' ∧ C'.size = C.size ∧
      (PEqualNP.TopForm.junk G C').card = (PEqualNP.TopForm.junk G C).card ∧
      PEqualNP.TopForm.TopForm G C' ∧ AndOffOn n C' Test :=
  main_ind_tests n G hG Test hTest _ C hC rfl hOff

lemma andOffOn_of_junk (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (Test : (Fin n → Bool) → Prop)
    (hTest : ∀ x, Test x → graphFun G ∅ x = false)
    (hJ : ∀ k ∈ PEqualNP.TopForm.junk G C,
      ∀ x, Test x → gateVal n C k x = false) : AndOffOn n C Test := by
  classical
  intro k hk hop x hx
  by_cases hj : k ∈ PEqualNP.TopForm.junk G C
  · exact hJ k hj x hx
  · have hbelow : ∀ y, wv n C y (n+k) = true → graphFun G ∅ y = true := by
      by_contra h
      exact hj ((mem_junk n G C k).2 ⟨hk,hop,h⟩)
    cases he : wv n C x (n+k)
    · rfl
    · have hf := hbelow x he
      rw [hTest x hx] at hf
      cases hf

lemma graph_unit_false (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (v : Fin n) : graphFun G ∅ (PEqualNP.SplitCount.unitInput v) = false := by
  have hn : ¬ ∃ a b : Fin n, G.Adj a b ∧
      PEqualNP.SplitCount.unitInput v a = true ∧ PEqualNP.SplitCount.unitInput v b = true := by
    rintro ⟨a,b,hab,ha,hb⟩
    have ha' : a = v := by simpa [PEqualNP.SplitCount.unitInput] using ha
    have hb' : b = v := by simpa [PEqualNP.SplitCount.unitInput] using hb
    subst a
    subst b
    exact G.irrefl hab
  simp [graphFun, hn]

theorem exists_top_form_preserving_unit_off (n : ℕ) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hG : G.edgeFinset.Nonempty)
    (hC : PEqualNP.TopForm.IsLeastAO G C)
    (hJ : ∀ k ∈ PEqualNP.TopForm.junk G C, ∀ v : Fin n,
      gateVal n C k (PEqualNP.SplitCount.unitInput v) = false) :
    ∃ C' : Circuit, PEqualNP.TopForm.IsLeastAO G C' ∧ C'.size = C.size ∧
      (PEqualNP.TopForm.junk G C').card = (PEqualNP.TopForm.junk G C).card ∧
      PEqualNP.TopForm.TopForm G C' ∧
      ∀ k ∈ PEqualNP.TopForm.junk G C', ∀ v : Fin n,
        gateVal n C' k (PEqualNP.SplitCount.unitInput v) = false := by
  let Test : (Fin n → Bool) → Prop := fun x => ∃ v, x = PEqualNP.SplitCount.unitInput v
  have hTest : ∀ x, Test x → graphFun G ∅ x = false := by
    rintro x ⟨v,rfl⟩
    exact graph_unit_false n G v
  have hOff : AndOffOn n C Test := andOffOn_of_junk n G C Test hTest (by
    rintro k hk x ⟨v,rfl⟩
    exact hJ k hk v)
  obtain ⟨C',h1,h2,h3,h4,h5⟩ := exists_top_form_preserving_tests n G C hG hC Test hTest hOff
  refine ⟨C',h1,h2,h3,h4,?_⟩
  intro k hk v
  obtain ⟨hklt,hop,_⟩ := (mem_junk n G C' k).1 hk
  exact h5 k hklt hop _ ⟨v,rfl⟩

lemma least_empty_graph_size_zero (n : ℕ) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hC : PEqualNP.TopForm.IsLeastAO G C)
    (hG : ¬ G.edgeFinset.Nonempty) : C.size = 0 := by
  have hnone (u v : Fin n) : ¬ G.Adj u v := by
    intro h
    apply hG
    exact ⟨s(u,v), by simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using h⟩
  let D : Circuit := ⟨[],n⟩
  have hD : PEqualNP.TopForm.IsAO2 n D := by
    simp [PEqualNP.TopForm.IsAO2, AndOrOnly, ReadsBack, D]
  have hfun : PEqualNP.MetaComplexity.circuitFun n D = graphFun G ∅ := by
    funext x
    change (List.ofFn x).getD n false = graphFun G ∅ x
    rw [List.getD_eq_default _ _ (by simp)]
    simp [graphFun, hnone]
  have hs := hC.2.2 D hD hfun
  have hz : C.size ≤ 0 := by simpa [D, Circuit.size] using hs
  omega

lemma edges_nonempty_of_junk_pos (n : ℕ) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hC : PEqualNP.TopForm.IsLeastAO G C)
    (hpos : 0 < (PEqualNP.TopForm.junk G C).card) : G.edgeFinset.Nonempty := by
  by_contra hG
  have hzero : C.gates.length = 0 := least_empty_graph_size_zero n G C hC hG
  simp [PEqualNP.TopForm.junk, PEqualNP.TopForm.gatesWhere, hzero] at hpos

/-- The exact two-junk premise in L-meta-5126 can be normalized without losing
the single-input rejection condition. No empty-graph exception remains. -/
theorem normalize_two_junk (n : ℕ) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hC : PEqualNP.TopForm.IsLeastAO G C)
    (hTwo : (PEqualNP.TopForm.junk G C).card = 2)
    (hJ : ∀ k ∈ PEqualNP.TopForm.junk G C, ∀ v : Fin n,
      gateVal n C k (PEqualNP.SplitCount.unitInput v) = false) :
    ∃ C' : Circuit, PEqualNP.TopForm.IsLeastAO G C' ∧ C'.size = C.size ∧
      (PEqualNP.TopForm.junk G C').card = 2 ∧ PEqualNP.TopForm.TopForm G C' ∧
      ∀ k ∈ PEqualNP.TopForm.junk G C', ∀ v : Fin n,
        gateVal n C' k (PEqualNP.SplitCount.unitInput v) = false := by
  have hG := edges_nonempty_of_junk_pos n G C hC (by omega)
  obtain ⟨C',h1,h2,h3,h4,h5⟩ := exists_top_form_preserving_unit_off n G C hG hC hJ
  exact ⟨C',h1,h2,h3.trans hTwo,h4,h5⟩

end Pnp5126TopForm
