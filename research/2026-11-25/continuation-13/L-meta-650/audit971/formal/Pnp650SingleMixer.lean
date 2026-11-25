import Pnp650TransferCore

/-!
Local research for held L-meta-650 / its negative twin.
The structural transfer APIs are the attributed generic slice in Pnp650TransferCore.
New result: a bipartite C4-free target with no centreless tops and exactly one
exceptional OR has at most one uncovered edge, assuming top shape and positive
edge-to-top trace. This is not a proof of the full task.
-/
namespace PEqualNP.Outside.Pnp650SingleMixer

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.Pnp650TransferCore

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

lemma common_unique (h4 : NoFourCycle G) {a b x y : Fin n} (ab : a ≠ b)
    (ax : G.Adj a x) (bx : G.Adj b x) (ay : G.Adj a y) (by' : G.Adj b y) : x = y := by
  apply Finset.card_le_one.mp (h4 a b ab)
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ax, bx⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ay, by'⟩

omit [DecidableRel G.Adj] in
lemma neighbors_color (color : Fin n → Bool)
    (hcolor : ∀ a b, G.Adj a b → color a ≠ color b)
    {c a b : Fin n} (ha : G.Adj c a) (hb : G.Adj c b) : color a = color b := by
  have h1 := hcolor c a ha
  have h2 := hcolor c b hb
  cases hc : color c <;> cases hx : color a <;> cases hy : color b <;> simp_all

lemma pair_negative {a b : Fin n} (h : ¬ G.Adj a b) : graphFun G ∅ (pairInput a b) = false := by
  apply Bool.eq_false_iff.mpr
  intro yes
  obtain ⟨u,v,uv,hu,hv⟩ : ∃ u v, G.Adj u v ∧ pairInput a b u = true ∧ pairInput a b v = true := by
    simpa [graphFun] using yes
  simp only [pairInput, decide_eq_true_eq] at hu hv
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · exact G.irrefl uv
  · exact h uv
  · exact h uv.symm
  · exact G.irrefl uv

lemma mixing_subset_exception (C : Circuit) : mixing G C ⊆ orN G C \ lam G C := by
  intro m hm
  obtain ⟨orn, different⟩ := Finset.mem_filter.mp hm
  refine Finset.mem_sdiff.mpr ⟨orn, ?_⟩
  intro hl
  obtain ⟨_, nonempty0, nonempty1, _⟩ := Finset.mem_filter.mp hl
  rw [Finset.nonempty_iff_ne_empty] at nonempty0 nonempty1
  apply different
  exact propext (by simp [nonempty0, nonempty1])

lemma force_guard_on_two (C : Circuit) (ao : IsAO2 n C) (m : ℕ)
    (single : orN G C \ lam G C = {m}) (allraw : centreless G C = ∅)
    (shape : ∀ a ∈ tops G C, ∀ l ∈ side C a (0 : Fin 2), ∀ r ∈ side C a (1 : Fin 2), G.Adj l r)
    (w a z b : Fin n) (missing : s(w,a) ∈ Ustar G C)
    (raw : (orIn n C (n+m)).Nonempty)
    (pos1 : gateVal n C m (pairInput w a) = true)
    (pos2 : gateVal n C m (pairInput z b) = true)
    (abs1 : ∀ r ∈ orIn n C (n+m), pairInput w a r = false)
    (abs2 : ∀ r ∈ orIn n C (n+m), pairInput z b r = false)
    (guard : ∀ y : Fin n → Bool, gateVal n C m y = true → y w = true → graphFun G ∅ y = true)
    (y : Fin n → Bool) (yw : y w = true)
    (pins : ∀ i, pairInput w a i = true → pairInput z b i = true → y i = true)
    (clauses : ∀ A : Finset (Fin n), A.Nonempty →
      (∃ c, ∀ v ∈ A, (G.deleteEdges (Ustar G C : Set (Sym2 (Fin n)))).Adj c v) →
      (∃ v ∈ A, pairInput w a v = true) → (∃ v ∈ A, pairInput z b v = true) →
      ∃ v ∈ A, y v = true) : graphFun G ∅ y = true := by
  let tests := [pairInput w a, pairInput z b]
  have member1 : pairInput w a ∈ tests := by simp [tests]
  have member2 : pairInput z b ∈ tests := by simp [tests]
  have lift := LocalMixerTransfer.prefix_transfer G C ao m single allraw shape tests w a
    missing member1 y (fun i h => pins i (h _ member1) (h _ member2))
    (fun A ne cover h => clauses A ne cover (h _ member1) (h _ member2))
  apply guard y (LocalMixerTransfer.mixer_truth G C ao m single tests raw ?_ ?_ y lift) yw
  · intro x hx
    simp [tests] at hx
    rcases hx with rfl | rfl
    · exact pos1
    · exact pos2
  · intro x hx
    simp [tests] at hx
    rcases hx with rfl | rfl
    · exact abs1
    · exact abs2

lemma routed_edges_equal (h4 : NoFourCycle G) (color : Fin n → Bool)
    (hcolor : ∀ a b, G.Adj a b → color a ≠ color b)
    (C : Circuit) (ao : IsAO2 n C) (m : ℕ)
    (single : orN G C \ lam G C = {m}) (allraw : centreless G C = ∅)
    (shape : ∀ a ∈ tops G C, ∀ l ∈ side C a (0 : Fin 2), ∀ r ∈ side C a (1 : Fin 2), G.Adj l r)
    (w a z b r : Fin n) (e1 : s(w,a) ∈ Ustar G C) (e2 : s(z,b) ∈ Ustar G C)
    (rw : (G.deleteEdges (Ustar G C : Set (Sym2 (Fin n)))).Adj r w)
    (rz : (G.deleteEdges (Ustar G C : Set (Sym2 (Fin n)))).Adj r z)
    (raw : (orIn n C (n+m)).Nonempty)
    (pos1 : gateVal n C m (pairInput w a) = true)
    (pos2 : gateVal n C m (pairInput z b) = true)
    (abs1 : ∀ q ∈ orIn n C (n+m), pairInput w a q = false)
    (abs2 : ∀ q ∈ orIn n C (n+m), pairInput z b q = false)
    (guard : ∀ y : Fin n → Bool, gateVal n C m y = true → y w = true → graphFun G ∅ y = true) :
    s(w,a) = s(z,b) := by
  have wa : G.Adj w a := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp e1).1
  have zb : G.Adj z b := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp e2).1
  have rw' := (SimpleGraph.deleteEdges_adj.mp rw).1
  have rz' := (SimpleGraph.deleteEdges_adj.mp rz).1
  have rna : r ≠ a := by
    intro eq
    subst a
    exact (SimpleGraph.deleteEdges_adj.mp rw).2 (by simpa only [Finset.mem_coe, Sym2.eq_swap] using e1)
  have rnb : r ≠ b := by
    intro eq
    subst b
    exact (SimpleGraph.deleteEdges_adj.mp rz).2 (by simpa only [Finset.mem_coe, Sym2.eq_swap] using e2)
  by_cases wz : w = z
  · subst z
    by_cases ab : a = b
    · subst b
      rfl
    have yes : graphFun G ∅ (pairInput w w) = true := by
      apply force_guard_on_two G C ao m single allraw shape w a w b e1 raw pos1 pos2 abs1 abs2 guard
        (pairInput w w) (by simp [pairInput])
      · intro i h1 h2
        simp only [pairInput, decide_eq_true_eq] at h1 h2 ⊢
        rcases h1 with rfl | rfl
        · exact Or.inl rfl
        · rcases h2 with h | h
          · exact Or.inl h
          · exact (ab h).elim
      · intro A _ cover hit1 hit2
        obtain ⟨c,hc⟩ := cover
        obtain ⟨p,hp,px⟩ := hit1
        obtain ⟨q,hq,qx⟩ := hit2
        simp only [pairInput, decide_eq_true_eq] at px qx
        rcases px with px | px
        · subst p
          exact ⟨w,hp,by simp [pairInput]⟩
        · subst p
          rcases qx with qx | qx
          · subst q
            exact ⟨w,hq,by simp [pairInput]⟩
          · subst q
            have ca := (SimpleGraph.deleteEdges_adj.mp (hc a hp)).1
            have cb := (SimpleGraph.deleteEdges_adj.mp (hc b hq)).1
            have wc : w = c := common_unique G h4 ab wa.symm zb.symm ca.symm cb.symm
            subst c
            exact ((SimpleGraph.deleteEdges_adj.mp (hc a hp)).2 e1).elim
    have no := pair_negative G (show ¬G.Adj w w from G.irrefl)
    simp [no] at yes
  · have cwz : color w = color z := neighbors_color G color hcolor rw' rz'
    have nwb : w ≠ b := by
      intro eq
      apply hcolor z b zb
      exact cwz.symm.trans (congrArg color eq)
    have naz : a ≠ z := by
      intro eq
      apply hcolor w a wa
      exact cwz.trans (congrArg color eq).symm
    have nab : a ≠ b := by
      intro eq
      have rb : r = b := common_unique G h4 wz rw'.symm rz'.symm (eq ▸ wa) zb
      exact rnb rb
    have cross : ¬ G.Adj w b := by
      intro wb
      exact rnb (common_unique G h4 wz rw'.symm rz'.symm wb zb)
    have yes : graphFun G ∅ (pairInput w b) = true := by
      apply force_guard_on_two G C ao m single allraw shape w a z b e1 raw pos1 pos2 abs1 abs2 guard
        (pairInput w b) (by simp [pairInput])
      · intro i h1 h2
        simp only [pairInput, decide_eq_true_eq] at h1 h2 ⊢
        rcases h1 with rfl | rfl
        · exact Or.inl rfl
        · rcases h2 with h | h
          · exact (naz h).elim
          · exact (nab h).elim
      · intro A _ cover hit1 hit2
        obtain ⟨c,hc⟩ := cover
        obtain ⟨p,hp,px⟩ := hit1
        obtain ⟨q,hq,qx⟩ := hit2
        simp only [pairInput, decide_eq_true_eq] at px qx
        rcases px with px | px
        · subst p
          exact ⟨w,hp,by simp [pairInput]⟩
        · subst p
          rcases qx with qx | qx
          · subst q
            have caz : color a = color z := neighbors_color G color hcolor
              (SimpleGraph.deleteEdges_adj.mp (hc a hp)).1 (SimpleGraph.deleteEdges_adj.mp (hc z hq)).1
            exact (hcolor w a wa (cwz.trans caz.symm)).elim
          · subst q
            exact ⟨b,hq,by simp [pairInput]⟩
    have no := pair_negative G cross
    simp [no] at yes

lemma pair_swap (u v : Fin n) : pairInput v u = pairInput u v := by
  funext i
  simp only [pairInput, or_comm]

/-- The complete one-exception subcase; no size or junk-count premise is used. -/
theorem single_exception_ustar_card_le_one (h4 : NoFourCycle G) (color : Fin n → Bool)
    (hcolor : ∀ a b, G.Adj a b → color a ≠ color b)
    (C : Circuit) (ao : IsAO2 n C) (m : ℕ)
    (single : orN G C \ lam G C = {m}) (allraw : centreless G C = ∅)
    (shape : ∀ a ∈ tops G C, ∀ l ∈ side C a (0 : Fin 2), ∀ r ∈ side C a (1 : Fin 2), G.Adj l r)
    (trace : ∀ u v : Fin n, s(u,v) ∈ Ustar G C →
      ∃ a ∈ tops G C, gateVal n C a (pairInput u v) = true) :
    (Ustar G C).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro e he f hf
  induction e using Sym2.inductionOn with | hf u v
  induction f using Sym2.inductionOn with | hf u' v'
  obtain ⟨top, htop, yes⟩ := trace u v he
  obtain ⟨k,hk,_,_⟩ := LocalMixCore.top_needs_mixing G C ao htop (shape top htop)
    (LocalReceiver.sides_nonempty allraw htop) he yes
  have km : k = m := by
    have mem := mixing_subset_exception G C hk
    simpa only [single, Finset.mem_singleton] using mem
  have singleMix : mixing G C = {m} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨km ▸ hk, ?_⟩
    intro j hj
    have mem := mixing_subset_exception G C hj
    simpa only [single, Finset.mem_singleton] using mem
  have route (u v : Fin n) (e : s(u,v) ∈ Ustar G C) :
      ∃ w a : Fin n, s(w,a) = s(u,v) ∧ (orIn n C (n+m)).Nonempty ∧
        gateVal n C m (pairInput w a) = true ∧
        (∀ r ∈ orIn n C (n+m), pairInput w a r = false) ∧
        (∀ r ∈ orIn n C (n+m), (G.deleteEdges (Ustar G C : Set (Sym2 (Fin n)))).Adj r w) ∧
        (∀ y : Fin n → Bool, gateVal n C m y = true → y w = true → graphFun G ∅ y = true) := by
    obtain ⟨top, htop, yes⟩ := trace u v e
    obtain ⟨raw,pos,abs,w,won,cov,guard⟩ :=
      LocalSingleMix.routed_single G C ao m singleMix allraw htop (shape top htop) e yes
    simp only [pairInput, decide_eq_true_eq] at won
    rcases won with won | won
    · subst w
      exact ⟨u,v,rfl,raw,pos,abs,cov,guard⟩
    · subst w
      exact ⟨v,u,Sym2.eq_swap,raw,by simpa only [pair_swap] using pos,
        by simpa only [pair_swap] using abs,cov,guard⟩
  obtain ⟨w,a,eqa,raw,pos1,abs1,cov1,guard⟩ := route u v he
  obtain ⟨z,b,eqb,_,pos2,abs2,cov2,_⟩ := route u' v' hf
  obtain ⟨r,hr⟩ := raw
  have same := routed_edges_equal G h4 color hcolor C ao m single allraw shape w a z b r
    (eqa ▸ he) (eqb ▸ hf) (cov1 r hr) (cov2 r hr) ⟨r,hr⟩ pos1 pos2 abs1 abs2 guard
  exact eqa.symm.trans (same.trans eqb)

end PEqualNP.Outside.Pnp650SingleMixer
