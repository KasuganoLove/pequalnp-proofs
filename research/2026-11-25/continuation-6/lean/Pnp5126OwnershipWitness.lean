import PEqualNP.Defs

-- Wire-evaluation and monotonicity helpers reused from the checked 1031/2343 research.
-- Their upstream source is L_meta_2668, with attribution to L-meta-1499 / PR3112.
-- New result: with at most two dirty ANDs, dirt has a witness on at most three vertices.
namespace PEqualNP.Outside.Pnp5126OwnershipWitness

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt2 (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt2 gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt2 gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  exact List.getD_eq_getElem _ _ hj

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt2 _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

def OpMono (R : Bool → Bool → Prop) : Prop :=
  ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
    (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

lemma opMono_eq : OpMono Eq := by
  intro op _ l f g h
  rw [List.map_congr_left h]

lemma opMono_imp : OpMono (fun a b => a = true → b = true) := by
  intro op hop l f g h
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro h1 i hi; exact h i hi (h1 i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [ite_eq_right hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [ite_eq_left hlt]; exact h⟩

lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h'; exact ⟨hlt, h'⟩
    · rw [ite_eq_right hlt] at h'; cases h'
  · intro h i hi
    rw [ite_eq_left (h i hi).1]; exact (h i hi).2

lemma mono_ops {C : Circuit} (hM : Monotone2 C) :
    ∀ k < C.gates.length, (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or := by
  intro k hk
  exact (hM _ (gateAt_mem hk)).1

lemma wire_monotone (n : ℕ) (C : Circuit) (hM : Monotone2 C) (x y : Fin n → Bool)
    (hxy : ∀ i, x i = true → y i = true) :
    ∀ u, val C (List.ofFn x) u = true → val C (List.ofFn y) u = true := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    by_cases hun : u < n
    · rw [val_input (n := n) (by simp) hun, val_input (n := n) (by simp) hun]
      simpa [hun] using hxy ⟨u, hun⟩
    · by_cases hge : n + C.gates.length ≤ u
      · rw [val_ge (n := n) (by simp) hge]
        intro h; cases h
      · obtain ⟨k, rfl⟩ : ∃ k, u = n + k := ⟨u - n, by omega⟩
        have hk : k < C.gates.length := by omega
        rw [val_gate (n := n) (by simp) hk, val_gate (n := n) (by simp) hk]
        apply opMono_imp _ (mono_ops hM k hk)
        intro i hi
        by_cases hil : i < n + k
        · rw [ite_eq_left hil, ite_eq_left hil]
          exact ih i hil
        · rw [ite_eq_right hil, ite_eq_right hil]
          exact id


open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.SplitCount PEqualNP.CleanedNonEdge

lemma mono_of_ao {n : ℕ} {C : Circuit} (hA : IsAO2 n C) : Monotone2 C := by
  intro g hg
  exact ⟨hA.1 g hg,(hA.2.2 g hg).le⟩

lemma val_fn_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val C (List.ofFn x) w = x ⟨w,hw⟩ := by
  rw [val_input (n := n) (by simp) hw]
  simp [List.getD_eq_getElem?_getD,hw]

def setInput {n : ℕ} (S : Finset (Fin n)) : Fin n → Bool :=
  fun v => decide (v ∈ S)

lemma setInput_subset {n : ℕ} {S T : Finset (Fin n)} (h : S ⊆ T) :
    ∀ v, setInput S v = true → setInput T v = true := by
  intro v hv
  simpa only [setInput,decide_eq_true_eq] using h (by simpa only [setInput,decide_eq_true_eq] using hv)

lemma setInput_singleton {n : ℕ} (v : Fin n) : setInput {v} = unitInput v := by
  funext w
  simp [setInput,unitInput]

lemma graph_negative_subset {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x y : Fin n → Bool) (hxy : ∀ v, y v = true → x v = true)
    (hx : graphFun G ∅ x = false) : graphFun G ∅ y = false := by
  by_contra hy
  have hy' : graphFun G ∅ y = true := by simpa using hy
  simp only [graphFun,Finset.notMem_empty,false_and,exists_false,decide_false,
    Bool.false_or,decide_eq_true_eq] at hy'
  obtain ⟨u,v,huv,hu,hv⟩ := hy'
  have hx' : graphFun G ∅ x = true := by
    simp only [graphFun,Finset.notMem_empty,false_and,exists_false,decide_false,
      Bool.false_or,decide_eq_true_eq]
    exact ⟨u,v,huv,hxy u hu,hxy v hv⟩
  rw [hx] at hx'
  cases hx'

/-- Propagate a family of possible witnesses through arbitrary OR circuitry;
ANDs are exactly the places where an additional witness must be supplied. -/
lemma wire_seed {n : ℕ} {C : Circuit} (hA : IsAO2 n C) (x : Fin n → Bool)
    (m : ℕ) (hm : m ≤ C.gates.length) {α : Type} (seed : α → Fin n → Bool)
    (valid : α → Prop)
    (hinput : ∀ v, x v = true → ∃ a, valid a ∧ seed a v = true)
    (hand : ∀ k < m, (gateAt C k).op = GateOp.and →
      val C (List.ofFn x) (n+k) = true →
      ∃ a, valid a ∧ val C (List.ofFn (seed a)) (n+k) = true) :
    ∀ w < n+m, val C (List.ofFn x) w = true →
      ∃ a, valid a ∧ val C (List.ofFn (seed a)) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hx
    by_cases hraw : w < n
    · have hxv : x ⟨w,hraw⟩ = true := by
        rwa [val_fn_input C x w hraw] at hx
      obtain ⟨a,ha,hav⟩ := hinput ⟨w,hraw⟩ hxv
      refine ⟨a,ha,?_⟩
      rwa [val_fn_input C (seed a) w hraw]
    · obtain ⟨k,rfl⟩ : ∃ k, w = n+k := ⟨w-n,by omega⟩
      have hk : k < m := by omega
      have hkC : k < C.gates.length := by omega
      rcases hA.1 _ (gateAt_mem hkC) with ha | ho
      · exact hand k hk ha hx
      · obtain ⟨u,hu,huLt,huVal⟩ := (val_or (n := n) (by simp) hkC ho).mp hx
        obtain ⟨a,ha,haw⟩ := ih u huLt (by omega) huVal
        exact ⟨a,ha,(val_or (n := n) (by simp) hkC ho).mpr ⟨u,hu,huLt,haw⟩⟩

/-- Before any AND firing on x, every firing wire has a singleton witness. -/
lemma before_first_and {n : ℕ} {C : Circuit} (hA : IsAO2 n C) (x : Fin n → Bool)
    (g : ℕ) (hg : g ≤ C.gates.length)
    (hnone : ∀ k < g, (gateAt C k).op = GateOp.and →
      val C (List.ofFn x) (n+k) = false) :
    ∀ w < n+g, val C (List.ofFn x) w = true →
      ∃ v, x v = true ∧ val C (List.ofFn (unitInput v)) w = true := by
  apply wire_seed hA x g hg unitInput (fun v => x v = true)
  · intro v hv
    exact ⟨v,hv,by simp [unitInput]⟩
  · intro k hk hop hkx
    rw [hnone k hk hop] at hkx
    cases hkx


lemma unit_le_set {n : ℕ} {S : Finset (Fin n)} {v : Fin n} (hv : v ∈ S) :
    ∀ w, unitInput v w = true → setInput S w = true := by
  intro w hw
  have he : w = v := by simpa [unitInput] using hw
  subst w
  simpa [setInput] using hv

/-- An AND with no earlier AND firing on x has a witness on two inputs. -/
lemma first_and_pair {n : ℕ} {C : Circuit} (hA : IsAO2 n C) (x : Fin n → Bool)
    (g : ℕ) (hg : g < C.gates.length) (hop : (gateAt C g).op = GateOp.and)
    (hgx : val C (List.ofFn x) (n+g) = true)
    (hnone : ∀ k < g, (gateAt C k).op = GateOp.and →
      val C (List.ofFn x) (n+k) = false) :
    ∃ S : Finset (Fin n), S.card ≤ 2 ∧ (∀ v ∈ S, x v = true) ∧
      val C (List.ofFn (setInput S)) (n+g) = true := by
  obtain ⟨a,b,hab⟩ := List.length_eq_two.mp (hA.2.2 _ (gateAt_mem hg))
  have hv := (val_and (n := n) (by simp) hg hop).mp hgx
  obtain ⟨ha,hax⟩ := hv a (by simp [hab])
  obtain ⟨hb,hbx⟩ := hv b (by simp [hab])
  obtain ⟨u,hu,hua⟩ := before_first_and hA x g hg.le hnone a ha hax
  obtain ⟨v,hv,hvb⟩ := before_first_and hA x g hg.le hnone b hb hbx
  refine ⟨{u,v},Finset.card_le_two,?_,?_⟩
  · intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact hu
    · have hwv : w = v := Finset.mem_singleton.mp hw
      simpa only [hwv] using hv
  · have hua' := wire_monotone n C (mono_of_ao hA) (unitInput u) (setInput {u,v})
        (unit_le_set (by simp)) a hua
    have hvb' := wire_monotone n C (mono_of_ao hA) (unitInput v) (setInput {u,v})
        (unit_le_set (by simp)) b hvb
    apply (val_and (n := n) (by simp) hg hop).mpr
    intro w hw
    rw [hab] at hw
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl | rfl
    · exact ⟨ha,hua'⟩
    · exact ⟨hb,hvb'⟩

/-- With a single earlier true AND available as a shared seed, another true AND
has a witness of size at most three. The same seed is reused in both operands. -/
lemma second_and_triple {n : ℕ} {C : Circuit} (hA : IsAO2 n C) (x : Fin n → Bool)
    (g t : ℕ) (ht : t < C.gates.length) (hop : (gateAt C t).op = GateOp.and)
    (htx : val C (List.ofFn x) (n+t) = true)
    (S : Finset (Fin n)) (hScard : S.card ≤ 2) (hSx : ∀ v ∈ S, x v = true)
    (hSg : val C (List.ofFn (setInput S)) (n+g) = true)
    (honly : ∀ k < t, (gateAt C k).op = GateOp.and →
      val C (List.ofFn x) (n+k) = true → k = g) :
    ∃ T : Finset (Fin n), T.card ≤ 3 ∧ (∀ v ∈ T, x v = true) ∧
      val C (List.ofFn (setInput T)) (n+t) = true := by
  let support : Option (Fin n) → Finset (Fin n) := fun a =>
    match a with | none => S | some v => {v}
  let valid : Option (Fin n) → Prop := fun a =>
    match a with | none => True | some v => x v = true
  have hseed : ∀ w < n+t, val C (List.ofFn x) w = true →
      ∃ a, valid a ∧ val C (List.ofFn (setInput (support a))) w = true := by
    apply wire_seed hA x t ht.le (fun a => setInput (support a)) valid
    · intro v hv
      exact ⟨some v,hv,by simp [support,setInput]⟩
    · intro k hk hop hkx
      have he : k = g := honly k hk hop hkx
      exact ⟨none,True.intro,by simpa only [support,he] using hSg⟩
  obtain ⟨a,b,hab⟩ := List.length_eq_two.mp (hA.2.2 _ (gateAt_mem ht))
  have hv := (val_and (n := n) (by simp) ht hop).mp htx
  obtain ⟨ha,hax⟩ := hv a (by simp [hab])
  obtain ⟨hb,hbx⟩ := hv b (by simp [hab])
  obtain ⟨sa,hsa,hva⟩ := hseed a ha hax
  obtain ⟨sb,hsb,hvb⟩ := hseed b hb hbx
  let T := support sa ∪ support sb
  have hTcard : T.card ≤ 3 := by
    cases sa with
    | none =>
      cases sb with
      | none => simpa [T,support] using (hScard.trans (by decide : 2 ≤ 3))
      | some v =>
        have hbnd := Finset.card_union_le S {v}
        simp only [Finset.card_singleton] at hbnd
        change (S ∪ {v}).card ≤ 3
        omega
    | some u =>
      cases sb with
      | none =>
        have hbnd := Finset.card_union_le ({u} : Finset (Fin n)) S
        simp only [Finset.card_singleton] at hbnd
        change ({u} ∪ S).card ≤ 3
        omega
      | some v =>
        have hbnd := Finset.card_union_le ({u} : Finset (Fin n)) {v}
        simp only [Finset.card_singleton] at hbnd
        change (({u} : Finset (Fin n)) ∪ {v}).card ≤ 3
        omega
  have hsupport : ∀ a, valid a → ∀ v ∈ support a, x v = true := by
    intro a ha v hv
    cases a with
    | none => exact hSx v hv
    | some u =>
      have he : v = u := by simpa [support] using hv
      subst v
      exact ha
  refine ⟨T,hTcard,?_,?_⟩
  · intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact hsupport sa hsa v hv
    · exact hsupport sb hsb v hv
  · have hva' := wire_monotone n C (mono_of_ao hA) (setInput (support sa)) (setInput T)
        (setInput_subset Finset.subset_union_left) a hva
    have hvb' := wire_monotone n C (mono_of_ao hA) (setInput (support sb)) (setInput T)
        (setInput_subset Finset.subset_union_right) b hvb
    apply (val_and (n := n) (by simp) ht hop).mpr
    intro w hw
    rw [hab] at hw
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl | rfl
    · exact ⟨ha,hva'⟩
    · exact ⟨hb,hvb'⟩


lemma mem_junk_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (k : ℕ) : k ∈ junk G C ↔
      k < C.gates.length ∧ (gateAt C k).op = GateOp.and ∧
        ∃ x, val C (List.ofFn x) (n+k) = true ∧ graphFun G ∅ x = false := by
  change (k ∈ (Finset.range C.gates.length).filter (fun j => IsDirtyAnd n G C j)) ↔ _
  rw [Finset.mem_filter,Finset.mem_range]
  change (k < C.gates.length ∧ (gateAt C k).op = GateOp.and ∧
    k < C.gates.length ∧ ∃ x, val C (List.ofFn x) (n+k) = true ∧ graphFun G ∅ x = false) ↔ _
  constructor
  · rintro ⟨hk,hop,_,x,hv,hf⟩
    exact ⟨hk,hop,x,hv,hf⟩
  · rintro ⟨hk,hop,x,hv,hf⟩
    exact ⟨hk,hop,hk,x,hv,hf⟩

/-- Two possible dirty AND gates suffice to bound every dirty witness by three
vertices; the witness remains a subset of the original negative input. -/
theorem two_junk_support_le_three {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hA : IsAO2 n C) (g t : ℕ) (hgt : g < t)
    (hJ : junk G C = {g,t}) (k : ℕ) (hk : k ∈ junk G C) :
    ∃ S : Finset (Fin n), S.card ≤ 3 ∧ graphFun G ∅ (setInput S) = false ∧
      gateVal n C k (setInput S) = true := by
  obtain ⟨hkC,hkop,x,hkx,hxF⟩ := (mem_junk_iff G C k).mp hk
  have honly (j : ℕ) (hj : j < C.gates.length) (hjo : (gateAt C j).op = GateOp.and)
      (hjx : val C (List.ofFn x) (n+j) = true) : j = g ∨ j = t := by
    have hjJ : j ∈ junk G C := (mem_junk_iff G C j).mpr ⟨hj,hjo,x,hjx,hxF⟩
    rw [hJ] at hjJ
    simpa only [Finset.mem_insert,Finset.mem_singleton] using hjJ
  have finish (S : Finset (Fin n)) (hc : S.card ≤ 3) (hSx : ∀ v ∈ S, x v = true)
      (hSk : val C (List.ofFn (setInput S)) (n+k) = true) :
      ∃ T : Finset (Fin n), T.card ≤ 3 ∧ graphFun G ∅ (setInput T) = false ∧
        gateVal n C k (setInput T) = true := by
    refine ⟨S,hc,?_,hSk⟩
    exact graph_negative_subset G x (setInput S)
      (fun v hv => hSx v (by simpa only [setInput,decide_eq_true_eq] using hv)) hxF
  rcases honly k hkC hkop hkx with hkg | hkt
  · subst k
    have hnone : ∀ j < g, (gateAt C j).op = GateOp.and →
        val C (List.ofFn x) (n+j) = false := by
      intro j hj hop
      cases he : val C (List.ofFn x) (n+j) with
      | false => rfl
      | true => rcases honly j (by omega) hop he with heq | heq <;> omega
    obtain ⟨S,hc,hSx,hSg⟩ := first_and_pair hA x g hkC hkop hkx hnone
    exact finish S (by omega) hSx hSg
  · subst k
    by_cases hgx : val C (List.ofFn x) (n+g) = true
    · have hgC : g < C.gates.length := by omega
      have hgop : (gateAt C g).op = GateOp.and := by
        have hgJ : g ∈ junk G C := by rw [hJ]; simp
        exact ((mem_junk_iff G C g).mp hgJ).2.1
      have hnone : ∀ j < g, (gateAt C j).op = GateOp.and →
          val C (List.ofFn x) (n+j) = false := by
        intro j hj hop
        cases he : val C (List.ofFn x) (n+j) with
        | false => rfl
        | true => rcases honly j (by omega) hop he with heq | heq <;> omega
      obtain ⟨S,hc,hSx,hSg⟩ := first_and_pair hA x g hgC hgop hgx hnone
      have htOnly : ∀ j < t, (gateAt C j).op = GateOp.and →
          val C (List.ofFn x) (n+j) = true → j = g := by
        intro j hj hop hjx
        rcases honly j (by omega) hop hjx with heq | heq
        · exact heq
        · omega
      obtain ⟨T,hcT,hTx,hTt⟩ := second_and_triple hA x g t hkC hkop hkx S hc hSx hSg htOnly
      exact finish T hcT hTx hTt
    · have hnone : ∀ j < t, (gateAt C j).op = GateOp.and →
          val C (List.ofFn x) (n+j) = false := by
        intro j hj hop
        cases he : val C (List.ofFn x) (n+j) with
        | false => rfl
        | true =>
          rcases honly j (by omega) hop he with heq | heq
          · exact False.elim (hgx (heq ▸ he))
          · omega
      obtain ⟨S,hc,hSx,hSt⟩ := first_and_pair hA x t hkC hkop hkx hnone
      exact finish S (by omega) hSx hSt


lemma wire_zero {n : ℕ} {C : Circuit} (hA : IsAO2 n C) :
    ∀ w, val C (List.ofFn (fun _ : Fin n => false)) w = false := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hraw : w < n
    · exact val_fn_input C _ w hraw
    by_cases hfar : n+C.gates.length ≤ w
    · exact val_ge (n := n) (by simp) hfar
    obtain ⟨k,rfl⟩ : ∃ k, w = n+k := ⟨w-n,by omega⟩
    have hk : k < C.gates.length := by omega
    obtain ⟨a,b,hab⟩ := List.length_eq_two.mp (hA.2.2 _ (gateAt_mem hk))
    have ha : a < n+k := hA.2.1 k hk a (by simp [hab])
    have hb : b < n+k := hA.2.1 k hk b (by simp [hab])
    rw [val_gate (n := n) (by simp) hk]
    rcases hA.1 _ (gateAt_mem hk) with hop | hop <;>
      simp only [hop,hab,List.map_cons,List.map_nil,ite_eq_left ha,ite_eq_left hb,ih a ha,ih b hb,
        GateOp.eval,List.all_cons,List.all_nil,List.any_cons,List.any_nil,
        Bool.false_and,Bool.false_or,id_eq]

lemma support_card_lower {n : ℕ} {C : Circuit} (hA : IsAO2 n C)
    (k : ℕ) (hoff : ∀ v : Fin n, gateVal n C k (unitInput v) = false)
    (S : Finset (Fin n)) (hS : gateVal n C k (setInput S) = true) : 2 ≤ S.card := by
  by_contra hcard
  have hle : S.card ≤ 1 := by omega
  by_cases hempty : S = ∅
  · subst S
    have he : setInput (∅ : Finset (Fin n)) = fun _ => false := by
      funext v
      simp [setInput]
    rw [he] at hS
    have hz := wire_zero hA (n+k)
    change gateVal n C k (fun _ => false) = false at hz
    rw [hz] at hS
    cases hS
  · obtain ⟨u,hu⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    have heq : S = {u} := by
      apply Finset.ext
      intro v
      constructor
      · intro hv
        exact Finset.mem_singleton.mpr ((Finset.card_le_one.mp hle) v hv u hu)
      · intro hv
        have hvu := Finset.mem_singleton.mp hv
        simpa only [hvu] using hu
    rw [heq,setInput_singleton,hoff u] at hS
    cases hS

/-- Every dirty AND in the exact two-junk, singleton-off setting has a negative
witness on either two or three original vertices. No minimality, coloring, or
cycle assumption is required. -/
theorem two_junk_off_witness {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hA : IsAO2 n C) (hcard : (junk G C).card = 2)
    (hoff : ∀ k ∈ junk G C, ∀ v : Fin n, gateVal n C k (unitInput v) = false) :
    ∀ k ∈ junk G C, ∃ S : Finset (Fin n), (S.card = 2 ∨ S.card = 3) ∧
      graphFun G ∅ (setInput S) = false ∧ gateVal n C k (setInput S) = true := by
  obtain ⟨g,t,hne,hJ⟩ := Finset.card_eq_two.mp hcard
  have horder : ∃ a b : ℕ, a < b ∧ junk G C = {a,b} := by
    rcases lt_or_gt_of_ne hne with hgt | htg
    · exact ⟨g,t,hgt,hJ⟩
    · exact ⟨t,g,htg,by simpa [Finset.pair_comm] using hJ⟩
  obtain ⟨g,t,hgt,hJ⟩ := horder
  intro k hk
  obtain ⟨S,hScard,hSF,hSk⟩ := two_junk_support_le_three G C hA g t hgt hJ k hk
  have hlow := support_card_lower hA k (hoff k hk) S hSk
  exact ⟨S,by omega,hSF,hSk⟩


/-- The earlier of the two junk gates always has an independent pair witness. -/
theorem two_junk_first_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hA : IsAO2 n C) (g t : ℕ) (hgt : g < t)
    (hJ : junk G C = {g,t})
    (hoff : ∀ v : Fin n, gateVal n C g (unitInput v) = false) :
    ∃ S : Finset (Fin n), S.card = 2 ∧ graphFun G ∅ (setInput S) = false ∧
      gateVal n C g (setInput S) = true := by
  have hgJ : g ∈ junk G C := by rw [hJ]; simp
  obtain ⟨hgC,hop,x,hgx,hxF⟩ := (mem_junk_iff G C g).mp hgJ
  have hnone : ∀ j < g, (gateAt C j).op = GateOp.and →
      val C (List.ofFn x) (n+j) = false := by
    intro j hj hjo
    cases he : val C (List.ofFn x) (n+j) with
    | false => rfl
    | true =>
      have hjJ : j ∈ junk G C := (mem_junk_iff G C j).mpr ⟨by omega,hjo,x,he,hxF⟩
      rw [hJ] at hjJ
      simp only [Finset.mem_insert,Finset.mem_singleton] at hjJ
      rcases hjJ with hjg | hjt <;> omega
  obtain ⟨S,hc,hSx,hSg⟩ := first_and_pair hA x g hgC hop hgx hnone
  have hlow := support_card_lower hA g hoff S hSg
  refine ⟨S,by omega,?_,hSg⟩
  exact graph_negative_subset G x (setInput S)
    (fun v hv => hSx v (by simpa only [setInput,decide_eq_true_eq] using hv)) hxF

/-- Any higher-degree dirt of the second gate is shared with the first gate.
If the later gate rejects every independent pair, some independent triple makes
both gates fire. -/
theorem second_pair_or_shared_triple {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hA : IsAO2 n C) (g t : ℕ) (hgt : g < t)
    (hJ : junk G C = {g,t})
    (hoff : ∀ k ∈ junk G C, ∀ v : Fin n, gateVal n C k (unitInput v) = false) :
    (∃ S : Finset (Fin n), S.card = 2 ∧ graphFun G ∅ (setInput S) = false ∧
      gateVal n C t (setInput S) = true) ∨
    (∃ S : Finset (Fin n), S.card = 3 ∧ graphFun G ∅ (setInput S) = false ∧
      gateVal n C g (setInput S) = true ∧ gateVal n C t (setInput S) = true) := by
  by_cases hpair : ∃ S : Finset (Fin n), S.card = 2 ∧ graphFun G ∅ (setInput S) = false ∧
      gateVal n C t (setInput S) = true
  · exact Or.inl hpair
  apply Or.inr
  have htJ : t ∈ junk G C := by rw [hJ]; simp
  have hcard : (junk G C).card = 2 := by rw [hJ]; simp [Nat.ne_of_lt hgt]
  obtain ⟨S,hScard,hSF,hSt⟩ := two_junk_off_witness G C hA hcard hoff t htJ
  have hSthree : S.card = 3 := hScard.resolve_left (fun h => hpair ⟨S,h,hSF,hSt⟩)
  refine ⟨S,hSthree,hSF,?_,hSt⟩
  by_contra hgfalse
  have hgfalse' : gateVal n C g (setInput S) = false := by simpa using hgfalse
  obtain ⟨htC,htop,_⟩ := (mem_junk_iff G C t).mp htJ
  have hnone : ∀ j < t, (gateAt C j).op = GateOp.and →
      val C (List.ofFn (setInput S)) (n+j) = false := by
    intro j hj hop
    cases he : val C (List.ofFn (setInput S)) (n+j) with
    | false => rfl
    | true =>
      have hjJ : j ∈ junk G C := (mem_junk_iff G C j).mpr ⟨by omega,hop,setInput S,he,hSF⟩
      rw [hJ] at hjJ
      simp only [Finset.mem_insert,Finset.mem_singleton] at hjJ
      rcases hjJ with hjg | hjt
      · subst j
        change gateVal n C g (setInput S) = true at he
        rw [hgfalse'] at he
        cases he
      · omega
  obtain ⟨T,hTc,hTx,hTt⟩ := first_and_pair hA (setInput S) t htC htop hSt hnone
  have hTlow := support_card_lower hA t (hoff t htJ) T hTt
  apply hpair
  refine ⟨T,by omega,?_,hTt⟩
  exact graph_negative_subset G (setInput S) (setInput T)
    (fun v hv => hTx v (by simpa only [setInput,decide_eq_true_eq] using hv)) hSF

end PEqualNP.Outside.Pnp5126OwnershipWitness
