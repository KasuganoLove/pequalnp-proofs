import PEqualNP.Defs

-- Physical erasure and monotonicity helpers adapted from upstream L_meta_2668.
-- That file credits the bypass construction to willakone, L-meta-1499, PR 3112.
-- The new statements below isolate a safe local alias in the exact Monotone2 model.
namespace PEqualNP.Outside.Pnp1031Pruning

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
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

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

lemma val_prefix {n : ℕ} {C D : Circuit} {x : List Bool} (hx : x.length = n) {m : ℕ}
    (hmC : m ≤ C.gates.length) (hmD : m ≤ D.gates.length)
    (hg : ∀ k < m, gateAt D k = gateAt C k) : ∀ u, u < n + m → val D x u = val C x u := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hu
    by_cases hun : u < n
    · rw [val_input hx hun, val_input hx hun]
    · obtain ⟨k, rfl⟩ : ∃ k, u = n + k := ⟨u - n, by omega⟩
      have hk : k < m := by omega
      rw [val_gate hx (by omega), val_gate hx (by omega), hg k hk]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < n + k
      · rw [ite_eq_left hi, ite_eq_left hi]; exact ih i hi (by omega)
      · rw [ite_eq_right hi, ite_eq_right hi]

def aliasWire (w i u : ℕ) : ℕ := if u = w then i else if w < u then u - 1 else u

def aliasGate (w i : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (aliasWire w i)⟩

def bypass (n : ℕ) (C : Circuit) (r i : ℕ) : Circuit :=
  ⟨(List.range (C.gates.length - 1)).map (fun k =>
      if k < r then gateAt C k else aliasGate (n + r) i (gateAt C (k + 1))),
    aliasWire (n + r) i C.output⟩

lemma bypass_length (n : ℕ) (C : Circuit) (r i : ℕ) :
    (bypass n C r i).gates.length = C.gates.length - 1 := by simp [bypass]

lemma bypass_output (n : ℕ) (C : Circuit) (r i : ℕ) :
    (bypass n C r i).output = aliasWire (n + r) i C.output := rfl

lemma gateAt_bypass {n : ℕ} {C : Circuit} {r i k : ℕ} (hk : k < C.gates.length - 1) :
    gateAt (bypass n C r i) k =
      if k < r then gateAt C k else aliasGate (n + r) i (gateAt C (k + 1)) := by
  have hk' : k < (bypass n C r i).gates.length := by rw [bypass_length]; exact hk
  rw [gateAt_eq hk']
  simp [bypass]

lemma bypass_val_lt {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r i : ℕ}
    (hr : r < C.gates.length) : ∀ u, u < n + r → val (bypass n C r i) x u = val C x u := by
  apply val_prefix hx (by omega) (by rw [bypass_length]; omega)
  intro k hk
  rw [gateAt_bypass (by omega), ite_eq_left hk]

lemma aliasWire_self (w i : ℕ) : aliasWire w i w = i := by simp [aliasWire]

lemma aliasWire_lt_self {w i u : ℕ} (hu : u < w) : aliasWire w i u = u := by
  unfold aliasWire; rw [ite_eq_right (by omega), ite_eq_right (by omega)]

lemma aliasWire_gt_self {w i u : ℕ} (hu : w < u) : aliasWire w i u = u - 1 := by
  unfold aliasWire; rw [ite_eq_right (by omega), ite_eq_left hu]

lemma bypass_rel {R : Bool → Bool → Prop} (hrefl : ∀ b, R b b) (hmono : OpMono R)
    {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
    {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
    (hR : (∃ k, r < k ∧ k < C.gates.length ∧ n + r ∈ (gateAt C k).inputs) →
      R (val C x (n + r)) (val C x i)) :
    ∀ u, u ≠ n + r → R (val C x u) (val (bypass n C r i) x (aliasWire (n + r) i u)) := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hne
    by_cases hlt : u < n + r
    · rw [aliasWire_lt_self hlt, bypass_val_lt hx hr u hlt]; exact hrefl _
    · rw [aliasWire_gt_self (by omega)]
      by_cases hge : n + C.gates.length ≤ u
      · rw [val_ge hx hge, val_ge hx (by rw [bypass_length]; omega)]; exact hrefl _
      · obtain ⟨k, rfl⟩ : ∃ k, u = n + (k + 1) := ⟨u - n - 1, by omega⟩
        have hk1 : k + 1 < C.gates.length := by omega
        have hkr : ¬ k < r := by omega
        have e : n + (k + 1) - 1 = n + k := by omega
        rw [e, val_gate hx hk1, val_gate hx (by rw [bypass_length]; omega),
          gateAt_bypass (by omega), ite_eq_right hkr]
        simp only [aliasGate, List.map_map]
        refine hmono _ (hAO _ hk1) _ _ _ ?_
        intro i' hi'
        simp only [Function.comp_apply]
        by_cases h1 : i' = n + r
        · subst h1
          rw [aliasWire_self, ite_eq_left (by omega)]
          have hgi : (if i < n + k then val (bypass n C r i) x i else false) = val C x i := by
            rcases hi with hi | hi
            · rw [ite_eq_left (by omega), bypass_val_lt hx hr i hi]
            · rw [ite_eq_right (by omega), val_ge hx hi]
          rw [hgi]
          exact hR ⟨k + 1, by omega, hk1, hi'⟩
        · by_cases h2 : i' < n + r
          · rw [aliasWire_lt_self h2, ite_eq_left (by omega), ite_eq_left (by omega),
              bypass_val_lt hx hr i' h2]
            exact hrefl _
          · by_cases h3 : i' < n + (k + 1)
            · have key := ih i' h3 h1
              rw [aliasWire_gt_self (by omega)] at key
              rw [aliasWire_gt_self (by omega), ite_eq_left h3, ite_eq_left (by omega)]
              exact key
            · rw [aliasWire_gt_self (by omega), ite_eq_right h3, ite_eq_right (by omega)]
              exact hrefl _

lemma bypass_eval_rel {R : Bool → Bool → Prop} (hrefl : ∀ b, R b b) (hmono : OpMono R)
    {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
    {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
    (hR : R (val C x (n + r)) (val C x i)) :
    R (C.eval x) ((bypass n C r i).eval x) := by
  rw [eval_eq_val, eval_eq_val, bypass_output]
  by_cases h : C.output = n + r
  · have hgi : val (bypass n C r i) x i = val C x i := by
      rcases hi with hi | hi
      · exact bypass_val_lt hx hr i hi
      · rw [val_ge hx hi, val_ge hx (by rw [bypass_length]; omega)]
    rw [h, aliasWire_self, hgi]; exact hR
  · exact bypass_rel hrefl hmono hx hAO hr hi (fun _ => hR) _ h

lemma bypass_eval_eq {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
    {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
    (hR : val C x (n + r) = val C x i) :
    (bypass n C r i).eval x = C.eval x :=
  (bypass_eval_rel (R := Eq) (fun _ => rfl) opMono_eq hx hAO hr hi hR).symm

lemma bypass_eval_unread {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
    {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
    (hout : C.output ≠ n + r)
    (hno : ∀ k, r < k → k < C.gates.length → n + r ∉ (gateAt C k).inputs) :
    (bypass n C r i).eval x = C.eval x := by
  rw [eval_eq_val, eval_eq_val, bypass_output]
  exact (bypass_rel (R := Eq) (fun _ => rfl) opMono_eq hx hAO hr hi
    (fun ⟨k, hrk, hk, hm⟩ => absurd hm (hno k hrk hk)) _ hout).symm

lemma bypass_AO {n : ℕ} {C : Circuit} {r i : ℕ} (hr : r < C.gates.length)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) :
    ∀ k < (bypass n C r i).gates.length,
      (gateAt (bypass n C r i) k).op = GateOp.and ∨
        (gateAt (bypass n C r i) k).op = GateOp.or := by
  intro k hk
  rw [bypass_length] at hk
  rw [gateAt_bypass hk]
  split_ifs with h
  · exact hAO k (by omega)
  · exact hAO (k + 1) (by omega)

lemma bypass_mem {n : ℕ} {C : Circuit} {r i : ℕ} :
    ∀ g ∈ (bypass n C r i).gates, ∃ g' ∈ C.gates, g.op = g'.op ∧
      g.inputs.length = g'.inputs.length := by
  intro g hg
  simp only [bypass, List.mem_map, List.mem_range] at hg
  obtain ⟨k, hk, rfl⟩ := hg
  split_ifs with h
  · exact ⟨gateAt C k, gateAt_mem (by omega), rfl, rfl⟩
  · exact ⟨gateAt C (k + 1), gateAt_mem (by omega), rfl, by simp [aliasGate]⟩

lemma aliasWire_lt {w i u m : ℕ} (hi : i < w) (hwm : w ≤ m) (hu : u < m + 1) :
    aliasWire w i u < m := by
  unfold aliasWire; split_ifs <;> omega

lemma bypass_readsBack {n : ℕ} {C : Circuit} {r i : ℕ} (hi : i < n + r)
    (hRB : ∀ k < C.gates.length, ∀ u ∈ (gateAt C k).inputs, u < n + k) :
    ∀ k < (bypass n C r i).gates.length,
      ∀ u ∈ (gateAt (bypass n C r i) k).inputs, u < n + k := by
  intro k hk u hu
  rw [bypass_length] at hk
  rw [gateAt_bypass hk] at hu
  split_ifs at hu with h
  · exact hRB k (by omega) u hu
  · simp only [aliasGate, List.mem_map] at hu
    obtain ⟨u', hu', rfl⟩ := hu
    have := hRB (k + 1) (by omega) u' hu'
    exact aliasWire_lt hi (by omega) (by omega)


lemma erase_eq_bypass (n : ℕ) (C : Circuit) (r i : ℕ) (hr : r < C.gates.length) :
    PEqualNP.CircuitMoves.eraseGate n C r i = bypass n C r i := by
  unfold PEqualNP.CircuitMoves.eraseGate
  rw [ite_eq_left hr]
  change Circuit.mk _ (aliasWire (n + r) i C.output) = Circuit.mk _ (aliasWire (n + r) i C.output)
  congr 1
  apply List.ext_getElem
  · simp [bypass]; omega
  · intro k hk hk'
    have hlen : (C.gates.take r).length = r := by simp; omega
    have hklen : k < C.gates.length - 1 := by simpa using hk'
    simp only [List.getElem_map, List.getElem_range]
    by_cases hkr : k < r
    · rw [ite_eq_left hkr, List.getElem_append_left (by omega), List.getElem_take,
        gateAt_eq (by omega)]
    · rw [ite_eq_right hkr, List.getElem_append_right (by omega), List.getElem_map,
        List.getElem_drop]
      simp only [hlen]
      have he : r + 1 + (k - r) = k + 1 := by omega
      simp only [he]
      rw [gateAt_eq (by omega : k + 1 < C.gates.length)]
      rfl

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

lemma circuit_monotone (n : ℕ) (C : Circuit) (hM : Monotone2 C) (x y : Fin n → Bool)
    (hxy : ∀ i, x i = true → y i = true) : C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true :=
  wire_monotone n C hM x y hxy C.output

lemma opMono_reverse : OpMono (fun a b => b = true → a = true) := by
  intro op hop l f g h
  exact opMono_imp op hop l g f h

lemma bypass_mono {n : ℕ} {C : Circuit} {r i : ℕ} (hM : Monotone2 C) :
    Monotone2 (bypass n C r i) := by
  intro g hg
  obtain ⟨g', hg', hop, hlen⟩ := bypass_mem g hg
  rw [hop, hlen]
  exact hM g' hg'

lemma graph_true {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ p l, G.Adj p l ∧ x p = true ∧ x l = true := by
  simp [graphFun]

lemma pair_true {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (p l : Fin n)
    (hp : G.Adj p l) : graphFun G ∅ (PEqualNP.EdgeOwnership.pairInput p l) = true := by
  rw [graph_true]
  exact ⟨p, l, hp, by simp [PEqualNP.EdgeOwnership.pairInput], by simp [PEqualNP.EdgeOwnership.pairInput]⟩

lemma edge_preserving_alias {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hM : Monotone2 C) (hf : circuitFun n C = graphFun G ∅)
    (r i : ℕ) (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
    (hlow : ∀ x : Fin n → Bool, val C (List.ofFn x) i = true →
      val C (List.ofFn x) (n + r) = true)
    (hedge : ∀ u v : Fin n, G.Adj u v →
      val C (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v)) (n + r) =
        val C (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v)) i) :
    circuitFun n (bypass n C r i) = circuitFun n C := by
  let D := bypass n C r i
  have hD : Monotone2 D := bypass_mono hM
  have hle (x : Fin n → Bool) : D.eval (List.ofFn x) = true → C.eval (List.ofFn x) = true :=
    bypass_eval_rel (R := fun a b => b = true → a = true) (fun _ => id) opMono_reverse
      (by simp) (mono_ops hM) hr hi (hlow x)
  funext x
  apply Bool.eq_iff_iff.mpr
  constructor
  · exact hle x
  · intro hx
    have hx' : graphFun G ∅ x = true := by rw [← hf]; exact hx
    obtain ⟨u, v, huv, hux, hvx⟩ := (graph_true G x).mp hx'
    refine circuit_monotone n D hD (PEqualNP.EdgeOwnership.pairInput u v) x ?_ ?_
    · intro k hk
      have hk' : k = u ∨ k = v := by simpa [PEqualNP.EdgeOwnership.pairInput] using hk
      rcases hk' with rfl | rfl
      · exact hux
      · exact hvx
    · change (bypass n C r i).eval _ = true
      rw [bypass_eval_eq (by simp) (mono_ops hM) hr hi (hedge u v huv)]
      change circuitFun n C _ = true
      rw [hf]
      exact pair_true G u v huv

lemma minimum_no_alias {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hm : IsMinimalMonoCircuit n C) (hf : circuitFun n C = graphFun G ∅)
    (r i : ℕ) (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
    (hlow : ∀ x : Fin n → Bool, val C (List.ofFn x) i = true →
      val C (List.ofFn x) (n + r) = true)
    (hedge : ∀ u v : Fin n, G.Adj u v →
      val C (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v)) (n + r) =
        val C (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v)) i) : False := by
  have heq := edge_preserving_alias G C hm.1 hf r i hr hi hlow hedge
  have hsize := hm.2 (bypass n C r i) (bypass_mono hm.1) heq
  change C.gates.length ≤ (bypass n C r i).gates.length at hsize
  rw [bypass_length] at hsize
  omega

def orSet {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  decide (∃ s ∈ S, x s = true)

lemma orSet_pair {n : ℕ} (S : Finset (Fin n)) (u v : Fin n) :
    orSet S (PEqualNP.EdgeOwnership.pairInput u v) = true ↔ u ∈ S ∨ v ∈ S := by
  simp only [orSet, decide_eq_true_eq, PEqualNP.EdgeOwnership.pairInput]
  constructor
  · rintro ⟨s, hs, hsu | hsv⟩
    · exact Or.inl (hsu ▸ hs)
    · exact Or.inr (hsv ▸ hs)
  · rintro (hu | hv)
    · exact ⟨u, hu, Or.inl rfl⟩
    · exact ⟨v, hv, Or.inr rfl⟩

lemma raw_val {n : ℕ} (C : Circuit) (x : Fin n → Bool) (c : Fin n) :
    val C (List.ofFn x) c.val = x c := by
  rw [val_input (by simp) c.isLt]
  simp [List.getD_eq_getElem?_getD]

lemma minimum_no_pure_product {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hm : IsMinimalMonoCircuit n C) (hf : circuitFun n C = graphFun G ∅)
    (r a b : ℕ) (hr : r < C.gates.length) (ha : a < n + r) (hb : b < n + r)
    (hop : (gateAt C r).op = GateOp.and) (hins : (gateAt C r).inputs = [a,b])
    (S T : Finset (Fin n)) (c : Fin n) (hcS : c ∈ S) (hcT : c ∈ T)
    (hinter : ∀ z : Fin n, z ∈ S → z ∈ T → z = c)
    (hcross : ∀ u ∈ S, ∀ v ∈ T, G.Adj u v → u = c ∨ v = c)
    (hS : ∀ x : Fin n → Bool, val C (List.ofFn x) a = orSet S x)
    (hT : ∀ x : Fin n → Bool, val C (List.ofFn x) b = orSet T x) : False := by
  have hg (x : Fin n → Bool) :
      val C (List.ofFn x) (n + r) = (orSet S x && orSet T x) := by
    rw [val_gate (by simp) hr, hop, hins]
    simp [GateOp.eval, ha, hb, hS, hT]
  apply minimum_no_alias G C hm hf r c.val hr (Or.inl (by have := c.isLt; omega))
  · intro x hx
    rw [raw_val] at hx
    rw [hg, Bool.and_eq_true]
    exact ⟨decide_eq_true ⟨c, hcS, hx⟩, decide_eq_true ⟨c, hcT, hx⟩⟩
  · intro u v huv
    rw [hg, raw_val]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, orSet_pair, PEqualNP.EdgeOwnership.pairInput,
      decide_eq_true_eq]
    constructor
    · rintro ⟨huS | hvS, huT | hvT⟩
      · exact Or.inl (hinter u huS huT).symm
      · exact (hcross u huS v hvT huv).imp Eq.symm Eq.symm
      · exact ((hcross v hvS u huT huv.symm).imp Eq.symm Eq.symm).symm
      · exact Or.inr (hinter v hvS hvT).symm
    · rintro (hcu | hcv)
      · subst u; exact ⟨Or.inl hcS, Or.inl hcT⟩
      · subst v; exact ⟨Or.inr hcS, Or.inr hcT⟩

lemma minimum_pure_product_intersection {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hm : IsMinimalMonoCircuit n C) (hf : circuitFun n C = graphFun G ∅)
    (r a b : ℕ) (hr : r < C.gates.length) (ha : a < n + r) (hb : b < n + r)
    (hop : (gateAt C r).op = GateOp.and) (hins : (gateAt C r).inputs = [a,b])
    (S T : Finset (Fin n))
    (hsep : ∀ u ∈ S, ∀ v ∈ T, ¬ G.Adj u v)
    (hS : ∀ x : Fin n → Bool, val C (List.ofFn x) a = orSet S x)
    (hT : ∀ x : Fin n → Bool, val C (List.ofFn x) b = orSet T x) :
    2 ≤ (S ∩ T).card := by
  by_contra hsmall
  have hcard : (S ∩ T).card ≤ 1 := by omega
  by_cases hne : (S ∩ T).Nonempty
  · obtain ⟨c, hc⟩ := hne
    have hcST := Finset.mem_inter.mp hc
    exact minimum_no_pure_product G C hm hf r a b hr ha hb hop hins S T c hcST.1 hcST.2
      (fun z hzS hzT => Finset.card_le_one.mp hcard z (Finset.mem_inter.mpr ⟨hzS, hzT⟩) c hc)
      (fun u hu v hv huv => False.elim (hsep u hu v hv huv)) hS hT
  · have hg (x : Fin n → Bool) :
        val C (List.ofFn x) (n + r) = (orSet S x && orSet T x) := by
      rw [val_gate (by simp) hr, hop, hins]
      simp [GateOp.eval, ha, hb, hS, hT]
    apply minimum_no_alias G C hm hf r (n + C.gates.length) hr (Or.inr le_rfl)
    · intro x hx
      rw [val_ge (by simp) le_rfl] at hx
      cases hx
    · intro u v huv
      rw [val_ge (by simp) le_rfl]
      cases hv : val C (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v)) (n + r) with
      | false => rfl
      | true =>
        exfalso
        rw [hg, Bool.and_eq_true, orSet_pair, orSet_pair] at hv
        rcases hv with ⟨huS | hvS, huT | hvT⟩
        · exact hne ⟨u, Finset.mem_inter.mpr ⟨huS, huT⟩⟩
        · exact hsep u huS v hvT huv
        · exact hsep v hvS u huT huv.symm
        · exact hne ⟨v, Finset.mem_inter.mpr ⟨hvS, hvT⟩⟩

-- The following safe-partner lemmas are reused from the prior 2391 research.
open PEqualNP.EdgeOwnership PEqualNP.TopForm

-- The elementary pair-input calculation follows the checked L_meta_1876 proof.
theorem graphFun_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u v : Fin n) : graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    simp only [pairInput, decide_eq_true_eq] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.irrefl hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.irrefl hab).elim
  · intro h
    exact ⟨u, v, h, by simp [pairInput], by simp [pairInput]⟩

theorem wmax_adj_singleton {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (j : ℕ)
    (mono : ∀ x y : Fin n → Bool, (∀ i, x i = true → y i = true) →
      gateVal n C j x = true → gateVal n C j y = true)
    (p : Fin n) (hp : gateVal n C j (fun i => decide (i = p)) = true)
    (w : Fin n) (hw : w ∈ wmax G C j) : G.Adj p w := by
  have hpair : gateVal n C j (pairInput p w) = true := by
    apply mono _ _ _ hp
    intro i hi
    have : i = p := of_decide_eq_true hi
    subst i
    simp [pairInput]
  have hs := (Finset.mem_filter.mp hw).2
  exact (graphFun_pair G p w).mp (hs (pairInput p w) hpair (by simp [pairInput]))

-- Two distinct accepted singletons allow at most one safe raw-input partner.
theorem wmax_card_le_one {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (noFour : NoFourCycle G) (C : Circuit) (j : ℕ)
    (mono : ∀ x y : Fin n → Bool, (∀ i, x i = true → y i = true) →
      gateVal n C j x = true → gateVal n C j y = true)
    (p q : Fin n) (distinct : p ≠ q)
    (hp : gateVal n C j (fun i => decide (i = p)) = true)
    (hq : gateVal n C j (fun i => decide (i = q)) = true) :
    (wmax G C j).card ≤ 1 := by
  have sub : wmax G C j ⊆ Finset.univ.filter (fun w => G.Adj p w ∧ G.Adj q w) := by
    intro w hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      wmax_adj_singleton G C j mono p hp w hw,
      wmax_adj_singleton G C j mono q hq w hw⟩
  exact (Finset.card_le_card sub).trans (noFour p q distinct)


lemma pure_product_unique_safe_partner {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : NoFourCycle G)
    (C : Circuit) (hm : IsMinimalMonoCircuit n C) (hf : circuitFun n C = graphFun G ∅)
    (r a b : ℕ) (hr : r < C.gates.length) (ha : a < n + r) (hb : b < n + r)
    (hop : (gateAt C r).op = GateOp.and) (hins : (gateAt C r).inputs = [a,b])
    (S T : Finset (Fin n))
    (hsep : ∀ u ∈ S, ∀ v ∈ T, ¬ G.Adj u v)
    (hS : ∀ x : Fin n → Bool, val C (List.ofFn x) a = orSet S x)
    (hT : ∀ x : Fin n → Bool, val C (List.ofFn x) b = orSet T x) :
    (wmax G C r).card ≤ 1 := by
  have hcard := minimum_pure_product_intersection G C hm hf r a b hr ha hb hop hins S T hsep hS hT
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp (show 1 < (S ∩ T).card by omega)
  have accepted (z : Fin n) (hz : z ∈ S ∩ T) :
      gateVal n C r (fun k => decide (k = z)) = true := by
    change val C (List.ofFn (fun k => decide (k = z))) (n + r) = true
    rw [val_gate (by simp) hr, hop, hins]
    simp only [GateOp.eval, List.map_cons, List.map_nil, ha, hb,
      ite_true, List.all_cons, List.all_nil, id_eq, Bool.and_true, hS, hT, Bool.and_eq_true]
    obtain ⟨hzS,hzT⟩ := Finset.mem_inter.mp hz
    exact ⟨decide_eq_true ⟨z,hzS,by simp⟩, decide_eq_true ⟨z,hzT,by simp⟩⟩
  apply wmax_card_le_one G hfour C r ?_ p q hpq (accepted p hp) (accepted q hq)
  intro x y hxy
  exact wire_monotone n C hm.1 x y hxy (n + r)

lemma erase_edge_preserving_alias {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hM : Monotone2 C) (hf : circuitFun n C = graphFun G ∅)
    (r i : ℕ) (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
    (hlow : ∀ x : Fin n → Bool, val C (List.ofFn x) i = true →
      val C (List.ofFn x) (n + r) = true)
    (hedge : ∀ u v : Fin n, G.Adj u v →
      val C (List.ofFn (pairInput u v)) (n + r) = val C (List.ofFn (pairInput u v)) i) :
    circuitFun n (PEqualNP.CircuitMoves.eraseGate n C r i) = circuitFun n C ∧
    (PEqualNP.CircuitMoves.eraseGate n C r i).size + 1 = C.size ∧
    Monotone2 (PEqualNP.CircuitMoves.eraseGate n C r i) := by
  rw [erase_eq_bypass n C r i hr]
  refine ⟨edge_preserving_alias G C hM hf r i hr hi hlow hedge, ?_, bypass_mono hM⟩
  change (bypass n C r i).gates.length + 1 = C.gates.length
  rw [bypass_length]
  omega

lemma isAO2_mono {n : ℕ} {C : Circuit} (h : IsAO2 n C) : Monotone2 C := by
  intro g hg
  exact ⟨h.1 g hg, (h.2.2 g hg).le⟩

lemma bypass_isAO2 {n : ℕ} {C : Circuit} (h : IsAO2 n C) {r i : ℕ}
    (hi : i < n + r) : IsAO2 n (bypass n C r i) := by
  refine ⟨?_, bypass_readsBack hi h.2.1, ?_⟩
  · intro g hg
    obtain ⟨g', hg', hop, _⟩ := bypass_mem g hg
    rw [hop]
    exact h.1 g' hg'
  · intro g hg
    obtain ⟨g', hg', _, hlen⟩ := bypass_mem g hg
    rw [hlen]
    exact h.2.2 g' hg'

lemma leastAO_no_alias {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hm : IsLeastAO G C)
    (r i : ℕ) (hr : r < C.gates.length) (hi : i < n + r)
    (hlow : ∀ x : Fin n → Bool, val C (List.ofFn x) i = true →
      val C (List.ofFn x) (n + r) = true)
    (hedge : ∀ u v : Fin n, G.Adj u v →
      val C (List.ofFn (pairInput u v)) (n + r) = val C (List.ofFn (pairInput u v)) i) : False := by
  have heq := edge_preserving_alias G C (isAO2_mono hm.1) hm.2.1 r i hr (Or.inl hi) hlow hedge
  have hsize := hm.2.2 (bypass n C r i) (bypass_isAO2 hm.1 hi) (heq.trans hm.2.1)
  change C.gates.length ≤ (bypass n C r i).gates.length at hsize
  rw [bypass_length] at hsize
  omega

lemma leastAO_no_pure_product {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hm : IsLeastAO G C)
    (r a b : ℕ) (hr : r < C.gates.length) (ha : a < n + r) (hb : b < n + r)
    (hop : (gateAt C r).op = GateOp.and) (hins : (gateAt C r).inputs = [a,b])
    (S T : Finset (Fin n)) (c : Fin n) (hcS : c ∈ S) (hcT : c ∈ T)
    (hinter : ∀ z : Fin n, z ∈ S → z ∈ T → z = c)
    (hcross : ∀ u ∈ S, ∀ v ∈ T, G.Adj u v → u = c ∨ v = c)
    (hS : ∀ x : Fin n → Bool, val C (List.ofFn x) a = orSet S x)
    (hT : ∀ x : Fin n → Bool, val C (List.ofFn x) b = orSet T x) : False := by
  have hg (x : Fin n → Bool) :
      val C (List.ofFn x) (n + r) = (orSet S x && orSet T x) := by
    rw [val_gate (by simp) hr, hop, hins]
    simp [GateOp.eval, ha, hb, hS, hT]
  apply leastAO_no_alias G C hm r c.val hr (by have := c.isLt; omega)
  · intro x hx
    rw [raw_val] at hx
    rw [hg, Bool.and_eq_true]
    exact ⟨decide_eq_true ⟨c, hcS, hx⟩, decide_eq_true ⟨c, hcT, hx⟩⟩
  · intro u v huv
    rw [hg, raw_val]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, orSet_pair, pairInput, decide_eq_true_eq]
    constructor
    · rintro ⟨huS | hvS, huT | hvT⟩
      · exact Or.inl (hinter u huS huT).symm
      · exact (hcross u huS v hvT huv).imp Eq.symm Eq.symm
      · exact ((hcross v hvS u huT huv.symm).imp Eq.symm Eq.symm).symm
      · exact Or.inr (hinter v hvS hvT).symm
    · rintro (hcu | hcv)
      · subst u; exact ⟨Or.inl hcS, Or.inl hcT⟩
      · subst v; exact ⟨Or.inr hcS, Or.inr hcT⟩

end PEqualNP.Outside.Pnp1031Pruning

