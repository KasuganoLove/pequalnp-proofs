import PEqualNP.Defs

-- Physical erasure helpers reused from the verified 1031 research.
-- Their source is L_meta_2668, with attribution to L-meta-1499 / PR3112.
-- The new results use separate positive and negative sample orders.
namespace PEqualNP.Outside.Pnp2343Pruning

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

def Fits {α β : Type} (positive : α → List Bool) (negative : β → List Bool) (C : Circuit) : Prop :=
  (∀ p, C.eval (positive p) = true) ∧ ∀ q, C.eval (negative q) = false

def LeastSamples {α β : Type} (n : ℕ) (positive : α → List Bool)
    (negative : β → List Bool) (C : Circuit) : Prop :=
  Monotone2 C ∧ ReadsBack n C ∧ Fits positive negative C ∧
    ∀ D : Circuit, Monotone2 D → ReadsBack n D → Fits positive negative D → C.size ≤ D.size

lemma bypass_samples {α β : Type} (n : ℕ) (positive : α → List Bool) (negative : β → List Bool)
    (hpLen : ∀ p, (positive p).length = n) (hnLen : ∀ q, (negative q).length = n)
    (C : Circuit) (hM : Monotone2 C) (hF : Fits positive negative C)
    (r i : ℕ) (hr : r < C.gates.length) (hi : i < n + r)
    (hp : ∀ p, val C (positive p) (n + r) = true → val C (positive p) i = true)
    (hn : ∀ q, val C (negative q) i = true → val C (negative q) (n + r) = true) :
    Fits positive negative (bypass n C r i) := by
  constructor
  · intro p
    exact bypass_eval_rel (R := fun a b => a = true → b = true) (fun _ => id) opMono_imp
      (hpLen p) (mono_ops hM) hr (Or.inl hi) (hp p) (hF.1 p)
  · intro q
    cases he : (bypass n C r i).eval (negative q) with
    | false => rfl
    | true =>
      have hc := bypass_eval_rel (R := fun a b => b = true → a = true) (fun _ => id) opMono_reverse
        (hnLen q) (mono_ops hM) hr (Or.inl hi) (hn q) he
      rw [hF.2 q] at hc
      cases hc

lemma erase_samples {α β : Type} (n : ℕ) (positive : α → List Bool) (negative : β → List Bool)
    (hpLen : ∀ p, (positive p).length = n) (hnLen : ∀ q, (negative q).length = n)
    (C : Circuit) (hM : Monotone2 C) (hR : ReadsBack n C) (hF : Fits positive negative C)
    (r i : ℕ) (hr : r < C.gates.length) (hi : i < n + r)
    (hp : ∀ p, val C (positive p) (n + r) = true → val C (positive p) i = true)
    (hn : ∀ q, val C (negative q) i = true → val C (negative q) (n + r) = true) :
    let D := PEqualNP.CircuitMoves.eraseGate n C r i
    Monotone2 D ∧ ReadsBack n D ∧ Fits positive negative D ∧ D.size + 1 = C.size := by
  dsimp only
  rw [erase_eq_bypass n C r i hr]
  refine ⟨bypass_mono hM, bypass_readsBack hi hR,
    bypass_samples n positive negative hpLen hnLen C hM hF r i hr hi hp hn, ?_⟩
  change (bypass n C r i).gates.length + 1 = C.gates.length
  rw [bypass_length]
  omega

lemma least_no_alias {α β : Type} (n : ℕ) (positive : α → List Bool) (negative : β → List Bool)
    (hpLen : ∀ p, (positive p).length = n) (hnLen : ∀ q, (negative q).length = n)
    (C : Circuit) (hmin : LeastSamples n positive negative C)
    (r i : ℕ) (hr : r < C.gates.length) (hi : i < n + r)
    (hp : ∀ p, val C (positive p) (n + r) = true → val C (positive p) i = true)
    (hn : ∀ q, val C (negative q) i = true → val C (negative q) (n + r) = true) : False := by
  obtain ⟨hM, hR, hF, hlen⟩ := erase_samples n positive negative hpLen hnLen C
    hmin.1 hmin.2.1 hmin.2.2.1 r i hr hi hp hn
  have hleast := hmin.2.2.2 _ hM hR hF
  omega

lemma and_negative_witness {α β : Type} (n : ℕ) (positive : α → List Bool) (negative : β → List Bool)
    (hpLen : ∀ p, (positive p).length = n) (hnLen : ∀ q, (negative q).length = n)
    (C : Circuit) (hmin : LeastSamples n positive negative C)
    (r a b : ℕ) (hr : r < C.gates.length)
    (hop : (gateAt C r).op = GateOp.and) (hins : (gateAt C r).inputs = [a,b]) :
    ∃ q, val C (negative q) a = true ∧ val C (negative q) b = false := by
  by_contra hex
  have ha : a < n + r := hmin.2.1 r hr a (by simp [hins])
  have hb : b < n + r := hmin.2.1 r hr b (by simp [hins])
  have hn (q : β) (hq : val C (negative q) a = true) : val C (negative q) b = true := by
    cases he : val C (negative q) b with
    | false => exact False.elim (hex ⟨q,hq,he⟩)
    | true => rfl
  apply least_no_alias n positive negative hpLen hnLen C hmin r a hr ha
  · intro p hp
    exact ((val_and (hpLen p) hr hop).mp hp) a (by simp [hins]) |>.2
  · intro q hq
    apply (val_and (hnLen q) hr hop).mpr
    intro i hi
    rw [hins] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact ⟨ha,hq⟩
    · exact ⟨hb,hn q hq⟩

lemma and_negative_incomparable {α β : Type} (n : ℕ) (positive : α → List Bool) (negative : β → List Bool)
    (hpLen : ∀ p, (positive p).length = n) (hnLen : ∀ q, (negative q).length = n)
    (C : Circuit) (hmin : LeastSamples n positive negative C)
    (r a b : ℕ) (hr : r < C.gates.length)
    (hop : (gateAt C r).op = GateOp.and) (hins : (gateAt C r).inputs = [a,b]) :
    (∃ q, val C (negative q) a = true ∧ val C (negative q) b = false) ∧
    (∃ q, val C (negative q) b = true ∧ val C (negative q) a = false) := by
  refine ⟨and_negative_witness n positive negative hpLen hnLen C hmin r a b hr hop hins, ?_⟩
  by_contra hex
  have ha : a < n + r := hmin.2.1 r hr a (by simp [hins])
  have hb : b < n + r := hmin.2.1 r hr b (by simp [hins])
  have hn (q : β) (hq : val C (negative q) b = true) : val C (negative q) a = true := by
    cases he : val C (negative q) a with
    | false => exact False.elim (hex ⟨q,hq,he⟩)
    | true => rfl
  apply least_no_alias n positive negative hpLen hnLen C hmin r b hr hb
  · intro p hp
    exact ((val_and (hpLen p) hr hop).mp hp) b (by simp [hins]) |>.2
  · intro q hq
    apply (val_and (hnLen q) hr hop).mpr
    intro i hi
    rw [hins] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact ⟨ha,hn q hq⟩
    · exact ⟨hb,hq⟩

lemma or_positive_incomparable {α β : Type} (n : ℕ) (positive : α → List Bool) (negative : β → List Bool)
    (hpLen : ∀ p, (positive p).length = n) (hnLen : ∀ q, (negative q).length = n)
    (C : Circuit) (hmin : LeastSamples n positive negative C)
    (r a b : ℕ) (hr : r < C.gates.length)
    (hop : (gateAt C r).op = GateOp.or) (hins : (gateAt C r).inputs = [a,b]) :
    (∃ p, val C (positive p) a = true ∧ val C (positive p) b = false) ∧
    (∃ p, val C (positive p) b = true ∧ val C (positive p) a = false) := by
  have ha : a < n + r := hmin.2.1 r hr a (by simp [hins])
  have hb : b < n + r := hmin.2.1 r hr b (by simp [hins])
  constructor
  · by_contra hex
    have hp (p : α) (h : val C (positive p) a = true) : val C (positive p) b = true := by
      cases he : val C (positive p) b with
      | false => exact False.elim (hex ⟨p,h,he⟩)
      | true => rfl
    apply least_no_alias n positive negative hpLen hnLen C hmin r b hr hb
    · intro p hg
      obtain ⟨i,hi,_,hv⟩ := (val_or (hpLen p) hr hop).mp hg
      rw [hins] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact hp p hv
      · exact hv
    · intro q hq
      exact (val_or (hnLen q) hr hop).mpr ⟨b,by simp [hins],hb,hq⟩
  · by_contra hex
    have hp (p : α) (h : val C (positive p) b = true) : val C (positive p) a = true := by
      cases he : val C (positive p) a with
      | false => exact False.elim (hex ⟨p,h,he⟩)
      | true => rfl
    apply least_no_alias n positive negative hpLen hnLen C hmin r a hr ha
    · intro p hg
      obtain ⟨i,hi,_,hv⟩ := (val_or (hpLen p) hr hop).mp hg
      rw [hins] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact hv
      · exact hp p hv
    · intro q hq
      exact (val_or (hnLen q) hr hop).mpr ⟨a,by simp [hins],ha,hq⟩

end PEqualNP.Outside.Pnp2343Pruning



-- Constant propagation helpers reused from the prior 2391 research.
-- That work adapts upstream L_meta_1680 and L_meta_1425.
-- The new normalization theorem preserves the count of all gates.

namespace PEqualNP.Outside.Pnp2343Pruning.Normalize
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_start (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_start gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_start gs w
  rw [ht, List.getD_append _ _ _ _ h]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

variable {n : ℕ}

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

abbrev Stat : Type := Bool ⊕ ℕ

def Stat.val (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

theorem elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)

theorem elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega

theorem elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
    (∃ g ∈ gs, k ∈ g.inputs) → (elim n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _ h; obtain ⟨g, hg, _⟩ := h; simp at hg
  | cons g gs ih =>
    intro acc hok hk hc hex
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
        rw [hnone]; simp
      have := elim_len n gs (elimStep n acc g)
      omega
    · have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        obtain ⟨g', hg', hk'⟩ := hex
        rcases List.mem_cons.1 hg' with rfl | h
        · exact absurd hk' hkg
        · exact ⟨g', h, hk'⟩
      have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          refine ⟨c, ?_⟩
          simp only [elimStep]
          rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
        hex'
      have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      omega

theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Sum.inl false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Sum.inl false)).val (wiresFrom acc.2 y) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_start r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Sum.inl false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Sum.inl false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

theorem elim_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List Stat × List Gate) :
    elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl

theorem elim_append (n : ℕ) (pre post : List Gate) (acc : List Stat × List Gate) :
    elim n (pre ++ post) acc = elim n post (elim n pre acc) := by
  simp [elim, List.foldl_append]

def idStats (n : ℕ) : List Stat := List.ofFn (fun i : Fin n => Sum.inr i)

theorem inv_id (n : ℕ) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y) (idStats n, []) := by
  refine ⟨by simp [idStats], ?_⟩
  intro i
  by_cases hlt : i < n
  · simp [idStats, hlt, Stat.Valid, Stat.val, wiresFrom]
  · rw [List.getD_eq_default _ _ (by simp [idStats]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

theorem getD_ofFn {α : Type} (m : ℕ) (F : Fin m → α) (d : α) (j : Fin m) :
    (List.ofFn F).getD j d = F j := by
  simp
theorem split_at {α : Type} : ∀ (l : List α) (p : ℕ) (g : α), l[p]? = some g →
    ∃ pre post, l = pre ++ g :: post ∧ pre.length = p := by
  intro l
  induction l with
  | nil => intro p g h; simp at h
  | cons x l ih =>
    intro p g h
    cases p with
    | zero =>
      simp at h
      subst h
      exact ⟨[], l, rfl, rfl⟩
    | succ p =>
      simp at h
      obtain ⟨pre, post, rfl, rfl⟩ := ih p g h
      exact ⟨x :: pre, post, rfl, rfl⟩

theorem simplify_small (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (m : ℕ)
    (ins : List Stat) (hl : ins.length ≤ 1) : (simplify op m ins).1 = none := by
  rcases hop with rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩
    · simp [simplify, simpAnd]
    · cases a <;> simp [simplify, simpAnd]
    · simp at hl
  · rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩
    · simp [simplify, simpOr]
    · cases a <;> simp [simplify, simpOr]
    · simp at hl

theorem wire_at (n : ℕ) (pre post : List Gate) (g : Gate) (X : List Bool) (hX : X.length = n) :
    (wiresFrom (pre ++ g :: post) X).getD (n + pre.length) false
      = g.op.eval (g.inputs.map fun i => (wiresFrom pre X).getD i false) := by
  have h1 : wiresFrom (pre ++ g :: post) X = wiresFrom post
      (wiresFrom pre X ++ [g.op.eval (g.inputs.map fun i => (wiresFrom pre X).getD i false)]) := by
    rw [wiresFrom_append]; rfl
  have hl : (wiresFrom pre X).length = n + pre.length := by
    rw [length_wiresFrom]; omega
  rw [h1, getD_wiresFrom _ _ _ (by simp [hl]), getD_snoc_len _ _ _ _ hl]

-- Replacing a gate by a gate of at most one input with the same value saves a gate.

def CleanGate (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ g.inputs = [j, k])

def CleanL (m : ℕ) (gs : List Gate) : Prop :=
  ∀ (p : ℕ) (g : Gate), gs[p]? = some g → CleanGate (m + p) g

theorem CleanGate.nok {m : ℕ} {g : Gate} (h : CleanGate m g) : NOk g := by
  rcases h with ⟨h1, j, _, h2⟩ | ⟨h1 | h1, j, k, _, _, h2⟩
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inr (Or.inr rfl)
    · rw [h2]; simp
    · intro _; rw [h2]; simp
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inl rfl
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inr (Or.inl rfl)
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h

theorem CleanGate.lt {m : ℕ} {g : Gate} (h : CleanGate m g) : ∀ a ∈ g.inputs, a < m := by
  intro a ha
  rcases h with ⟨_, j, hj, h2⟩ | ⟨_, j, k, hj, hk, h2⟩
  · rw [h2] at ha
    simp at ha
    subst ha; exact hj
  · rw [h2] at ha
    simp at ha
    rcases ha with rfl | rfl
    · exact hj
    · exact hk

theorem clean_nok (m : ℕ) (gs : List Gate) (h : CleanL m gs) : ∀ g ∈ gs, NOk g := by
  intro g hg
  obtain ⟨p, hp⟩ := List.mem_iff_getElem?.1 hg
  exact (h p g hp).nok

theorem simplify_clean (op : GateOp) (m : ℕ) (ins : List Stat) (hv : ∀ s ∈ ins, s.Valid m) :
    ∀ g ∈ (simplify op m ins).1, CleanGate m g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg
    refine Or.inr ⟨Or.inl rfl, _, _, ?_, ?_, rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg
    refine Or.inr ⟨Or.inr rfl, _, _, ?_, ?_, rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg
    refine Or.inl ⟨rfl, _, ?_, rfl⟩
    exact hv _ List.mem_cons_self
  · simp at hg
  · simp at hg

theorem toList_getElem? {α : Type} (o : Option α) (k : ℕ) (a : α)
    (h : o.toList[k]? = some a) : k = 0 ∧ a ∈ o := by
  cases o with
  | none => simp at h
  | some b =>
    cases k with
    | zero => simp at h; simp [h]
    | succ k => simp at h

theorem clean_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      CleanL n acc.2 → CleanL n (elim n gs acc).2 := by
  induction gs with
  | nil => intro w acc _ _ h; exact h
  | cons g gs ih =>
    intro w acc hok hinv hcl
    have hinv' : Inv n y (wiresFrom [g] w) (elimStep n acc g) :=
      inv_elim n y hy [g] w acc (fun g' hg' => hok g' (by simp at hg'; simp [hg'])) hinv
    refine ih _ (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) hinv' ?_
    intro p g' hp
    have hp' : (acc.2 ++ (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)[p]? = some g' := hp
    by_cases hlt : p < acc.2.length
    · rw [List.getElem?_append_left hlt] at hp'
      exact hcl p g' hp'
    · rw [List.getElem?_append_right (by omega)] at hp'
      obtain ⟨h0, hmem⟩ := toList_getElem? _ _ _ hp'
      have hpl : p = acc.2.length := by omega
      rw [hpl]
      exact simplify_clean _ _ _ (fun s hs => by
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        exact (hinv.2 a).1) g' hmem


theorem simplify_op (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, g.op = op := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; rfl)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; rfl)
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; rfl)
  · simp at hg
  · simp at hg

def AO (gs : List Gate) : Prop :=
  ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or

theorem elim_ao (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    AO gs → AO acc.2 → AO (elim n gs acc).2 := by
  induction gs with
  | nil => intro acc _ h; exact h
  | cons g gs ih =>
    intro acc hgs h
    apply ih (elimStep n acc g) (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · rw [simplify_op _ _ _ g' (by simpa using h1)]
      exact hgs g List.mem_cons_self

theorem ao_clean_isAO2 (n : ℕ) (gs : List Gate) (o : ℕ)
    (hao : AO gs) (hc : CleanL n gs) : PEqualNP.TopForm.IsAO2 n ⟨gs, o⟩ := by
  refine ⟨hao, ?_, ?_⟩
  · intro j hj w hw
    have hg : PEqualNP.MetaComplexity.NestedCover.gateAt ⟨gs, o⟩ j = gs[j] := by
      exact List.getD_eq_getElem _ _ hj
    rw [hg] at hw
    exact (hc j gs[j] (List.getElem?_eq_getElem hj)).lt w hw
  · intro g hg
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hg
    rcases hc j g hj with h | h
    · obtain ⟨hop, _⟩ := h
      rcases hao g hg with ha | ho <;> simp_all
    · obtain ⟨_, a, b, _, _, hi⟩ := h
      simp [hi]

theorem normalize_nonconstant (n : ℕ) (C : Circuit) (hM : Monotone2 C)
    (f : (Fin n → Bool) → Bool) (hf : circuitFun n C = f)
    (hnc : ∃ x y, f x ≠ f y) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧ circuitFun n D = f ∧ D.size ≤ C.size := by
  let acc := elim n C.gates (idStats n, [])
  have hok : ∀ g ∈ C.gates, Ok g := by
    intro g hg
    refine ⟨?_, (hM g hg).2⟩
    rcases (hM g hg).1 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  have hao : AO C.gates := fun g hg => (hM g hg).1
  have hinv : ∀ x : Fin n → Bool,
      Inv n (List.ofFn x) (wiresFrom C.gates (List.ofFn x)) acc :=
    fun x => inv_elim n _ (by simp) C.gates _ _ hok (inv_id n x)
  have hval : ∀ x : Fin n → Bool,
      (acc.1.getD C.output (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn x)) = f x := by
    intro x
    exact ((hinv x).2 C.output).2.trans (congrFun hf x)
  have hlen : acc.2.length ≤ C.size := by
    have h := elim_len n C.gates (idStats n, [])
    simpa only [acc, Circuit.size, List.length_nil, zero_add] using h
  cases hs : acc.1.getD C.output (Sum.inl false) with
  | inl b =>
    exfalso
    obtain ⟨x, y, hxy⟩ := hnc
    apply hxy
    rw [← hval x, ← hval y, hs]
    rfl
  | inr w =>
    refine ⟨⟨acc.2, w⟩, ?_, ?_, hlen⟩
    · apply ao_clean_isAO2
      · exact elim_ao n C.gates _ hao (by intro g hg; simp at hg)
      · exact clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) C.gates _ _ hok
          (inv_id n _) (by intro p g hp; simp at hp)
    · funext x
      have hx := hval x
      rw [hs] at hx
      exact hx


end PEqualNP.Outside.Pnp2343Pruning.Normalize

namespace PEqualNP.Outside.Pnp2343Pruning

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

lemma exists_least_samples {α β : Type} (n : ℕ) (positive : α → List Bool) (negative : β → List Bool)
    (C : Circuit) (hM : Monotone2 C) (hR : ReadsBack n C) (hF : Fits positive negative C) :
    ∃ D : Circuit, LeastSamples n positive negative D ∧ D.size ≤ C.size := by
  classical
  let A (k : ℕ) : Prop := ∃ D : Circuit,
    Monotone2 D ∧ ReadsBack n D ∧ Fits positive negative D ∧ D.size = k
  have hex : ∃ k, A k := ⟨C.size,C,hM,hR,hF,rfl⟩
  obtain ⟨D,hDm,hDr,hDf,hDsize⟩ := Nat.find_spec hex
  refine ⟨D,⟨hDm,hDr,hDf,?_⟩,?_⟩
  · intro E hEm hEr hEf
    rw [hDsize]
    exact Nat.find_min' hex ⟨E,hEm,hEr,hEf,rfl⟩
  · rw [hDsize]
    exact Nat.find_min' hex ⟨C,hM,hR,hF,rfl⟩

lemma ofFn_getD {n : ℕ} (x : List Bool) (hx : x.length = n) :
    List.ofFn (fun i : Fin n => x.getD i.val false) = x := by
  apply List.ext_getElem
  · simp [hx]
  · intro i hi hi'
    simp only [List.getElem_ofFn, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hi', Option.getD_some]

lemma eval_of_funEq {n : ℕ} {C D : Circuit} (h : circuitFun n D = circuitFun n C)
    (x : List Bool) (hx : x.length = n) : D.eval x = C.eval x := by
  have hh := congrFun h (fun i : Fin n => x.getD i.val false)
  simpa only [circuitFun, ofFn_getD x hx] using hh

lemma sample_nonconstant {α β : Type} (n : ℕ) (positive : α → List Bool) (negative : β → List Bool)
    (hpLen : ∀ p, (positive p).length = n) (hnLen : ∀ q, (negative q).length = n)
    (p0 : α) (q0 : β) (C : Circuit) (hF : Fits positive negative C) :
    ∃ x y : Fin n → Bool, circuitFun n C x ≠ circuitFun n C y := by
  refine ⟨fun i => (positive p0).getD i.val false,
    fun i => (negative q0).getD i.val false, ?_⟩
  simp only [circuitFun, ofFn_getD _ (hpLen p0), ofFn_getD _ (hnLen q0), hF.1 p0, hF.2 q0]
  decide

lemma least_normalized_samples {α β : Type} (n : ℕ) (positive : α → List Bool) (negative : β → List Bool)
    (hpLen : ∀ p, (positive p).length = n) (hnLen : ∀ q, (negative q).length = n)
    (p0 : α) (q0 : β) (C : Circuit) (hM : Monotone2 C) (hR : ReadsBack n C)
    (hF : Fits positive negative C) :
    ∃ D : Circuit, LeastSamples n positive negative D ∧ PEqualNP.TopForm.IsAO2 n D ∧ D.size ≤ C.size := by
  obtain ⟨B,hB,hBC⟩ := exists_least_samples n positive negative C hM hR hF
  obtain ⟨D,hD,hDB,hsize⟩ := Normalize.normalize_nonconstant n B hB.1 (circuitFun n B) rfl
    (sample_nonconstant n positive negative hpLen hnLen p0 q0 B hB.2.2.1)
  have hDm : Monotone2 D := by
    intro g hg
    exact ⟨hD.1 g hg,(hD.2.2 g hg).le⟩
  have hDf : Fits positive negative D := by
    constructor
    · intro p
      rw [eval_of_funEq hDB _ (hpLen p)]
      exact hB.2.2.1.1 p
    · intro q
      rw [eval_of_funEq hDB _ (hnLen q)]
      exact hB.2.2.1.2 q
  refine ⟨D,⟨hDm,hD.2.1,hDf,?_⟩,hD,hsize.trans hBC⟩
  intro E hEm hEr hEf
  exact hsize.trans (hB.2.2.2 E hEm hEr hEf)

lemma least_binary_inputs_distinct {α β : Type} (n : ℕ) (positive : α → List Bool) (negative : β → List Bool)
    (hpLen : ∀ p, (positive p).length = n) (hnLen : ∀ q, (negative q).length = n)
    (C : Circuit) (hmin : LeastSamples n positive negative C)
    (r a b : ℕ) (hr : r < C.gates.length) (hins : (gateAt C r).inputs = [a,b]) : a ≠ b := by
  rcases (hmin.1 (gateAt C r) (gateAt_mem hr)).1 with hand | hor
  · obtain ⟨q, hqa, hqb⟩ := and_negative_witness n positive negative hpLen hnLen C hmin r a b hr hand hins
    intro hab
    rw [hab,hqb] at hqa
    cases hqa
  · obtain ⟨⟨p,hpa,hpb⟩,_⟩ := or_positive_incomparable n positive negative hpLen hnLen C hmin r a b hr hor hins
    intro hab
    rw [hab,hpb] at hpa
    cases hpa

def diff : Finset (Fin 13) := {0,1,3,9}

def quad (Q : Finset (Fin 13)) : Prop :=
  Q.card = 4 ∧ ∀ l : Fin 13, (Q.filter (fun p => p - l ∈ diff)).card ≤ 2

abbrev Flag := {e : Fin 13 × Fin 13 // e.1 - e.2 ∈ diff}
abbrev Quad := {Q : Finset (Fin 13) // quad Q}

def augment (s : List ℕ) (x : List Bool) : List Bool :=
  x ++ [s.any (fun i => x.getD i false)]

def positive (s : List ℕ) (e : Flag) : List Bool :=
  augment s (List.ofFn (fun p : Fin 13 => decide (p = e.val.1)) ++
    List.ofFn (fun l : Fin 13 => decide (l = e.val.2)))

def negative (s : List ℕ) (Q : Quad) : List Bool :=
  augment s (List.ofFn (fun p : Fin 13 => decide (p ∈ Q.val)) ++
    List.ofFn (fun l : Fin 13 => decide (∀ p ∈ Q.val, p - l ∉ diff)))

lemma positive_length (s : List ℕ) (e : Flag) : (positive s e).length = 27 := by
  simp [positive,augment]

lemma negative_length (s : List ℕ) (Q : Quad) : (negative s Q).length = 27 := by
  simp [negative,augment]

def flag0 : Flag := ⟨(0,0),by decide⟩
def quad0 : Quad := ⟨{0,1,2,5},by unfold quad diff; decide⟩

theorem free_or_normal_form (C : Circuit) (s : List ℕ) (hM : Monotone2 C)
    (hR : ∀ i : Fin C.gates.length, ∀ w ∈ (C.gates.get i).inputs, w < 27 + i.val)
    (hF : Fits (positive s) (negative s) C) :
    ∃ D : Circuit, LeastSamples 27 (positive s) (negative s) D ∧
      PEqualNP.TopForm.IsAO2 27 D ∧ D.size ≤ C.size ∧
      ∀ r < D.gates.length, ∃ a b : ℕ, (gateAt D r).inputs = [a,b] ∧ a ≠ b := by
  have hR' : ReadsBack 27 C := by
    intro j hj w hw
    have hg : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj
    rw [hg] at hw
    exact hR ⟨j,hj⟩ w hw
  obtain ⟨D,hmin,hAO,hsize⟩ := least_normalized_samples 27 (positive s) (negative s)
    (positive_length s) (negative_length s) flag0 quad0 C hM hR' hF
  refine ⟨D,hmin,hAO,hsize,?_⟩
  intro r hr
  obtain ⟨a,b,hab⟩ := List.length_eq_two.mp (hAO.2.2 (gateAt D r) (gateAt_mem hr))
  exact ⟨a,b,hab,least_binary_inputs_distinct 27 (positive s) (negative s)
    (positive_length s) (negative_length s) D hmin r a b hr hab⟩

end PEqualNP.Outside.Pnp2343Pruning
