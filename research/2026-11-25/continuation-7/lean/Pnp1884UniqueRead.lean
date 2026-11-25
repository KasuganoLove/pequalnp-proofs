import PEqualNP.Defs

-- Wire helpers reused from the checked 1031/2343/5126 research, whose upstream
-- source is L_meta_2668 with attribution to L-meta-1499 / PR3112.
-- New result: a uniquely read nonzero Petersen variable cannot enter an AND/OR
-- gate together with another primitive input, even with free NOT(x0).
namespace PEqualNP.Outside.Pnp1884UniqueRead

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


/-- If an input is only read at one gate, equalizing that gate's output erases
all effects of changing the input. The other gates may have arbitrary operators. -/
lemma sole_reader_collision {n : ℕ} (C : Circuit) (x y : List Bool)
    (hx : x.length = n) (hy : y.length = n) (v r : ℕ) (_hv : v < n)
    (hinput : ∀ i < n, i ≠ v → x.getD i false = y.getD i false)
    (hreads : ∀ k < C.gates.length, k ≠ r → v ∉ (gateAt C k).inputs)
    (hgate : val C x (n+r) = val C y (n+r)) (hout : C.output ≠ v) : C.eval x = C.eval y := by
  have wire : ∀ w, w ≠ v → val C x w = val C y w := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hwv
      by_cases hraw : w < n
      · rw [val_input hx hraw,val_input hy hraw]
        exact hinput w hraw hwv
      by_cases hfar : n+C.gates.length ≤ w
      · rw [val_ge hx hfar,val_ge hy hfar]
      obtain ⟨k,rfl⟩ : ∃ k, w = n+k := ⟨w-n,by omega⟩
      have hk : k < C.gates.length := by omega
      by_cases hkr : k = r
      · simpa only [hkr] using hgate
      rw [val_gate hx hk,val_gate hy hk]
      congr 1
      apply List.map_congr_left
      intro u hu
      by_cases hut : u < n+k
      · rw [ite_eq_left hut,ite_eq_left hut]
        exact ih u hut (fun huv => hreads k hk hkr (huv ▸ hu))
      · rw [ite_eq_right hut,ite_eq_right hut]
  exact wire C.output hout

def target (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
  x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

def augmented (x : Fin 10 → Bool) : List Bool := List.ofFn x ++ [!x 0]

def masks : List ℕ := [
0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
4,1,0,0,1,4,1,9,1,20,1,36,1,64,1,129,1,257,1,513,1,4,
2,9,8,2,0,0,2,8,2,18,2,34,2,72,2,128,2,258,2,514,9,2,
4,5,4,18,16,4,0,0,4,16,4,36,4,68,4,144,4,256,4,516,5,4,
8,1,1,10,1,5,1,8,0,0,1,40,1,65,1,129,1,257,1,512,1,8,
128,1,1,130,1,5,1,9,1,144,0,0,1,65,1,128,1,256,1,513,1,128,
2,257,256,2,2,260,2,10,2,18,2,34,0,0,2,130,2,256,2,512,257,2,
4,5,4,34,32,4,4,40,4,20,4,32,4,68,0,0,4,260,4,512,5,4,
8,9,8,10,8,36,32,8,8,48,8,32,8,64,8,136,0,0,8,520,9,8,
16,65,16,18,16,20,16,72,64,16,16,48,16,64,16,128,16,272,0,0,65,16]

def witness (v : Fin 10) (w : Fin 11) (b : Bool) : Fin 10 → Bool :=
  fun u => (masks.getD ((v.val*11+w.val)*2 + if b then 1 else 0) 0).testBit u.val

-- Small kernel-checked pinning table. No search result is assumed.
set_option maxHeartbeats 2500000 in
set_option maxRecDepth 16000 in
lemma pinning_certificate : ∀ (v : Fin 10) (w : Fin 11) (b : Bool), v ≠ 0 → w.val ≠ v.val →
    let x := witness v w b
    let y := Function.update x v true
    target x = false ∧ target y = true ∧
    (augmented x).getD w.val false = b ∧ (augmented y).getD w.val false = b ∧
    ∀ u : Fin 11, u.val ≠ v.val →
      (augmented x).getD u.val false = (augmented y).getD u.val false := by
  decide +kernel


lemma blocked_gate_value {n : ℕ} (C : Circuit) (z : List Bool) (hz : z.length = n)
    (r v w : ℕ) (hr : r < C.gates.length) (hv : v < n) (hw : w < n) (b : Bool)
    (hins : (gateAt C r).inputs = [v,w] ∨ (gateAt C r).inputs = [w,v])
    (hop : ((gateAt C r).op = GateOp.and ∧ b = false) ∨
      ((gateAt C r).op = GateOp.or ∧ b = true))
    (hzw : z.getD w false = b) : val C z (n+r) = b := by
  have hv' : v < n+r := by omega
  have hw' : w < n+r := by omega
  have hvalw : val C z w = b := (val_input hz hw).trans hzw
  rw [val_gate hz hr]
  rcases hop with ⟨hop,rfl⟩ | ⟨hop,rfl⟩
  · rcases hins with hin | hin <;>
      simp only [hop,hin,List.map_cons,List.map_nil,ite_eq_left hv',ite_eq_left hw',
        hvalw,GateOp.eval,List.all_cons,List.all_nil,id_eq,Bool.and_true,
        Bool.and_false,Bool.false_and]
  · rcases hins with hin | hin <;>
      simp only [hop,hin,List.map_cons,List.map_nil,ite_eq_left hv',ite_eq_left hw',
        hvalw,GateOp.eval,List.any_cons,List.any_nil,id_eq,Bool.or_false,
        Bool.or_true,Bool.true_or]

/-- For canonical free-NOT(x0) inputs, a nonzero variable used at one gate
cannot be ANDed or ORed there with another primitive input. Any correct circuit
must read that variable elsewhere (or output it directly, already impossible
for the Petersen target). -/
theorem no_unique_primitive_gate (C : Circuit) (r : ℕ) (v : Fin 10) (w : Fin 11)
    (hr : r < C.gates.length) (hv0 : v ≠ 0) (hwv : w.val ≠ v.val)
    (hcomputes : ∀ x : Fin 10 → Bool, C.eval (augmented x) = target x)
    (hout : C.output ≠ v.val)
    (hreads : ∀ k < C.gates.length, k ≠ r → v.val ∉ (gateAt C k).inputs)
    (hop : (gateAt C r).op = GateOp.and ∨ (gateAt C r).op = GateOp.or)
    (hins : (gateAt C r).inputs = [v.val,w.val] ∨
      (gateAt C r).inputs = [w.val,v.val]) : False := by
  have collide (b : Bool)
      (hblock : ((gateAt C r).op = GateOp.and ∧ b = false) ∨
        ((gateAt C r).op = GateOp.or ∧ b = true)) : False := by
    let x := witness v w b
    let y := Function.update x v true
    obtain ⟨hPx,hPy,hxw,hyw,hagree⟩ := pinning_certificate v w b hv0 hwv
    have hxlen : (augmented x).length = 11 := by simp [augmented]
    have hylen : (augmented y).length = 11 := by simp [augmented]
    have hv11 : v.val < 11 := by have := v.isLt; omega
    have hgate : val C (augmented x) (11+r) = val C (augmented y) (11+r) := by
      rw [blocked_gate_value C (augmented x) hxlen r v.val w.val hr hv11 w.isLt b hins hblock hxw,
        blocked_gate_value C (augmented y) hylen r v.val w.val hr hv11 w.isLt b hins hblock hyw]
    have hinput : ∀ i < 11, i ≠ v.val →
        (augmented x).getD i false = (augmented y).getD i false := by
      intro i hi hine
      exact hagree ⟨i,hi⟩ hine
    have heq := sole_reader_collision C (augmented x) (augmented y) hxlen hylen v.val r
      hv11 hinput hreads hgate hout
    rw [hcomputes x,hcomputes y] at heq
    change target (witness v w b) = target (Function.update (witness v w b) v true) at heq
    rw [hPx,hPy] at heq
    cases heq
  rcases hop with ha | ho
  · exact collide false (Or.inl ⟨ha,rfl⟩)
  · exact collide true (Or.inr ⟨ho,rfl⟩)


lemma target_unit_false : ∀ v : Fin 10,
    target (fun u => decide (u = v)) = false := by decide +kernel

theorem output_not_raw (C : Circuit)
    (hcomputes : ∀ x : Fin 10 → Bool, C.eval (augmented x) = target x)
    (v : Fin 10) : C.output ≠ v.val := by
  intro ho
  let x : Fin 10 → Bool := fun u => decide (u = v)
  have hx : (augmented x).length = 11 := by simp [augmented]
  have hv : v.val < 11 := by have := v.isLt; omega
  have hbit : (augmented x).getD v.val false = true := by
    change (List.ofFn x ++ [!x 0]).getD v.val false = true
    rw [List.getD_append _ _ _ _ (by simpa using v.isLt)]
    rw [List.getD_eq_getElem _ _ (by simpa using v.isLt),List.getElem_ofFn]
    simp [x]
  have hh := hcomputes x
  change val C (augmented x) C.output = target x at hh
  rw [ho,val_input hx hv,hbit] at hh
  have hf : target x = false := target_unit_false v
  rw [hf] at hh
  cases hh

/-- A primitive AND/OR join forces a second reader of each participating
nonzero raw variable. This statement needs no gate-budget hypothesis. -/
theorem primitive_join_forces_another_reader (C : Circuit) (r : ℕ)
    (v : Fin 10) (w : Fin 11) (hr : r < C.gates.length) (hv0 : v ≠ 0)
    (hwv : w.val ≠ v.val)
    (hcomputes : ∀ x : Fin 10 → Bool, C.eval (augmented x) = target x)
    (hop : (gateAt C r).op = GateOp.and ∨ (gateAt C r).op = GateOp.or)
    (hins : (gateAt C r).inputs = [v.val,w.val] ∨
      (gateAt C r).inputs = [w.val,v.val]) :
    ∃ k < C.gates.length, k ≠ r ∧ v.val ∈ (gateAt C k).inputs := by
  by_contra hnone
  exact no_unique_primitive_gate C r v w hr hv0 hwv hcomputes (output_not_raw C hcomputes v)
    (fun k hk hkr hread => hnone ⟨k,hk,hkr,hread⟩) hop hins

end PEqualNP.Outside.Pnp1884UniqueRead
