import Pnp1884UniqueRead

/-!
Active-reader strengthening of the primitive-input collision lemma.
The active-pin definition is exactly the convention in L-meta-5367 / L-meta-5369:
NOT reads only its first listed input, while the other operators read the list.
The imported pinning certificate and wire helpers retain their original attribution.
-/
namespace PEqualNP.Outside.Pnp1884ActiveRead

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.Outside.Pnp1884UniqueRead

/-- Same active-input convention used for reader counts in 5367/5369. -/
def activePins (g : Gate) : List ℕ :=
  match g.op with
  | .not => g.inputs.take 1
  | _ => g.inputs

lemma activePins_eq_rec (g : Gate) : activePins g =
  GateOp.rec (motive := fun _ => List ℕ) g.inputs g.inputs (g.inputs.take 1)
    (fun _ => g.inputs) g.inputs g.op := by
  unfold activePins
  cases g.op <;> rfl

lemma activePins_not (g : Gate) (hop : g.op = GateOp.not) : activePins g = g.inputs.take 1 := by
  unfold activePins
  rw [hop]

lemma activePins_other (g : Gate) (hop : g.op ≠ GateOp.not) : activePins g = g.inputs := by
  cases ho : g.op with
  | and => simp [activePins,ho]
  | or => simp [activePins,ho]
  | not => exact False.elim (hop ho)
  | mod m => simp [activePins,ho]
  | maj => simp [activePins,ho]

lemma mem_activePins_iff (g : Gate) (v : ℕ) : v ∈ activePins g ↔
    (g.op = GateOp.not ∧ g.inputs.head? = some v) ∨
    (g.op ≠ GateOp.not ∧ v ∈ g.inputs) := by
  by_cases hop : g.op = GateOp.not
  · rw [activePins_not g hop]
    cases hin : g.inputs with
    | nil => simp [hop]
    | cons a as => simp [hop,eq_comm]
  · rw [activePins_other g hop]
    simp [hop]

/-- Agreement on active pins suffices for the value of any root-model gate.
This handles unused NOT tails explicitly and does not need a fan-in assumption. -/
lemma eval_active_congr (g : Gate) (f h : ℕ → Bool)
    (hpin : ∀ i ∈ activePins g, f i = h i) :
    g.op.eval (g.inputs.map f) = g.op.eval (g.inputs.map h) := by
  by_cases hop : g.op = GateOp.not
  · rw [hop]
    cases hin : g.inputs with
    | nil => rfl
    | cons a as =>
      have ha : a ∈ activePins g := by rw [activePins_not g hop,hin]; simp
      simp only [List.map_cons,GateOp.eval,List.headD_cons]
      rw [hpin a ha]
  · congr 1
    apply List.map_congr_left
    intro i hi
    exact hpin i (by rw [activePins_other g hop]; exact hi)

/-- Equalizing the sole active reader erases every effect of changing a raw
input, even if arbitrary NOT tails mention that input at other gates. -/
lemma sole_active_reader_collision {n : ℕ} (C : Circuit) (x y : List Bool)
    (hx : x.length = n) (hy : y.length = n) (v r : ℕ)
    (hinput : ∀ i < n, i ≠ v → x.getD i false = y.getD i false)
    (hreads : ∀ k < C.gates.length, k ≠ r → v ∉ activePins (gateAt C k))
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
      apply eval_active_congr
      intro u hu
      by_cases hut : u < n+k
      · rw [ite_eq_left hut,ite_eq_left hut]
        exact ih u hut (fun huv => hreads k hk hkr (huv ▸ hu))
      · rw [ite_eq_right hut,ite_eq_right hut]
  exact wire C.output hout

/-- The other active reader is forced by the same checked pinning table. -/
theorem no_sole_active_primitive_gate (C : Circuit) (r : ℕ) (v : Fin 10) (w : Fin 11)
    (hr : r < C.gates.length) (hv0 : v ≠ 0) (hwv : w.val ≠ v.val)
    (hcomputes : ∀ x : Fin 10 → Bool, C.eval (augmented x) = target x)
    (hreads : ∀ k < C.gates.length, k ≠ r → v.val ∉ activePins (gateAt C k))
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
    have heq := sole_active_reader_collision C (augmented x) (augmented y) hxlen hylen v.val r
      hinput hreads hgate (output_not_raw C hcomputes v)
    rw [hcomputes x,hcomputes y] at heq
    change target (witness v w b) = target (Function.update (witness v w b) v true) at heq
    rw [hPx,hPy] at heq
    cases heq
  rcases hop with ha | ho
  · exact collide false (Or.inl ⟨ha,rfl⟩)
  · exact collide true (Or.inr ⟨ho,rfl⟩)

/-- A primitive AND/OR join forces another active reader, not an unused NOT
argument. No minimum-size or fan-in restriction is needed. -/
theorem primitive_join_forces_another_active_reader (C : Circuit) (r : ℕ)
    (v : Fin 10) (w : Fin 11) (hr : r < C.gates.length) (hv0 : v ≠ 0)
    (hwv : w.val ≠ v.val)
    (hcomputes : ∀ x : Fin 10 → Bool, C.eval (augmented x) = target x)
    (hop : (gateAt C r).op = GateOp.and ∨ (gateAt C r).op = GateOp.or)
    (hins : (gateAt C r).inputs = [v.val,w.val] ∨
      (gateAt C r).inputs = [w.val,v.val]) :
    ∃ k < C.gates.length, k ≠ r ∧ v.val ∈ activePins (gateAt C k) := by
  by_contra hnone
  exact no_sole_active_primitive_gate C r v w hr hv0 hwv hcomputes
    (fun k hk hkr hread => hnone ⟨k,hk,hkr,hread⟩) hop hins

/-- Equivalent head-versus-membership formulation for direct use with the
active-reader predicates of the public reduction. -/
theorem primitive_join_forces_active_head (C : Circuit) (r : ℕ)
    (v : Fin 10) (w : Fin 11) (hr : r < C.gates.length) (hv0 : v ≠ 0)
    (hwv : w.val ≠ v.val)
    (hcomputes : ∀ x : Fin 10 → Bool, C.eval (augmented x) = target x)
    (hop : (gateAt C r).op = GateOp.and ∨ (gateAt C r).op = GateOp.or)
    (hins : (gateAt C r).inputs = [v.val,w.val] ∨
      (gateAt C r).inputs = [w.val,v.val]) :
    ∃ k < C.gates.length, k ≠ r ∧
      (((gateAt C k).op = GateOp.not ∧ (gateAt C k).inputs.head? = some v.val) ∨
       ((gateAt C k).op ≠ GateOp.not ∧ v.val ∈ (gateAt C k).inputs)) := by
  obtain ⟨k,hk,hkr,hread⟩ := primitive_join_forces_another_active_reader C r v w hr hv0 hwv
    hcomputes hop hins
  exact ⟨k,hk,hkr,(mem_activePins_iff _ _).mp hread⟩

end PEqualNP.Outside.Pnp1884ActiveRead
