import Mathlib
import PEqualNP.Defs

namespace Pnp2309Scratch
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def activeInputs (g : Gate) : List Nat :=
  if g.op.eval [false] = true then g.inputs.take 1 else g.inputs

def reads (g : Gate) : Bool := [0, 9].any fun j => (activeInputs g).contains j

def target (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
  (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
  (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wiresFrom_start (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    change wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) = _
    rw [ht]; simp

lemma getD_wiresFrom (gs : List Gate) (w : List Bool) (i : Nat) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_start gs w
  rw [ht, List.getD_append _ _ _ _ h]

lemma getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : Nat) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma gate_congr_away (g : Gate)
    (hok : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (w w' : List Bool)
    (hw : ∀ i, i ≠ 0 → i ≠ 9 → w.getD i false = w'.getD i false)
    (hmiss : 0 ∉ activeInputs g ∧ 9 ∉ activeInputs g) :
    g.op.eval (g.inputs.map fun i => w.getD i false) =
      g.op.eval (g.inputs.map fun i => w'.getD i false) := by
  obtain ⟨op, ins⟩ := g
  rcases hok with h | h | h
  · change op = GateOp.and at h
    subst op
    simp only [activeInputs, GateOp.eval, List.all_cons, List.all_nil] at hmiss
    congr 1
    apply List.map_congr_left
    intro i hi
    exact hw i (fun e => hmiss.1 (e ▸ hi)) (fun e => hmiss.2 (e ▸ hi))
  · change op = GateOp.or at h
    subst op
    simp only [activeInputs, GateOp.eval, List.any_cons, List.any_nil] at hmiss
    congr 1
    apply List.map_congr_left
    intro i hi
    exact hw i (fun e => hmiss.1 (e ▸ hi)) (fun e => hmiss.2 (e ▸ hi))
  · change op = GateOp.not at h
    subst op
    cases ins with
    | nil => rfl
    | cons i ins =>
      have h0 : i ≠ 0 := by
        simpa [activeInputs, GateOp.eval, eq_comm] using hmiss.1
      have h9 : i ≠ 9 := by
        simpa [activeInputs, GateOp.eval, eq_comm] using hmiss.2
      change Bool.not (w.getD i false) = Bool.not (w'.getD i false)
      rw [hw i h0 h9]

lemma tail_congr_away (gs : List Gate)
    (hok : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hmiss : ∀ g ∈ gs, 0 ∉ activeInputs g ∧ 9 ∉ activeInputs g) :
    ∀ w w' : List Bool, 10 ≤ w.length → w.length = w'.length →
    (∀ i, i ≠ 0 → i ≠ 9 → w.getD i false = w'.getD i false) →
    ∀ i, i ≠ 0 → i ≠ 9 →
      (wiresFrom gs w).getD i false = (wiresFrom gs w').getD i false := by
  induction gs with
  | nil => intro w w' _ _ hw; exact hw
  | cons g gs ih =>
    intro w w' hlen hlen' hw
    have hv := gate_congr_away g (hok g List.mem_cons_self) w w' hw
      (hmiss g List.mem_cons_self)
    apply ih (fun k hk => hok k (List.mem_cons_of_mem _ hk))
      (fun k hk => hmiss k (List.mem_cons_of_mem _ hk))
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
      (by simp; omega) (by simp [hlen'])
    intro i h0 h9
    by_cases hi : i = w.length
    · subst i
      calc
        _ = g.op.eval (g.inputs.map fun i => w.getD i false) := by simp
        _ = g.op.eval (g.inputs.map fun i => w'.getD i false) := hv
        _ = _ := by rw [hlen']; simp
    · rw [getD_snoc_ne _ _ _ _ hi, getD_snoc_ne _ _ _ _ (by omega)]
      exact hw i h0 h9

def base (edge : Bool) (toggle : Bool) : Fin 9 → Bool :=
  fun i => if i = 0 then toggle else if i = 1 then edge else false

lemma base_target : target (base true false) = false ∧ target (base true true) = true ∧
    target (base false false) = false ∧ target (base false true) = false := by decide

lemma start_congr (edge : Bool) :
    ∀ i, i ≠ 0 → i ≠ 9 →
      (List.ofFn (base edge false) ++ [true]).getD i false =
      (List.ofFn (base edge true) ++ [false]).getD i false := by
  intro i h0 h9
  by_cases hi : i < 9
  · rw [List.getD_append _ _ _ _ (by simpa), List.getD_append _ _ _ _ (by simpa)]
    interval_cases i <;> simp_all [base]
  · rw [List.getD_eq_default _ _ (by simp; omega),
        List.getD_eq_default _ _ (by simp; omega)]

lemma first_value (C : Circuit) (g : Gate) (gs : List Gate)
    (hgates : C.gates = g :: gs)
    (hfirst : ∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = !x 0)
    (x : Fin 9 → Bool) :
    g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false) = !x 0 := by
  have hf := hfirst x
  change (wiresFrom C.gates (List.ofFn x)).getD 9 false = _ at hf
  rw [hgates] at hf
  change (wiresFrom gs (List.ofFn x ++ [g.op.eval
    (g.inputs.map fun i => (List.ofFn x).getD i false)])).getD 9 false = _ at hf
  rw [getD_wiresFrom _ _ _ (by simp)] at hf
  simpa using hf

lemma cannot_have_zero_readers (C : Circuit) (hfan : FanInTwo C)
    (hfirst : ∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = !x 0)
    (hfun : circuitFun 9 C = target)
    (hzero : ((C.gates.drop 1).filter reads).length = 0) : False := by
  have hnil : C.gates ≠ [] := by
    intro h
    have hf := hfirst (base false false)
    simp [Circuit.wires, h, base] at hf
  obtain ⟨g, gs, hgates⟩ := List.exists_cons_of_ne_nil hnil
  have hmiss : ∀ k ∈ gs, 0 ∉ activeInputs k ∧ 9 ∉ activeInputs k := by
    rw [hgates] at hzero
    simp only [List.drop_succ_cons, List.drop_zero, List.length_eq_zero_iff,
      List.filter_eq_nil_iff] at hzero
    intro k hk
    have hn := hzero k hk
    simpa [reads] using hn
  have htail : ∀ k ∈ gs, k.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) := by
    intro k hk
    exact (hfan k (hgates ▸ List.mem_cons_of_mem g hk)).1
  have houtput0 : C.output ≠ 0 := by
    intro ho
    have h := congrFun hfun (base false true)
    change (wiresFrom C.gates (List.ofFn (base false true))).getD C.output false = _ at h
    rw [ho, getD_wiresFrom _ _ _ (by simp)] at h
    have ht := base_target.2.2.2
    simp [base, ht] at h
  have houtput9 : C.output ≠ 9 := by
    intro ho
    have h := congrFun hfun (base false false)
    change (C.wires (List.ofFn (base false false))).getD C.output false = _ at h
    rw [ho, hfirst] at h
    have ht := base_target.2.2.1
    simp [base, ht] at h
  have hEq := tail_congr_away gs htail hmiss
    (List.ofFn (base true false) ++ [true])
    (List.ofFn (base true true) ++ [false]) (by simp) (by simp)
    (start_congr true) C.output houtput0 houtput9
  have hEval (b : Bool) :
      C.eval (List.ofFn (base true b)) =
      (wiresFrom gs (List.ofFn (base true b) ++ [!b])).getD C.output false := by
    unfold Circuit.eval Circuit.wires
    rw [hgates]
    change (wiresFrom gs (List.ofFn (base true b) ++
      [g.op.eval (g.inputs.map fun i => (List.ofFn (base true b)).getD i false)])).getD _ _ = _
    rw [first_value C g gs hgates hfirst]
    rfl
  have hFalse := congrFun hfun (base true false)
  have hTrue := congrFun hfun (base true true)
  change C.eval (List.ofFn (base true false)) = _ at hFalse
  change C.eval (List.ofFn (base true true)) = _ at hTrue
  rw [hEval false, base_target.1] at hFalse
  rw [hEval true, base_target.2.1] at hTrue
  exact Bool.false_ne_true (hFalse.symm.trans (hEq.trans hTrue))

lemma active_reader_count_positive (C : Circuit) (hfan : FanInTwo C)
    (hfirst : ∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = !x 0)
    (hfun : circuitFun 9 C = target) :
    1 ≤ (((C.gates.drop 1).map (fun g =>
      Gate.mk g.op (if g.op.eval [false] = true then g.inputs.take 1 else g.inputs))).filter
        (fun g => [0, 9].any fun j => g.inputs.contains j)).length := by
  have heq : (((C.gates.drop 1).map (fun g =>
      Gate.mk g.op (if g.op.eval [false] = true then g.inputs.take 1 else g.inputs))).filter
        (fun g => [0, 9].any fun j => g.inputs.contains j)).length =
      ((C.gates.drop 1).filter reads).length := by
    simp only [List.filter_map, List.length_map]
    rfl
  rw [heq]
  exact Nat.one_le_iff_ne_zero.mpr (cannot_have_zero_readers C hfan hfirst hfun)

end Pnp2309Scratch
