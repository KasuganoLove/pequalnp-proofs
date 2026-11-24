import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2604

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def run (gs : List Gate) (xs : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) xs

lemma run_length (gs : List Gate) (xs : List Bool) :
    (run gs xs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (xs ++ [g.op.eval (g.inputs.map fun i => xs.getD i false)])).length = _
    rw [ih]
    simp
    omega

lemma run_input (gs : List Gate) (xs : List Bool) (i : ℕ) (hi : i < xs.length) :
    (run gs xs).getD i false = xs.getD i false := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (xs ++ [g.op.eval (g.inputs.map fun k => xs.getD k false)])).getD i false = _
    rw [ih _ (by simp; omega), List.getD_append _ _ _ _ hi]

lemma run_snoc (gs : List Gate) (g : Gate) (xs : List Bool) :
    run (gs ++ [g]) xs = run gs xs ++
      [g.op.eval (g.inputs.map fun i => (run gs xs).getD i false)] := by
  simp [run, List.foldl_append]

lemma run_set_early (gs : List Gate) (j t : ℕ) (g' : Gate) (xs : List Bool)
    (ht : t < xs.length + j) :
    (run (gs.set j g') xs).getD t false = (run gs xs).getD t false := by
  induction gs generalizing j xs with
  | nil => simp [run]
  | cons g gs ih =>
    cases j with
    | zero =>
      have h : t < xs.length := by simpa using ht
      exact (run_input _ xs t h).trans (run_input _ xs t h).symm
    | succ j =>
      change (run (gs.set j g')
        (xs ++ [g.op.eval (g.inputs.map fun i => xs.getD i false)])).getD t false =
        (run gs (xs ++ [g.op.eval (g.inputs.map fun i => xs.getD i false)])).getD t false
      apply ih
      simp only [List.length_append, List.length_singleton]
      omega

lemma run_set_or_false (gs : List Gate) (j u t : ℕ) (xs : List Bool)
    (hg : gs[j]? = some { op := GateOp.or, inputs := [u, t] })
    (ht : t < xs.length + j)
    (hf : (run gs xs).getD t false = false) :
    run (gs.set j { op := GateOp.or, inputs := [u] }) xs = run gs xs := by
  induction gs generalizing j xs with
  | nil => simp at hg
  | cons g gs ih =>
    cases j with
    | zero =>
      have he : g = { op := GateOp.or, inputs := [u, t] } := by simpa using hg
      subst g
      have h : t < xs.length := by simpa using ht
      have hf' : xs.getD t false = false := by
        rw [← run_input _ xs t h]
        exact hf
      change run gs (xs ++ [GateOp.or.eval ([u].map fun i => xs.getD i false)]) =
        run gs (xs ++ [GateOp.or.eval ([u, t].map fun i => xs.getD i false)])
      simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
        id_eq, Bool.or_false, hf']
    | succ j =>
      change gs[j]? = some { op := GateOp.or, inputs := [u, t] } at hg
      change run (gs.set j { op := GateOp.or, inputs := [u] })
        (xs ++ [g.op.eval (g.inputs.map fun i => xs.getD i false)]) =
        run gs (xs ++ [g.op.eval (g.inputs.map fun i => xs.getD i false)])
      apply ih j _ hg
      · simp only [List.length_append, List.length_singleton]
        omega
      · exact hf

end PEqualNP.Outside.L_meta_2604

theorem PEqualNP.Outside.L_meta_2604 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (j u t : ℕ), PEqualNP.MetaComplexity.Monotone2 C → j < C.gates.length → C.gates[j]? = some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [u, t] } → t < n + j → (∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD t false = true → PEqualNP.MetaComplexity.circuitFun n C x = true) → PEqualNP.MetaComplexity.circuitFun n { gates := C.gates.set j { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [u] } ++ [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [C.output, t] }], output := n + C.gates.length } = PEqualNP.MetaComplexity.circuitFun n C := by
  intro n C j u t hmono hj hgate ht himp
  funext x
  let xs := List.ofFn x
  let gs := C.gates.set j { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [u] }
  have hlen : (PEqualNP.Outside.L_meta_2604.run gs xs).length = n + C.gates.length := by
    simp [PEqualNP.Outside.L_meta_2604.run_length, gs, xs]
  have hearly := PEqualNP.Outside.L_meta_2604.run_set_early C.gates j t
    { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [u] } xs
    (by simpa [xs] using ht)
  change (PEqualNP.Outside.L_meta_2604.run
    (gs ++ [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [C.output, t] }]) xs).getD
    (n + C.gates.length) false = (PEqualNP.Outside.L_meta_2604.run C.gates xs).getD C.output false
  rw [PEqualNP.Outside.L_meta_2604.run_snoc]
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp only [hlen, Nat.sub_self, List.getD_cons_zero, PEqualNP.CircuitLowerBounds.GateOp.eval,
    List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
  cases hv : (PEqualNP.Outside.L_meta_2604.run C.gates xs).getD t false with
  | false =>
    have heq := PEqualNP.Outside.L_meta_2604.run_set_or_false C.gates j u t xs hgate
      (by simpa [xs] using ht) hv
    change PEqualNP.Outside.L_meta_2604.run gs xs = _ at heq
    rw [heq, hv]
    simp
  | true =>
    have hout := himp x hv
    change (PEqualNP.Outside.L_meta_2604.run C.gates xs).getD C.output false = true at hout
    change (PEqualNP.Outside.L_meta_2604.run gs xs).getD t false = _ at hearly
    rw [hearly, hv, hout]
    simp
