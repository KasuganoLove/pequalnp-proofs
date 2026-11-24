import Mathlib.Data.List.Count
import Mathlib.Data.List.GetD
import Mathlib.Tactic
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace Pnp3608Finite

def capGate (bound : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (fun i => min i bound)⟩

def capCircuit (bound : ℕ) (C : Circuit) : Circuit :=
  ⟨C.gates.map (capGate bound), C.output⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem getD_cap (w : List Bool) (bound i : ℕ) (h : w.length ≤ bound) :
    w.getD (min i bound) false = w.getD i false := by
  by_cases hi : i ≤ bound
  · rw [Nat.min_eq_left hi]
  · have hb : bound ≤ i := by omega
    rw [Nat.min_eq_right hb, List.getD_eq_default w false h,
      List.getD_eq_default w false (by omega)]

theorem step_cap (w : List Bool) (bound : ℕ) (g : Gate) (h : w.length ≤ bound) :
    step w (capGate bound g) = step w g := by
  unfold step capGate
  simp only [List.map_map, Function.comp_def]
  congr 2
  apply congrArg g.op.eval
  apply List.map_congr_left
  intro i _
  exact getD_cap w bound i h

theorem fold_cap (gs : List Gate) (bound : ℕ) (w : List Bool)
    (h : w.length + gs.length ≤ bound + 1) :
    (gs.map (capGate bound)).foldl step w = gs.foldl step w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    have hw : w.length ≤ bound := by simp only [List.length_cons] at h; omega
    simp only [List.map_cons, List.foldl_cons, step_cap w bound g hw]
    apply ih
    simp only [step, List.length_append, List.length_cons, List.length_nil]
    simp only [List.length_cons] at h
    omega

theorem wires_cap (C : Circuit) (x : List Bool) (bound : ℕ)
    (h : x.length + C.size ≤ bound + 1) :
    (capCircuit bound C).wires x = C.wires x :=
  fold_cap C.gates bound x h

theorem eval_cap (C : Circuit) (x : List Bool) (bound : ℕ)
    (h : x.length + C.size ≤ bound + 1) :
    (capCircuit bound C).eval x = C.eval x := by
  unfold Circuit.eval
  rw [wires_cap C x bound h]
  rfl

theorem cap_eq_below (bound i k : ℕ) (hk : k < bound) :
    min i bound = k ↔ i = k := by omega

theorem count_cap (xs : List ℕ) (bound k : ℕ) (hk : k < bound) :
    (xs.map (fun i => min i bound)).count k = xs.count k := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.map_cons, List.count_cons, ih]
    have ha : (min a bound == k) = (a == k) := by
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq, cap_eq_below bound a k hk]
    rw [ha]

theorem operands_cap (C : Circuit) (bound : ℕ) :
    ((capCircuit bound C).gates.flatMap Gate.inputs) =
      (C.gates.flatMap Gate.inputs).map (fun i => min i bound) := by
  simp only [capCircuit, List.flatMap_map, capGate,
    List.map_flatMap]

theorem count_operands_cap (C : Circuit) (bound k : ℕ) (hk : k < bound) :
    ((capCircuit bound C).gates.flatMap Gate.inputs).count k =
      (C.gates.flatMap Gate.inputs).count k := by
  rw [operands_cap, count_cap _ bound k hk]

theorem all_indices_cap (C : Circuit) (bound : ℕ) :
    ∀ g ∈ (capCircuit bound C).gates, ∀ i ∈ g.inputs, i ≤ bound := by
  intro g hg i hi
  obtain ⟨old, _, rfl⟩ := List.mem_map.mp hg
  obtain ⟨oldi, _, rfl⟩ := List.mem_map.mp hi
  exact Nat.min_le_right _ _

theorem fanInTwo_cap (C : Circuit) (bound : ℕ) (h : FanInTwo C) :
    FanInTwo (capCircuit bound C) := by
  intro g hg
  obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hg
  simpa [capGate] using h old hold

theorem size_cap (C : Circuit) (bound : ℕ) :
    (capCircuit bound C).size = C.size := by
  simp [capCircuit, Circuit.size]

theorem unaryNot_cap (C : Circuit) (bound : ℕ)
    (h : ∀ g ∈ C.gates, g.op = GateOp.not → g.inputs.length ≤ 1) :
    ∀ g ∈ (capCircuit bound C).gates,
      g.op = GateOp.not → g.inputs.length ≤ 1 := by
  intro g hg hn
  obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hg
  simpa [capGate] using h old hold hn

theorem pair_cap_inv (g : Gate) (bound a b : ℕ) (ha : a < bound) (hb : b < bound)
    (h : (capGate bound g).inputs = [a,b]) : g.inputs = [a,b] := by
  have len : g.inputs.length = 2 := by simpa [capGate] using congrArg List.length h
  obtain ⟨x,y,hi⟩ := List.length_eq_two.mp len
  have hxy : min x bound = a ∧ min y bound = b := by simpa [capGate, hi] using h
  rw [hi, (cap_eq_below bound x a ha).mp hxy.1, (cap_eq_below bound y b hb).mp hxy.2]

theorem covers_cap (C : Circuit) (bound : ℕ)
    (h : ∀ k < bound, k ∈ C.gates.flatMap Gate.inputs) :
    ∀ k < bound, k ∈ (capCircuit bound C).gates.flatMap Gate.inputs := by
  intro k hk
  apply List.count_pos_iff.mp
  rw [count_operands_cap C bound k hk]
  exact List.count_pos_iff.mpr (h k hk)

theorem multi_cap (C : Circuit) (bound : ℕ) :
    ((Finset.range bound).filter
      (fun k => 2 ≤ ((capCircuit bound C).gates.flatMap Gate.inputs).count k)) =
    ((Finset.range bound).filter (fun k => 2 ≤ (C.gates.flatMap Gate.inputs).count k)) := by
  apply Finset.filter_congr
  intro k hk
  rw [count_operands_cap C bound k (Finset.mem_range.mp hk)]

theorem raw_pairs_cap (C : Circuit)
    (h : ∀ g ∈ C.gates, ∀ a b : Fin 9, a ≠ b →
      (g.op = GateOp.and ∨ g.op = GateOp.or) → g.inputs = [a.val,b.val] →
      2 ≤ (C.gates.flatMap Gate.inputs).count a.val ∨
      2 ≤ (C.gates.flatMap Gate.inputs).count b.val) :
    ∀ g ∈ (capCircuit 23 C).gates, ∀ a b : Fin 9, a ≠ b →
      (g.op = GateOp.and ∨ g.op = GateOp.or) → g.inputs = [a.val,b.val] →
      2 ≤ ((capCircuit 23 C).gates.flatMap Gate.inputs).count a.val ∨
      2 ≤ ((capCircuit 23 C).gates.flatMap Gate.inputs).count b.val := by
  intro g hg a b hab hop hpair
  obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hg
  have ha : a.val < 23 := by omega
  have hb : b.val < 23 := by omega
  rw [count_operands_cap C 23 a.val ha, count_operands_cap C 23 b.val hb]
  exact h old hold a b hab hop (pair_cap_inv old 23 a.val b.val ha hb hpair)

theorem two_nots_cap (C : Circuit) (bound : ℕ)
    (h : ∃ i j : Fin C.gates.length,
      i < j ∧ 3 ≤ i.val ∧ i.val ≤ 6 ∧ j.val < 13 ∧
      (C.gates.get i).op = GateOp.not ∧ (C.gates.get j).op = GateOp.not ∧
      ∀ k : Fin C.gates.length, (C.gates.get k).op = GateOp.not → k = i ∨ k = j) :
    ∃ i j : Fin (capCircuit bound C).gates.length,
      i < j ∧ 3 ≤ i.val ∧ i.val ≤ 6 ∧ j.val < 13 ∧
      ((capCircuit bound C).gates.get i).op = GateOp.not ∧
      ((capCircuit bound C).gates.get j).op = GateOp.not ∧
      ∀ k : Fin (capCircuit bound C).gates.length,
        ((capCircuit bound C).gates.get k).op = GateOp.not → k = i ∨ k = j := by
  obtain ⟨i,j,hij,hlo,hhi,hj,hiN,hjN,honly⟩ := h
  let lift : Fin C.gates.length → Fin (capCircuit bound C).gates.length :=
    fun k => ⟨k.val, by simpa only [capCircuit, List.length_map] using k.isLt⟩
  refine ⟨lift i,lift j,hij,hlo,hhi,hj,?_,?_,?_⟩
  · simpa [lift, capCircuit, capGate] using hiN
  · simpa [lift, capCircuit, capGate] using hjN
  · intro k hk
    let old : Fin C.gates.length := ⟨k.val, by simpa [capCircuit] using k.isLt⟩
    have hn : (C.gates.get old).op = GateOp.not := by
      change ((C.gates.map (capGate bound))[k.val]'k.isLt).op = GateOp.not at hk
      have hm := List.getElem_map (capGate bound) (l := C.gates) (i := k.val) (h := k.isLt)
      exact (congrArg Gate.op hm).symm.trans hk
    rcases honly old hn with he | he
    · exact Or.inl (Fin.ext (congrArg (fun t : Fin C.gates.length => t.val) he))
    · exact Or.inr (Fin.ext (congrArg (fun t : Fin C.gates.length => t.val) he))

def sortPair : Gate → Gate
  | ⟨GateOp.and, [a,b]⟩ => ⟨GateOp.and, [min a b, max a b]⟩
  | ⟨GateOp.or, [a,b]⟩ => ⟨GateOp.or, [min a b, max a b]⟩
  | g => g

theorem step_sortPair (w : List Bool) (g : Gate) :
    step w (sortPair g) = step w g := by
  obtain ⟨op,ins⟩ := g
  cases ins with
  | nil => cases op <;> rfl
  | cons a rest =>
    cases rest with
    | nil => cases op <;> rfl
    | cons b rest =>
      cases rest with
      | cons c tail => cases op <;> rfl
      | nil =>
        cases op <;> try rfl
        all_goals
          by_cases hab : a ≤ b
          · simp [sortPair, Nat.min_eq_left hab, Nat.max_eq_right hab]
          · have hba : b ≤ a := by omega
            simp [sortPair, Nat.min_eq_right hba, Nat.max_eq_left hba,
              step, GateOp.eval, Bool.and_comm, Bool.or_comm]

theorem fold_sortPair (gs : List Gate) (w : List Bool) :
    (gs.map sortPair).foldl step w = gs.foldl step w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, List.foldl_cons, step_sortPair, ih]

theorem eval_cap_3608 (C : Circuit) (hsize : C.size = 14) (r : ℕ) :
    (capCircuit 23 C).eval
      ((List.ofFn fun i : Fin 9 => r.testBit i.val) ++ [r.testBit 0 || r.testBit 2]) =
    C.eval
      ((List.ofFn fun i : Fin 9 => r.testBit i.val) ++ [r.testBit 0 || r.testBit 2]) := by
  apply eval_cap
  simp [hsize]

end Pnp3608Finite
