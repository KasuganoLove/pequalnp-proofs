import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Every gate of a fifteen-gate counterexample must fire on at least two of the twelve edge inputs.
-- The remaining search uses these per-gate conditions and the twenty-four extremal output tests.
theorem PEqualNP.Outside.R_meta_2766_724
    (covered : ∀ C : Circuit, Monotone2 C → C.size≤15 → circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) →
      let pos := ([3,6,12,17,24,33,66,132,160,264,288,320] : List ℕ)
      ∀ (j : Fin C.size) (r : ℕ), r∈pos → ∃ s∈pos, s≠r ∧
        (C.wires (List.ofFn (fun i : Fin 9 => s.testBit i.val))).getD (9+j.val) false = true)
    (residual : ∀ C : Circuit, Monotone2 C → C.size=15 → C.output=23 → C.gates[0]?=some ⟨.or,[0,3]⟩ →
      (let pos := ([3,6,12,17,24,33,66,132,160,264,288,320] : List ℕ)
      ∀ (j : Fin C.size) (r : ℕ), r∈pos → ∃ s∈pos, s≠r ∧
        (C.wires (List.ofFn (fun i : Fin 9 => s.testBit i.val))).getD (9+j.val) false = true) →
      let out := fun m : ℕ => C.eval (List.ofFn (fun i : Fin 9 => m.testBit i.val))
      (∀ m ∈ ([3,6,12,17,24,33,66,132,160,264,288,320] : List ℕ), out m = true) →
      (∀ m ∈ ([42,50,69,104,116,138,201,208,261,276,385,402] : List ℕ), out m = false) → False) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   (x1.gates.length = (15 : ℕ) ∧       x1.output = (23 : ℕ) ∧         x1.gates[(0 : ℕ)]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(0 : ℕ), (3 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } ∧           ∀ (x2 : ℕ) (x3 : x2 < x1.gates.length),             have x4 : PEqualNP.CircuitLowerBounds.Gate := x1.gates[x2];             have x5 : ℕ → Prop := fun (x5 : ℕ) => x5 < (9 : ℕ) + x2 ∨ x5 = (24 : ℕ);             have x6 : ℕ → ℕ := fun (x6 : ℕ) => if x6 < (9 : ℕ) then x6 else if x6 = (24 : ℕ) then (9 : ℕ) else x6 + (1 : ℕ);             x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [] : PEqualNP.CircuitLowerBounds.Gate } ∨ (∃ (x7 : ℕ), x5 x7 ∧ x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [x7] : PEqualNP.CircuitLowerBounds.Gate }) ∨ ∃ (x7 : ℕ) (x8 : ℕ), x5 x7 ∧ x5 x8 ∧ x6 x7 ≤ x6 x8 ∧ (x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x7, x8] : PEqualNP.CircuitLowerBounds.Gate } ∨ x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [x7, x8] : PEqualNP.CircuitLowerBounds.Gate })) →     List.countP (fun (x3 : PEqualNP.CircuitLowerBounds.Gate) => x3.op.eval [Bool.false]) x1.gates = (0 : ℕ) → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 ≠ fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) := by
  intro C normal count computed
  obtain ⟨len,out,first,legal⟩ := normal
  have mono : Monotone2 C := by
    intro g hg
    obtain ⟨i,hi,hg'⟩ := List.getElem_of_mem hg
    have hz := List.countP_eq_zero.mp count g hg
    rcases legal i hi with eq | ⟨a,_,eq⟩ | ⟨a,b,_,_,_,eq | eq⟩
    · simp [←hg',eq]
    · rw [←hg',eq] at hz; exact (hz rfl).elim
    · simp [←hg',eq]
    · simp [←hg',eq]
  have size : C.size=15 := len
  apply residual C mono size out first (covered C mono (Nat.le_of_eq size) computed)
  · intro m hm
    have yes : ∀ m ∈ ([3,6,12,17,24,33,66,132,160,264,288,320] : List ℕ), (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) (fun i => m.testBit i.val) = true := by decide +kernel
    exact (congrFun computed (fun i => m.testBit i.val)).trans (yes m hm)
  · intro m hm
    have no : ∀ m ∈ ([42,50,69,104,116,138,201,208,261,276,385,402] : List ℕ), (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) (fun i => m.testBit i.val) = false := by decide +kernel
    exact (congrFun computed (fun i => m.testBit i.val)).trans (no m hm)
