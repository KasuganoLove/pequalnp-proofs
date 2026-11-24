import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.PetersenRows

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The monotonicity lemmas are from the project's Helpers/LowMergeWires.
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def LeL (a b : List Bool) : Prop := ∀ i, a.getD i false = true → b.getD i false = true

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ)
    (f f' : ℕ → Bool) (h : ∀ i, f i = true → f' i = true) :
    op.eval (l.map f) = true → op.eval (l.map f') = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
    intro H x hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact h i (H (f i) ⟨i, hi, rfl⟩)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
    rintro ⟨x, ⟨i, hi, rfl⟩, hx⟩
    exact ⟨f' i, ⟨i, hi, rfl⟩, h i hx⟩

theorem fold_mono (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ a b : List Bool, a.length = b.length → LeL a b →
      LeL (gs.foldl step a) (gs.foldl step b) := by
  induction gs with
  | nil => intro a b _ h; exact h
  | cons g gs ih =>
    intro a b hl h
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    · simp [step, hl]
    · intro i hi
      unfold step at hi ⊢
      by_cases hia : i < a.length
      · rw [List.getD_append _ _ _ _ hia] at hi
        rw [List.getD_append _ _ _ _ (by omega)]
        exact h i hi
      · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
        rw [List.getD_append_right _ _ _ _ (by omega)]
        rw [← hl]
        by_cases he : i - a.length = 0
        · rw [he] at hi ⊢
          simp only [List.getD_cons_zero] at hi ⊢
          exact eval_mono g.op (hgs g List.mem_cons_self) _ _ _ (fun k => h k) hi
        · obtain ⟨m, hm⟩ : ∃ m, i - a.length = m + 1 := ⟨i - a.length - 1, by omega⟩
          rw [hm] at hi; simp at hi

theorem wires_mono (C : Circuit) (hC : IsMonotoneCircuit C) (a b : List Bool)
    (hl : a.length = b.length) (h : LeL a b) : LeL (C.wires a) (C.wires b) :=
  fold_mono C.gates hC a b hl h

def rows : List Nat :=
  [3,6,12,17,24,33,42,50,66,69,104,116,132,138,160,201,208,261,264,276,288,320,385,402]

def yes : List Nat := [3,6,12,17,24,33,66,132,160,264,288,320]

def edges : List (Fin 9 × Fin 9) :=
  [(0,1),(1,2),(2,3),(0,4),(3,4),(0,5),(1,6),(2,7),(5,7),(3,8),(5,8),(6,8)]

def f (x : Fin 9 → Bool) : Bool := edges.any (fun e => x e.1 && x e.2)

def v (r : Nat) (i : Fin 9) := r.testBit i.val

def enc (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 || x 4]

def below (x y : Fin 9 → Bool) : Prop := ∀ i, x i = true → y i = true

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem positiveCover : ∀ x : Fin 9 → Bool, f x = true →
    ∃ r ∈ rows, r ∈ yes ∧ ∀ i, v r i = true → x i = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem negativeCover : ∀ x : Fin 9 → Bool, f x = false →
    ∃ r ∈ rows, r ∉ yes ∧ ∀ i, x i = true → v r i = true := by
  decide +kernel

theorem enc_monotone (x y : Fin 9 → Bool) (h : below x y) : LeL (enc x) (enc y) := by
  intro i
  by_cases hi : i < 9
  · rw [enc, enc, List.getD_append _ _ _ _ (by simpa using hi),
      List.getD_append _ _ _ _ (by simpa using hi)]
    interval_cases i <;> simpa using h _
  · by_cases he : i = 9
    · subst i
      have imply : x 0 || x 4 = true → y 0 || y 4 = true := by
        simp only [Bool.or_eq_true]
        exact Or.imp (h 0) (h 4)
      simpa [enc] using imply
    · rw [List.getD_eq_default _ _ (by simp [enc]; omega)]
      simp

theorem rows_determine (C : Circuit) (hm : Monotone2 C)
    (tests : ∀ r ∈ rows, C.eval (enc (v r)) = decide (r ∈ yes)) :
    ∀ x : Fin 9 → Bool, C.eval (enc x) = f x := by
  have mop : IsMonotoneCircuit C := fun g hg => by simpa using (hm g hg).1
  have up (x y : Fin 9 → Bool) (h : below x y) :
      C.eval (enc x) = true → C.eval (enc y) = true :=
    wires_mono C mop (enc x) (enc y) (by simp [enc]) (enc_monotone x y h) C.output
  intro x
  cases he : f x with
  | false =>
    obtain ⟨r, hr, hn, h⟩ := negativeCover x he
    by_contra! wrong
    have actual := up x (v r) h (by simpa using wrong)
    simp [tests r hr, hn] at actual
  | true =>
    obtain ⟨r, hr, hy, h⟩ := positiveCover x he
    exact up (v r) x h (by simp [tests r hr, hy])

end PEqualNP.Outside.PetersenRows

theorem PEqualNP.Outside.PetersenRows : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C → (∀ x3 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (42 : ℕ), (50 : ℕ), (66 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (132 : ℕ), (138 : ℕ), (160 : ℕ), (201 : ℕ), (208 : ℕ), (261 : ℕ), (264 : ℕ), (276 : ℕ), (288 : ℕ), (320 : ℕ), (385 : ℕ), (402 : ℕ)],         have x5 : Fin (9 : ℕ) → Bool := fun (x5 : Fin (9 : ℕ)) => x3.testBit ↑x5;         C.eval (List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ))]) = Decidable.decide (x3 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ)])) → ∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 4]) = (fun x : Fin 9 → Bool => ([(0, 1), (1, 2), (2, 3), (0, 4), (3, 4), (0, 5), (1, 6), (2, 7), (5, 7), (3, 8), (5, 8), (6, 8)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)) x :=
  PEqualNP.Outside.PetersenRows.rows_determine
