import Mathlib.Data.List.GetD
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace Pnp3321Rewrite

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def run (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) :
    (L ++ [S]).getD L.length d = S := by simp

theorem continuation_agree_except (k : ℕ) (gs : List Gate) : ∀ w w' : List Bool,
    (∀ g ∈ gs, k ∉ g.inputs) → w.length = w'.length →
    (∀ j, j ≠ k → w.getD j false = w'.getD j false) →
    ∀ j, j ≠ k → (run gs w).getD j false = (run gs w').getD j false := by
  induction gs with
  | nil => intro w w' _ _ h; exact h
  | cons g gs ih =>
    intro w w' hno hl h
    have hno' := hno g List.mem_cons_self
    have e : (g.inputs.map fun i => w.getD i false) = g.inputs.map fun i => w'.getD i false :=
      List.map_congr_left (fun a ha => h a (fun e => hno' (e ▸ ha)))
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
      (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg')) (by simp [hl])
    intro j hj
    by_cases hjl : j = w.length
    · rw [hjl, getD_snoc_eq, hl, getD_snoc_eq, e]
    · rw [getD_snoc_ne _ _ _ _ hjl, getD_snoc_ne _ _ _ _ (by omega)]
      exact h j hj

def dirtyBlock : List Gate :=
  [⟨GateOp.or,[0,1]⟩,⟨GateOp.or,[0,2]⟩,⟨GateOp.and,[6,7]⟩,
   ⟨GateOp.or,[8,1]⟩,⟨GateOp.or,[8,2]⟩]

def cleanBlock : List Gate :=
  [⟨GateOp.or,[0,1]⟩,⟨GateOp.or,[0,2]⟩,⟨GateOp.or,[0,0]⟩,
   ⟨GateOp.or,[6,6]⟩,⟨GateOp.or,[7,7]⟩]

theorem block_lengths : ∀ x : Fin 6 → Bool,
    (run dirtyBlock (List.ofFn x)).length = 11 ∧
    (run cleanBlock (List.ofFn x)).length = 11 := by
  decide +kernel

theorem block_agree : ∀ (x : Fin 6 → Bool) (j : Fin 11), j.val ≠ 8 →
    (run dirtyBlock (List.ofFn x)).getD j.val false =
    (run cleanBlock (List.ofFn x)).getD j.val false := by
  decide +kernel

theorem block_agree_all (x : Fin 6 → Bool) (j : ℕ) (hj : j ≠ 8) :
    (run dirtyBlock (List.ofFn x)).getD j false =
    (run cleanBlock (List.ofFn x)).getD j false := by
  by_cases h : j < 11
  · exact block_agree x ⟨j,h⟩ hj
  · obtain ⟨hold,hnew⟩ := block_lengths x
    rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]

theorem block_rewrite_continuation (tail : List Gate)
    (hno : ∀ g ∈ tail, 8 ∉ g.inputs) (x : Fin 6 → Bool) :
    ∀ j, j ≠ 8 →
      (run (dirtyBlock ++ tail) (List.ofFn x)).getD j false =
      (run (cleanBlock ++ tail) (List.ofFn x)).getD j false := by
  simp only [run, List.foldl_append]
  apply continuation_agree_except 8 tail
    (run dirtyBlock (List.ofFn x)) (run cleanBlock (List.ofFn x)) hno
  · obtain ⟨hold,hnew⟩ := block_lengths x
    rw [hold,hnew]
  · exact block_agree_all x

theorem block_rewrite_eval (tail : List Gate) (output : ℕ)
    (hno : ∀ g ∈ tail, 8 ∉ g.inputs) (hout : output ≠ 8) (x : Fin 6 → Bool) :
    (⟨dirtyBlock ++ tail,output⟩ : Circuit).eval (List.ofFn x) =
    (⟨cleanBlock ++ tail,output⟩ : Circuit).eval (List.ofFn x) :=
  block_rewrite_continuation tail hno x output hout

theorem block_rewrite_size (tail : List Gate) (output : ℕ) :
    (⟨cleanBlock ++ tail,output⟩ : Circuit).size =
    (⟨dirtyBlock ++ tail,output⟩ : Circuit).size := by
  simp [Circuit.size, dirtyBlock, cleanBlock]

theorem cleanBlock_only_or : ∀ g ∈ cleanBlock, g.op = GateOp.or := by
  intro g hg
  simp [cleanBlock] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem cleanBlock_fanin : ∀ g ∈ cleanBlock, g.inputs.length ≤ 2 := by
  intro g hg
  simp [cleanBlock] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> decide

theorem monotone_preserved (tail : List Gate) (output : ℕ)
    (hmono : Monotone2 (⟨dirtyBlock ++ tail,output⟩ : Circuit)) :
    Monotone2 (⟨cleanBlock ++ tail,output⟩ : Circuit) := by
  intro g hg
  rcases List.mem_append.mp hg with h | h
  · exact ⟨by simp [cleanBlock_only_or g h], cleanBlock_fanin g h⟩
  · exact hmono g (List.mem_append_right _ h)

theorem cleanBlock_readsBack :
    NestedCover.ReadsBack 6 (⟨cleanBlock,0⟩ : Circuit) := by
  intro j hj i hi
  have hcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by
    simp [cleanBlock] at hj
    omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl <;>
    simp [NestedCover.gateAt, cleanBlock] at hi
  all_goals omega

theorem later_gate_eq (tail : List Gate) (output j : ℕ) (hj : 5 ≤ j) :
    NestedCover.gateAt (⟨cleanBlock ++ tail,output⟩ : Circuit) j =
    NestedCover.gateAt (⟨dirtyBlock ++ tail,output⟩ : Circuit) j := by
  change (cleanBlock ++ tail).getD j ⟨GateOp.or,[]⟩ =
    (dirtyBlock ++ tail).getD j ⟨GateOp.or,[]⟩
  rw [List.getD_append_right cleanBlock tail _ j (by simpa [cleanBlock] using hj),
    List.getD_append_right dirtyBlock tail _ j (by simpa [dirtyBlock] using hj)]
  rfl

theorem readsBack_preserved (tail : List Gate) (output : ℕ)
    (hback : NestedCover.ReadsBack 6 (⟨dirtyBlock ++ tail,output⟩ : Circuit)) :
    NestedCover.ReadsBack 6 (⟨cleanBlock ++ tail,output⟩ : Circuit) := by
  intro j hj i hi
  by_cases hsmall : j < 5
  · have hcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl <;>
      simp [NestedCover.gateAt, cleanBlock] at hi
    all_goals omega
  · rw [later_gate_eq tail output j (by omega)] at hi
    exact hback j (by simpa [cleanBlock, dirtyBlock] using hj) i hi

theorem and_wire_preserved (tail : List Gate) (output j : ℕ)
    (hno : ∀ g ∈ tail, 8 ∉ g.inputs)
    (hand : (NestedCover.gateAt (⟨cleanBlock ++ tail,output⟩ : Circuit) j).op = GateOp.and) :
    5 ≤ j ∧
    (NestedCover.gateAt (⟨dirtyBlock ++ tail,output⟩ : Circuit) j).op = GateOp.and ∧
    ∀ x : Fin 6 → Bool,
      ((⟨cleanBlock ++ tail,output⟩ : Circuit).wires (List.ofFn x)).getD (6+j) false =
      ((⟨dirtyBlock ++ tail,output⟩ : Circuit).wires (List.ofFn x)).getD (6+j) false := by
  have hj : 5 ≤ j := by
    by_contra h
    have hcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl <;>
      simp [NestedCover.gateAt, cleanBlock] at hand
  refine ⟨hj,?_,?_⟩
  · rwa [later_gate_eq tail output j hj] at hand
  · intro x
    exact (block_rewrite_continuation tail hno x (6+j) (by omega)).symm

theorem cleanBlock_binary : ∀ g ∈ cleanBlock, g.inputs.length = 2 := by
  intro g hg
  simp [cleanBlock] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem isAO2_preserved (tail : List Gate) (output : ℕ)
    (hao : PEqualNP.TopForm.IsAO2 6 (⟨dirtyBlock ++ tail,output⟩ : Circuit)) :
    PEqualNP.TopForm.IsAO2 6 (⟨cleanBlock ++ tail,output⟩ : Circuit) := by
  obtain ⟨hops,hback,hbinary⟩ := hao
  refine ⟨?_,readsBack_preserved tail output hback,?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with h | h
    · exact Or.inr (cleanBlock_only_or g h)
    · exact hops g (List.mem_append_right _ h)
  · intro g hg
    rcases List.mem_append.mp hg with h | h
    · exact cleanBlock_binary g h
    · exact hbinary g (List.mem_append_right _ h)

end Pnp3321Rewrite
