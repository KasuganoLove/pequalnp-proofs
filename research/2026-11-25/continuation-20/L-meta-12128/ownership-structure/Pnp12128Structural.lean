import PEqualNP.Outside.L_meta_12030

/-
Research-only semantic bridge for the live L-meta-12128 task.
The final public file must inline the generic helpers and import Defs only.
The imported helpers reuse ptrdsh's merged L-meta-11315 (PR #15263), adapted
from L-meta-10458, Apache-2.0. No generic helper is changed here.
-/

namespace PEqualNP.Outside.Pnp12128Structural

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_12030

def target6 (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4276676736 * 2 ^ 32 + 4269860864)
    (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

def embed (i : Fin 6) : Fin 7 := ⟨i.val, by omega⟩

def flipWire (i : Fin 6) : BF :=
  fun x => if i.val = 3 then !(x (embed i)) else x (embed i)

def initials : List BF := List.ofFn flipWire

def initialVars : Finset (Fin 7) := {0, 1, 2, 3, 4, 5}

def flipped : BF := fun x => target6 (fun i => flipWire i x)

theorem ori_flipWire (i : Fin 6) : ori (flipWire i) = var (embed i) := by
  funext x
  fin_cases i <;> simp [flipWire, ori, var, embed]

theorem embed_mem (i : Fin 6) : embed i ∈ initialVars := by
  fin_cases i <;> decide

theorem flipped_eq_table :
    flipped = graphTable 309702352993452452166218478907754938600 := by
  apply equalSeven
  decide +kernel

theorem binary_ge_nine (gates : List Gate) (o : ℕ) (legal : GOK gates)
    (comp : ∀ x : Fin 6 → Bool,
      Circuit.eval ⟨gates, o⟩ (List.ofFn x) = target6 x) :
    9 ≤ countBinary gates := by
  have evaluated (x : Fin 7 → Bool) :
      Circuit.eval ⟨gates, o⟩ (initials.map fun w => w x) =
        graphTable 309702352993452452166218478907754938600 x := by
    change Circuit.eval ⟨gates, o⟩ ((List.ofFn flipWire).map fun w => w x) = _
    rw [List.map_ofFn, comp]
    exact congrFun flipped_eq_table x
  have hg : (wiresF gates initials).getD o zF =
      graphTable 309702352993452452166218478907754938600 := by
    funext x
    rw [← evaluated x, ← getD_map_x, ← wires_eq]
    rfl
  have start := trans_binary gates initials (sourceVars initialVars) legal (by
    intro w hw
    change w ∈ List.ofFn flipWire at hw
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hw
    exact Or.inr ⟨embed i, embed_mem i, ori_flipWire i⟩) o
  rw [hg, ori_zp (by decide :
    (graphTable 309702352993452452166218478907754938600) (fun _ => false) = false)] at start
  rcases start with e | base
  · have c := congrFun e (assignment 3)
    exact False.elim ((by decide :
      (graphTable 309702352993452452166218478907754938600) (assignment 3) ≠ false) c)
  obtain ⟨t1, pay1, h1⟩ := remove_var
    (graphTable 309702352993452452166218478907754938600) 5 initialVars
    (countBinary gates) ⟨assignment 47, by decide⟩ (by
      intro h
      have c := congrFun h (assignment 3)
      exact (by decide :
        rst 5 (graphTable 309702352993452452166218478907754938600)
          (assignment 3) ≠ false) c) base
  have eq1 : rst 5 (graphTable 309702352993452452166218478907754938600) =
      graphTable 171460045283391933962914148873001631976 := equalSeven (by decide)
  rw [eq1] at h1
  obtain ⟨t2, pay2, h2⟩ := remove_var
    (graphTable 171460045283391933962914148873001631976) 3 (initialVars.erase 5)
    t1 ⟨assignment 11, by decide⟩ (by
      intro h
      have c := congrFun h (assignment 3)
      exact (by decide :
        rst 3 (graphTable 171460045283391933962914148873001631976)
          (assignment 3) ≠ false) c) h1
  have eq2 : rst 3 (graphTable 171460045283391933962914148873001631976) =
      graphTable 338947478310315587971925210585225947368 := equalSeven (by decide)
  rw [eq2] at h2
  let core : Fin 4 → Fin 7 := ![0, 1, 2, 4]
  have injective : Function.Injective core := by decide +kernel
  have single : ∀ i,
      (graphTable 338947478310315587971925210585225947368) (singleInput (core i)) = false := by
    decide +kernel
  have pair : ∀ i j, i ≠ j →
      (graphTable 338947478310315587971925210585225947368) (pairInput (core i) (core j)) = true := by
    decide +kernel
  have sources : ∀ w, sourceVars ((initialVars.erase 5).erase 3) w →
      ∃ j, w = var (core j) := by
    rintro w ⟨i, hi, rfl⟩
    have covered : ∀ i ∈ ((initialVars.erase 5).erase 3), ∃ j, core j = i := by
      decide +kernel
    obtain ⟨j, rfl⟩ := covered i hi
    exact ⟨j, rfl⟩
  have mapped := UC_monoS gF (fun _ => True) t2 _ _ _ sources h2
  by_contra! small
  exact U4 core injective (graphTable 338947478310315587971925210585225947368)
    single pair (UC_le (by omega) mapped)

theorem with_not_ge_ten (gates : List Gate) (o : ℕ) (legal : GOK gates)
    (hnot : ∃ g ∈ gates, g.op = GateOp.not)
    (comp : ∀ x : Fin 6 → Bool,
      Circuit.eval ⟨gates, o⟩ (List.ofFn x) = target6 x) :
    10 ≤ gates.length := by
  have b := binary_ge_nine gates o legal comp
  have h := countBinary_lt gates hnot
  omega

end PEqualNP.Outside.Pnp12128Structural
