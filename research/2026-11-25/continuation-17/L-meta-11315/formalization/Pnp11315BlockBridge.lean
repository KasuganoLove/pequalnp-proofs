import Pnp11315SplitCore

-- The finite-index bridge is adapted from this session's Pnp10486NestedBridge.
-- treeBlock, treeBlock_at, and treeBlock_merge are copied with namespace changes
-- from odinfree's merged L_meta_10486.lean, PR #14954, under Apache-2.0.
-- Upstream commit: 3f343d41f5196063193260b654053e2c750b7878.
-- This module contains no numerical rejection or assumed branch count.
namespace PEqualNP.Outside.L_meta_11315.Signed

theorem optimized_false_of_getD (n extra : Nat) (ws : List W) (m : Nat)
    (hcount : (children extra ws).length = m)
    (hgoal : (ws == [goal] || ws == [~~~goal]) = false)
    (h : ∀ i : Fin m,
      optimized n ((children extra ws).getD i.val (0, [])).1
        ((children extra ws).getD i.val (0, [])).2 = false) :
    optimized (n + 1) extra ws = false := by
  apply optimized_succ_false n extra ws hgoal
  intro q hq
  obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp hq
  have him : i < m := by simpa only [hcount] using hi
  have hp := h ⟨i, him⟩
  simpa only [List.getD_eq_getElem _ _ hi, heq] using hp

def treeBlock (start count : Nat) (check : Nat → Bool) : Bool :=
  (Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun _ next i => check i && next (i + 1)) count) start

theorem treeBlock_at {start count i : Nat} {check : Nat → Bool}
    (h : treeBlock start count check = true) (lo : start ≤ i) (hi : i < start + count) :
    check i = true := by
  induction count generalizing start with
  | zero => omega
  | succ count ih =>
    change (check start && treeBlock (start + 1) count check) = true at h
    rcases Bool.and_eq_true_iff.mp h with ⟨here, rest⟩
    by_cases eq : i = start
    · simpa [eq] using here
    · exact ih rest (by omega) (by omega)

theorem treeBlock_merge {start left right : Nat} {check : Nat → Bool}
    (a : treeBlock start left check = true)
    (b : treeBlock (start + left) right check = true) :
    treeBlock start (left + right) check = true := by
  induction left generalizing start with
  | zero => simpa using b
  | succ left ih =>
    rw [Nat.succ_add]
    change (check start && treeBlock (start + 1) (left + right) check) = true
    change (check start && treeBlock (start + 1) left check) = true at a
    rcases Bool.and_eq_true_iff.mp a with ⟨here, rest⟩
    exact Bool.and_eq_true_iff.mpr ⟨here, ih rest (by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using b)⟩

theorem optimized_false_of_treeBlock (n extra : Nat) (ws : List W) (m : Nat)
    (hcount : (children extra ws).length = m)
    (hgoal : (ws == [goal] || ws == [~~~goal]) = false)
    (hblock : treeBlock 0 m (fun j =>
      !(optimized n ((children extra ws).getD j (0, [])).1
        ((children extra ws).getD j (0, [])).2)) = true) :
    optimized (n + 1) extra ws = false := by
  apply optimized_false_of_getD n extra ws m hcount hgoal
  intro i
  have hi := treeBlock_at hblock (Nat.zero_le i.val) (by simp)
  exact Bool.eq_false_of_not_eq_true' hi

end PEqualNP.Outside.L_meta_11315.Signed
