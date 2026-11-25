import Pnp11315SplitCore

/- Finite first-level bookkeeping for the literal L9539 signed live-wire search.
   The underlying algorithm and attribution are preserved in Pnp11315Core.
   This module checks only finite data and assembles supplied branch proofs;
   it does not assume or compute the recursive branch rejections. -/
namespace PEqualNP.Outside.L_meta_11315.Signed

set_option maxRecDepth 16000

theorem children_count : (children 3 rows).length = 92 := by
  decide +kernel

theorem full_only : ∀ ws ∈ rows.sublists,
    (decide (ws.length ≤ 9 + 1) && (cuts ws == -1)) = true → ws = rows := by
  decide +kernel

theorem initial_not_goal : (rows == [goal] || rows == [~~~goal]) = false := by
  decide +kernel

theorem reject_of_branches
    (h : ∀ i : Fin 92,
      optimized 8 ((children 3 rows).getD i.val (0, [])).1
        ((children 3 rows).getD i.val (0, [])).2 = false) :
    search 9 rows = false := by
  apply search_false_of_full 9 rows full_only
  change optimized 9 3 rows = false
  apply optimized_succ_false 8 3 rows initial_not_goal
  intro q hq
  obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp hq
  have hi92 : i < 92 := by simpa only [children_count] using hi
  have hp := h ⟨i, hi92⟩
  simpa only [List.getD_eq_getElem _ _ hi, heq] using hp

end PEqualNP.Outside.L_meta_11315.Signed
