import Pnp10486SplitCore

/- Finite first-level bookkeeping for the literal L9539 signed live-wire search.
   The underlying algorithm and attribution are preserved in Pnp10486LiteralCore.
   This module checks only finite data and assembles supplied branch proofs;
   it does not assume or compute the recursive branch rejections. -/
namespace PEqualNP.Outside.L_meta_10486.Signed

set_option maxRecDepth 16000

theorem children_count : (children 4 rows).length = 88 := by
  decide +kernel

theorem full_only : ∀ ws ∈ rows.sublists,
    (decide (ws.length ≤ 10 + 1) && (cuts ws == -1)) = true → ws = rows := by
  decide +kernel

theorem initial_not_goal : (rows == [goal] || rows == [~~~goal]) = false := by
  decide +kernel

theorem reject_of_branches
    (h : ∀ i : Fin 88,
      optimized 9 ((children 4 rows).getD i.val (0, [])).1
        ((children 4 rows).getD i.val (0, [])).2 = false) :
    search 10 rows = false := by
  apply search_false_of_full 10 rows full_only
  change optimized 10 4 rows = false
  apply optimized_succ_false 9 4 rows initial_not_goal
  intro q hq
  obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp hq
  have hi88 : i < 88 := by simpa only [children_count] using hi
  have hp := h ⟨i, hi88⟩
  simpa only [List.getD_eq_getElem _ _ hi, heq] using hp

end PEqualNP.Outside.L_meta_10486.Signed
