import Pnp10486SplitCore

/- Finite-index aggregation for one step of the existing signed live-wire search.
   This contains no numerical rejection and no fixed sample width or branch count.
   The checker and its source attribution are inherited from Pnp10486SplitCore. -/
namespace PEqualNP.Outside.L_meta_10486.Signed

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

end PEqualNP.Outside.L_meta_10486.Signed
