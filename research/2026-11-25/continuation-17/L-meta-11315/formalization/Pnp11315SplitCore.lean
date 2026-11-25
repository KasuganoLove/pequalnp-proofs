import Pnp11315Core

/- One-step decomposition of the existing signed live-wire checker.
   This changes neither its operations nor its acceptance conditions. -/
namespace PEqualNP.Outside.L_meta_11315.Signed

def guardedChildren (b : Bool) (xs : List (Nat × List W)) : List (Nat × List W) :=
  if b then xs else []

theorem guardedChildren_any (b : Bool) (xs : List (Nat × List W))
    (f : Nat × List W → Bool) :
    (guardedChildren b xs).any f = (b && xs.any f) := by
  cases b <;> rfl

def dispatchChildren (extra : Nat) (a b : W) (r : List W) : List (Nat × List W) :=
  let base := cuts r
  (ops a b).flatMap fun w =>
    let v := sep w ||| base
    guardedChildren (v == -1) [(extra, w :: r)] ++
    guardedChildren (extra != 0)
      (guardedChildren (v ||| sep a == -1) [(extra - 1, w :: a :: r)] ++
       guardedChildren (v ||| sep b == -1) [(extra - 1, w :: b :: r)]) ++
    guardedChildren (decide (extra ≥ 2))
      (guardedChildren (v ||| sep a ||| sep b == -1)
        [(extra - 2, w :: a :: b :: r)])

theorem dispatch_eq_children_any (extra : Nat) (next : Nat → List W → Bool)
    (a b : W) (r : List W) :
    dispatch extra next a b r =
      (dispatchChildren extra a b r).any (fun q => next q.1 q.2) := by
  simp only [dispatch, dispatchChildren, List.any_flatMap, List.any_append,
    guardedChildren_any, List.any_cons, List.any_nil, Bool.or_false,
    Bool.and_assoc]

def children (extra : Nat) (ws : List W) : List (Nat × List W) :=
  (pairs ws).flatMap fun (a, b, r) => dispatchChildren extra a b r

theorem optimized_succ_children (n extra : Nat) (ws : List W) :
    optimized (n + 1) extra ws =
      ((ws == [goal] || ws == [~~~goal]) ||
        (children extra ws).any (fun q => optimized n q.1 q.2)) := by
  simp only [optimized, children, List.any_flatMap, dispatch_eq_children_any]

theorem optimized_succ_false (n extra : Nat) (ws : List W)
    (hgoal : (ws == [goal] || ws == [~~~goal]) = false)
    (hchildren : ∀ q ∈ children extra ws, optimized n q.1 q.2 = false) :
    optimized (n + 1) extra ws = false := by
  rw [optimized_succ_children, hgoal]
  simp only [Bool.false_or]
  apply List.any_eq_false.mpr
  intro q hq
  simp only [hchildren q hq, Bool.false_eq_true, not_false_eq_true]

theorem search_false_of_full (n : Nat) (inputs : List W)
    (hfull : ∀ ws ∈ inputs.sublists,
      (decide (ws.length ≤ n + 1) && (cuts ws == -1)) = true → ws = inputs)
    (hreject : optimized n (n + 1 - inputs.length) inputs = false) :
    search n inputs = false := by
  apply List.any_eq_false.mpr
  intro ws hws
  by_cases hcut : (decide (ws.length ≤ n + 1) && (cuts ws == -1)) = true
  · have heq := hfull ws hws hcut
    subst ws
    simp only [hreject, Bool.and_false, Bool.false_eq_true, not_false_eq_true]
  · have hz : (decide (ws.length ≤ n + 1) && (cuts ws == -1)) = false :=
      Bool.eq_false_iff.mpr hcut
    rw [hz]
    simp only [Bool.false_and, Bool.false_eq_true, not_false_eq_true]

end PEqualNP.Outside.L_meta_11315.Signed
