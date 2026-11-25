import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Push
import PEqualNP.Defs

/-!
Research dependency extracted verbatim from the generic structural sections of
open-goat/pequalnp-proofs, PEqualNP/Outside/L_meta_5228.lean (Apache-2.0).
Source SHA256: 0b3f20c44ae8739ae961579014fe617e87e12e3af5d333c91c658990ee82eada.
The original explicitly credits the OR-path characterization to willakone,
project PR 3118. Only the enclosing namespace is changed. No graph-specific
finite certificate, task theorem, axiom, or admission is imported or copied.
This is a local research dependency, not a task submission.
-/
namespace PEqualNP.Outside.Pnp650TransferCore

namespace LocalLambda
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
def OrStep (n : ℕ) (C : Circuit) (w w' : ℕ) : Prop :=
  ∃ k, k < C.gates.length ∧ w = n + k ∧ (gateAt C k).op = GateOp.or ∧
    w' ∈ (gateAt C k).inputs ∧ w' < n + k

open PEqualNP.CleanedNonEdge

lemma orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

lemma orSets_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (orStep n) []).getD j [] ↔
      j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          i ∈ (gs.foldl (orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (orStep n) []).length = gs.length := by
      rw [orSets_len]; simp
    have key : ∀ k, k < gs.length →
        (orStep n (gs.foldl (orStep n) []) g).getD k [] =
          (gs.foldl (orStep n) []).getD k [] := by
      intro k hk
      simp only [orStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, h3⟩
        refine ⟨by simp; omega, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]
          exact h3
      · rintro ⟨_, h3⟩
        refine ⟨h, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · rw [key (w - n) (by omega)] at h3
          exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      by_cases hop : g.op = GateOp.or
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] =
            gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (gs.foldl (orStep n) []).getD (w - n) []) := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
        constructor
        · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
          · exact ⟨by simp, Or.inl h3⟩
          · refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
            rw [key (w - n) (by omega)]
            exact h3
        · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
          · exact Or.inl h3
          · rw [key (w - n) (by omega)] at h3
            exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] = [gs.length] := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_singleton]
        constructor
        · intro h3
          exact ⟨by simp, Or.inl h3⟩
        · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
          · exact h3
          · exact (hop hop2).elim
    · have e0 : (orStep n (gs.foldl (orStep n) []) g).getD j [] = [] := by
        simp only [orStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    OrReaches n C (n + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g)) := by
  have h := orSets_char n C.gates g k
  unfold OrReaches orSets gateAt
  have e : n + k - n = k := by omega
  rw [e, h]
  constructor
  · rintro ⟨_, hk, h3⟩
    refine ⟨hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h2, h1, h3⟩
  · rintro ⟨hk, h3⟩
    refine ⟨by omega, hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h2, h1, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩

lemma reach_orReaches {n : ℕ} {C : Circuit} {w w2 : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w2) :
    ∀ g, w2 = n + g → g < C.gates.length → OrReaches n C w g := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro g h1 hg
    subst h1
    exact (orReaches_iff n C g g).mpr ⟨hg, Or.inl rfl⟩
  | @head a c hstep hrest ih =>
    intro g h1 hg
    obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
    exact (orReaches_iff n C k g).mpr ⟨hk, Or.inr ⟨hop, c, hin, hlt, ih g h1 hg⟩⟩

lemma orReaches_reach {n : ℕ} {C : Circuit} (g : ℕ) :
    ∀ w, OrReaches n C w g →
      Relation.ReflTransGen (OrStep n C) w (n + g) ∧ g < C.gates.length := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    have hnw : n ≤ w := h.1
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    obtain ⟨hk, h3⟩ := (orReaches_iff n C k g).mp h
    rcases h3 with rfl | ⟨hop, i, hi, hlt, hr⟩
    · exact ⟨Relation.ReflTransGen.refl, hk⟩
    · obtain ⟨hr2, hg⟩ := ih i hlt hr
      exact ⟨Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hi, hlt⟩ hr2, hg⟩

lemma mem_orIn_reach {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
    (hu : u ∈ PEqualNP.TopForm.orIn n C p) :
    Relation.ReflTransGen (OrStep n C) p u.val := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  rcases hu with h | ⟨k, hk, hr, hop, hin⟩
  · rw [h]
  · exact (orReaches_reach k p hr).1.tail ⟨k, hk, rfl, hop, hin, by omega⟩

lemma reach_mem_orIn {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p u.val) :
    u ∈ PEqualNP.TopForm.orIn n C p := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases Relation.ReflTransGen.cases_tail hr with h | ⟨c, hpc, hstep⟩
  · exact Or.inl h
  · obtain ⟨k, hk, rfl, hop, hin, _⟩ := hstep
    exact Or.inr ⟨k, hk, reach_orReaches hpc k rfl hk, hop, hin⟩

open PEqualNP.TopForm

lemma orIn_subset_of_reaches {n : ℕ} {C : Circuit} {w k : ℕ} (h : OrReaches n C w k) :
    orIn n C (n+k) ⊆ orIn n C w := fun v hv =>
  reach_mem_orIn v ((orReaches_reach k w h).1.trans (mem_orIn_reach v hv))

lemma cross_outside {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    {a : ℕ} (ha : a ∈ tops G C)
    (hc : ∀ u ∈ side C a (0 : Fin 2), ∀ v ∈ side C a (1 : Fin 2), G.Adj u v)
    {u v : Fin n} (hu : u ∈ side C a (0 : Fin 2)) (hv : v ∈ side C a (1 : Fin 2)) :
    G.Adj u v ∧ s(u,v) ∉ Ustar G C := by
  refine ⟨hc u hu v hv, ?_⟩
  intro missing
  apply (Finset.mem_sdiff.mp missing).2
  exact Finset.mem_biUnion.mpr ⟨a,ha,Finset.mem_image.mpr
    ⟨(u,v),Finset.mem_product.mpr ⟨hu,hv⟩,rfl⟩⟩

lemma lambda_raw_clause {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (cross : ∀ a ∈ tops G C, ∀ u ∈ side C a (0 : Fin 2), ∀ v ∈ side C a (1 : Fin 2), G.Adj u v)
    {k : ℕ} (hk : k ∈ lam G C) :
    ∃ c : Fin n, ∀ v ∈ orIn n C (n+k), (G.deleteEdges (Ustar G C : Set (Sym2 (Fin n)))).Adj c v := by
  obtain ⟨_,_,a,ha,b,hcard,reach⟩ := (Finset.mem_filter.mp hk).2
  obtain ⟨c,hside⟩ := Finset.card_eq_one.mp hcard
  have hc : c ∈ side (n := n) C a (1-b) := hside ▸ Finset.mem_singleton_self _
  refine ⟨c,fun v hv => ?_⟩
  have hv' : v ∈ side (n := n) C a b := orIn_subset_of_reaches reach hv
  fin_cases b
  · have pair := cross_outside ha (cross a ha) hv' (show c ∈ side C a 1 from hc)
    apply SimpleGraph.deleteEdges_adj.mpr
    have swap : s(c,v) = s(v,c) := Sym2.eq_swap
    exact ⟨pair.1.symm, fun h => pair.2 (swap ▸ h)⟩
  · exact SimpleGraph.deleteEdges_adj.mpr (cross_outside ha (cross a ha) (show c ∈ side C a 0 from hc) hv')

end LocalLambda

-- The wire evaluation equations are from willakone, project PR 3118.
namespace LocalTransfer
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [if_neg hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [if_neg hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [if_pos hlt]; exact h⟩

lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h'; exact ⟨hlt, h'⟩
    · rw [if_neg hlt] at h'; cases h'
  · intro h i hi
    rw [if_pos (h i hi).1]; exact (h i hi).2


lemma tests_through_ands {n : ℕ} (C : Circuit) (basis : AndOrOnly C)
    (tests : List (Fin n → Bool)) (first : Fin n → Bool) (present : first ∈ tests)
    (y : Fin n → Bool) (stop : ℕ)
    (input : ∀ i : Fin n, (∀ x ∈ tests, x i = true) → y i = true)
    (ors : ∀ k < C.gates.length, n+k < stop → (gateAt C k).op = GateOp.or →
      (∀ x ∈ tests, val C (List.ofFn x) (n+k) = true) → val C (List.ofFn y) (n+k) = true) :
    ∀ w < stop, w < n+C.gates.length →
      (∀ x ∈ tests, val C (List.ofFn x) w = true) → val C (List.ofFn y) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro before valid positive
    by_cases hpin : w < n
    · let i : Fin n := ⟨w,hpin⟩
      have hval (x : Fin n → Bool) : val C (List.ofFn x) w = x i := by
        rw [val_input (n := n) (by simp) hpin]
        simp [List.getD_eq_getElem?_getD,hpin,i]
      rw [hval]
      apply input i
      intro x hx
      exact hval x ▸ positive x hx
    · obtain ⟨k,rfl⟩ : ∃ k, w = n+k := ⟨w-n,by omega⟩
      have hk : k < C.gates.length := by omega
      rcases basis _ (gateAt_mem hk) with hand | hor
      · apply (val_and (n := n) (by simp) hk hand).2
        intro v hv
        have earlier := ((val_and (n := n) (by simp) hk hand).1 (positive first present) v hv).1
        refine ⟨earlier,ih v earlier (by omega) (by omega) ?_⟩
        intro x hx
        exact ((val_and (n := n) (by simp) hk hand).1 (positive x hx) v hv).2
      · exact ors k hk before hor positive

end LocalTransfer

namespace LocalPure
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open LocalLambda LocalTransfer

lemma value_of_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (v : Fin n) :
    val C (List.ofFn x) v.val = x v := by
  rw [val_input (n := n) (by simp) v.isLt]
  simp [List.getD_eq_getElem?_getD]

lemma upward {n : ℕ} {C : Circuit} (x : Fin n → Bool) {a b : ℕ}
    (path : Relation.ReflTransGen (OrStep n C) a b) (yes : val C (List.ofFn x) b = true) :
    val C (List.ofFn x) a = true := by
  induction path using Relation.ReflTransGen.head_induction_on with
  | refl => exact yes
  | head step _ ih =>
    obtain ⟨k,hk,rfl,hop,port,hprior⟩ := step
    exact (val_or (n := n) (by simp) hk hop).mpr ⟨_,port,hprior,ih⟩

lemma raw_pin {n : ℕ} {C : Circuit} {v : Fin n} (x : Fin n → Bool) {w : ℕ}
    (hv : v ∈ orIn n C w) (hon : x v = true) : val C (List.ofFn x) w = true :=
  upward x (mem_orIn_reach v hv) ((value_of_input C x v).trans hon)

lemma raw_above_singleton {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} {k : ℕ} {v : Fin n} (hv : v ∈ orIn n C (n+k)) : ¬BelowF G C k := by
  intro below
  let x : Fin n → Bool := fun u => decide (u = v)
  have noedge : graphFun G ∅ x = false := by
    simp [graphFun,x]
  have on := raw_pin x hv (by simp [x])
  have bad := below x on
  simp [noedge] at bad

lemma raw_gate {n : ℕ} (C : Circuit) (k : ℕ) (u : Fin n) :
    u ∈ orIn n C (n+k) ↔ k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, w < n+k ∧ u ∈ orIn n C w := by
  constructor
  · intro hu
    rcases Relation.ReflTransGen.cases_head (mem_orIn_reach u hu) with he | ⟨w,hs,rest⟩
    · have := u.isLt; omega
    · obtain ⟨j,hj,eq,op,port,lt⟩ := hs
      have : j = k := by omega
      subst j
      exact ⟨hj,op,w,port,lt,reach_mem_orIn u rest⟩
  · rintro ⟨hk,op,w,port,lt,hu⟩
    apply reach_mem_orIn u
    exact Relation.ReflTransGen.head ⟨k,hk,rfl,op,port,lt⟩ (mem_orIn_reach u hu)

lemma lambda_port {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (ao : IsAO2 n C) {k w : ℕ} (hk : k ∈ lam G C)
    (hw : w ∈ (gateAt C k).inputs) : (orIn n C w).Nonempty := by
  letI : DecidableEq GateOp := gateOpDecEq
  obtain ⟨hor,h0,h1,_⟩ := Finset.mem_filter.mp hk
  have valid : k < C.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp hor).1
  obtain ⟨p,q,eq⟩ := List.length_eq_two.mp (ao.2.2 _ (gateAt_mem valid))
  have op0 : opnd C k 0 = p := by simp [opnd,eq]
  have op1 : opnd C k 1 = q := by simp [opnd,eq]
  rw [op0] at h0
  rw [op1] at h1
  simp only [eq,List.mem_cons,List.not_mem_nil,or_false] at hw
  exact hw.elim (fun h => h ▸ h0) (fun h => h ▸ h1)

lemma pure_before {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (ao : IsAO2 n C) (stop : ℕ)
    (all : ∀ k, n+k < stop → k ∈ orN G C → k ∈ lam G C) (x : Fin n → Bool) :
    ∀ w < stop, (orIn n C w).Nonempty → val C (List.ofFn x) w = true →
      ∃ v ∈ orIn n C w, x v = true := by
  letI : DecidableEq GateOp := gateOpDecEq
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro before raw yes
    by_cases pin : w < n
    · let v : Fin n := ⟨w,pin⟩
      have mem : v ∈ orIn n C w := Finset.mem_filter.mpr ⟨Finset.mem_univ _,Or.inl rfl⟩
      exact ⟨v,mem,(value_of_input C x v).symm.trans yes⟩
    · obtain ⟨k,rfl⟩ : ∃ k, w = n+k := ⟨w-n,by omega⟩
      obtain ⟨a,ha⟩ := raw
      obtain ⟨hk,hop,_⟩ := (raw_gate C k a).mp ha
      have orn : k ∈ orN G C := Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr hk,hop,raw_above_singleton ha⟩
      obtain ⟨p,hp,hprior,hval⟩ := (val_or (n := n) (by simp) hk hop).mp yes
      obtain ⟨v,hv,hx⟩ := ih p hprior (by omega) (lambda_port ao (all k before orn) hp) hval
      exact ⟨v,(raw_gate C k v).mpr ⟨hk,hop,p,hp,hprior,hv⟩,hx⟩

end LocalPure

namespace LocalMixTrace
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.MetaComplexity.NestedCover
open LocalLambda LocalPure LocalTransfer

lemma exceptional_source {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (ao : IsAO2 n C) (x : Fin n → Bool) :
    ∀ w, (orIn n C w).Nonempty → val C (List.ofFn x) w = true →
      (∀ v ∈ orIn n C w, x v = false) →
      ∃ k ∈ orN G C \ lam G C, OrReaches n C w k ∧ (orIn n C (n+k)).Nonempty ∧
        gateVal n C k x = true ∧ ∀ v ∈ orIn n C (n+k), x v = false := by
  letI : DecidableEq GateOp := gateOpDecEq
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro raw yes absent
    by_cases hw : w < n
    · let v : Fin n := ⟨w,hw⟩
      have mem : v ∈ orIn n C w := Finset.mem_filter.mpr ⟨Finset.mem_univ _,Or.inl rfl⟩
      have high : x v = true := (value_of_input C x v).symm.trans yes
      exact (Bool.false_ne_true ((absent v mem).symm.trans high)).elim
    · obtain ⟨k,rfl⟩ : ∃ k, w = n+k := ⟨w-n,by omega⟩
      obtain ⟨v,hv⟩ := raw
      obtain ⟨hk,hop,_⟩ := (raw_gate C k v).mp hv
      have orn : k ∈ orN G C := Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr hk,hop,raw_above_singleton hv⟩
      by_cases normal : k ∈ lam G C
      · obtain ⟨p,port,prior,on⟩ := (val_or (n := n) (by simp) hk hop).mp yes
        have absentP (v : Fin n) (h : v ∈ orIn n C p) : x v = false :=
          absent v ((raw_gate C k v).mpr ⟨hk,hop,p,port,prior,h⟩)
        obtain ⟨j,hj,path,atJ,onJ,off⟩ := ih p prior (lambda_port ao normal port) on absentP
        exact ⟨j,hj,(orReaches_iff n C k j).mpr ⟨hk,Or.inr ⟨hop,p,port,prior,path⟩⟩,atJ,onJ,off⟩
      · exact ⟨k,Finset.mem_sdiff.mpr ⟨orn,normal⟩,
          (orReaches_iff n C k k).mpr ⟨hk,Or.inl rfl⟩,⟨v,hv⟩,yes,absent⟩

end LocalMixTrace

namespace LocalBefore
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open LocalLambda LocalTransfer LocalPure

lemma earlier_exception {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (ao : IsAO2 n C) {a : ℕ} (ha : a ∈ tops G C)
    (cross : ∀ l ∈ side C a (0 : Fin 2), ∀ r ∈ side C a (1 : Fin 2), G.Adj l r)
    (nonempty : ∀ b : Fin 2, (side (n := n) C a b).Nonempty)
    {u v : Fin n} (missing : s(u,v) ∈ Ustar G C)
    (htrue : gateVal n C a (pairInput u v) = true) :
    ∃ k ∈ orN G C \ lam G C, k < a := by
  letI : DecidableEq GateOp := gateOpDecEq
  by_contra no
  have normal (k : ℕ) (before : n+k < n+a) (horn : k ∈ orN G C) : k ∈ lam G C := by
    by_contra outside
    exact no ⟨k,Finset.mem_sdiff.mpr ⟨horn,outside⟩,by omega⟩
  obtain ⟨hvalid,hand,_⟩ := Finset.mem_filter.mp ha
  have hk : a < C.gates.length := Finset.mem_range.mp hvalid
  obtain ⟨p,q,ports⟩ := List.length_eq_two.mp (ao.2.2 _ (gateAt_mem hk))
  have vp := (val_and (n := n) (x := List.ofFn (pairInput u v)) (by simp) hk hand).mp htrue
  have hp := vp p (by simp [ports])
  have hq := vp q (by simp [ports])
  have np : (orIn n C p).Nonempty := by simpa [side,opnd,ports] using nonempty 0
  have nq : (orIn n C q).Nonempty := by simpa [side,opnd,ports] using nonempty 1
  obtain ⟨l,hl,lv⟩ := pure_before G C ao (n+a) normal (pairInput u v) p hp.1 np hp.2
  obtain ⟨r,hr,rv⟩ := pure_before G C ao (n+a) normal (pairInput u v) q hq.1 nq hq.2
  have left : l ∈ side C a (0 : Fin 2) := by simpa [side,opnd,ports] using hl
  have right : r ∈ side C a (1 : Fin 2) := by simpa [side,opnd,ports] using hr
  obtain ⟨adj,star⟩ := cross_outside ha cross left right
  have lcase : l = u ∨ l = v := of_decide_eq_true lv
  have rcase : r = u ∨ r = v := of_decide_eq_true rv
  rcases lcase with rfl | rfl <;> rcases rcase with rfl | rfl
  · exact G.irrefl adj
  · exact star missing
  · have swap : s(r,l) = s(l,r) := Sym2.eq_swap
    exact star (swap ▸ missing)
  · exact G.irrefl adj

end LocalBefore

namespace LocalReceiver
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.MetaComplexity.NestedCover
open LocalLambda LocalPure LocalTransfer LocalMixTrace LocalBefore

lemma sides_nonempty {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (empty : centreless G C = ∅) {a : ℕ} (ha : a ∈ tops G C) (b : Fin 2) :
    (side (n := n) C a b).Nonempty := by
  letI : DecidableEq GateOp := gateOpDecEq
  apply Finset.nonempty_iff_ne_empty.mpr
  intro h
  have bad : a ∈ centreless G C := by
    apply Finset.mem_filter.mpr
    refine ⟨ha,?_⟩
    fin_cases b
    · exact Or.inl h
    · exact Or.inr h
  simp [empty] at bad

lemma top_ports {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (ao : IsAO2 n C) {a : ℕ} (ha : a ∈ tops G C) (x : Fin n → Bool) :
    gateVal n C a x = true ↔ ∀ b : Fin 2, val C (List.ofFn x) (opnd C a b) = true := by
  letI : DecidableEq GateOp := gateOpDecEq
  obtain ⟨valid,hand,_⟩ := Finset.mem_filter.mp ha
  have hk := Finset.mem_range.mp valid
  obtain ⟨p,q,ports⟩ := List.length_eq_two.mp (ao.2.2 _ (gateAt_mem hk))
  change val C (List.ofFn x) (n+a) = true ↔ _
  rw [val_and (n := n) (by simp) hk hand]
  constructor
  · intro pos b
    apply (pos _ _).2
    fin_cases b <;> simp [opnd,ports]
  · intro h i hi
    refine ⟨ao.2.1 a hk i hi,?_⟩
    have choices : i = p ∨ i = q := by simpa [ports] using hi
    rcases choices with rfl | rfl
    · simpa [opnd,ports] using h 0
    · simpa [opnd,ports] using h 1

lemma one_blank {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    {a : ℕ} (ha : a ∈ tops G C)
    (cross : ∀ l ∈ side C a (0 : Fin 2), ∀ r ∈ side C a (1 : Fin 2), G.Adj l r)
    {u v : Fin n} (missing : s(u,v) ∈ Ustar G C) :
    ¬ ((∃ l ∈ side C a (0 : Fin 2), pairInput u v l = true) ∧
       (∃ r ∈ side C a (1 : Fin 2), pairInput u v r = true)) := by
  rintro ⟨⟨l,hl,lv⟩,r,hr,rv⟩
  obtain ⟨adj,star⟩ := cross_outside ha cross hl hr
  have lcase : l = u ∨ l = v := of_decide_eq_true lv
  have rcase : r = u ∨ r = v := of_decide_eq_true rv
  rcases lcase with rfl | rfl <;> rcases rcase with rfl | rfl
  · exact G.irrefl adj
  · exact star missing
  · have swap : s(r,l) = s(l,r) := Sym2.eq_swap
    exact star (swap ▸ missing)
  · exact G.irrefl adj

lemma receiver_transfer {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (ao : IsAO2 n C) {a m : ℕ} (ha : a ∈ tops G C)
    (cross : ∀ l ∈ side C a (0 : Fin 2), ∀ r ∈ side C a (1 : Fin 2), G.Adj l r)
    (b : Fin 2) (path : OrReaches n C (opnd C a b) m) {w : Fin n} (hw : w ∈ side C a (1-b)) :
    (∀ r ∈ orIn n C (n+m), (G.deleteEdges (Ustar G C : Set (Sym2 (Fin n)))).Adj r w) ∧
    (∀ y : Fin n → Bool, gateVal n C m y = true → y w = true → graphFun G ∅ y = true) := by
  letI : DecidableEq GateOp := gateOpDecEq
  constructor
  · intro r hr
    have left : r ∈ side C a b := orIn_subset_of_reaches path hr
    fin_cases b
    · exact SimpleGraph.deleteEdges_adj.mpr (cross_outside ha cross left (show w ∈ side C a 1 from hw))
    · exact (SimpleGraph.deleteEdges_adj.mpr (cross_outside ha cross (show w ∈ side C a 0 from hw) left)).symm
  · intro y hm high
    have first := upward y (orReaches_reach m _ path).1 hm
    have second := raw_pin y hw high
    have below := (Finset.mem_filter.mp ha).2.2
    apply below y
    apply (top_ports ao ha y).mpr
    intro d
    fin_cases b <;> fin_cases d
    · exact first
    · exact second
    · exact second
    · exact first

lemma route_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (ao : IsAO2 n C) (m : ℕ) (single : orN G C \ lam G C = {m})
    (allraw : centreless G C = ∅) {a : ℕ} (ha : a ∈ tops G C)
    (cross : ∀ l ∈ side C a (0 : Fin 2), ∀ r ∈ side C a (1 : Fin 2), G.Adj l r)
    {u v : Fin n} (missing : s(u,v) ∈ Ustar G C) (on : gateVal n C a (pairInput u v) = true) :
    (orIn n C (n+m)).Nonempty ∧ gateVal n C m (pairInput u v) = true ∧
    (∀ r ∈ orIn n C (n+m), pairInput u v r = false) ∧
    ∃ w : Fin n, pairInput u v w = true ∧
      (∀ r ∈ orIn n C (n+m), (G.deleteEdges (Ustar G C : Set (Sym2 (Fin n)))).Adj r w) ∧
      ∀ y : Fin n → Bool, gateVal n C m y = true → y w = true → graphFun G ∅ y = true := by
  let seen := fun (b : Fin 2) => ∃ r ∈ side C a b, pairInput u v r = true
  have source (b : Fin 2) (off : ¬seen b) :
      OrReaches n C (opnd C a b) m ∧ (orIn n C (n+m)).Nonempty ∧
      gateVal n C m (pairInput u v) = true ∧ ∀ r ∈ orIn n C (n+m), pairInput u v r = false := by
    have absent (r : Fin n) (hr : r ∈ side C a b) : pairInput u v r = false := by
      cases h : pairInput u v r
      · rfl
      · exact (off ⟨r,hr,h⟩).elim
    obtain ⟨j,hj,prop⟩ := exceptional_source G C ao (pairInput u v) _ (sides_nonempty allraw ha b)
      ((top_ports ao ha _).mp on b) absent
    have eq : j = m := by simpa [single] using hj
    exact eq ▸ prop
  have splitter : ∃ b : Fin 2, ¬seen b ∧ seen (1-b) := by
    by_cases h0 : seen 0
    · exact ⟨1,fun h1 => one_blank ha cross missing ⟨h0,h1⟩,h0⟩
    · by_cases h1 : seen 1
      · exact ⟨0,h0,h1⟩
      · obtain ⟨left,⟨r,hr⟩,_⟩ := source 0 h0
        have right := (source 1 h1).1
        exact (G.irrefl (cross r (orIn_subset_of_reaches left hr) r (orIn_subset_of_reaches right hr))).elim
  obtain ⟨b,off,w,hw,xw⟩ := splitter
  obtain ⟨path,ne,pos,absent⟩ := source b off
  exact ⟨ne,pos,absent,w,xw,receiver_transfer ao ha cross b path hw⟩

end LocalReceiver

namespace LocalMixCore
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.MetaComplexity.NestedCover
open LocalLambda LocalPure LocalTransfer LocalReceiver

lemma unmixed_port {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {C : Circuit}
    (ao : IsAO2 n C) {k p : ℕ} (raw : (orIn n C (n+k)).Nonempty) (plain : k ∉ mixing G C)
    (hp : p ∈ (gateAt C k).inputs) : (orIn n C p).Nonempty := by
  letI : DecidableEq GateOp := gateOpDecEq
  obtain ⟨r,hr⟩ := raw
  obtain ⟨hk,hor,s,hs,_,source⟩ := (raw_gate C k r).mp hr
  obtain ⟨a,b,ports⟩ := List.length_eq_two.mp (ao.2.2 _ (gateAt_mem hk))
  have orn : k ∈ orN G C := Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr hk,hor,raw_above_singleton hr⟩
  have same : (orIn n C a = ∅) = (orIn n C b = ∅) := by
    by_contra ne
    apply plain
    apply Finset.mem_filter.mpr
    exact ⟨orn,by simpa [opnd,ports] using ne⟩
  have options (w : ℕ) (hw : w ∈ (gateAt C k).inputs) : w=a ∨ w=b := by simpa [ports] using hw
  apply Finset.nonempty_iff_ne_empty.mpr
  intro empty
  have ea : orIn n C a = ∅ := (options p hp).elim (fun eq => eq ▸ empty)
    (fun eq => same.mpr (eq ▸ empty))
  have es : orIn n C s = ∅ := (options s hs).elim (fun eq => eq.symm ▸ ea)
    (fun eq => eq.symm ▸ same.mp ea)
  simp [es] at source

lemma mixing_source {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (ao : IsAO2 n C) (x : Fin n → Bool) :
    ∀ w, (orIn n C w).Nonempty → val C (List.ofFn x) w = true →
      (∀ v ∈ orIn n C w, x v = false) →
      ∃ k ∈ mixing G C, OrReaches n C w k ∧ (orIn n C (n+k)).Nonempty ∧
        gateVal n C k x = true ∧ ∀ v ∈ orIn n C (n+k), x v = false := by
  letI : DecidableEq GateOp := gateOpDecEq
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro raw yes absent
    by_cases hw : w < n
    · let v : Fin n := ⟨w,hw⟩
      have mem : v ∈ orIn n C w := Finset.mem_filter.mpr ⟨Finset.mem_univ _,Or.inl rfl⟩
      exact (Bool.false_ne_true ((absent v mem).symm.trans ((value_of_input C x v).symm.trans yes))).elim
    · obtain ⟨k,rfl⟩ : ∃ k, w = n+k := ⟨w-n,by omega⟩
      obtain ⟨v,hv⟩ := raw
      obtain ⟨hk,hop,_⟩ := (raw_gate C k v).mp hv
      by_cases mixed : k ∈ mixing G C
      · exact ⟨k,mixed,(orReaches_iff n C k k).mpr ⟨hk,Or.inl rfl⟩,⟨v,hv⟩,yes,absent⟩
      · obtain ⟨p,port,prior,on⟩ := (val_or (n := n) (by simp) hk hop).mp yes
        have absentP (v : Fin n) (h : v ∈ orIn n C p) : x v = false :=
          absent v ((raw_gate C k v).mpr ⟨hk,hop,p,port,prior,h⟩)
        obtain ⟨j,hj,path,atJ,onJ,off⟩ := ih p prior (unmixed_port G ao ⟨v,hv⟩ mixed port) on absentP
        exact ⟨j,hj,(orReaches_iff n C k j).mpr ⟨hk,Or.inr ⟨hop,p,port,prior,path⟩⟩,atJ,onJ,off⟩

lemma path_le {n : ℕ} {C : Circuit} {w v : ℕ} (path : Relation.ReflTransGen (OrStep n C) w v) : v ≤ w := by
  induction path with
  | refl => exact le_rfl
  | tail _ step ih =>
    obtain ⟨_,_,rfl,_,_,lt⟩ := step
    omega

lemma reach_le {n : ℕ} {C : Circuit} {w k : ℕ} (h : OrReaches n C w k) : n+k ≤ w :=
  path_le (orReaches_reach k w h).1

lemma raw_until_mixer {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (ao : IsAO2 n C) (stop : ℕ)
    (clean : ∀ k ∈ mixing G C, stop ≤ n+k) (x : Fin n → Bool)
    {w : ℕ} (prior : w < stop) (raw : (orIn n C w).Nonempty) (on : val C (List.ofFn x) w = true) :
    ∃ v ∈ orIn n C w, x v = true := by
  by_contra absent
  have off (v : Fin n) (hv : v ∈ orIn n C w) : x v = false := by
    cases h : x v
    · rfl
    · exact (absent ⟨v,hv,h⟩).elim
  obtain ⟨k,hk,path,_⟩ := mixing_source G C ao x w raw on off
  have bound := reach_le path
  have late := clean k hk
  omega

lemma top_needs_mixing {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (ao : IsAO2 n C) {a : ℕ} (top : a ∈ tops G C)
    (cross : ∀ l ∈ side C a (0 : Fin 2), ∀ r ∈ side C a (1 : Fin 2), G.Adj l r)
    (nonempty : ∀ b : Fin 2, (side (n := n) C a b).Nonempty)
    {u v : Fin n} (missing : s(u,v) ∈ Ustar G C) (yes : gateVal n C a (pairInput u v) = true) :
    ∃ k ∈ mixing G C, k < a ∧ gateVal n C k (pairInput u v) = true := by
  letI : DecidableEq GateOp := gateOpDecEq
  have port (b : Fin 2) : opnd C a b < n+a := by
    have valid := Finset.mem_range.mp (Finset.mem_filter.mp top).1
    apply ao.2.1 a valid
    obtain ⟨p,q,ports⟩ := List.length_eq_two.mp (ao.2.2 _ (gateAt_mem valid))
    fin_cases b <;> simp [opnd,ports]
  have blank : ∃ b : Fin 2, ∀ r ∈ side C a b, pairInput u v r = false := by
    by_contra all
    push Not at all
    apply one_blank top cross missing
    exact ⟨by simpa using all 0,by simpa using all 1⟩
  obtain ⟨b,off⟩ := blank
  obtain ⟨k,hk,path,_,on,_⟩ := mixing_source G C ao _ _ (nonempty b) ((top_ports ao top _).mp yes b) off
  have h1 := reach_le path
  have h2 := port b
  exact ⟨k,hk,by omega,on⟩

end LocalMixCore

namespace LocalCone
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge
open LocalLambda

-- The cone recursion, order, and transitivity lemmas are due to willakone, project PR 3111.
lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3

lemma inCone_lt (n : ℕ) (C : Circuit) (i : ℕ) :
    ∀ j, InCone n C i j → i < j ∧ j < C.gates.length := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k, hk, _, h3 | h3⟩ := h
    · exact ⟨by omega, h0⟩
    · have := (ih k hk h3).1
      exact ⟨by omega, h0⟩

lemma inCone_trans (n : ℕ) (C : Circuit) (a k : ℕ) (hak : InCone n C a k) :
    ∀ j, InCone n C k j → InCone n C a j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k2, hk2, hin, h3 | h3⟩ := h
    · subst h3
      rw [inCone_iff]
      exact ⟨h0, k, hk2, hin, Or.inr hak⟩
    · rw [inCone_iff]
      exact ⟨h0, k2, hk2, hin, Or.inr (ih k2 hk2 h3)⟩

lemma follow_only_ors {n : ℕ} {C : Circuit} (read : ReadsBack n C) (a : ℕ) :
    ∀ b, InCone n C a b →
      (∀ k, InCone n C a k → InCone n C k b → (gateAt C k).op = GateOp.or) →
      ∃ p ∈ (gateAt C b).inputs, OrReaches n C p a := by
  intro b
  induction b using Nat.strong_induction_on with
  | ind b ih =>
    intro inside clean
    obtain ⟨hb,k,prior,port,h⟩ := (inCone_iff n C a b).mp inside
    have hk : k < C.gates.length := by omega
    have kb := (inCone_iff n C k b).mpr ⟨hb,k,prior,port,Or.inl rfl⟩
    refine ⟨n+k,port,?_⟩
    rcases h with rfl | ak
    · exact (orReaches_iff n C _ _).mpr ⟨hk,Or.inl rfl⟩
    · obtain ⟨p,hp,path⟩ := ih k prior ak (fun j aJ jK => clean j aJ (inCone_trans n C j k jK b kb))
      apply (orReaches_iff n C k a).mpr
      exact ⟨hk,Or.inr ⟨clean k ak kb,p,hp,read k hk p hp,path⟩⟩

end LocalCone

namespace LocalEmptyOR
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover
open LocalBefore

lemma sole_centreless_true {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (ao : IsAO2 n C) (z : ℕ) (hz : centreless G C = {z})
    (empty : orN G C \ lam G C = ∅)
    (shape : ∀ a ∈ tops G C, ∀ l ∈ side C a (0 : Fin 2), ∀ r ∈ side C a (1 : Fin 2), G.Adj l r)
    (trace : ∀ u v : Fin n, s(u,v) ∈ Ustar G C → ∃ a ∈ tops G C, gateVal n C a (pairInput u v) = true) :
    ∀ u v : Fin n, s(u,v) ∈ Ustar G C → gateVal n C z (pairInput u v) = true := by
  letI : DecidableEq GateOp := gateOpDecEq
  intro u v hu
  obtain ⟨a,ha,yes⟩ := trace u v hu
  by_cases hc : a ∈ centreless G C
  · have az : a=z := by simpa [hz] using hc
    exact az ▸ yes
  · have both : ∀ b : Fin 2, (side (n := n) C a b).Nonempty := by
      intro b
      apply Finset.nonempty_iff_ne_empty.mpr
      intro missing
      apply hc
      apply Finset.mem_filter.mpr
      refine ⟨ha,?_⟩
      fin_cases b
      · exact Or.inl missing
      · exact Or.inr missing
    obtain ⟨_,hk,_⟩ := earlier_exception G C ao ha (shape a ha) both hu yes
    simp [empty] at hk

end LocalEmptyOR

namespace LocalBelow
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge
open LocalTransfer LocalPure

lemma true_top_before {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (ao : IsAO2 n C) (x : Fin n → Bool) :
    ∀ w < n + C.gates.length,
      (∀ y : Fin n → Bool, val C (List.ofFn y) w = true → graphFun G ∅ y = true) →
      val C (List.ofFn x) w = true →
      ∃ a ∈ tops G C, n + a ≤ w ∧ gateVal n C a x = true := by
  letI : DecidableEq GateOp := gateOpDecEq
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro valid below on
    by_cases hw : w < n
    · let v : Fin n := ⟨w,hw⟩
      let one : Fin n → Bool := fun i => decide (i = v)
      have high : val C (List.ofFn one) w = true := by
        change val C (List.ofFn one) v.val = true
        rw [value_of_input]
        simp [one]
      have bad := below one high
      simp [graphFun,one] at bad
    · obtain ⟨k,rfl⟩ : ∃ k, w = n+k := ⟨w-n,by omega⟩
      have hk : k < C.gates.length := by omega
      rcases ao.1 _ (gateAt_mem hk) with hand | hor
      · exact ⟨k,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk,hand,below⟩,le_rfl,on⟩
      · obtain ⟨p,port,prior,yes⟩ := (val_or (n := n) (by simp) hk hor).mp on
        have lower (y : Fin n → Bool) (h : val C (List.ofFn y) p = true) :
            graphFun G ∅ y = true :=
          below y ((val_or (n := n) (by simp) hk hor).mpr ⟨p,port,prior,h⟩)
        obtain ⟨a,ha,limit,yes⟩ := ih p prior (by omega) lower yes
        exact ⟨a,ha,by omega,yes⟩

end LocalBelow

namespace LocalSingleMix
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.MetaComplexity.NestedCover
open LocalLambda LocalPure LocalTransfer LocalBefore LocalBelow LocalReceiver LocalMixCore

lemma mixer_lower {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    {m : ℕ} (single : mixing G C = {m}) (j : ℕ) (hj : j ∈ mixing G C) : n+m ≤ n+j := by
  have eq : j=m := by simpa [single] using hj
  omega

lemma routed_single {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (ao : IsAO2 n C) (m : ℕ) (single : mixing G C = {m})
    (allraw : centreless G C = ∅) {a : ℕ} (ha : a ∈ tops G C)
    (cross : ∀ l ∈ side C a (0 : Fin 2), ∀ r ∈ side C a (1 : Fin 2), G.Adj l r)
    {u v : Fin n} (missing : s(u,v) ∈ Ustar G C) (on : gateVal n C a (pairInput u v) = true) :
    (orIn n C (n+m)).Nonempty ∧ gateVal n C m (pairInput u v) = true ∧
    (∀ r ∈ orIn n C (n+m), pairInput u v r = false) ∧
    ∃ w : Fin n, pairInput u v w = true ∧
      (∀ r ∈ orIn n C (n+m), (G.deleteEdges (Ustar G C : Set (Sym2 (Fin n)))).Adj r w) ∧
      ∀ y : Fin n → Bool, gateVal n C m y = true → y w = true → graphFun G ∅ y = true := by
  let seen := fun (b : Fin 2) => ∃ r ∈ side C a b, pairInput u v r = true
  have source (b : Fin 2) (off : ¬seen b) :
      OrReaches n C (opnd C a b) m ∧ (orIn n C (n+m)).Nonempty ∧
      gateVal n C m (pairInput u v) = true ∧ ∀ r ∈ orIn n C (n+m), pairInput u v r = false := by
    have absent (r : Fin n) (hr : r ∈ side C a b) : pairInput u v r = false := by
      cases h : pairInput u v r
      · rfl
      · exact (off ⟨r,hr,h⟩).elim
    obtain ⟨j,hj,prop⟩ := mixing_source G C ao (pairInput u v) _ (sides_nonempty allraw ha b)
      ((top_ports ao ha _).mp on b) absent
    have eq : j = m := by simpa [single] using hj
    exact eq ▸ prop
  have splitter : ∃ b : Fin 2, ¬seen b ∧ seen (1-b) := by
    by_cases h0 : seen 0
    · exact ⟨1,fun h1 => one_blank ha cross missing ⟨h0,h1⟩,h0⟩
    · by_cases h1 : seen 1
      · exact ⟨0,h0,h1⟩
      · obtain ⟨left,⟨r,hr⟩,_⟩ := source 0 h0
        have right := (source 1 h1).1
        exact (G.irrefl (cross r (orIn_subset_of_reaches left hr) r (orIn_subset_of_reaches right hr))).elim
  obtain ⟨b,off,w,hw,xw⟩ := splitter
  obtain ⟨path,ne,pos,absent⟩ := source b off
  exact ⟨ne,pos,absent,w,xw,receiver_transfer ao ha cross b path hw⟩

lemma truth_single {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (ao : IsAO2 n C) (m : ℕ) (single : mixing G C = {m})
    (tests : List (Fin n → Bool)) (raw : (orIn n C (n+m)).Nonempty)
    (pos : ∀ x ∈ tests, gateVal n C m x = true)
    (absent : ∀ x ∈ tests, ∀ r ∈ orIn n C (n+m), x r = false)
    (y : Fin n → Bool)
    (lift : ∀ w < n+m, w < n+C.gates.length →
      (∀ x ∈ tests, val C (List.ofFn x) w = true) → val C (List.ofFn y) w = true) :
    gateVal n C m y = true := by
  obtain ⟨r,hr⟩ := raw
  obtain ⟨hk,hor,z,zmem,_,rz⟩ := (raw_gate C m r).mp hr
  obtain ⟨p,q,ports⟩ := List.length_eq_two.mp (ao.2.2 _ (gateAt_mem hk))
  have solve (l d : ℕ) (hl : l ∈ (gateAt C m).inputs) (hd : d ∈ (gateAt C m).inputs)
      (either : ∀ i ∈ (gateAt C m).inputs, i=l ∨ i=d) (hasRaw : (orIn n C l).Nonempty) :
      gateVal n C m y = true := by
    have ld := ao.2.1 m hk l hl
    have dd := ao.2.1 m hk d hd
    apply (val_or (n := n) (by simp) hk hor).mpr
    refine ⟨d,hd,dd,lift d dd (by omega) ?_⟩
    intro x hx
    obtain ⟨s,hs,_,on⟩ := (val_or (n := n) (by simp) hk hor).mp (pos x hx)
    rcases either s hs with rfl | rfl
    · obtain ⟨w,hw,wx⟩ := raw_until_mixer G C ao (n+m) (mixer_lower single)
        x ld hasRaw on
      have off := absent x hx w ((raw_gate C m w).mpr ⟨hk,hor,_,hl,ld,hw⟩)
      simp [off] at wx
    · exact on
  have hp : p ∈ (gateAt C m).inputs := by simp [ports]
  have hq : q ∈ (gateAt C m).inputs := by simp [ports]
  have all (i : ℕ) (hi : i ∈ (gateAt C m).inputs) : i=p ∨ i=q := by simpa [ports] using hi
  rcases all z zmem with rfl | rfl
  · exact solve _ _ hp hq all ⟨r,rz⟩
  · exact solve _ _ hq hp (fun i hi => (all i hi).symm) ⟨r,rz⟩

lemma prefix_with_one {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (ao : IsAO2 n C) (m d : ℕ)
    (only : orN G C \ lam G C ⊆ {m,d}) (single : mixing G C = {m})
    (dRaw : d < m → (orIn n C (n+d)).Nonempty)
    (allraw : centreless G C = ∅)
    (shape : ∀ a ∈ tops G C, ∀ l ∈ side C a (0 : Fin 2), ∀ r ∈ side C a (1 : Fin 2), G.Adj l r)
    (tests : List (Fin n → Bool)) (u v : Fin n) (e : s(u,v) ∈ Ustar G C) (present : pairInput u v ∈ tests)
    (y : Fin n → Bool) (pins : ∀ i : Fin n, (∀ x ∈ tests, x i = true) → y i = true)
    (clauses : ∀ A : Finset (Fin n), A.Nonempty →
      (∃ c : Fin n, ∀ v ∈ A, (G.deleteEdges (Ustar G C : Set (Sym2 (Fin n)))).Adj c v) →
      (∀ x ∈ tests, ∃ v ∈ A, x v = true) → ∃ v ∈ A, y v = true)
    (extra : (∀ x ∈ tests, ∃ v ∈ orIn n C (n+d), x v = true) → ∃ v ∈ orIn n C (n+d), y v = true) :
    ∀ w < n+m, w < n+C.gates.length →
      (∀ x ∈ tests, val C (List.ofFn x) w = true) → val C (List.ofFn y) w = true := by
  letI : DecidableEq GateOp := gateOpDecEq
  apply tests_through_ands C ao.1 tests (pairInput u v) present y (n+m) pins
  intro k hk prior hor pos
  by_cases below : BelowF G C k
  · obtain ⟨a,ha,le,yes⟩ := true_top_before G C ao (pairInput u v) (n+k) (by omega) below (pos _ present)
    obtain ⟨j,hj,jlt,_⟩ := top_needs_mixing G C ao ha (shape a ha) (sides_nonempty allraw ha) e yes
    have eq : j=m := by simpa [single] using hj
    omega
  · have orn : k ∈ orN G C := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk,hor,below⟩
    have lift (raw : (orIn n C (n+k)).Nonempty)
        (extract : (∀ x ∈ tests, ∃ v ∈ orIn n C (n+k), x v = true) → ∃ v ∈ orIn n C (n+k), y v = true) :
        val C (List.ofFn y) (n+k) = true := by
      obtain ⟨v,hv,on⟩ := extract (fun x hx =>
        raw_until_mixer G C ao (n+m) (mixer_lower single) x prior raw (pos x hx))
      exact raw_pin y hv on
    by_cases normal : k ∈ lam G C
    · obtain ⟨p,q,ports⟩ := List.length_eq_two.mp (ao.2.2 _ (gateAt_mem hk))
      have port : p ∈ (gateAt C k).inputs := by simp [ports]
      obtain ⟨i,hi⟩ := lambda_port ao normal port
      have raw : (orIn n C (n+k)).Nonempty :=
        ⟨i,(raw_gate C k i).mpr ⟨hk,hor,p,port,ao.2.1 k hk p port,hi⟩⟩
      exact lift raw (clauses _ raw (lambda_raw_clause shape normal))
    · have options := only (Finset.mem_sdiff.mpr ⟨orn,normal⟩)
      have eq : k=d := by
        have cases : k=m ∨ k=d := by simpa using options
        omega
      subst k
      exact lift (dRaw (by omega)) extra

end LocalSingleMix

namespace LocalMixerTransfer
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.MetaComplexity.NestedCover
open LocalLambda LocalPure LocalTransfer LocalBefore LocalBelow LocalReceiver

lemma earlier_lambda {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    {m : ℕ} (single : orN G C \ lam G C = {m}) {k : ℕ} (prior : n+k < n+m)
    (hk : k ∈ orN G C) : k ∈ lam G C := by
  by_contra h
  have mem : k ∈ orN G C \ lam G C := Finset.mem_sdiff.mpr ⟨hk,h⟩
  have eq : k = m := by simpa [single] using mem
  omega

lemma prefix_transfer {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (ao : IsAO2 n C) (m : ℕ) (single : orN G C \ lam G C = {m})
    (allraw : centreless G C = ∅)
    (shape : ∀ a ∈ tops G C, ∀ l ∈ side C a (0 : Fin 2), ∀ r ∈ side C a (1 : Fin 2), G.Adj l r)
    (tests : List (Fin n → Bool)) (u v : Fin n) (e : s(u,v) ∈ Ustar G C) (present : pairInput u v ∈ tests)
    (y : Fin n → Bool) (pins : ∀ i : Fin n, (∀ x ∈ tests, x i = true) → y i = true)
    (clauses : ∀ A : Finset (Fin n), A.Nonempty →
      (∃ c : Fin n, ∀ v ∈ A, (G.deleteEdges (Ustar G C : Set (Sym2 (Fin n)))).Adj c v) →
      (∀ x ∈ tests, ∃ v ∈ A, x v = true) → ∃ v ∈ A, y v = true) :
    ∀ w < n+m, w < n+C.gates.length →
      (∀ x ∈ tests, val C (List.ofFn x) w = true) → val C (List.ofFn y) w = true := by
  letI : DecidableEq GateOp := gateOpDecEq
  apply tests_through_ands C ao.1 tests (pairInput u v) present y (n+m) pins
  intro k hk prior hor pos
  by_cases below : BelowF G C k
  · obtain ⟨a,ha,le,yes⟩ := true_top_before G C ao (pairInput u v) (n+k) (by omega) below
      (pos _ present)
    obtain ⟨j,hj,jlt⟩ := earlier_exception G C ao ha (shape a ha) (sides_nonempty allraw ha) e yes
    have eq : j = m := by simpa [single] using hj
    omega
  · have normal := earlier_lambda single prior (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk,hor,below⟩)
    obtain ⟨p,q,ports⟩ := List.length_eq_two.mp (ao.2.2 _ (gateAt_mem hk))
    have port : p ∈ (gateAt C k).inputs := by simp [ports]
    obtain ⟨i,hi⟩ := lambda_port ao normal port
    have raw : (orIn n C (n+k)).Nonempty :=
      ⟨i,(raw_gate C k i).mpr ⟨hk,hor,p,port,ao.2.1 k hk p port,hi⟩⟩
    obtain ⟨v,hv,on⟩ := clauses _ raw (lambda_raw_clause shape normal)
      (fun x hx => pure_before G C ao (n+m) (fun _ h => earlier_lambda single h) x _ prior raw (pos x hx))
    exact raw_pin y hv on

lemma mixer_truth {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (ao : IsAO2 n C) (m : ℕ) (single : orN G C \ lam G C = {m})
    (tests : List (Fin n → Bool)) (raw : (orIn n C (n+m)).Nonempty)
    (pos : ∀ x ∈ tests, gateVal n C m x = true)
    (absent : ∀ x ∈ tests, ∀ r ∈ orIn n C (n+m), x r = false)
    (y : Fin n → Bool)
    (lift : ∀ w < n+m, w < n+C.gates.length →
      (∀ x ∈ tests, val C (List.ofFn x) w = true) → val C (List.ofFn y) w = true) :
    gateVal n C m y = true := by
  obtain ⟨r,hr⟩ := raw
  obtain ⟨hk,hor,z,zmem,_,rz⟩ := (raw_gate C m r).mp hr
  obtain ⟨p,q,ports⟩ := List.length_eq_two.mp (ao.2.2 _ (gateAt_mem hk))
  have solve (l d : ℕ) (hl : l ∈ (gateAt C m).inputs) (hd : d ∈ (gateAt C m).inputs)
      (either : ∀ i ∈ (gateAt C m).inputs, i=l ∨ i=d) (hasRaw : (orIn n C l).Nonempty) :
      gateVal n C m y = true := by
    have ld := ao.2.1 m hk l hl
    have dd := ao.2.1 m hk d hd
    apply (val_or (n := n) (by simp) hk hor).mpr
    refine ⟨d,hd,dd,lift d dd (by omega) ?_⟩
    intro x hx
    obtain ⟨s,hs,_,on⟩ := (val_or (n := n) (by simp) hk hor).mp (pos x hx)
    rcases either s hs with rfl | rfl
    · obtain ⟨w,hw,wx⟩ := pure_before G C ao (n+m) (fun _ h => earlier_lambda single h)
        x _ ld hasRaw on
      have off := absent x hx w ((raw_gate C m w).mpr ⟨hk,hor,_,hl,ld,hw⟩)
      simp [off] at wx
    · exact on
  have hp : p ∈ (gateAt C m).inputs := by simp [ports]
  have hq : q ∈ (gateAt C m).inputs := by simp [ports]
  have all (i : ℕ) (hi : i ∈ (gateAt C m).inputs) : i=p ∨ i=q := by simpa [ports] using hi
  rcases all z zmem with rfl | rfl
  · exact solve _ _ hp hq all ⟨r,rz⟩
  · exact solve _ _ hq hp (fun i hi => (all i hi).symm) ⟨r,rz⟩

end LocalMixerTransfer


end PEqualNP.Outside.Pnp650TransferCore
