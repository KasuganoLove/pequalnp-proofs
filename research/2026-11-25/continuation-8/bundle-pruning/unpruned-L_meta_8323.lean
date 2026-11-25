import Mathlib
import PEqualNP.Defs

-- Source module: Pnp4201Cover105
namespace PEqualNP.Outside.L_meta_8323

namespace Part0

abbrev Inc (p l : Fin 21) : Prop :=
  (l.val + 21 - p.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)

def incidences : Finset (Fin 21 × Fin 21) :=
  Finset.univ.filter fun e => Inc e.1 e.2

def commonLines (p q : Fin 21) : Finset (Fin 21) :=
  Finset.univ.filter fun l => Inc p l ∧ Inc q l

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16000 in
lemma incidence_count : incidences.card = 105 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16000 in
lemma commonLines_card_le_one : ∀ p q : Fin 21, p ≠ q → (commonLines p q).card ≤ 1 := by
  decide +kernel

lemma rectangle_has_singleton_side (A B : Finset (Fin 21))
    (hrect : ∀ p ∈ A, ∀ l ∈ B, Inc p l) : A.card ≤ 1 ∨ B.card ≤ 1 := by
  by_cases hA : A.card ≤ 1
  · exact Or.inl hA
  · obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp (by omega : 1 < A.card)
    have hsub : B ⊆ commonLines p q := by
      intro l hl
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ l, hrect p hp l hl, hrect q hq l hl⟩
    exact Or.inr ((Finset.card_le_card hsub).trans (commonLines_card_le_one p q hpq))

lemma rectangle_card_le_weight (A B : Finset (Fin 21))
    (hA : A.Nonempty) (hB : B.Nonempty)
    (hrect : ∀ p ∈ A, ∀ l ∈ B, Inc p l) :
    (A ×ˢ B).card ≤ A.card + B.card - 1 := by
  have ha : 0 < A.card := Finset.card_pos.mpr hA
  have hb : 0 < B.card := Finset.card_pos.mpr hB
  rw [Finset.card_product]
  rcases rectangle_has_singleton_side A B hrect with h | h
  · have he : A.card = 1 := by omega
    rw [he, Nat.one_mul]
    omega
  · have he : B.card = 1 := by omega
    rw [he, Nat.mul_one]
    omega

theorem cover_cost_ge_105 (F : Finset (Finset (Fin 21) × Finset (Fin 21)))
    (hrect : ∀ p ∈ F, p.1.Nonempty ∧ p.2.Nonempty ∧
      ∀ u ∈ p.1, ∀ v ∈ p.2, Inc u v)
    (hcover : ∀ u v : Fin 21, Inc u v → ∃ p ∈ F, u ∈ p.1 ∧ v ∈ p.2) :
    105 ≤ F.sum (fun p => p.1.card + p.2.card - 1) := by
  have hsub : incidences ⊆ F.biUnion (fun p => p.1 ×ˢ p.2) := by
    intro e he
    obtain ⟨p, hp, hu, hv⟩ := hcover e.1 e.2 (Finset.mem_filter.mp he).2
    exact Finset.mem_biUnion.mpr ⟨p, hp, Finset.mem_product.mpr ⟨hu, hv⟩⟩
  calc
    105 = incidences.card := incidence_count.symm
    _ ≤ (F.biUnion (fun p => p.1 ×ˢ p.2)).card := Finset.card_le_card hsub
    _ ≤ F.sum (fun p => (p.1 ×ˢ p.2).card) := Finset.card_biUnion_le
    _ ≤ F.sum (fun p => p.1.card + p.2.card - 1) := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hA, hB, hI⟩ := hrect p hp
      exact rectangle_card_le_weight p.1 p.2 hA hB hI

theorem exact_8470 : ∀ (x1 : Finset (Finset (Fin (21 : ℕ)) × Finset (Fin (21 : ℕ)))), (∀ x2 ∈ x1, x2.1.Nonempty ∧ x2.2.Nonempty ∧ ∀ x4 ∈ x2.1, ∀ x6 ∈ x2.2, (↑x6 + (21 : ℕ) - ↑x4) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) → (∀ (x3 x4 : Fin (21 : ℕ)), (↑x4 + (21 : ℕ) - ↑x3) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)] → ∃ x6 ∈ x1, x3 ∈ x6.1 ∧ x4 ∈ x6.2) → (105 : ℕ) ≤ ∑ x4 ∈ x1, (x4.1.card + x4.2.card - (1 : ℕ)) := by
  exact cover_cost_ge_105

end Part0

end PEqualNP.Outside.L_meta_8323

-- Source module: Pnp4201Graph
namespace PEqualNP.Outside.L_meta_8323

namespace Part1

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_8323.Part0

def Forward (u v : Fin 42) : Prop :=
  u.val < 21 ∧ 21 ≤ v.val ∧
    (v.val + 21 - u.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)

instance (u v : Fin 42) : Decidable (Forward u v) := by
  unfold Forward
  infer_instance

def pg4 : SimpleGraph (Fin 42) := SimpleGraph.fromRel Forward

instance : DecidableRel pg4.Adj := by
  intro u v
  change Decidable (u ≠ v ∧ (Forward u v ∨ Forward v u))
  infer_instance

def point (p : Fin 21) : Fin 42 := ⟨p.val, by have := p.isLt; omega⟩
def line (l : Fin 21) : Fin 42 := ⟨21 + l.val, by have := l.isLt; omega⟩

lemma point_injective : Function.Injective point := by
  intro p q h
  apply Fin.ext
  exact congrArg (fun v : Fin 42 => v.val) h

lemma line_injective : Function.Injective line := by
  intro p q h
  apply Fin.ext
  have hv := congrArg Fin.val h
  change 21 + p.val = 21 + q.val at hv
  omega

lemma point_ne_line (p l : Fin 21) : point p ≠ line l := by
  intro h
  have hv := congrArg Fin.val h
  have hp := p.isLt
  change p.val = 21 + l.val at hv
  omega

lemma vertex_split (v : Fin 42) : (∃ p : Fin 21, v = point p) ∨
    (∃ l : Fin 21, v = line l) := by
  by_cases hv : v.val < 21
  · exact Or.inl ⟨⟨v.val, hv⟩, rfl⟩
  · refine Or.inr ⟨⟨v.val - 21, by have := v.isLt; omega⟩, ?_⟩
    apply Fin.ext
    dsimp [line]
    omega

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16000 in
lemma adj_point_line : ∀ p l : Fin 21, pg4.Adj (point p) (line l) ↔ Inc p l := by
  decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16000 in
lemma not_adj_point_point : ∀ p q : Fin 21, ¬ pg4.Adj (point p) (point q) := by
  decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16000 in
lemma not_adj_line_line : ∀ p q : Fin 21, ¬ pg4.Adj (line p) (line q) := by
  decide +kernel

lemma adj_line_point (l p : Fin 21) : pg4.Adj (line l) (point p) ↔ Inc p l := by
  rw [SimpleGraph.adj_comm]
  exact adj_point_line p l

def color (v : Fin 42) : Bool := decide (v.val < 21)

theorem bipartite : ∀ u v : Fin 42, pg4.Adj u v → color u ≠ color v := by
  intro u v h
  rcases ((SimpleGraph.fromRel_adj ..).mp h).2 with h | h
  · simp [color, h.1, not_lt.mpr h.2.1]
  · simp [color, h.1, not_lt.mpr h.2.1]

theorem noFourCycle : PEqualNP.TopForm.NoFourCycle pg4 := by
  intro a b hab
  apply Finset.card_le_one.mpr
  intro u hu v hv
  obtain ⟨hau, hbu⟩ := (Finset.mem_filter.mp hu).2
  obtain ⟨hav, hbv⟩ := (Finset.mem_filter.mp hv).2
  rcases vertex_split a with ⟨p, rfl⟩ | ⟨p, rfl⟩
  · rcases vertex_split b with ⟨q, rfl⟩ | ⟨q, rfl⟩
    · have hpq : p ≠ q := fun h => hab (congrArg point h)
      rcases vertex_split u with ⟨l, rfl⟩ | ⟨l, rfl⟩
      · exact False.elim (not_adj_point_point p l hau)
      rcases vertex_split v with ⟨m, rfl⟩ | ⟨m, rfl⟩
      · exact False.elim (not_adj_point_point p m hav)
      apply congrArg line
      apply Finset.card_le_one.mp (commonLines_card_le_one p q hpq)
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (adj_point_line p l).mp hau, (adj_point_line q l).mp hbu⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (adj_point_line p m).mp hav, (adj_point_line q m).mp hbv⟩
    · rcases vertex_split u with ⟨l, rfl⟩ | ⟨l, rfl⟩
      · exact False.elim (not_adj_point_point p l hau)
      · exact False.elim (not_adj_line_line q l hbu)
  · rcases vertex_split b with ⟨q, rfl⟩ | ⟨q, rfl⟩
    · rcases vertex_split u with ⟨l, rfl⟩ | ⟨l, rfl⟩
      · exact False.elim (not_adj_point_point q l hbu)
      · exact False.elim (not_adj_line_line p l hau)
    · rcases vertex_split u with ⟨l, rfl⟩ | ⟨l, rfl⟩
      swap
      · exact False.elim (not_adj_line_line p l hau)
      rcases vertex_split v with ⟨m, rfl⟩ | ⟨m, rfl⟩
      swap
      · exact False.elim (not_adj_line_line p m hav)
      apply congrArg point
      by_contra hlm
      have hpq : p = q := Finset.card_le_one.mp (commonLines_card_le_one l m hlm) p
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (adj_line_point p l).mp hau, (adj_line_point p m).mp hav⟩)
        q (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (adj_line_point q l).mp hbu, (adj_line_point q m).mp hbv⟩)
      exact hab (congrArg line hpq)

def orderedEdges : Finset (Fin 42 × Fin 42) :=
  Finset.univ.filter fun e => e.1 < e.2 ∧ pg4.Adj e.1 e.2

def incidencePair (e : Fin 21 × Fin 21) : Fin 42 × Fin 42 := (point e.1, line e.2)

lemma incidencePair_injective : Function.Injective incidencePair := by
  intro a b h
  apply Prod.ext
  · exact point_injective (congrArg Prod.fst h)
  · exact line_injective (congrArg Prod.snd h)

lemma orderedEdges_eq : orderedEdges = incidences.image incidencePair := by
  ext e
  rcases e with ⟨u, v⟩
  constructor
  · intro h
    obtain ⟨hlt, hadj⟩ := (Finset.mem_filter.mp h).2
    have hforward : Forward u v := by
      rcases ((SimpleGraph.fromRel_adj ..).mp hadj).2 with h | h
      · exact h
      · have huv : u.val < v.val := hlt
        have := h.1
        have := h.2.1
        omega
    let p : Fin 21 := ⟨u.val, hforward.1⟩
    let l : Fin 21 := ⟨v.val - 21, by have := v.isLt; have := hforward.2.1; omega⟩
    have hp : point p = u := rfl
    have hl : line l = v := by
      apply Fin.ext
      dsimp [line, l]
      have := hforward.2.1
      omega
    have hinc : Inc p l := (adj_point_line p l).mp (by rw [hp, hl]; exact hadj)
    exact Finset.mem_image.mpr ⟨(p, l), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hinc⟩,
      by simp only [incidencePair, hp, hl]⟩
  · intro h
    obtain ⟨⟨p,l⟩, hmem, he⟩ := Finset.mem_image.mp h
    have hinc := (Finset.mem_filter.mp hmem).2
    have htarget : (point p, line l) = (u,v) := he
    cases htarget
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, (adj_point_line p l).mpr hinc⟩
    change p.val < 21 + l.val
    have := p.isLt
    omega

theorem orderedEdges_card : orderedEdges.card = 105 := by
  rw [orderedEdges_eq, Finset.card_image_of_injective _ incidencePair_injective]
  exact incidence_count

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 16000 in
theorem edgeFinset_card : pg4.edgeFinset.card = 105 := by
  decide +kernel

def PublicTarget (x : Fin 42 → Bool) : Prop :=
  ∃ u v : Fin 42, Forward u v ∧ x u = true ∧ x v = true

theorem graphFun_true_iff (x : Fin 42 → Bool) :
    graphFun pg4 ∅ x = true ↔ PublicTarget x := by
  have hgraph : graphFun pg4 ∅ x = true ↔
      ∃ u v : Fin 42, pg4.Adj u v ∧ x u = true ∧ x v = true := by
    simp [graphFun]
  rw [hgraph]
  constructor
  · rintro ⟨u,v,h,hu,hv⟩
    rcases ((SimpleGraph.fromRel_adj ..).mp h).2 with h | h
    · exact ⟨u,v,h,hu,hv⟩
    · exact ⟨v,u,h,hv,hu⟩
  · rintro ⟨u,v,h,hu,hv⟩
    refine ⟨u,v,(SimpleGraph.fromRel_adj ..).mpr ⟨?_,Or.inl h⟩,hu,hv⟩
    intro he
    have heval := congrArg Fin.val he
    have := h.1
    have := h.2.1
    omega

theorem computes_iff (C : Circuit) :
    (∀ x : Fin 42 → Bool, C.eval (List.ofFn x) = true ↔ PublicTarget x) ↔
    circuitFun 42 C = graphFun pg4 ∅ := by
  constructor
  · intro h
    funext x
    apply Bool.eq_iff_iff.mpr
    exact (h x).trans (graphFun_true_iff x).symm
  · intro h x
    change circuitFun 42 C x = true ↔ PublicTarget x
    rw [h]
    exact graphFun_true_iff x

theorem nonconstant : ∃ x y : Fin 42 → Bool, graphFun pg4 ∅ x ≠ graphFun pg4 ∅ y := by
  let x : Fin 42 → Bool := fun _ => false
  let y : Fin 42 → Bool := fun v => decide (v = 0 ∨ v = 21)
  have hx : graphFun pg4 ∅ x = false := by simp [graphFun, x]
  have hy : graphFun pg4 ∅ y = true := by
    apply (graphFun_true_iff y).mpr
    exact ⟨0,21,by decide +kernel,by decide +kernel,by decide +kernel⟩
  exact ⟨x,y,by rw [hx,hy]; decide⟩

def AllANDSafe (C : Circuit) : Prop :=
  ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
    ∀ x : Fin 42 → Bool, gateVal 42 C j x = true → PublicTarget x

theorem allANDSafe_iff (C : Circuit) : AllANDSafe C ↔
    ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      PEqualNP.TopForm.BelowF pg4 C j := by
  constructor
  · intro h j hj hop x hx
    exact (graphFun_true_iff x).mpr (h j hj hop x hx)
  · intro h j hj hop x hx
    exact (graphFun_true_iff x).mp (h j hj hop x hx)

end Part1

end PEqualNP.Outside.L_meta_8323

-- Source module: PEqualNP.Outside.L_meta_2235
namespace PEqualNP.Outside.L_meta_8323

namespace Part2

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def s2230_stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma s2230_wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl s2230_stepWire x := rfl

lemma s2230_foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl s2230_stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [s2230_stepWire]
    omega

lemma s2230_foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl s2230_stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (s2230_stepWire w g).length := by simp [s2230_stepWire]; omega
    rw [ih (s2230_stepWire w g) hlt]
    simp [s2230_stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma s2230_getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma s2230_wires_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [s2230_wires_eq_foldl, s2230_foldl_stepWire_length, List.length_ofFn]

lemma s2230_split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

def s2230_W (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD u false

lemma s2230_gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma s2230_W_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length) :
    s2230_W n C x (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
      if i < n + k then s2230_W n C x i else false) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := s2230_split_gates C.gates k hk
  have hga : gateAt C k = gj := by rw [s2230_gateAt_eq C k hk]; exact hgj
  rw [hga]
  let w0 := pre.foldl s2230_stepWire (List.ofFn x)
  have hw0_len : w0.length = n + k := by
    simp [w0, s2230_foldl_stepWire_length, hpre_len]
  have hCj : s2230_W n C x (n + k) = gj.op.eval (gj.inputs.map fun i => w0.getD i false) := by
    simp only [s2230_W]
    rw [s2230_wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
    rw [s2230_foldl_stepWire_getD_lt post (s2230_stepWire w0 gj) (n + k) (by simp [s2230_stepWire]; omega)]
    simp [s2230_stepWire, List.getD_eq_getElem?_getD, hw0_len]
  rw [hCj]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  by_cases hi : i < n + k
  · simp only [hi, ↓reduceIte]
    simp only [s2230_W]
    rw [s2230_wires_eq_foldl, hgs, List.foldl_append]
    exact (s2230_foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)).symm
  · simp only [hi, ↓reduceIte]
    exact s2230_getD_ge_length w0 i (by omega)

lemma s2230_W_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    s2230_W n C x u = x ⟨u, hu⟩ := by
  simp only [s2230_W]
  rw [s2230_wires_eq_foldl, s2230_foldl_stepWire_getD_lt C.gates (List.ofFn x) u (by simpa using hu)]
  simp [List.getD_eq_getElem?_getD, hu]

open PEqualNP.CleanedNonEdge in
lemma s2230_orFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

open PEqualNP.CleanedNonEdge in
lemma s2230_orStep_mem_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) (x : ℕ) :
    x ∈ (orStep n cs g).getD cs.length [] ↔ x = cs.length ∨ (g.op = GateOp.or ∧
      ∃ w ∈ g.inputs, n ≤ w ∧ w < n + cs.length ∧ x ∈ cs.getD (w - n) []) := by
  by_cases h : g.op = GateOp.or
  · simp only [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl, h,
      ↓reduceIte, true_and, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some,
      List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro (h1 | ⟨w, ⟨hw, hn, hlt⟩, hx⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨w, hw, hn, hlt, hx⟩
    · rintro (h1 | ⟨w, hw, hn, hlt, hx⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨w, ⟨hw, hn, hlt⟩, hx⟩
  · simp [orStep, List.getD_eq_getElem?_getD, h]

open PEqualNP.CleanedNonEdge in
lemma s2230_orStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (orStep n cs g).getD m [] = cs.getD m [] := by
  simp [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

open PEqualNP.CleanedNonEdge in
lemma s2230_orFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (orStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (orStep n cs g) (by simp [orStep]; omega)]
    exact s2230_orStep_getD_lt n cs g k hk

open PEqualNP.CleanedNonEdge in
lemma s2230_orSets_mem_iff (n : ℕ) (C : Circuit) (k x : ℕ) (hk : k < C.gates.length) :
    x ∈ (orSets n C).getD k [] ↔ x = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧ x ∈ (orSets n C).getD (w - n) []) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := s2230_split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [s2230_gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : orSets n C = post.foldl (orStep n) (orStep n (pre.foldl (orStep n) []) gk) := by
    simp only [orSets]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (orStep n) []).length = k := by
    rw [s2230_orFold_length]; simp [hpre_len]
  have hl1 : (orStep n (pre.foldl (orStep n) []) gk).length = k + 1 := by
    simp [orStep, hl0]
  have h1 : (orSets n C).getD k [] = (orStep n (pre.foldl (orStep n) []) gk).getD k [] := by
    rw [hc, s2230_orFold_getD_lt n post _ k (by omega)]
  have h2 : ∀ m, m < k → (orSets n C).getD m [] = (pre.foldl (orStep n) []).getD m [] := by
    intro m hm
    rw [hc, s2230_orFold_getD_lt n post _ m (by omega)]
    exact s2230_orStep_getD_lt n _ gk m (by omega)
  have h3 := s2230_orStep_mem_last n (pre.foldl (orStep n) []) gk x
  rw [hl0] at h3
  rw [h1, h3]
  constructor
  · rintro (h | ⟨hop, w, hw, hn, hlt, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [h2 (w - n) (by omega)]; exact hx⟩
  · rintro (h | ⟨hop, w, hw, hn, hlt, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [← h2 (w - n) (by omega)]; exact hx⟩

open PEqualNP.CleanedNonEdge PEqualNP.ReadK PEqualNP.TopForm

lemma s2230_orReaches_self (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    OrReaches n C (n + j) j := by
  unfold OrReaches
  refine ⟨Nat.le_add_right n j, ?_⟩
  rw [Nat.add_sub_cancel_left, s2230_orSets_mem_iff n C j j hj]
  exact Or.inl rfl

lemma s2230_orReaches_step (n : ℕ) (C : Circuit) (j i g : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (hi : i ∈ (gateAt C j).inputs) (hlt : i < n + j)
    (h : OrReaches n C i g) : OrReaches n C (n + j) g := by
  unfold OrReaches at h ⊢
  refine ⟨Nat.le_add_right n j, ?_⟩
  rw [Nat.add_sub_cancel_left, s2230_orSets_mem_iff n C j g hj]
  exact Or.inr ⟨hop, i, hi, h.1, hlt, h.2⟩

lemma s2230_mem_filter_iff_gen {α : Type} (p : α → Prop) (d : DecidablePred p) (s : Finset α) (a : α) :
    a ∈ @Finset.filter α p d s ↔ a ∈ s ∧ p a :=
  @Finset.mem_filter α p d s a

lemma s2230_mem_orIn (n : ℕ) (C : Circuit) (w : ℕ) (i : Fin n) :
    i ∈ orIn n C w ↔ ((i : ℕ) = w ∨ ∃ k < C.gates.length,
      OrReaches n C w k ∧ (gateAt C k).op = GateOp.or ∧ (i : ℕ) ∈ (gateAt C k).inputs) := by
  unfold orIn
  exact ⟨fun h => ((s2230_mem_filter_iff_gen _ _ _ _).1 h).2,
    fun h => (s2230_mem_filter_iff_gen _ _ _ _).2 ⟨Finset.mem_univ _, h⟩⟩

lemma s2230_orIn_up (n : ℕ) (C : Circuit) (j i : ℕ) (a : Fin n) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (hi : i ∈ (gateAt C j).inputs) (hlt : i < n + j)
    (h : a ∈ orIn n C i) : a ∈ orIn n C (n + j) := by
  rw [s2230_mem_orIn] at h ⊢
  right
  rcases h with h | ⟨k, hk, hr, hopk, hin⟩
  · exact ⟨j, hj, s2230_orReaches_self n C j hj, hop, by rw [h]; exact hi⟩
  · exact ⟨k, hk, s2230_orReaches_step n C j i k hj hop hi hlt hr, hopk, hin⟩

def s2230_FR (S : List ℕ) (k : ℕ) (R : List (List (List ℕ))) (g : Gate) : List (List ℕ) :=
  match g.op with
  | GateOp.or => (g.inputs.map fun i => R.getD i []).foldl (fun acc A => A.foldl insertNew acc) []
  | GateOp.and => (g.inputs.map fun i => R.getD i []).foldl (andStep k) [S.map fun _ => 0]
  | _ => []

def s2230_stepR (S : List ℕ) (k : ℕ) (R : List (List (List ℕ))) (g : Gate) : List (List (List ℕ)) :=
  R ++ [s2230_FR S k R g]

lemma s2230_readVectors_eq (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) :
    readVectors C n S k = C.gates.foldl (s2230_stepR S k) ((List.range n).map (leafVectors S k)) := by
  first
    | rfl
    | (unfold readVectors; congr 1; funext R g; rcases g with ⟨op, ins⟩; cases op <;> rfl)

lemma s2230_FR_or (S : List ℕ) (k : ℕ) (R : List (List (List ℕ))) (g : Gate) (h : g.op = GateOp.or) :
    s2230_FR S k R g =
      (g.inputs.map fun i => R.getD i []).foldl (fun acc A => A.foldl insertNew acc) [] := by
  obtain ⟨op, ins⟩ := g
  have h2 : op = GateOp.or := h
  subst h2
  rfl

lemma s2230_FR_and (S : List ℕ) (k : ℕ) (R : List (List (List ℕ))) (g : Gate)
    (h : g.op = GateOp.and) :
    s2230_FR S k R g = (g.inputs.map fun i => R.getD i []).foldl (andStep k) [S.map fun _ => 0] := by
  obtain ⟨op, ins⟩ := g
  have h2 : op = GateOp.and := h
  subst h2
  rfl

lemma s2230_foldR_length (S : List ℕ) (k : ℕ) (gs : List Gate) (R : List (List (List ℕ))) :
    (gs.foldl (s2230_stepR S k) R).length = R.length + gs.length := by
  induction gs generalizing R with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [s2230_stepR]
    omega

lemma s2230_foldR_getD_lt (S : List ℕ) (k : ℕ) (gs : List Gate) (R : List (List (List ℕ))) (i : ℕ)
    (hi : i < R.length) : (gs.foldl (s2230_stepR S k) R).getD i [] = R.getD i [] := by
  induction gs generalizing R with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (s2230_stepR S k R g).length := by simp [s2230_stepR]; omega
    rw [ih (s2230_stepR S k R g) hlt]
    simp [s2230_stepR, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

def s2230_RV (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) (w : ℕ) : List (List ℕ) :=
  (readVectors C n S k).getD w []

lemma s2230_RV_input (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) (w : ℕ) (hw : w < n) :
    s2230_RV C n S k w = leafVectors S k w := by
  simp only [s2230_RV]
  rw [s2230_readVectors_eq, s2230_foldR_getD_lt S k C.gates ((List.range n).map (leafVectors S k)) w
    (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

lemma s2230_RV_gate (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) (j : ℕ) (hj : j < C.gates.length) :
    ∃ Rp : List (List (List ℕ)),
      (∀ i, i < n + j → Rp.getD i [] = s2230_RV C n S k i) ∧
      s2230_RV C n S k (n + j) = s2230_FR S k Rp (gateAt C j) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := s2230_split_gates C.gates j hj
  have hga : gateAt C j = gj := by rw [s2230_gateAt_eq C j hj]; exact hgj
  rw [hga]
  obtain ⟨Rp, hRp⟩ : ∃ Rp, Rp = pre.foldl (s2230_stepR S k) ((List.range n).map (leafVectors S k)) :=
    ⟨_, rfl⟩
  have hlen : Rp.length = n + j := by
    rw [hRp, s2230_foldR_length]
    simp only [List.length_map, List.length_range, hpre_len]
  have hall : readVectors C n S k = post.foldl (s2230_stepR S k) (s2230_stepR S k Rp gj) := by
    rw [s2230_readVectors_eq, hgs, List.foldl_append, List.foldl_cons, hRp]
  have hlen1 : (s2230_stepR S k Rp gj).length = n + j + 1 := by
    simp [s2230_stepR, hlen]
  refine ⟨Rp, ?_, ?_⟩
  · intro i hi
    simp only [s2230_RV]
    rw [hall, s2230_foldR_getD_lt S k post (s2230_stepR S k Rp gj) i (by omega)]
    simp [s2230_stepR, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (show i < Rp.length by omega)]
  · simp only [s2230_RV]
    rw [hall, s2230_foldR_getD_lt S k post (s2230_stepR S k Rp gj) (n + j) (by omega)]
    simp [s2230_stepR, List.getD_eq_getElem?_getD, hlen]

lemma s2230_mem_foldl_insertNew (L : List (List ℕ)) (acc : List (List ℕ)) (v : List ℕ)
    (h : v ∈ L.foldl insertNew acc) : v ∈ acc ∨ v ∈ L := by
  induction L generalizing acc with
  | nil => exact Or.inl h
  | cons x L ih =>
    rw [List.foldl_cons] at h
    rcases ih _ h with h1 | h1
    · unfold insertNew at h1
      split_ifs at h1
      · exact Or.inl h1
      · rcases List.mem_append.1 h1 with h2 | h2
        · exact Or.inl h2
        · have h3 : v = x := by simpa using h2
          exact Or.inr (by simp [h3])
    · exact Or.inr (List.mem_cons_of_mem _ h1)

lemma s2230_mem_andStep (k : ℕ) (A B : List (List ℕ)) (v : List ℕ) (h : v ∈ andStep k A B) :
    ∃ u ∈ A, ∃ u2 ∈ B, v = capAdd k u u2 := by
  unfold andStep at h
  rcases s2230_mem_foldl_insertNew _ _ _ h with h1 | h1
  · simp at h1
  · simp only [List.mem_flatMap, List.mem_map] at h1
    obtain ⟨u, hu, u2, hu2, rfl⟩ := h1
    exact ⟨u, hu, u2, hu2, rfl⟩

lemma s2230_capAdd_pair (k x1 y1 x2 y2 : ℕ) :
    capAdd k [x1, y1] [x2, y2] = [min (x1 + x2) (k + 1), min (y1 + y2) (k + 1)] := by
  first
    | rfl
    | simp [capAdd]

lemma s2230_leaf_eq (a b w : ℕ) :
    leafVectors [a, b] 1 w =
      if w ∈ [a, b] then [[if a = w then 1 else 0, if b = w then 1 else 0]] else [] := by
  first
    | rfl
    | (unfold leafVectors; simp)

theorem s2230_inv (n : ℕ) (C : Circuit) (a b : Fin n) (hC : IsAO2 n C) (hab : a.val < b.val) :
    ∀ w : ℕ, ∀ v ∈ s2230_RV C n [a.val, b.val] 1 w, ∃ x y : ℕ, v = [x, y] ∧ 1 ≤ x + y ∧
      (x = 1 → y = 0 →
        a ∈ orIn n C w ∧ s2230_W n C (fun k1 : Fin n => decide (k1 = a)) w = true) ∧
      (x = 0 → y = 1 →
        b ∈ orIn n C w ∧ s2230_W n C (fun k1 : Fin n => decide (k1 = b)) w = true) ∧
      (x = 1 → y = 1 → ∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧
        OrReaches n C w j ∧
        ((a ∈ side (n := n) C j 0 ∧ b ∈ side (n := n) C j 1) ∨
          (b ∈ side (n := n) C j 0 ∧ a ∈ side (n := n) C j 1))) := by
  obtain ⟨hAnd, hBack, hTwo⟩ := hC
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro v hv
    by_cases hwn : w < n
    · rw [s2230_RV_input C n _ 1 w hwn, s2230_leaf_eq] at hv
      by_cases hwa : a.val = w
      · have hwb : ¬ b.val = w := by omega
        rw [if_pos (List.mem_cons.2 (Or.inl hwa.symm)), if_pos hwa, if_neg hwb] at hv
        have hv2 : v = [1, 0] := List.mem_singleton.1 hv
        refine ⟨1, 0, hv2, by omega, ?_, ?_, ?_⟩
        · intro _ _
          refine ⟨?_, ?_⟩
          · rw [s2230_mem_orIn]
            exact Or.inl hwa
          · rw [s2230_W_input n C _ w hwn]
            exact decide_eq_true (Fin.ext hwa.symm)
        · intro h3 h4
          omega
        · intro h3 h4
          omega
      · by_cases hwb : b.val = w
        · rw [if_pos (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inl hwb.symm)))),
            if_neg hwa, if_pos hwb] at hv
          have hv2 : v = [0, 1] := List.mem_singleton.1 hv
          refine ⟨0, 1, hv2, by omega, ?_, ?_, ?_⟩
          · intro h3 h4
            omega
          · intro _ _
            refine ⟨?_, ?_⟩
            · rw [s2230_mem_orIn]
              exact Or.inl hwb
            · rw [s2230_W_input n C _ w hwn]
              exact decide_eq_true (Fin.ext hwb.symm)
          · intro h3 h4
            omega
        · exfalso
          have hm : ¬ w ∈ [a.val, b.val] := by
            intro hm
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
            omega
          rw [if_neg hm] at hv
          simp at hv
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      by_cases hj : j < C.gates.length
      · have hmem : gateAt C j ∈ C.gates := by
          rw [s2230_gateAt_eq C j hj]
          exact List.getElem_mem hj
        have hlen2 := hTwo _ hmem
        have hback := hBack j hj
        obtain ⟨Rp, hRp, hRV⟩ := s2230_RV_gate C n [a.val, b.val] 1 j hj
        rcases hinp : (gateAt C j).inputs with _ | ⟨i1, _ | ⟨i2, _ | ⟨i3, rest⟩⟩⟩
        · exfalso
          rw [hinp] at hlen2
          simp at hlen2
        · exfalso
          rw [hinp] at hlen2
          simp at hlen2
        · have hm1 : i1 ∈ (gateAt C j).inputs := by rw [hinp]; simp
          have hm2 : i2 ∈ (gateAt C j).inputs := by rw [hinp]; simp
          have hi1 : i1 < n + j := hback i1 hm1
          have hi2 : i2 < n + j := hback i2 hm2
          rcases hAnd _ hmem with hop | hop
          · rw [hRV, s2230_FR_and _ _ _ _ hop, hinp] at hv
            simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil,
              hRp i1 hi1, hRp i2 hi2] at hv
            obtain ⟨t, ht, u2, hu2, rfl⟩ := s2230_mem_andStep _ _ _ _ hv
            obtain ⟨z, hz, u1, hu1, rfl⟩ := s2230_mem_andStep _ _ _ _ ht
            have hz2 : z = [0, 0] := by simpa using hz
            subst hz2
            obtain ⟨x1, y1, rfl, h1, ha1, hb1, _⟩ := ih i1 hi1 u1 hu1
            obtain ⟨x2, y2, rfl, h2, ha2, hb2, _⟩ := ih i2 hi2 u2 hu2
            refine ⟨min (min (0 + x1) (1 + 1) + x2) (1 + 1),
              min (min (0 + y1) (1 + 1) + y2) (1 + 1), ?_, by omega, ?_, ?_, ?_⟩
            · rw [s2230_capAdd_pair, s2230_capAdd_pair]
            · intro hx hy
              omega
            · intro hx hy
              omega
            · intro hx hy
              have hcase : (x1 = 1 ∧ y1 = 0 ∧ x2 = 0 ∧ y2 = 1) ∨
                  (x1 = 0 ∧ y1 = 1 ∧ x2 = 1 ∧ y2 = 0) := by omega
              refine ⟨j, hj, hop, s2230_orReaches_self n C j hj, ?_⟩
              have hs0 : side (n := n) C j 0 = orIn n C i1 := by
                first
                  | (unfold side opnd; rw [hinp]; rfl)
                  | simp [side, opnd, hinp]
              have hs1 : side (n := n) C j 1 = orIn n C i2 := by
                first
                  | (unfold side opnd; rw [hinp]; rfl)
                  | simp [side, opnd, hinp]
              rw [hs0, hs1]
              rcases hcase with ⟨e1, e2, e3, e4⟩ | ⟨e1, e2, e3, e4⟩
              · exact Or.inl ⟨(ha1 e1 e2).1, (hb2 e3 e4).1⟩
              · exact Or.inr ⟨(hb1 e1 e2).1, (ha2 e3 e4).1⟩
          · rw [hRV, s2230_FR_or _ _ _ _ hop, hinp] at hv
            simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil,
              hRp i1 hi1, hRp i2 hi2] at hv
            have hsrc : ∃ i, i ∈ (gateAt C j).inputs ∧ i < n + j ∧
                v ∈ s2230_RV C n [a.val, b.val] 1 i := by
              rcases s2230_mem_foldl_insertNew _ _ _ hv with h | h
              · rcases s2230_mem_foldl_insertNew _ _ _ h with h3 | h3
                · simp at h3
                · exact ⟨i1, hm1, hi1, h3⟩
              · exact ⟨i2, hm2, hi2, h⟩
            obtain ⟨i, him, hilt, hvi⟩ := hsrc
            obtain ⟨x, y, hxy, h1, ha1, hb1, hab1⟩ := ih i hilt v hvi
            have hW : ∀ z : Fin n → Bool, s2230_W n C z i = true → s2230_W n C z (n + j) = true := by
              intro z hz
              rw [s2230_W_gate n C z j hj, hop]
              simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id]
              exact ⟨i, him, by simp only [hilt, ite_true]; exact hz⟩
            refine ⟨x, y, hxy, h1, ?_, ?_, ?_⟩
            · intro hx hy
              exact ⟨s2230_orIn_up n C j i a hj hop him hilt (ha1 hx hy).1, hW _ (ha1 hx hy).2⟩
            · intro hx hy
              exact ⟨s2230_orIn_up n C j i b hj hop him hilt (hb1 hx hy).1, hW _ (hb1 hx hy).2⟩
            · intro hx hy
              obtain ⟨j2, hj2, hop2, hr2, hsd⟩ := hab1 hx hy
              exact ⟨j2, hj2, hop2, s2230_orReaches_step n C j i j2 hj hop him hilt hr2, hsd⟩
        · exfalso
          rw [hinp] at hlen2
          simp at hlen2 <;> omega
      · exfalso
        have hnil : s2230_RV C n [a.val, b.val] 1 (n + j) = [] := by
          simp only [s2230_RV]
          rw [s2230_readVectors_eq]
          exact List.getD_eq_default _ _ (by
            rw [s2230_foldR_length]
            simp only [List.length_map, List.length_range]
            omega)
        rw [hnil] at hv
        simp at hv

theorem s2230 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (a b : Fin n), PEqualNP.TopForm.IsAO2 n C → (∀ a1 : Fin n, PEqualNP.MetaComplexity.circuitFun n C (fun k1 => decide (k1 = a1)) = false) → a < b → PEqualNP.ReadK.readsAtMost C n [a.val, b.val] 1 = true → ∃ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output j ∧ ((a ∈ PEqualNP.TopForm.side (n := n) C j 0 ∧ b ∈ PEqualNP.TopForm.side (n := n) C j 1) ∨ (b ∈ PEqualNP.TopForm.side (n := n) C j 0 ∧ a ∈ PEqualNP.TopForm.side (n := n) C j 1)) := by
  intro n C a b hC hsingle hab hread
  have hlt : a.val < b.val := hab
  unfold readsAtMost at hread
  rw [List.any_eq_true] at hread
  obtain ⟨v, hv, hall⟩ := hread
  obtain ⟨x, y, rfl, h1, ha, hb, hab2⟩ := s2230_inv n C a b hC hlt C.output v hv
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    decide_eq_true_eq] at hall
  obtain ⟨hx, hy⟩ := hall
  have hcases : (x = 1 ∧ y = 0) ∨ (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 1) := by omega
  rcases hcases with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩
  · exfalso
    have h3 : circuitFun n C (fun k1 : Fin n => decide (k1 = a)) = true := (ha e1 e2).2
    rw [hsingle a] at h3
    exact Bool.false_ne_true h3
  · exfalso
    have h3 : circuitFun n C (fun k1 : Fin n => decide (k1 = b)) = true := (hb e1 e2).2
    rw [hsingle b] at h3
    exact Bool.false_ne_true h3
  · exact hab2 e1 e2

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def s2231_stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma s2231_wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl s2231_stepWire x := rfl

lemma s2231_foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl s2231_stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [s2231_stepWire]
    omega

lemma s2231_foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl s2231_stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (s2231_stepWire w g).length := by simp [s2231_stepWire]; omega
    rw [ih (s2231_stepWire w g) hlt]
    simp [s2231_stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma s2231_getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma s2231_wires_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [s2231_wires_eq_foldl, s2231_foldl_stepWire_length, List.length_ofFn]

lemma s2231_split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

def s2231_W (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD u false

lemma s2231_gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma s2231_W_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length) :
    s2231_W n C x (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
      if i < n + k then s2231_W n C x i else false) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := s2231_split_gates C.gates k hk
  have hga : gateAt C k = gj := by rw [s2231_gateAt_eq C k hk]; exact hgj
  rw [hga]
  let w0 := pre.foldl s2231_stepWire (List.ofFn x)
  have hw0_len : w0.length = n + k := by
    simp [w0, s2231_foldl_stepWire_length, hpre_len]
  have hCj : s2231_W n C x (n + k) = gj.op.eval (gj.inputs.map fun i => w0.getD i false) := by
    simp only [s2231_W]
    rw [s2231_wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
    rw [s2231_foldl_stepWire_getD_lt post (s2231_stepWire w0 gj) (n + k) (by simp [s2231_stepWire]; omega)]
    simp [s2231_stepWire, List.getD_eq_getElem?_getD, hw0_len]
  rw [hCj]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  by_cases hi : i < n + k
  · simp only [hi, ↓reduceIte]
    simp only [s2231_W]
    rw [s2231_wires_eq_foldl, hgs, List.foldl_append]
    exact (s2231_foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)).symm
  · simp only [hi, ↓reduceIte]
    exact s2231_getD_ge_length w0 i (by omega)

lemma s2231_W_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    s2231_W n C x u = x ⟨u, hu⟩ := by
  simp only [s2231_W]
  rw [s2231_wires_eq_foldl, s2231_foldl_stepWire_getD_lt C.gates (List.ofFn x) u (by simpa using hu)]
  simp [List.getD_eq_getElem?_getD, hu]

open PEqualNP.CleanedNonEdge in
lemma s2231_orFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

open PEqualNP.CleanedNonEdge in
lemma s2231_orStep_mem_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) (x : ℕ) :
    x ∈ (orStep n cs g).getD cs.length [] ↔ x = cs.length ∨ (g.op = GateOp.or ∧
      ∃ w ∈ g.inputs, n ≤ w ∧ w < n + cs.length ∧ x ∈ cs.getD (w - n) []) := by
  by_cases h : g.op = GateOp.or
  · simp only [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl, h,
      ↓reduceIte, true_and, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some,
      List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro (h1 | ⟨w, ⟨hw, hn, hlt⟩, hx⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨w, hw, hn, hlt, hx⟩
    · rintro (h1 | ⟨w, hw, hn, hlt, hx⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨w, ⟨hw, hn, hlt⟩, hx⟩
  · simp [orStep, List.getD_eq_getElem?_getD, h]

open PEqualNP.CleanedNonEdge in
lemma s2231_orStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (orStep n cs g).getD m [] = cs.getD m [] := by
  simp [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

open PEqualNP.CleanedNonEdge in
lemma s2231_orFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (orStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (orStep n cs g) (by simp [orStep]; omega)]
    exact s2231_orStep_getD_lt n cs g k hk

open PEqualNP.CleanedNonEdge in
lemma s2231_orSets_mem_iff (n : ℕ) (C : Circuit) (k x : ℕ) (hk : k < C.gates.length) :
    x ∈ (orSets n C).getD k [] ↔ x = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧ x ∈ (orSets n C).getD (w - n) []) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := s2231_split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [s2231_gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : orSets n C = post.foldl (orStep n) (orStep n (pre.foldl (orStep n) []) gk) := by
    simp only [orSets]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (orStep n) []).length = k := by
    rw [s2231_orFold_length]; simp [hpre_len]
  have hl1 : (orStep n (pre.foldl (orStep n) []) gk).length = k + 1 := by
    simp [orStep, hl0]
  have h1 : (orSets n C).getD k [] = (orStep n (pre.foldl (orStep n) []) gk).getD k [] := by
    rw [hc, s2231_orFold_getD_lt n post _ k (by omega)]
  have h2 : ∀ m, m < k → (orSets n C).getD m [] = (pre.foldl (orStep n) []).getD m [] := by
    intro m hm
    rw [hc, s2231_orFold_getD_lt n post _ m (by omega)]
    exact s2231_orStep_getD_lt n _ gk m (by omega)
  have h3 := s2231_orStep_mem_last n (pre.foldl (orStep n) []) gk x
  rw [hl0] at h3
  rw [h1, h3]
  constructor
  · rintro (h | ⟨hop, w, hw, hn, hlt, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [h2 (w - n) (by omega)]; exact hx⟩
  · rintro (h | ⟨hop, w, hw, hn, hlt, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [← h2 (w - n) (by omega)]; exact hx⟩

lemma s2231_W_or (n : ℕ) (C : Circuit) (x : Fin n → Bool) (r : ℕ) (hr : r < C.gates.length)
    (hop : (gateAt C r).op = GateOp.or) (i : ℕ) (hi : i ∈ (gateAt C r).inputs)
    (hlt : i < n + r) (hv : s2231_W n C x i = true) : s2231_W n C x (n + r) = true := by
  rw [s2231_W_gate n C x r hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  exact ⟨i, hi, by rw [if_pos hlt]; exact hv⟩

lemma s2231_W_and (n : ℕ) (C : Circuit) (x : Fin n → Bool) (r : ℕ) (hr : r < C.gates.length)
    (hop : (gateAt C r).op = GateOp.and)
    (h : ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ s2231_W n C x i = true) :
    s2231_W n C x (n + r) = true := by
  rw [s2231_W_gate n C x r hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  intro i hi
  rw [if_pos (h i hi).1]; exact (h i hi).2

open PEqualNP.CleanedNonEdge in
lemma s2231_reach_val (n : ℕ) (C : Circuit) (x : Fin n → Bool) (g : ℕ)
    (hv : s2231_W n C x (n + g) = true) :
    ∀ k, k < C.gates.length → g ∈ (orSets n C).getD k [] → s2231_W n C x (n + k) = true := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk hmem
    rcases (s2231_orSets_mem_iff n C k g hk).mp hmem with h | ⟨hop, w, hw, hn, hlt, hx⟩
    · rw [← h]; exact hv
    · have h3 := ih (w - n) (by omega) (by omega) hx
      have e : n + (w - n) = w := by omega
      rw [e] at h3
      exact s2231_W_or n C x k hk hop w hw hlt h3

open PEqualNP.CleanedNonEdge in
lemma s2231_reach_up (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w g : ℕ)
    (h : OrReaches n C w g) (hv : s2231_W n C x (n + g) = true) : s2231_W n C x w = true := by
  obtain ⟨hn, hmem⟩ := h
  by_cases hk : w - n < C.gates.length
  · have h3 := s2231_reach_val n C x g hv (w - n) hk hmem
    have e : n + (w - n) = w := by omega
    rw [e] at h3
    exact h3
  · exfalso
    have hlen : (orSets n C).length = C.gates.length := by
      unfold orSets; rw [s2231_orFold_length]; simp
    have hge : (orSets n C).length ≤ w - n := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge] at hmem
    simp at hmem

lemma s2231_mem_filter_gen {α : Type} (p : α → Prop) (d : DecidablePred p) (s : Finset α) (a : α)
    (h : a ∈ @Finset.filter α p d s) : p a :=
  ((@Finset.mem_filter α p d s a).mp h).2

lemma s2231_side_val (n : ℕ) (C : Circuit) (x : Fin n → Bool) (j : ℕ) (b : Fin 2) (i : Fin n)
    (hi : i ∈ PEqualNP.TopForm.side (n := n) C j b) (hx : x i = true) :
    s2231_W n C x (PEqualNP.TopForm.opnd C j b) = true := by
  unfold PEqualNP.TopForm.side PEqualNP.TopForm.orIn at hi
  have hi2 := s2231_mem_filter_gen _ _ _ _ hi
  rcases hi2 with h | ⟨k, hk, hreach, hop, hin⟩
  · rw [← h, s2231_W_input n C x i.val i.isLt]; exact hx
  · have hk1 : s2231_W n C x (n + k) = true := by
      apply s2231_W_or n C x k hk hop i.val hin (by have := i.isLt; omega)
      rw [s2231_W_input n C x i.val i.isLt]; exact hx
    exact s2231_reach_up n C x _ k hreach hk1

def s2231_px {n : ℕ} (u v : Fin n) : Fin n → Bool := fun k => decide (k = u ∨ k = v)

lemma s2231_px_self {n : ℕ} (t : Fin n) : s2231_px t t = (fun k : Fin n => decide (k = t)) := by
  funext k; simp [s2231_px]

lemma s2231_part1 (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hNF : PEqualNP.TopForm.NoFourCycle G) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (h1 : ∀ a1 : Fin n, circuitFun n C (fun k1 => decide (k1 = a1)) = false)
    (h2 : ∀ a2 b2 : Fin n, a2 ≠ b2 → ¬ G.Adj a2 b2 →
      circuitFun n C (fun k2 => decide (k2 = a2 ∨ k2 = b2)) = false)
    (j : ℕ) (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and)
    (hr : PEqualNP.CleanedNonEdge.OrReaches n C C.output j) :
    (∀ w : Fin n, w ∈ PEqualNP.TopForm.side (n := n) C j 0 →
        w ∉ PEqualNP.TopForm.side (n := n) C j 1) ∧
      (∀ u : Fin n, u ∈ PEqualNP.TopForm.side (n := n) C j 0 →
        ∀ v : Fin n, v ∈ PEqualNP.TopForm.side (n := n) C j 1 → G.Adj u v) ∧
      ((PEqualNP.TopForm.side (n := n) C j 0).card ≤ 1 ∨
        (PEqualNP.TopForm.side (n := n) C j 1).card ≤ 1) := by
  obtain ⟨_, hRB, hlen2⟩ := hAO
  have hgm : gateAt C j ∈ C.gates := by rw [s2231_gateAt_eq C j hj]; exact List.getElem_mem hj
  have hl2 : (gateAt C j).inputs.length = 2 := hlen2 _ hgm
  have hrb : ∀ i ∈ (gateAt C j).inputs, i < n + j := hRB j hj
  obtain ⟨a0, b0, hl⟩ := List.length_eq_two.mp hl2
  have e0 : PEqualNP.TopForm.opnd C j 0 = a0 := by
    unfold PEqualNP.TopForm.opnd; rw [hl]; rfl
  have e1 : PEqualNP.TopForm.opnd C j 1 = b0 := by
    unfold PEqualNP.TopForm.opnd; rw [hl]; rfl
  have hcross : ∀ u : Fin n, u ∈ PEqualNP.TopForm.side (n := n) C j 0 →
      ∀ v : Fin n, v ∈ PEqualNP.TopForm.side (n := n) C j 1 → u ≠ v ∧ G.Adj u v := by
    intro u hu v hv
    have hxu : s2231_px u v u = true := by simp [s2231_px]
    have hxv : s2231_px u v v = true := by simp [s2231_px]
    have va := s2231_side_val n C (s2231_px u v) j 0 u hu hxu
    have vb := s2231_side_val n C (s2231_px u v) j 1 v hv hxv
    rw [e0] at va
    rw [e1] at vb
    have hg : s2231_W n C (s2231_px u v) (n + j) = true := by
      apply s2231_W_and n C (s2231_px u v) j hj hop
      intro i hi
      have hi2 := hi
      rw [hl] at hi2
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi2
      rcases hi2 with h | h
      · exact ⟨hrb i hi, by rw [h]; exact va⟩
      · exact ⟨hrb i hi, by rw [h]; exact vb⟩
    have hW : circuitFun n C (s2231_px u v) = true := s2231_reach_up n C (s2231_px u v) C.output j hr hg
    have hne : u ≠ v := by
      intro e
      subst e
      rw [s2231_px_self] at hW
      have hf : true = false := hW.symm.trans (h1 _)
      cases hf
    refine ⟨hne, ?_⟩
    by_contra hna
    have hf : true = false := hW.symm.trans (h2 u v hne hna)
    cases hf
  refine ⟨?_, fun u hu v hv => (hcross u hu v hv).2, ?_⟩
  · intro w hw0 hw1
    exact (hcross w hw0 w hw1).1 rfl
  · by_contra hcon
    push_neg at hcon
    obtain ⟨c0, c1⟩ := hcon
    obtain ⟨u, hu, u2, hu2, hne⟩ := Finset.one_lt_card.mp c0
    obtain ⟨v, hv, v2, hv2, hnv⟩ := Finset.one_lt_card.mp c1
    have hc := hNF u u2 hne
    rw [Finset.card_le_one] at hc
    exact hnv (hc v (Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hcross u hu v hv).2,
      (hcross u2 hu2 v hv).2⟩) v2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (hcross u hu v2 hv2).2, (hcross u2 hu2 v2 hv2).2⟩))

def s2231_cen (n : ℕ) (C : Circuit) (i : ℕ) : Finset (Fin n) :=
  if (PEqualNP.TopForm.side (n := n) C i 0).card ≤ 1 then PEqualNP.TopForm.side (n := n) C i 0
  else if (PEqualNP.TopForm.side (n := n) C i 1).card ≤ 1 then
    PEqualNP.TopForm.side (n := n) C i 1
  else ∅

lemma s2231_cen_card (n : ℕ) (C : Circuit) (i : ℕ) : (s2231_cen n C i).card ≤ 1 := by
  unfold s2231_cen
  split_ifs with h0 h1
  · exact h0
  · exact h1
  · simp

theorem s2231 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → (∀ a1 : Fin n, PEqualNP.MetaComplexity.circuitFun n C (fun k1 => decide (k1 = a1)) = false) → (∀ a2 b2 : Fin n, a2 ≠ b2 → ¬ G.Adj a2 b2 → PEqualNP.MetaComplexity.circuitFun n C (fun k2 => decide (k2 = a2 ∨ k2 = b2)) = false) → (∀ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.CleanedNonEdge.OrReaches n C C.output j → (∀ w : Fin n, w ∈ PEqualNP.TopForm.side (n := n) C j 0 → w ∉ PEqualNP.TopForm.side (n := n) C j 1) ∧ (∀ u : Fin n, u ∈ PEqualNP.TopForm.side (n := n) C j 0 → ∀ v : Fin n, v ∈ PEqualNP.TopForm.side (n := n) C j 1 → G.Adj u v) ∧ ((PEqualNP.TopForm.side (n := n) C j 0).card ≤ 1 ∨ (PEqualNP.TopForm.side (n := n) C j 1).card ≤ 1)) ∧ (∀ F : Finset ℕ, (∀ e ∈ (Finset.univ.filter (fun e1 : Fin n × Fin n => e1.1 < e1.2 ∧ G.Adj e1.1 e1.2 ∧ PEqualNP.ReadK.readsAtMost C n [e1.1.val, e1.2.val] 1 = true)), ∃ i ∈ F, i < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output i ∧ ((e.1 ∈ PEqualNP.TopForm.side (n := n) C i 0 ∧ e.2 ∈ PEqualNP.TopForm.side (n := n) C i 1) ∨ (e.2 ∈ PEqualNP.TopForm.side (n := n) C i 0 ∧ e.1 ∈ PEqualNP.TopForm.side (n := n) C i 1))) → ∃ T : Finset (Fin n), T.card ≤ F.card ∧ ∀ e3 ∈ (Finset.univ.filter (fun e2 : Fin n × Fin n => e2.1 < e2.2 ∧ G.Adj e2.1 e2.2 ∧ PEqualNP.ReadK.readsAtMost C n [e2.1.val, e2.2.val] 1 = true)), e3.1 ∈ T ∨ e3.2 ∈ T) := by
  intro n G _ C hNF hAO h1 h2
  have P1 := s2231_part1 n G C hNF hAO h1 h2
  refine ⟨P1, ?_⟩
  intro F hF
  refine ⟨F.biUnion (s2231_cen n C), ?_, ?_⟩
  · have hc1 : (F.biUnion (s2231_cen n C)).card ≤ F.sum (fun i => (s2231_cen n C i).card) :=
      Finset.card_biUnion_le
    have hc2 : F.sum (fun i => (s2231_cen n C i).card) ≤ F.sum (fun _ : ℕ => (1 : ℕ)) :=
      Finset.sum_le_sum (fun i _ => s2231_cen_card n C i)
    have hc3 : F.sum (fun _ : ℕ => (1 : ℕ)) = F.card := by simp
    exact le_trans hc1 (le_trans hc2 (le_of_eq hc3))
  · intro e he
    obtain ⟨i, hiF, hi, hop, hreach, hside⟩ := hF e he
    obtain ⟨_, _, hcard⟩ := P1 i hi hop hreach
    by_cases c0 : (PEqualNP.TopForm.side (n := n) C i 0).card ≤ 1
    · have hc : s2231_cen n C i = PEqualNP.TopForm.side (n := n) C i 0 := by
        unfold s2231_cen; rw [if_pos c0]
      rcases hside with ⟨h, _⟩ | ⟨h, _⟩
      · left; exact Finset.mem_biUnion.mpr ⟨i, hiF, by rw [hc]; exact h⟩
      · right; exact Finset.mem_biUnion.mpr ⟨i, hiF, by rw [hc]; exact h⟩
    · have c1 : (PEqualNP.TopForm.side (n := n) C i 1).card ≤ 1 := hcard.resolve_left c0
      have hc : s2231_cen n C i = PEqualNP.TopForm.side (n := n) C i 1 := by
        unfold s2231_cen; rw [if_neg c0, if_pos c1]
      rcases hside with ⟨_, h⟩ | ⟨_, h⟩
      · right; exact Finset.mem_biUnion.mpr ⟨i, hiF, by rw [hc]; exact h⟩
      · left; exact Finset.mem_biUnion.mpr ⟨i, hiF, by rw [hc]; exact h⟩

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

lemma s2233_gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma s2233_gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [s2233_gateAt_eq hj]; exact List.getElem_mem hj

open PEqualNP.CleanedNonEdge

lemma s2233_orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

lemma s2233_orSets_char (n : ℕ) (gs : List Gate) :
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
      rw [s2233_orSets_len]; simp
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

lemma s2233_orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    OrReaches n C (n + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g)) := by
  have h := s2233_orSets_char n C.gates g k
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

lemma s2233_tail_step (n : ℕ) (C : Circuit) (g : ℕ) :
    ∀ w, OrReaches n C w g → g ≠ w - n →
      ∃ k, k < C.gates.length ∧ OrReaches n C w k ∧ (gateAt C k).op = GateOp.or ∧
        n + g ∈ (gateAt C k).inputs := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h hne
    have hnw : n ≤ w := h.1
    obtain ⟨k0, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    obtain ⟨hk, h3⟩ := (s2233_orReaches_iff n C k0 g).mp h
    rcases h3 with h3 | ⟨hop, i, hi, hlt, hr⟩
    · exact (hne (by omega)).elim
    · have hself : OrReaches n C (n + k0) k0 :=
        (s2233_orReaches_iff n C k0 k0).mpr ⟨hk, Or.inl rfl⟩
      by_cases hg : g = i - n
      · refine ⟨k0, hk, hself, hop, ?_⟩
        have hni : n ≤ i := hr.1
        have e : n + g = i := by omega
        rw [e]
        exact hi
      · obtain ⟨k, hkl, hrk, hopk, hin⟩ := ih i hlt hr hg
        exact ⟨k, hkl,
          (s2233_orReaches_iff n C k0 k).mpr ⟨hk, Or.inr ⟨hop, i, hi, hlt, hrk⟩⟩, hopk, hin⟩

def s2233_par (n : ℕ) (C : Circuit) (O : Finset ℕ) : Finset ℕ :=
  O.biUnion (fun k => ((gateAt C k).inputs.toFinset).image (fun w => w - n))

lemma s2233_par_card (n : ℕ) (C : Circuit) (O : Finset ℕ)
    (h : ∀ k ∈ O, (gateAt C k).inputs.length = 2) : (s2233_par n C O).card ≤ O.card * 2 := by
  unfold s2233_par
  calc (O.biUnion (fun k => ((gateAt C k).inputs.toFinset).image (fun w => w - n))).card
      ≤ ∑ k ∈ O, (((gateAt C k).inputs.toFinset).image (fun w => w - n)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _k ∈ O, 2 := by
        apply Finset.sum_le_sum
        intro k hk
        exact Finset.card_image_le.trans
          ((List.toFinset_card_le _).trans (le_of_eq (h k hk)))
    _ = O.card * 2 := by rw [Finset.sum_const, smul_eq_mul]

theorem s2233 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (F : Finset ℕ), PEqualNP.TopForm.IsAO2 n C → (∀ j ∈ F, j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output j) → F.card ≤ Set.ncard {i : ℕ | i < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output i} + 1 := by
  intro n C F hC hF
  obtain ⟨_, _, hlen⟩ := hC
  obtain ⟨O, hO⟩ : ∃ O : Finset ℕ, ∀ i, i ∈ O ↔ (i < C.gates.length ∧
      (gateAt C i).op = GateOp.or ∧ OrReaches n C C.output i) :=
      by
    have hfin : {i : ℕ | i < C.gates.length ∧ (gateAt C i).op = GateOp.or ∧
        OrReaches n C C.output i}.Finite := by
      apply (Finset.finite_toSet (Finset.range C.gates.length)).subset
      intro i hi
      have hi2 : i < C.gates.length ∧ (gateAt C i).op = GateOp.or ∧
          OrReaches n C C.output i := Eq.mp Set.mem_setOf_eq hi
      exact Finset.mem_coe.mpr (Finset.mem_range.mpr hi2.1)
    refine ⟨hfin.toFinset, fun i => ?_⟩
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  have hset : {i : ℕ | i < C.gates.length ∧ (gateAt C i).op = GateOp.or ∧
      OrReaches n C C.output i} = (↑O : Set ℕ) := by
    ext i
    simp only [Set.mem_setOf_eq, Finset.mem_coe, hO]
  rw [hset, Set.ncard_coe_finset]
  have hdisj : Disjoint F O := by
    rw [Finset.disjoint_left]
    intro a ha hb
    have h1 := (hF a ha).2.1
    have h2 := ((hO a).mp hb).2.1
    rw [h1] at h2
    exact GateOp.noConfusion h2
  have hsub : F ∪ O ⊆ insert (C.output - n) (s2233_par n C O) := by
    intro g hg
    have hr : OrReaches n C C.output g := by
      rcases Finset.mem_union.mp hg with h | h
      · exact (hF g h).2.2
      · exact ((hO g).mp h).2.2
    by_cases hgo : g = C.output - n
    · exact Finset.mem_insert.mpr (Or.inl hgo)
    · obtain ⟨k, hk, hrk, hop, hin⟩ := s2233_tail_step n C g C.output hr hgo
      refine Finset.mem_insert.mpr (Or.inr ?_)
      unfold s2233_par
      exact Finset.mem_biUnion.mpr ⟨k, (hO k).mpr ⟨hk, hop, hrk⟩,
        Finset.mem_image.mpr ⟨n + g, List.mem_toFinset.mpr hin, by omega⟩⟩
  have hcard := s2233_par_card n C O (fun k hk => hlen _ (s2233_gateAt_mem ((hO k).mp hk).1))
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj] at h1
  have h2 := Finset.card_insert_le (C.output - n) (s2233_par n C O)
  omega

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.CleanedNonEdge

def s2234_stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma s2234_wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl s2234_stepWire x := rfl

lemma s2234_foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl s2234_stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [s2234_stepWire]
    omega

lemma s2234_foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl s2234_stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (s2234_stepWire w g).length := by simp [s2234_stepWire]; omega
    rw [ih (s2234_stepWire w g) hlt]
    simp [s2234_stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma s2234_getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma s2234_wires_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [s2234_wires_eq_foldl, s2234_foldl_stepWire_length, List.length_ofFn]

lemma s2234_split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

def s2234_W (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD u false

lemma s2234_gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma s2234_W_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length) :
    s2234_W n C x (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
      if i < n + k then s2234_W n C x i else false) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := s2234_split_gates C.gates k hk
  have hga : gateAt C k = gj := by rw [s2234_gateAt_eq C k hk]; exact hgj
  rw [hga]
  let w0 := pre.foldl s2234_stepWire (List.ofFn x)
  have hw0_len : w0.length = n + k := by
    simp [w0, s2234_foldl_stepWire_length, hpre_len]
  have hCj : s2234_W n C x (n + k) = gj.op.eval (gj.inputs.map fun i => w0.getD i false) := by
    simp only [s2234_W]
    rw [s2234_wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
    rw [s2234_foldl_stepWire_getD_lt post (s2234_stepWire w0 gj) (n + k) (by simp [s2234_stepWire]; omega)]
    simp [s2234_stepWire, List.getD_eq_getElem?_getD, hw0_len]
  rw [hCj]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  by_cases hi : i < n + k
  · simp only [hi, ↓reduceIte]
    simp only [s2234_W]
    rw [s2234_wires_eq_foldl, hgs, List.foldl_append]
    exact (s2234_foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)).symm
  · simp only [hi, ↓reduceIte]
    exact s2234_getD_ge_length w0 i (by omega)

lemma s2234_W_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    s2234_W n C x u = x ⟨u, hu⟩ := by
  simp only [s2234_W]
  rw [s2234_wires_eq_foldl, s2234_foldl_stepWire_getD_lt C.gates (List.ofFn x) u (by simpa using hu)]
  simp [List.getD_eq_getElem?_getD, hu]

lemma s2234_orFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

lemma s2234_orStep_mem_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) (x : ℕ) :
    x ∈ (orStep n cs g).getD cs.length [] ↔ x = cs.length ∨ (g.op = GateOp.or ∧
      ∃ w ∈ g.inputs, n ≤ w ∧ w < n + cs.length ∧ x ∈ cs.getD (w - n) []) := by
  by_cases h : g.op = GateOp.or
  · simp only [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl, h,
      ↓reduceIte, true_and, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some,
      List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro (h1 | ⟨w, ⟨hw, hn, hlt⟩, hx⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨w, hw, hn, hlt, hx⟩
    · rintro (h1 | ⟨w, hw, hn, hlt, hx⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨w, ⟨hw, hn, hlt⟩, hx⟩
  · simp [orStep, List.getD_eq_getElem?_getD, h]

lemma s2234_orStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (orStep n cs g).getD m [] = cs.getD m [] := by
  simp [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

lemma s2234_orFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (orStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (orStep n cs g) (by simp [orStep]; omega)]
    exact s2234_orStep_getD_lt n cs g k hk

lemma s2234_orSets_mem_iff (n : ℕ) (C : Circuit) (k x : ℕ) (hk : k < C.gates.length) :
    x ∈ (orSets n C).getD k [] ↔ x = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧ x ∈ (orSets n C).getD (w - n) []) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := s2234_split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [s2234_gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : orSets n C = post.foldl (orStep n) (orStep n (pre.foldl (orStep n) []) gk) := by
    simp only [orSets]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (orStep n) []).length = k := by
    rw [s2234_orFold_length]; simp [hpre_len]
  have hl1 : (orStep n (pre.foldl (orStep n) []) gk).length = k + 1 := by
    simp [orStep, hl0]
  have h1 : (orSets n C).getD k [] = (orStep n (pre.foldl (orStep n) []) gk).getD k [] := by
    rw [hc, s2234_orFold_getD_lt n post _ k (by omega)]
  have h2 : ∀ m, m < k → (orSets n C).getD m [] = (pre.foldl (orStep n) []).getD m [] := by
    intro m hm
    rw [hc, s2234_orFold_getD_lt n post _ m (by omega)]
    exact s2234_orStep_getD_lt n _ gk m (by omega)
  have h3 := s2234_orStep_mem_last n (pre.foldl (orStep n) []) gk x
  rw [hl0] at h3
  rw [h1, h3]
  constructor
  · rintro (h | ⟨hop, w, hw, hn, hlt, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [h2 (w - n) (by omega)]; exact hx⟩
  · rintro (h | ⟨hop, w, hw, hn, hlt, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [← h2 (w - n) (by omega)]; exact hx⟩

lemma s2234_qorSets_len (n : ℕ) (C : Circuit) : (orSets n C).length = C.gates.length := by
  simp only [orSets]
  rw [s2234_orFold_length]
  simp

lemma s2234_qreach_iff (n : ℕ) (C : Circuit) (k g : ℕ) (hk : k < C.gates.length) :
    OrReaches n C (n + k) g ↔ g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, w < n + k ∧ OrReaches n C w g) := by
  have e : n + k - n = k := by omega
  constructor
  · intro h
    have h2 := h.2
    rw [e] at h2
    rcases (s2234_orSets_mem_iff n C k g hk).1 h2 with h3 | ⟨hop, w, hw, hn, hlt, hx⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, hlt, hn, hx⟩
  · intro h
    refine ⟨by omega, ?_⟩
    rw [e]
    refine (s2234_orSets_mem_iff n C k g hk).2 ?_
    rcases h with h | ⟨hop, w, hw, hlt, hr⟩
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hr.1, hlt, hr.2⟩

lemma s2234_qreach_bound (n : ℕ) (C : Circuit) (w g : ℕ) (h : OrReaches n C w g) :
    n ≤ w ∧ w - n < C.gates.length := by
  refine ⟨h.1, ?_⟩
  by_contra hc
  have h2 := h.2
  have hlen : (orSets n C).length ≤ w - n := by rw [s2234_qorSets_len]; omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hlen] at h2
  simp at h2

lemma s2234_qreach_self (n : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    OrReaches n C (n + k) k := (s2234_qreach_iff n C k k hk).2 (Or.inl rfl)

lemma s2234_qreach_le (n : ℕ) (C : Circuit) (g : ℕ) : ∀ w : ℕ, OrReaches n C w g → n + g ≤ w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    obtain ⟨h1, h2⟩ := s2234_qreach_bound n C w g h
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    have hk : k < C.gates.length := by omega
    rcases (s2234_qreach_iff n C k g hk).1 h with h3 | ⟨_, w', _, hlt, hr⟩
    · omega
    · have := ih w' hlt hr
      omega

lemma s2234_qreach_trans (n : ℕ) (C : Circuit) (i g : ℕ) (hg : OrReaches n C (n + i) g) :
    ∀ w : ℕ, OrReaches n C w i → OrReaches n C w g := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    obtain ⟨h1, h2⟩ := s2234_qreach_bound n C w i h
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    have hk : k < C.gates.length := by omega
    rcases (s2234_qreach_iff n C k i hk).1 h with h3 | ⟨hop, w', hw', hlt, hr⟩
    · rw [← h3]; exact hg
    · exact (s2234_qreach_iff n C k g hk).2 (Or.inr ⟨hop, w', hw', hlt, ih w' hlt hr⟩)

lemma s2234_qmem_orIn (n : ℕ) (C : Circuit) (w : ℕ) (b : Fin n) :
    b ∈ PEqualNP.TopForm.orIn n C w ↔ ((b : ℕ) = w ∨ ∃ k, k < C.gates.length ∧
      OrReaches n C w k ∧ (gateAt C k).op = GateOp.or ∧ (b : ℕ) ∈ (gateAt C k).inputs) := by
  unfold PEqualNP.TopForm.orIn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

lemma s2234_qorIn_eq_self (n : ℕ) (C : Circuit) (w : ℕ)
    (hw : ¬ (n ≤ w ∧ w - n < C.gates.length ∧ (gateAt C (w - n)).op = GateOp.or)) :
    ∀ b ∈ PEqualNP.TopForm.orIn n C w, (b : ℕ) = w := by
  intro b hb
  rcases (s2234_qmem_orIn n C w b).1 hb with h | ⟨k', hk', hr, hop', hi⟩
  · exact h
  · exfalso
    obtain ⟨h1, h2⟩ := s2234_qreach_bound n C w k' hr
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    have e : n + k - n = k := by omega
    rw [e] at hw h2
    rcases (s2234_qreach_iff n C k k' h2).1 hr with h | ⟨hop, _⟩
    · rw [h] at hop'
      exact hw ⟨h1, h2, hop'⟩
    · exact hw ⟨h1, h2, hop⟩

lemma s2234_qorIn_small (n : ℕ) (C : Circuit) (w : ℕ)
    (hw : ¬ (n ≤ w ∧ w - n < C.gates.length ∧ (gateAt C (w - n)).op = GateOp.or)) :
    (PEqualNP.TopForm.orIn n C w).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  have h1 := s2234_qorIn_eq_self n C w hw a ha
  have h2 := s2234_qorIn_eq_self n C w hw b hb
  exact Fin.ext (by omega)

lemma s2234_qorIn_or (n : ℕ) (C : Circuit) (k a b : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (hin : (gateAt C k).inputs = [a, b])
    (ha : a < n + k) (hb : b < n + k) :
    PEqualNP.TopForm.orIn n C (n + k) =
      PEqualNP.TopForm.orIn n C a ∪ PEqualNP.TopForm.orIn n C b := by
  have hma : a ∈ (gateAt C k).inputs := by rw [hin]; simp
  have hmb : b ∈ (gateAt C k).inputs := by rw [hin]; simp
  ext i
  rw [Finset.mem_union, s2234_qmem_orIn, s2234_qmem_orIn, s2234_qmem_orIn]
  constructor
  · rintro (h | ⟨k', hk', hr, hop', hi⟩)
    · exfalso
      have := i.2
      omega
    · rcases (s2234_qreach_iff n C k k' hk).1 hr with h | ⟨_, w, hw, hwlt, hr'⟩
      · rw [h, hin, List.mem_cons, List.mem_singleton] at hi
        rcases hi with h4 | h4
        · exact Or.inl (Or.inl h4)
        · exact Or.inr (Or.inl h4)
      · rw [hin, List.mem_cons, List.mem_singleton] at hw
        rcases hw with h4 | h4
        · rw [h4] at hr'
          exact Or.inl (Or.inr ⟨k', hk', hr', hop', hi⟩)
        · rw [h4] at hr'
          exact Or.inr (Or.inr ⟨k', hk', hr', hop', hi⟩)
  · rintro ((h | ⟨k', hk', hr, hop', hi⟩) | (h | ⟨k', hk', hr, hop', hi⟩))
    · exact Or.inr ⟨k, hk, s2234_qreach_self n C k hk, hop, by rw [h]; exact hma⟩
    · exact Or.inr ⟨k', hk', (s2234_qreach_iff n C k k' hk).2 (Or.inr ⟨hop, a, hma, ha, hr⟩), hop', hi⟩
    · exact Or.inr ⟨k, hk, s2234_qreach_self n C k hk, hop, by rw [h]; exact hmb⟩
    · exact Or.inr ⟨k', hk', (s2234_qreach_iff n C k k' hk).2 (Or.inr ⟨hop, b, hmb, hb, hr⟩), hop', hi⟩

lemma s2234_qorIn_sub (n : ℕ) (C : Circuit) (i w : ℕ) (hr : OrReaches n C w i) :
    PEqualNP.TopForm.orIn n C (n + i) ⊆ PEqualNP.TopForm.orIn n C w := by
  intro b hb
  rcases (s2234_qmem_orIn n C (n + i) b).1 hb with h | ⟨k, hk, hr', hop, hi⟩
  · exfalso
    have := b.2
    omega
  · exact (s2234_qmem_orIn n C w b).2 (Or.inr ⟨k, hk, s2234_qreach_trans n C i k hr' w hr, hop, hi⟩)

lemma s2234_qval_reach (n : ℕ) (C : Circuit) (x : Fin n → Bool) (g : ℕ)
    (hv : s2234_W n C x (n + g) = true) :
    ∀ w : ℕ, OrReaches n C w g → s2234_W n C x w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    obtain ⟨h1, h2⟩ := s2234_qreach_bound n C w g h
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    have hk : k < C.gates.length := by omega
    rcases (s2234_qreach_iff n C k g hk).1 h with h3 | ⟨hop, w', hw', hlt, hr⟩
    · rw [← h3]; exact hv
    · rw [s2234_W_gate n C x k hk, hop]
      simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id]
      exact ⟨w', hw', by simp only [hlt, ite_true]; exact ih w' hlt hr⟩

lemma s2234_qval_orIn (n : ℕ) (C : Circuit) (w : ℕ) (b : Fin n)
    (hb : b ∈ PEqualNP.TopForm.orIn n C w) :
    s2234_W n C (fun r : Fin n => decide (r = b)) w = true := by
  rcases (s2234_qmem_orIn n C w b).1 hb with h | ⟨k, hk, hr, hop, hi⟩
  · rw [← h, s2234_W_input n C _ (b : ℕ) b.2]
    simp
  · refine s2234_qval_reach n C _ k ?_ w hr
    rw [s2234_W_gate n C _ k hk, hop]
    simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id]
    have hlt : (b : ℕ) < n + k := by
      have := b.2
      omega
    refine ⟨(b : ℕ), hi, ?_⟩
    simp only [hlt, ite_true]
    rw [s2234_W_input n C _ (b : ℕ) b.2]
    simp

lemma s2234_qpart1 (n : ℕ) (C : Circuit)
    (h0 : ∀ a1 : Fin n, circuitFun n C (fun k1 => decide (k1 = a1)) = false)
    (i : ℕ) (hcard : 2 ≤ (PEqualNP.TopForm.orIn n C (n + i)).card) :
    ¬ OrReaches n C C.output i := by
  intro hr
  have hpos : 0 < (PEqualNP.TopForm.orIn n C (n + i)).card := by omega
  obtain ⟨b, hb⟩ := Finset.card_pos.1 hpos
  have h1 := s2234_qval_orIn n C (n + i) b hb
  have h2 := s2234_qval_reach n C _ i h1 C.output hr
  have h3 : s2234_W n C (fun r : Fin n => decide (r = b)) C.output = false := h0 b
  rw [h2] at h3
  cases h3

noncomputable def s2234_srv (n : ℕ) (C : Circuit) (R : Finset ℕ) : Finset ℕ :=
  @Finset.filter ℕ (fun i => (gateAt C i).op = GateOp.or ∧
    2 ≤ (PEqualNP.TopForm.orIn n C (n + i)).card ∧ ∃ w ∈ R, OrReaches n C w i)
    (fun _ => Classical.propDecidable _) (Finset.range C.gates.length)

lemma s2234_qmem_srv (n : ℕ) (C : Circuit) (R : Finset ℕ) (i : ℕ) :
    i ∈ s2234_srv n C R ↔ (i < C.gates.length ∧ (gateAt C i).op = GateOp.or ∧
      2 ≤ (PEqualNP.TopForm.orIn n C (n + i)).card ∧ ∃ w ∈ R, OrReaches n C w i) := by
  unfold s2234_srv
  rw [@Finset.mem_filter _ _ (fun _ => Classical.propDecidable _), Finset.mem_range]

lemma s2234_qsrv_mono (n : ℕ) (C : Circuit) (R R' : Finset ℕ) (h : R ⊆ R') :
    s2234_srv n C R ⊆ s2234_srv n C R' := by
  intro i hi
  obtain ⟨h1, h2, h3, w, hw, hr⟩ := (s2234_qmem_srv n C R i).1 hi
  exact (s2234_qmem_srv n C R' i).2 ⟨h1, h2, h3, w, h hw, hr⟩

lemma s2234_qcount (n : ℕ) (C : Circuit) (hRB : ReadsBack n C)
    (hlen2 : ∀ g ∈ C.gates, g.inputs.length = 2) :
    ∀ (m : ℕ) (R : Finset ℕ), (∀ w ∈ R, w < m) →
      (R.biUnion (PEqualNP.TopForm.orIn n C)).card ≤ (s2234_srv n C R).card + R.card := by
  intro m
  induction m with
  | zero =>
    intro R hR
    have hRe : R = ∅ := Finset.eq_empty_of_forall_notMem (fun w hw => by
      have := hR w hw
      omega)
    subst hRe
    simp
  | succ m ih =>
    intro R hR
    by_cases hm : m ∈ R
    · have hR0 : ∀ w ∈ R.erase m, w < m := by
        intro w hw
        have h1 := Finset.ne_of_mem_erase hw
        have h2 := hR w (Finset.mem_of_mem_erase hw)
        omega
      have hins : insert m (R.erase m) = R := Finset.insert_erase hm
      have hcardR : (R.erase m).card + 1 = R.card := Finset.card_erase_add_one hm
      have hU : R.biUnion (PEqualNP.TopForm.orIn n C) =
          PEqualNP.TopForm.orIn n C m ∪ (R.erase m).biUnion (PEqualNP.TopForm.orIn n C) := by
        rw [← Finset.biUnion_insert (a := m) (s := R.erase m)
          (t := PEqualNP.TopForm.orIn n C), hins]
      by_cases hs : n ≤ m ∧ m - n < C.gates.length ∧ (gateAt C (m - n)).op = GateOp.or ∧
          2 ≤ (PEqualNP.TopForm.orIn n C m).card
      · obtain ⟨hs1, hs2, hs3, hs4⟩ := hs
        obtain ⟨k, rfl⟩ : ∃ k, m = n + k := ⟨m - n, by omega⟩
        have e : n + k - n = k := by omega
        rw [e] at hs2 hs3
        have hmem : gateAt C k ∈ C.gates := by
          rw [s2234_gateAt_eq C k hs2]
          exact List.getElem_mem hs2
        have hl := hlen2 _ hmem
        obtain ⟨a, b, hin⟩ : ∃ a b, (gateAt C k).inputs = [a, b] := List.length_eq_two.1 hl
        have hma : a ∈ (gateAt C k).inputs := by rw [hin]; simp
        have hmb : b ∈ (gateAt C k).inputs := by rw [hin]; simp
        have ha : a < n + k := hRB k hs2 a hma
        have hb : b < n + k := hRB k hs2 b hmb
        have hor := s2234_qorIn_or n C k a b hs2 hs3 hin ha hb
        have hR' : ∀ w ∈ insert a (insert b (R.erase (n + k))), w < n + k := by
          intro w hw
          rw [Finset.mem_insert, Finset.mem_insert] at hw
          rcases hw with h | h | h
          · omega
          · omega
          · exact hR0 w h
        have hih := ih _ hR'
        have hU' : (insert a (insert b (R.erase (n + k)))).biUnion (PEqualNP.TopForm.orIn n C) =
            R.biUnion (PEqualNP.TopForm.orIn n C) := by
          rw [hU, Finset.biUnion_insert, Finset.biUnion_insert, hor, Finset.union_assoc]
        have hc' : (insert a (insert b (R.erase (n + k)))).card ≤ (R.erase (n + k)).card + 2 := by
          have h1 := Finset.card_insert_le a (insert b (R.erase (n + k)))
          have h2 := Finset.card_insert_le b (R.erase (n + k))
          omega
        have hsub : s2234_srv n C (insert a (insert b (R.erase (n + k)))) ⊆ (s2234_srv n C R).erase k := by
          intro i hi
          obtain ⟨h1, h2, h3, w, hw, hr⟩ := (s2234_qmem_srv n C _ i).1 hi
          have hle := s2234_qreach_le n C i w hr
          have hwlt := hR' w hw
          rw [Finset.mem_erase]
          refine ⟨by omega, (s2234_qmem_srv n C R i).2 ⟨h1, h2, h3, ?_⟩⟩
          rw [Finset.mem_insert, Finset.mem_insert] at hw
          rcases hw with h | h | h
          · rw [h] at hr
            exact ⟨n + k, hm, (s2234_qreach_iff n C k i hs2).2 (Or.inr ⟨hs3, a, hma, ha, hr⟩)⟩
          · rw [h] at hr
            exact ⟨n + k, hm, (s2234_qreach_iff n C k i hs2).2 (Or.inr ⟨hs3, b, hmb, hb, hr⟩)⟩
          · exact ⟨w, Finset.mem_of_mem_erase h, hr⟩
        have hkmem : k ∈ s2234_srv n C R :=
          (s2234_qmem_srv n C R k).2 ⟨hs2, hs3, hs4, n + k, hm, s2234_qreach_self n C k hs2⟩
        have hc2 : ((s2234_srv n C R).erase k).card + 1 = (s2234_srv n C R).card :=
          Finset.card_erase_add_one hkmem
        have hc3 := Finset.card_le_card hsub
        rw [hU'] at hih
        omega
      · have hsmall : (PEqualNP.TopForm.orIn n C m).card ≤ 1 := by
          by_cases hs' : n ≤ m ∧ m - n < C.gates.length ∧ (gateAt C (m - n)).op = GateOp.or
          · by_contra hc
            exact hs ⟨hs'.1, hs'.2.1, hs'.2.2, by omega⟩
          · exact s2234_qorIn_small n C m hs'
        have hih := ih _ hR0
        have hmono := Finset.card_le_card (s2234_qsrv_mono n C _ _ (Finset.erase_subset m R))
        have hun := Finset.card_union_le (PEqualNP.TopForm.orIn n C m)
          ((R.erase m).biUnion (PEqualNP.TopForm.orIn n C))
        rw [hU]
        omega
    · refine ih R (fun w hw => ?_)
      have h1 := hR w hw
      have h2 : w ≠ m := fun h => hm (h ▸ hw)
      omega

lemma s2234_qfinal (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (F : Finset ℕ)
    (ctr : ℕ → Fin n) (lf : ℕ → ℕ)
    (hG : PEqualNP.TopForm.NoFourCycle G) (hRB : ReadsBack n C)
    (hlen2 : ∀ g ∈ C.gates, g.inputs.length = 2)
    (hadj : ∀ j ∈ F, ∀ b : Fin n, b ∈ PEqualNP.TopForm.orIn n C (lf j) → G.Adj (ctr j) b) :
    ∑ c : Fin n, (Finset.univ.filter (fun b2 : Fin n => ∃ j2 ∈ F, ctr j2 = c ∧ b2 ∈ PEqualNP.TopForm.orIn n C (lf j2))).card ≤ Set.ncard {i2 : ℕ | i2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i2).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ 2 ≤ (PEqualNP.TopForm.orIn n C (n + i2)).card ∧ ∃ j3 ∈ F, PEqualNP.CleanedNonEdge.OrReaches n C (lf j3) i2} + F.card := by
  have key : ∀ (S : Set ℕ) (A B : ℕ), (∀ i, i ∈ S ↔ i ∈ s2234_srv n C (F.image lf)) →
      A ≤ (s2234_srv n C (F.image lf)).card + B → A ≤ S.ncard + B := by
    intro S A B hS hA
    have hSe : S = ((s2234_srv n C (F.image lf) : Finset ℕ) : Set ℕ) := by
      ext i
      exact (hS i).trans Finset.mem_coe.symm
    rw [hSe, Set.ncard_coe_finset]
    exact hA
  refine key _ _ _ ?_ ?_
  · intro i
    rw [Set.mem_ofPred_eq, s2234_qmem_srv]
    constructor
    · rintro ⟨h1, h2, h3, j, hj, hr⟩
      exact ⟨h1, h2, h3, lf j, Finset.mem_image_of_mem lf hj, hr⟩
    · rintro ⟨h1, h2, h3, w, hw, hr⟩
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hw
      exact ⟨h1, h2, h3, j, hj, hr⟩
  · have hpt : ∀ c : Fin n, ∀ X : Finset (Fin n),
        (∀ b, b ∈ X ↔ ∃ j ∈ F, ctr j = c ∧ b ∈ PEqualNP.TopForm.orIn n C (lf j)) →
        X.card ≤ (s2234_srv n C ((F.filter (fun j => ctr j = c)).image lf)).card +
          (F.filter (fun j => ctr j = c)).card := by
      intro c X hX
      have hXe : X = ((F.filter (fun j => ctr j = c)).image lf).biUnion
          (PEqualNP.TopForm.orIn n C) := by
        ext b
        rw [hX b, Finset.mem_biUnion]
        constructor
        · rintro ⟨j, hj, hc, hb⟩
          exact ⟨lf j, Finset.mem_image_of_mem lf (Finset.mem_filter.2 ⟨hj, hc⟩), hb⟩
        · rintro ⟨w, hw, hb⟩
          obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hw
          obtain ⟨hj1, hj2⟩ := Finset.mem_filter.1 hj
          exact ⟨j, hj1, hj2, hb⟩
      have hc := s2234_qcount n C hRB hlen2
        (((F.filter (fun j => ctr j = c)).image lf).sup id + 1)
        ((F.filter (fun j => ctr j = c)).image lf)
        (fun w hw => Nat.lt_succ_of_le (Finset.le_sup (f := id) hw))
      have hi := Finset.card_image_le (s := F.filter (fun j => ctr j = c)) (f := lf)
      rw [hXe]
      omega
    have hdisj : ∀ c c' : Fin n, c ≠ c' → ∀ i,
        i ∈ s2234_srv n C ((F.filter (fun j => ctr j = c)).image lf) →
        i ∈ s2234_srv n C ((F.filter (fun j => ctr j = c')).image lf) → False := by
      intro c c' hne i h1 h2
      obtain ⟨hi, hop, hcard, w, hw, hr⟩ := (s2234_qmem_srv n C _ i).1 h1
      obtain ⟨_, _, _, w', hw', hr'⟩ := (s2234_qmem_srv n C _ i).1 h2
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hw
      obtain ⟨j', hj', rfl⟩ := Finset.mem_image.1 hw'
      obtain ⟨hjF, hjc⟩ := Finset.mem_filter.1 hj
      obtain ⟨hjF', hjc'⟩ := Finset.mem_filter.1 hj'
      refine absurd (le_trans hcard (le_trans (Finset.card_le_card ?_) (hG c c' hne))) (by omega)
      intro b hb
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · rw [← hjc]
        exact hadj j hjF b (s2234_qorIn_sub n C i (lf j) hr hb)
      · rw [← hjc']
        exact hadj j' hjF' b (s2234_qorIn_sub n C i (lf j') hr' hb)
    have hpd : ((Finset.univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint
        (fun c => s2234_srv n C ((F.filter (fun j => ctr j = c)).image lf)) := by
      intro c _ c' _ hne
      exact Finset.disjoint_left.2 (fun i h1 h2 => hdisj c c' hne i h1 h2)
    have hsum1 : ∑ c : Fin n, (s2234_srv n C ((F.filter (fun j => ctr j = c)).image lf)).card ≤
        (s2234_srv n C (F.image lf)).card := by
      rw [← Finset.card_biUnion hpd]
      apply Finset.card_le_card
      intro i hi
      obtain ⟨c, _, hc⟩ := Finset.mem_biUnion.1 hi
      exact s2234_qsrv_mono n C _ _ (Finset.image_subset_image (Finset.filter_subset _ _)) hc
    have hsum2 : ∑ c : Fin n, (F.filter (fun j => ctr j = c)).card = F.card :=
      (Finset.card_eq_sum_card_fiberwise (f := ctr) (s := F) (t := Finset.univ)
        (by intro x _; simp)).symm
    have hpt2 : ∀ c ∈ (Finset.univ : Finset (Fin n)), (Finset.univ.filter (fun b2 : Fin n => ∃ j2 ∈ F, ctr j2 = c ∧ b2 ∈ PEqualNP.TopForm.orIn n C (lf j2))).card ≤
        (s2234_srv n C ((F.filter (fun j => ctr j = c)).image lf)).card +
          (F.filter (fun j => ctr j = c)).card := fun c _ => hpt c _ (fun b => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and])
    refine le_trans (Finset.sum_le_sum hpt2) ?_
    rw [Finset.sum_add_distrib]
    exact add_le_add hsum1 (le_of_eq hsum2)

theorem s2234 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (F : Finset ℕ) (ctr : ℕ → Fin n) (lf : ℕ → ℕ), PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → (∀ a1 : Fin n, PEqualNP.MetaComplexity.circuitFun n C (fun k1 => decide (k1 = a1)) = false) → (∀ j ∈ F, ∀ b : Fin n, b ∈ PEqualNP.TopForm.orIn n C (lf j) → G.Adj (ctr j) b) → (∀ i < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or → 2 ≤ (PEqualNP.TopForm.orIn n C (n + i)).card → (∃ j1 ∈ F, PEqualNP.CleanedNonEdge.OrReaches n C (lf j1) i) → ¬ PEqualNP.CleanedNonEdge.OrReaches n C C.output i) ∧ ∑ c : Fin n, (Finset.univ.filter (fun b2 : Fin n => ∃ j2 ∈ F, ctr j2 = c ∧ b2 ∈ PEqualNP.TopForm.orIn n C (lf j2))).card ≤ Set.ncard {i2 : ℕ | i2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i2).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ 2 ≤ (PEqualNP.TopForm.orIn n C (n + i2)).card ∧ ∃ j3 ∈ F, PEqualNP.CleanedNonEdge.OrReaches n C (lf j3) i2} + F.card := by
  intro n G hdec C F ctr lf hG hAO h0 hadj
  refine ⟨?_, ?_⟩
  · intro i _ _ hcard _
    exact s2234_qpart1 n C h0 i hcard
  · exact s2234_qfinal n G C F ctr lf hG hAO.2.1 hAO.2.2 hadj

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge PEqualNP.TopForm

theorem three_count (L : ℕ) (F : Finset ℕ) (A B : Set ℕ)
    (hF : ∀ j ∈ F, j < L) (hA : ∀ i ∈ A, i < L) (hB : ∀ i ∈ B, i < L)
    (hFA : ∀ j ∈ F, j ∉ A) (hFB : ∀ j ∈ F, j ∉ B) (hAB : ∀ i ∈ A, i ∉ B) :
    F.card + A.ncard + B.ncard ≤ L := by
  classical
  have hAf : A.Finite := (Set.finite_lt_nat L).subset (fun i hi => hA i hi)
  have hBf : B.Finite := (Set.finite_lt_nat L).subset (fun i hi => hB i hi)
  rw [Set.ncard_eq_toFinset_card A hAf, Set.ncard_eq_toFinset_card B hBf]
  have h1 : Disjoint F hAf.toFinset := by
    rw [Finset.disjoint_left]
    intro j hj hj2
    exact hFA j hj ((Set.Finite.mem_toFinset hAf).mp hj2)
  have h2 : Disjoint (F ∪ hAf.toFinset) hBf.toFinset := by
    rw [Finset.disjoint_left]
    intro j hj hj2
    have hjB := (Set.Finite.mem_toFinset hBf).mp hj2
    rcases Finset.mem_union.mp hj with h | h
    · exact hFB j h hjB
    · exact hAB j ((Set.Finite.mem_toFinset hAf).mp h) hjB
  have h3 : (F ∪ hAf.toFinset) ∪ hBf.toFinset ⊆ Finset.range L := by
    intro j hj
    rw [Finset.mem_range]
    rcases Finset.mem_union.mp hj with h | h
    · rcases Finset.mem_union.mp h with h | h
      · exact hF j h
      · exact hA j ((Set.Finite.mem_toFinset hAf).mp h)
    · exact hB j ((Set.Finite.mem_toFinset hBf).mp h)
  have h4 := Finset.card_le_card h3
  rw [Finset.card_union_of_disjoint h2, Finset.card_union_of_disjoint h1, Finset.card_range] at h4
  exact h4

theorem sum_card_ge {n : ℕ} (E : Finset (Fin n × Fin n)) (U : Fin n → Finset (Fin n))
    (hlt : ∀ e ∈ E, e.1 < e.2) (h : ∀ e ∈ E, e.2 ∈ U e.1 ∨ e.1 ∈ U e.2) :
    E.card ≤ ∑ c : Fin n, (U c).card := by
  classical
  have hs := Finset.card_sigma (Finset.univ : Finset (Fin n)) U
  rw [← hs]
  have key1 : ∀ e ∈ E, (if e.2 ∈ U e.1 then (⟨e.1, e.2⟩ : Σ _ : Fin n, Fin n) else ⟨e.2, e.1⟩)
      ∈ (Finset.univ : Finset (Fin n)).sigma U := by
    intro e he
    by_cases hc : e.2 ∈ U e.1
    · rw [if_pos hc]
      exact Finset.mem_sigma.mpr ⟨Finset.mem_univ _, hc⟩
    · rw [if_neg hc]
      rcases h e he with h1 | h1
      · exact absurd h1 hc
      · exact Finset.mem_sigma.mpr ⟨Finset.mem_univ _, h1⟩
  have key2 : ∀ e e2 : Fin n × Fin n, e.1 < e.2 → e2.1 < e2.2 →
      (if e.2 ∈ U e.1 then (⟨e.1, e.2⟩ : Σ _ : Fin n, Fin n) else ⟨e.2, e.1⟩) =
      (if e2.2 ∈ U e2.1 then (⟨e2.1, e2.2⟩ : Σ _ : Fin n, Fin n) else ⟨e2.2, e2.1⟩) → e = e2 := by
    intro e e2 h1 h2 heq
    by_cases c1 : e.2 ∈ U e.1
    · by_cases c2 : e2.2 ∈ U e2.1
      · rw [if_pos c1, if_pos c2] at heq
        have ha : e.1 = e2.1 := congrArg Sigma.fst heq
        have hb : e.2 = e2.2 := congrArg (fun s : (Σ _ : Fin n, Fin n) => (s.2 : Fin n)) heq
        exact Prod.ext ha hb
      · rw [if_pos c1, if_neg c2] at heq
        have ha : e.1 = e2.2 := congrArg Sigma.fst heq
        have hb : e.2 = e2.1 := congrArg (fun s : (Σ _ : Fin n, Fin n) => (s.2 : Fin n)) heq
        rw [ha, hb] at h1
        exact absurd h1 (lt_asymm h2)
    · by_cases c2 : e2.2 ∈ U e2.1
      · rw [if_neg c1, if_pos c2] at heq
        have ha : e.2 = e2.1 := congrArg Sigma.fst heq
        have hb : e.1 = e2.2 := congrArg (fun s : (Σ _ : Fin n, Fin n) => (s.2 : Fin n)) heq
        rw [ha, hb] at h1
        exact absurd h1 (lt_asymm h2)
      · rw [if_neg c1, if_neg c2] at heq
        have ha : e.2 = e2.2 := congrArg Sigma.fst heq
        have hb : e.1 = e2.1 := congrArg (fun s : (Σ _ : Fin n, Fin n) => (s.2 : Fin n)) heq
        exact Prod.ext hb ha
  refine Finset.card_le_card_of_injOn
    (fun e => if e.2 ∈ U e.1 then (⟨e.1, e.2⟩ : Σ _ : Fin n, Fin n) else ⟨e.2, e.1⟩) ?_ ?_
  · intro e he
    exact key1 e he
  · intro e he e2 he2 heq
    exact key2 e e2 (hlt e he) (hlt e2 he2) heq

theorem core (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (E : Finset (Fin n × Fin n))
    (hlt : ∀ e ∈ E, e.1 < e.2)
    (h30 : ∀ e ∈ E, ∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧
      OrReaches n C C.output j ∧
      ((e.1 ∈ side (n := n) C j 0 ∧ e.2 ∈ side (n := n) C j 1) ∨
        (e.2 ∈ side (n := n) C j 0 ∧ e.1 ∈ side (n := n) C j 1)))
    (h31a : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → OrReaches n C C.output j →
      (∀ w : Fin n, w ∈ side (n := n) C j 0 → w ∉ side (n := n) C j 1) ∧
      (∀ u : Fin n, u ∈ side (n := n) C j 0 → ∀ v : Fin n, v ∈ side (n := n) C j 1 → G.Adj u v) ∧
      ((side (n := n) C j 0).card ≤ 1 ∨ (side (n := n) C j 1).card ≤ 1))
    (h31b : ∀ F : Finset ℕ, (∀ e ∈ E, ∃ i ∈ F, i < C.gates.length ∧
        (gateAt C i).op = GateOp.and ∧ OrReaches n C C.output i ∧
        ((e.1 ∈ side (n := n) C i 0 ∧ e.2 ∈ side (n := n) C i 1) ∨
          (e.2 ∈ side (n := n) C i 0 ∧ e.1 ∈ side (n := n) C i 1))) →
      ∃ T : Finset (Fin n), T.card ≤ F.card ∧ ∀ e3 ∈ E, e3.1 ∈ T ∨ e3.2 ∈ T)
    (h33 : ∀ F : Finset ℕ, (∀ j ∈ F, j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧
        OrReaches n C C.output j) →
      F.card ≤ Set.ncard {i : ℕ | i < C.gates.length ∧ (gateAt C i).op = GateOp.or ∧
        OrReaches n C C.output i} + 1)
    (h34 : ∀ (F : Finset ℕ) (ctr : ℕ → Fin n) (lf : ℕ → ℕ),
      (∀ j ∈ F, ∀ b : Fin n, b ∈ orIn n C (lf j) → G.Adj (ctr j) b) →
      (∀ i < C.gates.length, (gateAt C i).op = GateOp.or → 2 ≤ (orIn n C (n + i)).card →
        (∃ j1 ∈ F, OrReaches n C (lf j1) i) → ¬ OrReaches n C C.output i) ∧
      ∑ c : Fin n, (Finset.univ.filter (fun b2 : Fin n =>
        ∃ j2 ∈ F, ctr j2 = c ∧ b2 ∈ orIn n C (lf j2))).card ≤
        Set.ncard {i2 : ℕ | i2 < C.gates.length ∧ (gateAt C i2).op = GateOp.or ∧
          2 ≤ (orIn n C (n + i2)).card ∧ ∃ j3 ∈ F, OrReaches n C (lf j3) i2} + F.card) :
    ∃ T : Finset (Fin n), (∀ e ∈ E, e.1 ∈ T ∨ e.2 ∈ T) ∧ E.card + T.card ≤ C.size + 1 := by
  classical
  by_cases hE : E = ∅
  · subst hE
    refine ⟨∅, ?_, ?_⟩
    · intro e he
      simp at he
    · rw [Finset.card_empty, Finset.card_empty]
      exact Nat.zero_le _
  obtain ⟨e0, he0⟩ := Finset.nonempty_iff_ne_empty.mpr hE
  obtain ⟨F, hF⟩ : ∃ F : Finset ℕ, ∀ j, j ∈ F ↔ (j < C.gates.length ∧
      (gateAt C j).op = GateOp.and ∧ OrReaches n C C.output j ∧
      (side (n := n) C j 0).Nonempty ∧ (side (n := n) C j 1).Nonempty) :=
    ⟨(Finset.range C.gates.length).filter (fun j => (gateAt C j).op = GateOp.and ∧
      OrReaches n C C.output j ∧
      (side (n := n) C j 0).Nonempty ∧ (side (n := n) C j 1).Nonempty),
      fun j => by rw [Finset.mem_filter, Finset.mem_range]⟩
  have hper : ∀ j : ℕ, ∃ (c : Fin n) (l : ℕ), j ∈ F →
      (∀ b : Fin n, b ∈ orIn n C l → G.Adj c b) ∧
      (∀ u : Fin n, u ∈ side (n := n) C j 0 → ∀ v : Fin n, v ∈ side (n := n) C j 1 →
        (c = u ∧ v ∈ orIn n C l) ∨ (c = v ∧ u ∈ orIn n C l)) := by
    intro j
    by_cases hj : j ∈ F
    · obtain ⟨hjl, hand, hor, hn0, hn1⟩ := (hF j).mp hj
      obtain ⟨hdis, hadj, hcard⟩ := h31a j hjl hand hor
      rcases hcard with hc | hc
      · obtain ⟨c, hc0⟩ := hn0
        refine ⟨c, opnd C j 1, fun _ => ⟨?_, ?_⟩⟩
        · intro b hb
          exact hadj c hc0 b hb
        · intro u hu v hv
          exact Or.inl ⟨Finset.card_le_one.mp hc c hc0 u hu, hv⟩
      · obtain ⟨c, hc1⟩ := hn1
        refine ⟨c, opnd C j 0, fun _ => ⟨?_, ?_⟩⟩
        · intro b hb
          exact (hadj b hb c hc1).symm
        · intro u hu v hv
          exact Or.inr ⟨Finset.card_le_one.mp hc c hc1 v hv, hu⟩
    · exact ⟨e0.1, 0, fun h => absurd h hj⟩
  choose ctr lf hcl using hper
  have hw : ∀ e ∈ E, ∃ i ∈ F, i < C.gates.length ∧
      (gateAt C i).op = GateOp.and ∧ OrReaches n C C.output i ∧
      ((e.1 ∈ side (n := n) C i 0 ∧ e.2 ∈ side (n := n) C i 1) ∨
        (e.2 ∈ side (n := n) C i 0 ∧ e.1 ∈ side (n := n) C i 1)) := by
    intro e he
    obtain ⟨j, hjl, hand, hor, hs⟩ := h30 e he
    refine ⟨j, (hF j).mpr ⟨hjl, hand, hor, ?_, ?_⟩, hjl, hand, hor, hs⟩
    · rcases hs with hs | hs
      · exact ⟨e.1, hs.1⟩
      · exact ⟨e.2, hs.1⟩
    · rcases hs with hs | hs
      · exact ⟨e.2, hs.2⟩
      · exact ⟨e.1, hs.2⟩
  obtain ⟨T, hTc, hTcov⟩ := h31b F hw
  have hFand : ∀ j ∈ F, j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧
      OrReaches n C C.output j := by
    intro j hj
    obtain ⟨ha, hb, hc, _⟩ := (hF j).mp hj
    exact ⟨ha, hb, hc⟩
  have h3 := h33 F hFand
  obtain ⟨h4a, h4b⟩ := h34 F ctr lf (fun j hj => (hcl j hj).1)
  have hEsum := le_trans (sum_card_ge E (fun c => Finset.univ.filter (fun b2 : Fin n =>
      ∃ j2 ∈ F, ctr j2 = c ∧ b2 ∈ orIn n C (lf j2))) hlt (by
    intro e he
    obtain ⟨j, hjF, _, _, _, hs⟩ := hw e he
    rcases hs with hs | hs
    · rcases (hcl j hjF).2 e.1 hs.1 e.2 hs.2 with h | h
      · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, hjF, h.1, h.2⟩)
      · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, hjF, h.1, h.2⟩)
    · rcases (hcl j hjF).2 e.2 hs.1 e.1 hs.2 with h | h
      · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, hjF, h.1, h.2⟩)
      · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, hjF, h.1, h.2⟩))) h4b
  have hcount := three_count C.gates.length F
    {i : ℕ | i < C.gates.length ∧ (gateAt C i).op = GateOp.or ∧ OrReaches n C C.output i}
    {i2 : ℕ | i2 < C.gates.length ∧ (gateAt C i2).op = GateOp.or ∧
      2 ≤ (orIn n C (n + i2)).card ∧ ∃ j3 ∈ F, OrReaches n C (lf j3) i2}
    (fun j hj => (hFand j hj).1) (fun i hi => hi.1) (fun i hi => hi.1)
    (fun j hj hjA => by
      have h1 := (hFand j hj).2.1
      have h2 : (gateAt C j).op = GateOp.or := hjA.2.1
      rw [h2] at h1
      cases h1)
    (fun j hj hjB => by
      have h1 := (hFand j hj).2.1
      have h2 : (gateAt C j).op = GateOp.or := hjB.2.1
      rw [h2] at h1
      cases h1)
    (fun i hi hiB => h4a i hi.1 hi.2.1 hiB.2.2.1 hiB.2.2.2 hi.2.2)
  refine ⟨T, hTcov, ?_⟩
  have hsz : C.size = C.gates.length := rfl
  rw [hsz]
  omega

theorem main_aux : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → (∀ a1 : Fin n, PEqualNP.MetaComplexity.circuitFun n C (fun k1 => decide (k1 = a1)) = false) → (∀ a2 b2 : Fin n, a2 ≠ b2 → ¬ G.Adj a2 b2 → PEqualNP.MetaComplexity.circuitFun n C (fun k2 => decide (k2 = a2 ∨ k2 = b2)) = false) → ∃ T : Finset (Fin n), (∀ e ∈ (Finset.univ.filter (fun e1 : Fin n × Fin n => e1.1 < e1.2 ∧ G.Adj e1.1 e1.2 ∧ PEqualNP.ReadK.readsAtMost C n [e1.1.val, e1.2.val] 1 = true)), e.1 ∈ T ∨ e.2 ∈ T) ∧ (Finset.univ.filter (fun e2 : Fin n × Fin n => e2.1 < e2.2 ∧ G.Adj e2.1 e2.2 ∧ PEqualNP.ReadK.readsAtMost C n [e2.1.val, e2.2.val] 1 = true)).card + T.card ≤ C.size + 1 := by
  intro n G _ C h4 hA h1 h2
  have h31 := s2231 n G C h4 hA h1 h2
  exact core n G C _ (fun e he => (Finset.mem_filter.mp he).2.1)
    (fun e he => s2230 n C e.1 e.2 hA h1 (Finset.mem_filter.mp he).2.1
      (Finset.mem_filter.mp he).2.2.2)
    h31.1 h31.2 (fun F => s2233 n C F hA) (fun F ctr lf => s2234 n G C F ctr lf h4 hA h1)

end Part2

theorem Part2 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → (∀ a1 : Fin n, PEqualNP.MetaComplexity.circuitFun n C (fun k1 => decide (k1 = a1)) = false) → (∀ a2 b2 : Fin n, a2 ≠ b2 → ¬ G.Adj a2 b2 → PEqualNP.MetaComplexity.circuitFun n C (fun k2 => decide (k2 = a2 ∨ k2 = b2)) = false) → ∃ T : Finset (Fin n), (∀ e ∈ (Finset.univ.filter (fun e1 : Fin n × Fin n => e1.1 < e1.2 ∧ G.Adj e1.1 e1.2 ∧ PEqualNP.ReadK.readsAtMost C n [e1.1.val, e1.2.val] 1 = true)), e.1 ∈ T ∨ e.2 ∈ T) ∧ (Finset.univ.filter (fun e2 : Fin n × Fin n => e2.1 < e2.2 ∧ G.Adj e2.1 e2.2 ∧ PEqualNP.ReadK.readsAtMost C n [e2.1.val, e2.2.val] 1 = true)).card + T.card ≤ C.size + 1 :=
  PEqualNP.Outside.L_meta_8323.Part2.main_aux

end PEqualNP.Outside.L_meta_8323

-- Source module: PEqualNP.Outside.L_meta_1501
namespace PEqualNP.Outside.L_meta_8323

namespace Part3

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_len (gs : List Gate) (w : List Bool) :
    (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepW]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepW w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepW w g).length := by simp [stepW]; omega
    rw [ih (stepW w g) hlt]
    simp [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma foldl_char (gs : List Gate) (w : List Bool) :
    ∀ j, j < gs.length → (gs.foldl stepW w).getD (w.length + j) false =
      (gs.getD j ⟨GateOp.or, []⟩).op.eval ((gs.getD j ⟨GateOp.or, []⟩).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepW w).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen := foldl_len gs w
    simp only [List.length_append, List.length_singleton] at hj
    have key : ∀ i, i < w.length + gs.length →
        (stepW (gs.foldl stepW w) g).getD i false = (gs.foldl stepW w).getD i false := by
      intro i hi
      simp only [stepW, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_or_ge j gs.length with h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [e1, key _ (by omega), ih j h]
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with hi
      · rw [key i (by omega)]
      · rfl
    · have hj' : j = gs.length := by omega
      subst hj'
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      have e2 : (stepW (gs.foldl stepW w) g).getD (w.length + gs.length) false =
          g.op.eval (g.inputs.map fun i => (gs.foldl stepW w).getD i false) := by
        simp only [stepW, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2]
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with hi
      · rw [key i hi]
      · simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by omega)]
        rfl

def wv (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepW x := rfl

lemma wv_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    wv n C x w = x ⟨w, hw⟩ := by
  unfold wv
  rw [wires_eq, foldl_getD_lt _ _ _ (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

def AOB (n : ℕ) (C : Circuit) : Prop :=
  ∀ j, j < C.gates.length →
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
      ∀ i ∈ (gateAt C j).inputs, i < n + j

lemma wv_rec (n : ℕ) (C : Circuit) (x : Fin n → Bool) (hC : AOB n C) (j : ℕ)
    (hj : j < C.gates.length) :
    wv n C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (wv n C x)) := by
  have h := foldl_char C.gates (List.ofFn x) j hj
  simp only [List.length_ofFn] at h
  unfold wv gateAt
  rw [wires_eq, h]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [if_pos ((hC j hj).2 i hi)]

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

lemma inCone_reader (n : ℕ) (C : Circuit) (i : ℕ) :
    ∀ j, InCone n C i j → ∃ r, r < C.gates.length ∧ i < r ∧ n + i ∈ (gateAt C r).inputs ∧
      (r = j ∨ InCone n C r j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    have h' := h
    rw [inCone_iff] at h'
    obtain ⟨h0, k, hk, hin, h3 | h3⟩ := h'
    · subst h3
      exact ⟨j, h0, hk, hin, Or.inl rfl⟩
    · obtain ⟨r, hr, hir, hrin, h4⟩ := ih k hk h3
      refine ⟨r, hr, hir, hrin, Or.inr ?_⟩
      rw [inCone_iff]
      refine ⟨h0, k, hk, hin, ?_⟩
      rcases h4 with h4 | h4
      · exact Or.inl h4
      · exact Or.inr h4

def tau (n r b w : ℕ) : ℕ := if w < n + r then w else if w = n + r then b else w - 1

def rho (r k : ℕ) : ℕ := if k < r then k else k + 1

def IsRedirect (n : ℕ) (C C' : Circuit) (r b : ℕ) : Prop :=
  ∀ k, k < C.gates.length - 1 →
    gateAt C' k = ⟨(gateAt C (rho r k)).op, (gateAt C (rho r k)).inputs.map (tau n r b)⟩

lemma transfer (n : ℕ) (C C' : Circuit) (r b : ℕ) (x : Fin n → Bool) (R : Bool → Bool → Prop)
    (hRrefl : ∀ a, R a a) (hRtrans : ∀ a b c, R a b → R b c → R a c)
    (hRand : ∀ (l : List ℕ) (f f' : ℕ → Bool), (∀ w ∈ l, R (f w) (f' w)) →
      R (GateOp.and.eval (l.map f)) (GateOp.and.eval (l.map f')))
    (hRor : ∀ (l : List ℕ) (f f' : ℕ → Bool), (∀ w ∈ l, R (f w) (f' w)) →
      R (GateOp.or.eval (l.map f)) (GateOp.or.eval (l.map f')))
    (hC : AOB n C) (hC' : AOB n C') (hr : r < C.gates.length) (hb : b < n + r)
    (hlen : C.gates.length - 1 ≤ C'.gates.length)
    (hred : IsRedirect n C C' r b) :
    ∀ w, w < n + C.gates.length → (n + r ≤ w → R (wv n C x (n + r)) (wv n C x b)) →
      R (wv n C x w) (wv n C' x (tau n r b w)) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hR0
    by_cases h1 : w < n
    · have ht : tau n r b w = w := by unfold tau; rw [if_pos (by omega)]
      rw [ht, wv_input n C x w h1, wv_input n C' x w h1]
      exact hRrefl _
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      by_cases hk : k = r
      · subst hk
        have ht : tau n k b (n + k) = b := by unfold tau; simp
        have htb : tau n k b b = b := by unfold tau; rw [if_pos hb]
        have h2 := ih b (by omega) (by omega) (fun h => absurd h (by omega))
        rw [htb] at h2
        rw [ht]
        exact hRtrans _ _ _ (hR0 le_rfl) h2
      · have hkm : k < C.gates.length := by omega
        obtain ⟨k', hk'1, hk'2, hk'3⟩ : ∃ k', tau n r b (n + k) = n + k' ∧ rho r k' = k ∧
            k' < C.gates.length - 1 := by
          by_cases hkr : k < r
          · refine ⟨k, ?_, ?_, by omega⟩
            · unfold tau; rw [if_pos (by omega)]
            · unfold rho; rw [if_pos hkr]
          · refine ⟨k - 1, ?_, ?_, by omega⟩
            · unfold tau; rw [if_neg (by omega), if_neg (by omega)]; omega
            · unfold rho; rw [if_neg (by omega)]; omega
        have hg := hred k' hk'3
        rw [hk'2] at hg
        rw [hk'1, wv_rec n C x hC k hkm, wv_rec n C' x hC' k' (by omega), hg]
        simp only [List.map_map]
        have hin : ∀ w ∈ (gateAt C k).inputs,
            R (wv n C x w) ((wv n C' x ∘ tau n r b) w) := by
          intro w hw'
          have hlt := (hC k hkm).2 w hw'
          exact ih w hlt (by omega) (fun h => hR0 (by omega))
        rcases (hC k hkm).1 with hop | hop
        · rw [hop]; exact hRand _ _ _ hin
        · rw [hop]; exact hRor _ _ _ hin

lemma transfer_eq (n : ℕ) (C C' : Circuit) (r b : ℕ) (x : Fin n → Bool)
    (hC : AOB n C) (hC' : AOB n C') (hr : r < C.gates.length) (hb : b < n + r)
    (hlen : C.gates.length - 1 ≤ C'.gates.length)
    (hred : IsRedirect n C C' r b) :
    ∀ w, w < n + C.gates.length → (n + r ≤ w → wv n C x (n + r) = wv n C x b) →
      wv n C x w = wv n C' x (tau n r b w) := by
  refine transfer n C C' r b x (fun a b => a = b) (fun _ => rfl) (fun _ _ _ h1 h2 => h1.trans h2)
    ?_ ?_ hC hC' hr hb hlen hred
  · intro l f f' h
    rw [List.map_congr_left h]
  · intro l f f' h
    rw [List.map_congr_left h]

lemma transfer_le (n : ℕ) (C C' : Circuit) (r b : ℕ) (x : Fin n → Bool)
    (hC : AOB n C) (hC' : AOB n C') (hr : r < C.gates.length) (hb : b < n + r)
    (hlen : C.gates.length - 1 ≤ C'.gates.length)
    (hred : IsRedirect n C C' r b) :
    ∀ w, w < n + C.gates.length →
      (n + r ≤ w → (wv n C x (n + r) = true → wv n C x b = true)) →
      (wv n C x w = true → wv n C' x (tau n r b w) = true) := by
  refine transfer n C C' r b x (fun a b => a = true → b = true) (fun _ h => h)
    (fun _ _ _ h1 h2 h => h2 (h1 h)) ?_ ?_ hC hC' hr hb hlen hred
  · intro l f f' h hall
    simp only [GateOp.eval] at hall ⊢
    rw [List.all_eq_true] at hall ⊢
    intro v hv
    rw [List.mem_map] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact h w hw (hall (f w) (List.mem_map.mpr ⟨w, hw, rfl⟩))
  · intro l f f' h hany
    simp only [GateOp.eval] at hany ⊢
    rw [List.any_eq_true] at hany ⊢
    obtain ⟨v, hv, hv2⟩ := hany
    rw [List.mem_map] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact ⟨f' w, List.mem_map.mpr ⟨w, hw, rfl⟩, h w hw hv2⟩

def gfun (n : ℕ) (C : Circuit) (r b : ℕ) (top : Gate) (k : ℕ) : Gate :=
  if k < C.gates.length - 1 then
    ⟨(gateAt C (rho r k)).op, (gateAt C (rho r k)).inputs.map (tau n r b)⟩ else top

def V1 (n : ℕ) (C : Circuit) (r b : ℕ) : Circuit :=
  ⟨(List.range (C.gates.length - 1)).map (gfun n C r b ⟨GateOp.or, []⟩), tau n r b C.output⟩

def V2 (n : ℕ) (C : Circuit) (r b i : ℕ) : Circuit :=
  ⟨(List.range C.gates.length).map (gfun n C r b ⟨GateOp.or, [tau n r b C.output, n + i]⟩),
    n + C.gates.length - 1⟩

lemma gateAt_range (m : ℕ) (g : ℕ → Gate) (out k : ℕ) (hk : k < m) :
    gateAt ⟨(List.range m).map g, out⟩ k = g k := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma V1_len (n : ℕ) (C : Circuit) (r b : ℕ) :
    (V1 n C r b).gates.length = C.gates.length - 1 := by simp [V1]

lemma V2_len (n : ℕ) (C : Circuit) (r b i : ℕ) :
    (V2 n C r b i).gates.length = C.gates.length := by simp [V2]

lemma V1_gate (n : ℕ) (C : Circuit) (r b k : ℕ) (hk : k < C.gates.length - 1) :
    gateAt (V1 n C r b) k =
      ⟨(gateAt C (rho r k)).op, (gateAt C (rho r k)).inputs.map (tau n r b)⟩ := by
  unfold V1
  rw [gateAt_range _ _ _ _ hk]
  unfold gfun
  rw [if_pos hk]

lemma V2_gate (n : ℕ) (C : Circuit) (r b i k : ℕ) (hk : k < C.gates.length - 1) :
    gateAt (V2 n C r b i) k =
      ⟨(gateAt C (rho r k)).op, (gateAt C (rho r k)).inputs.map (tau n r b)⟩ := by
  unfold V2
  rw [gateAt_range _ _ _ _ (by omega)]
  unfold gfun
  rw [if_pos hk]

lemma V2_top (n : ℕ) (C : Circuit) (r b i : ℕ) (hm : 0 < C.gates.length) :
    gateAt (V2 n C r b i) (C.gates.length - 1) =
      ⟨GateOp.or, [tau n r b C.output, n + i]⟩ := by
  unfold V2
  rw [gateAt_range _ _ _ _ (by omega)]
  unfold gfun
  rw [if_neg (by omega)]

def AO2 (n : ℕ) (C : Circuit) : Prop :=
  ∀ j, j < C.gates.length →
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
      (∃ a b, (gateAt C j).inputs = [a, b]) ∧ ∀ i ∈ (gateAt C j).inputs, i < n + j

lemma aob {n : ℕ} {C : Circuit} (h : AO2 n C) : AOB n C :=
  fun j hj => ⟨(h j hj).1, (h j hj).2.2⟩

lemma rho_lt (r k m : ℕ) (hr : r < m) (hk : k < m - 1) : rho r k < m := by
  unfold rho; split_ifs <;> omega

lemma tau_lt (n r b w k : ℕ) (hb : b < n + r) (hw : w < n + rho r k) :
    tau n r b w < n + k := by
  unfold tau; unfold rho at hw; split_ifs at hw ⊢ <;> omega

lemma tau_low (n r b w : ℕ) (hw : w < n + r) : tau n r b w = w := by
  unfold tau; rw [if_pos hw]

lemma tau_rho (n r b k : ℕ) : tau n r b (n + rho r k) = n + k := by
  unfold tau rho; split_ifs <;> omega

lemma eval_or_pair (f : ℕ → Bool) (a b : ℕ) :
    GateOp.or.eval ([a, b].map f) = (f a || f b) := by simp [GateOp.eval]

lemma eval_and_pair (f : ℕ → Bool) (a b : ℕ) :
    GateOp.and.eval ([a, b].map f) = (f a && f b) := by simp [GateOp.eval]

lemma V1_AO2 (n : ℕ) (C : Circuit) (r b : ℕ) (hC : AO2 n C) (hr : r < C.gates.length)
    (hb : b < n + r) : AO2 n (V1 n C r b) := by
  intro k hk
  rw [V1_len] at hk
  rw [V1_gate n C r b k hk]
  obtain ⟨h1, ⟨a, c, h2⟩, h3⟩ := hC (rho r k) (rho_lt r k _ hr hk)
  refine ⟨h1, ⟨tau n r b a, tau n r b c, by simp [h2]⟩, ?_⟩
  intro w hw
  simp only [List.mem_map] at hw
  obtain ⟨w0, hw0, rfl⟩ := hw
  exact tau_lt n r b w0 k hb (h3 w0 hw0)

lemma V2_AO2 (n : ℕ) (C : Circuit) (r b i : ℕ) (hC : AO2 n C) (hr : r < C.gates.length)
    (hb : b < n + r) (hi : i < r) (hout : C.output < n + C.gates.length) :
    AO2 n (V2 n C r b i) := by
  intro k hk
  rw [V2_len] at hk
  by_cases hk1 : k < C.gates.length - 1
  · rw [V2_gate n C r b i k hk1]
    obtain ⟨h1, ⟨a, c, h2⟩, h3⟩ := hC (rho r k) (rho_lt r k _ hr hk1)
    refine ⟨h1, ⟨tau n r b a, tau n r b c, by simp [h2]⟩, ?_⟩
    intro w hw
    simp only [List.mem_map] at hw
    obtain ⟨w0, hw0, rfl⟩ := hw
    exact tau_lt n r b w0 k hb (h3 w0 hw0)
  · have hk2 : k = C.gates.length - 1 := by omega
    subst hk2
    rw [V2_top n C r b i (by omega)]
    refine ⟨Or.inr rfl, ⟨_, _, rfl⟩, ?_⟩
    intro w hw
    have hw' : w = tau n r b C.output ∨ w = n + i := by simpa using hw
    rcases hw' with rfl | rfl
    · unfold tau; split_ifs <;> omega
    · omega

lemma V1_red (n : ℕ) (C : Circuit) (r b : ℕ) : IsRedirect n C (V1 n C r b) r b :=
  fun k hk => V1_gate n C r b k hk

lemma V2_red (n : ℕ) (C : Circuit) (r b i : ℕ) : IsRedirect n C (V2 n C r b i) r b :=
  fun k hk => V2_gate n C r b i k hk

lemma V1_fun (n : ℕ) (C : Circuit) (r b : ℕ) (x : Fin n → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : b < n + r) (hout : C.output < n + C.gates.length)
    (h1 : wv n C x b = true → wv n C x C.output = true)
    (h2 : wv n C x b = false → wv n C x (n + r) = false) :
    wv n (V1 n C r b) x (V1 n C r b).output = wv n C x C.output := by
  have hC' := V1_AO2 n C r b hC hr hb
  have hlen : C.gates.length - 1 ≤ (V1 n C r b).gates.length := by rw [V1_len]
  show wv n (V1 n C r b) x (tau n r b C.output) = wv n C x C.output
  cases hbv : wv n C x b with
  | true =>
    rw [h1 hbv]
    exact transfer_le n C _ r b x (aob hC) (aob hC') hr hb hlen (V1_red n C r b) C.output hout
      (fun _ _ => hbv) (h1 hbv)
  | false =>
    exact (transfer_eq n C _ r b x (aob hC) (aob hC') hr hb hlen (V1_red n C r b) C.output hout
      (fun _ => by rw [h2 hbv, hbv])).symm

lemma V2_low (n : ℕ) (C : Circuit) (r b i : ℕ) (x : Fin n → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : b < n + r) (hi : i < r)
    (hout : C.output < n + C.gates.length) :
    ∀ w, w < n + r → wv n (V2 n C r b i) x w = wv n C x w := by
  intro w hw
  have h := transfer_eq n C _ r b x (aob hC) (aob (V2_AO2 n C r b i hC hr hb hi hout)) hr hb
    (by rw [V2_len]; omega) (V2_red n C r b i) w (by omega) (fun h => absurd h (by omega))
  rw [tau_low n r b w hw] at h
  exact h.symm

lemma V2_same (n : ℕ) (C : Circuit) (r b i : ℕ) (x : Fin n → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : b < n + r) (hi : i < r)
    (hout : C.output < n + C.gates.length) (h0 : wv n C x (n + r) = wv n C x b) :
    ∀ w, w < n + C.gates.length → wv n (V2 n C r b i) x (tau n r b w) = wv n C x w := by
  intro w hw
  exact (transfer_eq n C _ r b x (aob hC) (aob (V2_AO2 n C r b i hC hr hb hi hout)) hr hb
    (by rw [V2_len]; omega) (V2_red n C r b i) w hw (fun _ => h0)).symm

lemma V2_out (n : ℕ) (C : Circuit) (r b i : ℕ) (x : Fin n → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : b < n + r) (hi : i < r)
    (hout : C.output < n + C.gates.length)
    (hbel : wv n C x (n + i) = true → wv n C x C.output = true)
    (h0 : wv n C x (n + i) = false → wv n C x (n + r) = wv n C x b) :
    wv n (V2 n C r b i) x (V2 n C r b i).output = wv n C x C.output := by
  have hC' := V2_AO2 n C r b i hC hr hb hi hout
  have hm : 0 < C.gates.length := by omega
  have e : (V2 n C r b i).output = n + (C.gates.length - 1) := by
    show n + C.gates.length - 1 = _
    omega
  rw [e, wv_rec n _ x (aob hC') (C.gates.length - 1) (by rw [V2_len]; omega),
    V2_top n C r b i hm]
  have hi' := V2_low n C r b i x hC hr hb hi hout (n + i) (by omega)
  dsimp only
  rw [eval_or_pair, hi']
  cases hv : wv n C x (n + i) with
  | true => rw [hbel hv]; simp
  | false =>
    rw [V2_same n C r b i x hC hr hb hi hout (h0 hv) C.output hout]; simp

lemma V1_fun_top (n : ℕ) (D : Circuit) (r c i y : ℕ) (x : Fin n → Bool) (hD : AO2 n D)
    (hr : r < D.gates.length - 1) (hc : c < n + r) (hi : i < r)
    (hout : D.output = n + (D.gates.length - 1))
    (htop : gateAt D (D.gates.length - 1) = ⟨GateOp.or, [y, n + i]⟩)
    (h0 : wv n D x (n + i) = false → wv n D x (n + r) = wv n D x c) :
    wv n (V1 n D r c) x (V1 n D r c).output = wv n D x D.output := by
  have hr' : r < D.gates.length := by omega
  have hE := V1_AO2 n D r c hD hr' hc
  have hlen : D.gates.length - 1 ≤ (V1 n D r c).gates.length := by rw [V1_len]
  have hred := V1_red n D r c
  show wv n (V1 n D r c) x (tau n r c D.output) = wv n D x D.output
  cases hv : wv n D x (n + i) with
  | false =>
    exact (transfer_eq n D _ r c x (aob hD) (aob hE) hr' hc hlen hred D.output (by omega)
      (fun _ => h0 hv)).symm
  | true =>
    have e1 : wv n D x D.output = true := by
      rw [hout, wv_rec n D x (aob hD) _ (by omega), htop]
      dsimp only
      rw [eval_or_pair, hv]; simp
    have e2 : tau n r c D.output = n + (D.gates.length - 2) := by
      rw [hout]; unfold tau; rw [if_neg (by omega), if_neg (by omega)]; omega
    have e3 : gateAt (V1 n D r c) (D.gates.length - 2) =
        ⟨GateOp.or, [tau n r c y, n + i]⟩ := by
      rw [V1_gate n D r c _ (by omega)]
      have hrho : rho r (D.gates.length - 2) = D.gates.length - 1 := by
        unfold rho; rw [if_neg (by omega)]; omega
      rw [hrho, htop]
      simp [tau_low n r c (n + i) (by omega)]
    have e4 : wv n (V1 n D r c) x (n + i) = true := by
      have h := transfer_eq n D _ r c x (aob hD) (aob hE) hr' hc hlen hred (n + i) (by omega)
        (fun h => absurd h (by omega))
      rw [tau_low n r c (n + i) (by omega)] at h
      rw [← h, hv]
    rw [e1, e2, wv_rec n _ x (aob hE) _ (by rw [V1_len]; omega), e3]
    dsimp only
    rw [eval_or_pair, e4]; simp

def Least (n : ℕ) (C : Circuit) : Prop :=
  AO2 n C ∧ ∀ D : Circuit, AO2 n D → (∀ x, wv n D x D.output = wv n C x C.output) →
    C.gates.length ≤ D.gates.length

lemma reader_or (n : ℕ) (C : Circuit) (hL : Least n C) (hout : C.output < n + C.gates.length)
    (i r : ℕ) (hr : r < C.gates.length)
    (hbel : ∀ x, wv n C x (n + i) = true → wv n C x C.output = true)
    (hin : n + i ∈ (gateAt C r).inputs) :
    (gateAt C r).op = GateOp.or ∧ ∃ c, c ≠ n + i ∧ c < n + r ∧
      ((gateAt C r).inputs = [n + i, c] ∨ (gateAt C r).inputs = [c, n + i]) := by
  obtain ⟨hop, ⟨a, c0, hab⟩, hlt⟩ := hL.1 r hr
  have hir : n + i < n + r := hlt _ hin
  have hin' : n + i = a ∨ n + i = c0 := by rw [hab] at hin; simpa using hin
  by_contra hcon
  have key : ∀ x, wv n C x (n + i) = false → wv n C x (n + r) = false := by
    intro x hx
    rw [wv_rec n C x (aob hL.1) r hr, hab]
    rcases hop with hop | hop
    · rw [hop, eval_and_pair]
      rcases hin' with h | h
      · rw [← h, hx]; rfl
      · rw [← h, hx]; simp
    · rw [hop, eval_or_pair]
      have ha : a = n + i := by
        by_contra hne
        apply hcon
        refine ⟨hop, a, hne, hlt a (by rw [hab]; simp), ?_⟩
        rcases hin' with h | h
        · exact absurd h.symm hne
        · right; rw [hab, h]
      have hc : c0 = n + i := by
        by_contra hne
        apply hcon
        refine ⟨hop, c0, hne, hlt c0 (by rw [hab]; simp), ?_⟩
        left; rw [hab, ha]
      rw [ha, hc, hx]; rfl
  have hfun : ∀ x, wv n (V1 n C r (n + i)) x (V1 n C r (n + i)).output = wv n C x C.output :=
    fun x => V1_fun n C r (n + i) x hL.1 hr hir hout (hbel x) (key x)
  have hle := hL.2 _ (V1_AO2 n C r (n + i) hL.1 hr hir) hfun
  rw [V1_len] at hle
  omega

lemma reader_unique (n : ℕ) (C : Circuit) (hL : Least n C)
    (hout : C.output < n + C.gates.length) (i r1 r2 : ℕ) (h12 : r1 < r2)
    (hr2 : r2 < C.gates.length)
    (hbel : ∀ x, wv n C x (n + i) = true → wv n C x C.output = true)
    (hin1 : n + i ∈ (gateAt C r1).inputs) (hin2 : n + i ∈ (gateAt C r2).inputs) : False := by
  have hr1 : r1 < C.gates.length := by omega
  obtain ⟨hop1, c1, hc1, hc1lt, hi1⟩ := reader_or n C hL hout i r1 hr1 hbel hin1
  obtain ⟨hop2, c2, hc2, hc2lt, hi2⟩ := reader_or n C hL hout i r2 hr2 hbel hin2
  have hir1 : i < r1 := by have := (hL.1 r1 hr1).2.2 _ hin1; omega
  have hir2 : i < r2 := by omega
  have k2 : ∀ x, wv n C x (n + i) = false → wv n C x (n + r2) = wv n C x c2 := by
    intro x hx
    rw [wv_rec n C x (aob hL.1) r2 hr2, hop2]
    rcases hi2 with h | h
    · rw [h, eval_or_pair, hx]; rfl
    · rw [h, eval_or_pair, hx]; simp
  have k1 : ∀ x, wv n C x (n + i) = false → wv n C x (n + r1) = wv n C x c1 := by
    intro x hx
    rw [wv_rec n C x (aob hL.1) r1 hr1, hop1]
    rcases hi1 with h | h
    · rw [h, eval_or_pair, hx]; rfl
    · rw [h, eval_or_pair, hx]; simp
  have hD : AO2 n (V2 n C r2 c2 i) := V2_AO2 n C r2 c2 i hL.1 hr2 hc2lt hir2 hout
  have hDlen := V2_len n C r2 c2 i
  have hDfun : ∀ x, wv n (V2 n C r2 c2 i) x (V2 n C r2 c2 i).output = wv n C x C.output :=
    fun x => V2_out n C r2 c2 i x hL.1 hr2 hc2lt hir2 hout (hbel x) (k2 x)
  have hDout : (V2 n C r2 c2 i).output = n + ((V2 n C r2 c2 i).gates.length - 1) := by
    rw [hDlen]
    show n + C.gates.length - 1 = n + (C.gates.length - 1)
    omega
  have hDtop : gateAt (V2 n C r2 c2 i) ((V2 n C r2 c2 i).gates.length - 1) =
      ⟨GateOp.or, [tau n r2 c2 C.output, n + i]⟩ := by
    rw [hDlen]
    exact V2_top n C r2 c2 i (by omega)
  have h0 : ∀ x, wv n (V2 n C r2 c2 i) x (n + i) = false →
      wv n (V2 n C r2 c2 i) x (n + r1) = wv n (V2 n C r2 c2 i) x c1 := by
    intro x hx
    rw [V2_low n C r2 c2 i x hL.1 hr2 hc2lt hir2 hout (n + i) (by omega)] at hx
    rw [V2_low n C r2 c2 i x hL.1 hr2 hc2lt hir2 hout (n + r1) (by omega),
      V2_low n C r2 c2 i x hL.1 hr2 hc2lt hir2 hout c1 (by omega)]
    exact k1 x hx
  have hEfun : ∀ x, wv n (V1 n (V2 n C r2 c2 i) r1 c1) x (V1 n (V2 n C r2 c2 i) r1 c1).output =
      wv n C x C.output := fun x =>
    (V1_fun_top n (V2 n C r2 c2 i) r1 c1 i (tau n r2 c2 C.output) x hD (by rw [hDlen]; omega)
      hc1lt hir1 hDout hDtop (h0 x)).trans (hDfun x)
  have hle := hL.2 _ (V1_AO2 n (V2 n C r2 c2 i) r1 c1 hD (by rw [hDlen]; omega) hc1lt) hEfun
  rw [V1_len, hDlen] at hle
  omega

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

lemma V2_cone (n : ℕ) (C : Circuit) (r c i : ℕ) (hC : AO2 n C) (hr : r < C.gates.length)
    (hc : c < n + r) (hcin : c ∈ (gateAt C r).inputs) (a' : ℕ) :
    ∀ b', b' < C.gates.length - 1 → InCone n (V2 n C r c i) a' b' →
      InCone n C (rho r a') (rho r b') := by
  intro b'
  induction b' using Nat.strong_induction_on with
  | _ b' ih =>
    intro hb' h
    rw [inCone_iff] at h
    obtain ⟨_, k', hk', hin, h3⟩ := h
    rw [V2_gate n C r c i b' hb'] at hin
    simp only [List.mem_map] at hin
    obtain ⟨w, hw, hwk⟩ := hin
    have hbm : rho r b' < C.gates.length := rho_lt r b' _ hr hb'
    have hwlt := (hC (rho r b') hbm).2.2 w hw
    have hrb : rho r b' ≤ b' + 1 := by unfold rho; split_ifs <;> omega
    have hrb2 : b' < r → rho r b' = b' := by intro h; unfold rho; rw [if_pos h]
    have hstep : InCone n C (rho r k') (rho r b') := by
      unfold tau at hwk
      by_cases h1 : w < n + r
      · rw [if_pos h1] at hwk
        have e : rho r k' = k' := by unfold rho; rw [if_pos (by omega)]
        rw [e, inCone_iff]
        refine ⟨hbm, k', by omega, ?_, Or.inl rfl⟩
        rw [← hwk]; exact hw
      · rw [if_neg h1] at hwk
        by_cases h2 : w = n + r
        · rw [if_pos h2] at hwk
          have e : rho r k' = k' := by unfold rho; rw [if_pos (by omega)]
          rw [e]
          have s1 : InCone n C k' r := by
            rw [inCone_iff]
            refine ⟨hr, k', by omega, ?_, Or.inl rfl⟩
            rw [← hwk]; exact hcin
          have s2 : InCone n C r (rho r b') := by
            rw [inCone_iff]
            refine ⟨hbm, r, by omega, ?_, Or.inl rfl⟩
            rw [← h2]; exact hw
          exact inCone_trans n C k' r s1 _ s2
        · rw [if_neg h2] at hwk
          have e : rho r k' = k' + 1 := by unfold rho; rw [if_neg (by omega)]
          rw [e, inCone_iff]
          refine ⟨hbm, k' + 1, by omega, ?_, Or.inl rfl⟩
          have e2 : n + (k' + 1) = w := by omega
          rw [e2]; exact hw
    rcases h3 with h3 | h3
    · rw [h3]; exact hstep
    · exact inCone_trans n C _ _ (ih k' hk' (by omega) h3) _ hstep

lemma V2_no_reader (n : ℕ) (C : Circuit) (r c i : ℕ) (hr : r < C.gates.length)
    (hi : i < r) (hci : c ≠ n + i)
    (huniq : ∀ k, k < C.gates.length → n + i ∈ (gateAt C k).inputs → k = r) :
    ∀ k', k' < C.gates.length - 1 → n + i ∉ (gateAt (V2 n C r c i) k').inputs := by
  intro k' hk' hin
  rw [V2_gate n C r c i k' hk'] at hin
  simp only [List.mem_map] at hin
  obtain ⟨w, hw, hwk⟩ := hin
  have hbm : rho r k' < C.gates.length := rho_lt r k' _ hr hk'
  have hne : rho r k' ≠ r := by unfold rho; split_ifs <;> omega
  unfold tau at hwk
  by_cases h1 : w < n + r
  · rw [if_pos h1] at hwk
    rw [hwk] at hw
    exact hne (huniq _ hbm hw)
  · rw [if_neg h1] at hwk
    by_cases h2 : w = n + r
    · rw [if_pos h2] at hwk
      exact hci hwk
    · rw [if_neg h2] at hwk
      omega

lemma V2_no_cone (n : ℕ) (C : Circuit) (r c i : ℕ) (hr : r < C.gates.length)
    (hi : i < r) (hci : c ≠ n + i)
    (huniq : ∀ k, k < C.gates.length → n + i ∈ (gateAt C k).inputs → k = r) :
    ∀ j', j' < C.gates.length - 1 → ¬ InCone n (V2 n C r c i) i j' := by
  intro j' hj' h
  obtain ⟨r', _, _, hrin, h4⟩ := inCone_reader n _ i j' h
  have hr'j : r' ≤ j' := by
    rcases h4 with h4 | h4
    · omega
    · have := (inCone_lt n _ r' j' h4).1
      omega
  exact V2_no_reader n C r c i hr hi hci huniq r' (by omega) hrin

lemma rho_inj (r : ℕ) : Function.Injective (rho r) := by
  intro a b h
  unfold rho at h
  split_ifs at h <;> omega

lemma rho_ne (r k : ℕ) : rho r k ≠ r := by
  unfold rho; split_ifs <;> omega

lemma rho_surj (r k m : ℕ) (hr : r < m) (hk : k < m) (hne : k ≠ r) : ∃ k', k' < m - 1 ∧ rho r k' = k := by
  by_cases h : k < r
  · exact ⟨k, by omega, by unfold rho; rw [if_pos h]⟩
  · exact ⟨k - 1, by omega, by unfold rho; rw [if_neg (by omega)]; omega⟩

lemma wires_len (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [wires_eq, foldl_len, List.length_ofFn]

lemma out_lt (n : ℕ) (C : Circuit) (x : Fin n → Bool) (h : wv n C x C.output = true) :
    C.output < n + C.gates.length := by
  by_contra hge
  unfold wv at h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [wires_len]; omega)] at h
  simp at h

lemma step3_core (n : ℕ) (C : Circuit) (hL : Least n C) (hout : C.output < n + C.gates.length)
    (i j : ℕ) (hbel : ∀ x, wv n C x (n + i) = true → wv n C x C.output = true)
    (hcone : InCone n C i j) :
    ∃ r c, r < C.gates.length ∧ i < r ∧ c < n + r ∧ c ≠ n + i ∧ c ∈ (gateAt C r).inputs ∧
      (gateAt C r).op = GateOp.or ∧
      (∀ k, k < C.gates.length → n + i ∈ (gateAt C k).inputs → k = r) ∧
      (∀ x, wv n C x (n + i) = false → wv n C x (n + r) = wv n C x c) := by
  obtain ⟨r, hr, hir, hrin, _⟩ := inCone_reader n C i j hcone
  obtain ⟨hop, c, hc, hclt, hi⟩ := reader_or n C hL hout i r hr hbel hrin
  refine ⟨r, c, hr, hir, hclt, hc, ?_, hop, ?_, ?_⟩
  · rcases hi with h | h <;> rw [h] <;> simp
  · intro k hk hkin
    rcases Nat.lt_trichotomy k r with h | h | h
    · exact (reader_unique n C hL hout i k r h hr hbel hkin hrin).elim
    · exact h
    · exact (reader_unique n C hL hout i r k h hk hbel hrin hkin).elim
  · intro x hx
    rw [wv_rec n C x (aob hL.1) r hr, hop]
    rcases hi with h | h
    · rw [h, eval_or_pair, hx]; rfl
    · rw [h, eval_or_pair, hx]; simp

lemma least_of_same (n : ℕ) (C D : Circuit) (hL : Least n C) (hD : AO2 n D)
    (hfun : ∀ x, wv n D x D.output = wv n C x C.output)
    (hlen : D.gates.length = C.gates.length) : Least n D :=
  ⟨hD, fun E hE hEf => by rw [hlen]; exact hL.2 E hE (fun x => (hEf x).trans (hfun x))⟩

lemma V2_gateval (n : ℕ) (C : Circuit) (r c i : ℕ) (x : Fin n → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : c < n + r) (hi : i < r)
    (hout : C.output < n + C.gates.length) (h0 : wv n C x (n + r) = wv n C x c)
    (k' : ℕ) (hk' : k' < C.gates.length - 1) :
    wv n (V2 n C r c i) x (n + k') = wv n C x (n + rho r k') := by
  have h := V2_same n C r c i x hC hr hb hi hout h0 (n + rho r k')
    (by have := rho_lt r k' _ hr hk'; omega)
  rw [tau_rho] at h
  exact h

lemma V2_below (n : ℕ) (C : Circuit) (r c i : ℕ) (F : (Fin n → Bool) → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : c < n + r) (hi : i < r)
    (hout : C.output < n + C.gates.length)
    (hbelF : ∀ x, wv n C x (n + i) = true → F x = true)
    (h0 : ∀ x, wv n C x (n + i) = false → wv n C x (n + r) = wv n C x c)
    (k' : ℕ) (hk' : k' < C.gates.length - 1) :
    (∀ x, wv n (V2 n C r c i) x (n + k') = true → F x = true) ↔
      (∀ x, wv n C x (n + rho r k') = true → F x = true) := by
  constructor
  · intro h x hv
    cases hx : wv n C x (n + i) with
    | true => exact hbelF x hx
    | false =>
      apply h x
      rw [V2_gateval n C r c i x hC hr hb hi hout (h0 x hx) k' hk']
      exact hv
  · intro h x hv
    cases hx : wv n C x (n + i) with
    | true => exact hbelF x hx
    | false =>
      apply h x
      rw [← V2_gateval n C r c i x hC hr hb hi hout (h0 x hx) k' hk']
      exact hv

lemma card_filter_rho (m r : ℕ) (hr : r < m) (P Q : ℕ → Prop) [DecidablePred P]
    [DecidablePred Q]
    (hPQ : ∀ k', k' < m - 1 → (Q k' ↔ P (rho r k'))) (hPr : ¬ P r) (hQ : ¬ Q (m - 1)) :
    ((Finset.range m).filter Q).card = ((Finset.range m).filter P).card := by
  apply Finset.card_bij (fun k' _ => rho r k')
  · intro k' hk'
    rw [Finset.mem_filter, Finset.mem_range] at hk' ⊢
    have hlt : k' < m - 1 := by
      rcases Nat.lt_or_ge k' (m - 1) with h | h
      · exact h
      · have hk'' : k' = m - 1 := by omega
        rw [hk''] at hk'
        exact absurd hk'.2 hQ
    exact ⟨rho_lt r k' m hr hlt, (hPQ k' hlt).mp hk'.2⟩
  · intro a _ b _ h
    exact rho_inj r h
  · intro k hk
    rw [Finset.mem_filter, Finset.mem_range] at hk
    have hne : k ≠ r := fun h => hPr (h ▸ hk.2)
    obtain ⟨k', hk'1, hk'2⟩ := rho_surj r k m hr hk.1 hne
    refine ⟨k', ?_, hk'2⟩
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, (hPQ k' hk'1).mpr (hk'2 ▸ hk.2)⟩

lemma card_pairs_rho (m r : ℕ) (hr : r < m) (P Q : ℕ → ℕ → Prop)
    [DecidablePred (fun p : ℕ × ℕ => P p.1 p.2)] [DecidablePred (fun p : ℕ × ℕ => Q p.1 p.2)]
    (hQP : ∀ a' b', a' < m → b' < m → Q a' b' →
      a' < m - 1 ∧ b' < m - 1 ∧ P (rho r a') (rho r b'))
    (i j : ℕ) (hi : i < m) (hj : j < m) (hP : P i j)
    (hne : ∀ a' b', Q a' b' → ¬ (rho r a' = i ∧ rho r b' = j)) :
    ((Finset.range m ×ˢ Finset.range m).filter (fun p : ℕ × ℕ => Q p.1 p.2)).card <
      ((Finset.range m ×ˢ Finset.range m).filter (fun p : ℕ × ℕ => P p.1 p.2)).card := by
  have hinj : Function.Injective (fun p : ℕ × ℕ => (rho r p.1, rho r p.2)) := by
    intro p q h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (rho_inj r h.1) (rho_inj r h.2)
  rw [← Finset.card_image_of_injective _ hinj]
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨(i, j), ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
      exact ⟨⟨hi, hj⟩, hP⟩
    · intro hmem
      rw [Finset.mem_image] at hmem
      obtain ⟨⟨a', b'⟩, hab, heq⟩ := hmem
      rw [Finset.mem_filter] at hab
      simp only [Prod.mk.injEq] at heq
      exact hne a' b' hab.2 heq
  · intro p hp
    rw [Finset.mem_image] at hp
    obtain ⟨⟨a', b'⟩, hab, rfl⟩ := hp
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hab
    obtain ⟨h1, h2, h3⟩ := hQP a' b' hab.1.1 hab.1.2 hab.2
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
    exact ⟨⟨rho_lt r a' m hr h1, rho_lt r b' m hr h2⟩, h3⟩

lemma step3_struct (n : ℕ) (C : Circuit) (F : (Fin n → Bool) → Bool) (hL : Least n C)
    (hF : ∀ x, wv n C x C.output = F x) (hout : C.output < n + C.gates.length)
    (i j : ℕ) (hbel : ∀ x, wv n C x (n + i) = true → F x = true)
    (hcone : InCone n C i j) :
    ∃ (C' : Circuit) (r : ℕ), r < C.gates.length ∧ i < r ∧ Least n C' ∧
      (∀ x, wv n C' x C'.output = F x) ∧ C'.gates.length = C.gates.length ∧
      (∀ k', k' < C.gates.length - 1 → (gateAt C' k').op = (gateAt C (rho r k')).op) ∧
      (gateAt C' (C.gates.length - 1)).op = GateOp.or ∧ (gateAt C r).op = GateOp.or ∧
      (∀ k', k' < C.gates.length - 1 →
        ((∀ x, wv n C' x (n + k') = true → F x = true) ↔
          (∀ x, wv n C x (n + rho r k') = true → F x = true))) ∧
      (∀ a' b', b' < C.gates.length - 1 → InCone n C' a' b' →
        InCone n C (rho r a') (rho r b')) ∧
      (∀ j', j' < C.gates.length - 1 → ¬ InCone n C' i j') := by
  have hbel' : ∀ x, wv n C x (n + i) = true → wv n C x C.output = true :=
    fun x h => by rw [hF]; exact hbel x h
  obtain ⟨r, c, hr, hir, hclt, hci, hcin, hop, huniq, h0⟩ :=
    step3_core n C hL hout i j hbel' hcone
  have hD := V2_AO2 n C r c i hL.1 hr hclt hir hout
  have hfun : ∀ x, wv n (V2 n C r c i) x (V2 n C r c i).output = wv n C x C.output :=
    fun x => V2_out n C r c i x hL.1 hr hclt hir hout (hbel' x) (h0 x)
  refine ⟨V2 n C r c i, r, hr, hir, least_of_same n C _ hL hD hfun (V2_len n C r c i),
    fun x => (hfun x).trans (hF x), V2_len n C r c i, ?_, ?_, hop, ?_, ?_, ?_⟩
  · intro k' hk'
    rw [V2_gate n C r c i k' hk']
  · rw [V2_top n C r c i (by omega)]
  · intro k' hk'
    exact V2_below n C r c i F hL.1 hr hclt hir hout hbel h0 k' hk'
  · intro a' b' hb' h
    exact V2_cone n C r c i hL.1 hr hclt hcin a' b' hb' h
  · exact V2_no_cone n C r c i hr hir hci huniq

lemma pairs_lt (n : ℕ) (C C' : Circuit) (r i j : ℕ) (hr : r < C.gates.length) (hir : i < r)
    (hlen : C'.gates.length = C.gates.length)
    (hops : ∀ k', k' < C.gates.length - 1 → (gateAt C' k').op = (gateAt C (rho r k')).op)
    (htop : (gateAt C' (C.gates.length - 1)).op = GateOp.or)
    (hcone : ∀ a' b', b' < C.gates.length - 1 → InCone n C' a' b' →
        InCone n C (rho r a') (rho r b'))
    (hno : ∀ j', j' < C.gates.length - 1 → ¬ InCone n C' i j')
    (hi : (gateAt C i).op = GateOp.and) (hj : (gateAt C j).op = GateOp.and)
    (hij : InCone n C i j)
    [DecidablePred (fun p : ℕ × ℕ => (gateAt C p.1).op = GateOp.and ∧
      (gateAt C p.2).op = GateOp.and ∧ InCone n C p.1 p.2)]
    [DecidablePred (fun p : ℕ × ℕ => (gateAt C' p.1).op = GateOp.and ∧
      (gateAt C' p.2).op = GateOp.and ∧ InCone n C' p.1 p.2)] :
    ((Finset.range C'.gates.length ×ˢ Finset.range C'.gates.length).filter
      (fun p : ℕ × ℕ => (gateAt C' p.1).op = GateOp.and ∧
        (gateAt C' p.2).op = GateOp.and ∧ InCone n C' p.1 p.2)).card <
    ((Finset.range C.gates.length ×ˢ Finset.range C.gates.length).filter
      (fun p : ℕ × ℕ => (gateAt C p.1).op = GateOp.and ∧
        (gateAt C p.2).op = GateOp.and ∧ InCone n C p.1 p.2)).card := by
  rw [hlen]
  have hjm := (inCone_lt n C i j hij)
  refine card_pairs_rho C.gates.length r hr
    (fun a b => (gateAt C a).op = GateOp.and ∧ (gateAt C b).op = GateOp.and ∧ InCone n C a b)
    (fun a b => (gateAt C' a).op = GateOp.and ∧ (gateAt C' b).op = GateOp.and ∧
      InCone n C' a b) ?_ i j (by omega) hjm.2 ⟨hi, hj, hij⟩ ?_
  · rintro a' b' _ hb' ⟨ha, hb, hab⟩
    have hb'' : b' < C.gates.length - 1 := by
      rcases Nat.lt_or_ge b' (C.gates.length - 1) with h | h
      · exact h
      · have e : b' = C.gates.length - 1 := by omega
        rw [e, htop] at hb
        exact absurd hb (by simp)
    have ha' := (inCone_lt n C' a' b' hab).1
    have ha'' : a' < C.gates.length - 1 := by omega
    refine ⟨ha'', hb'', ?_, ?_, hcone a' b' hb'' hab⟩
    · rw [← hops a' ha'']; exact ha
    · rw [← hops b' hb'']; exact hb
  · rintro a' b' ⟨_, hb, hab⟩ ⟨h1, _⟩
    have hb'' : b' < C.gates.length - 1 := by
      rcases Nat.lt_or_ge b' (C.gates.length - 1) with h | h
      · exact h
      · have hb3 := (inCone_lt n C' a' b' hab).2
        have e : b' = C.gates.length - 1 := by omega
        rw [e, htop] at hb
        exact absurd hb (by simp)
    have e : rho r i = i := by unfold rho; rw [if_pos hir]
    have e2 : a' = i := rho_inj r (h1.trans e.symm)
    rw [e2] at hab
    exact hno b' hb'' hab

lemma card_mem_rho (m r : ℕ) (hr : r < m) (P Q : ℕ → Prop) (S S' : Finset ℕ)
    (hS : ∀ k, k ∈ S ↔ k < m ∧ P k) (hS' : ∀ k, k ∈ S' ↔ k < m ∧ Q k)
    (hPQ : ∀ k', k' < m - 1 → (Q k' ↔ P (rho r k'))) (hPr : ¬ P r) (hQ : ¬ Q (m - 1)) :
    S'.card = S.card := by
  apply Finset.card_bij (fun k' _ => rho r k')
  · intro k' hk'
    rw [hS'] at hk'
    rw [hS]
    have hlt : k' < m - 1 := by
      rcases Nat.lt_or_ge k' (m - 1) with h | h
      · exact h
      · have hk'' : k' = m - 1 := by omega
        rw [hk''] at hk'
        exact absurd hk'.2 hQ
    exact ⟨rho_lt r k' m hr hlt, (hPQ k' hlt).mp hk'.2⟩
  · intro a _ b _ h
    exact rho_inj r h
  · intro k hk
    rw [hS] at hk
    have hne : k ≠ r := fun h => hPr (h ▸ hk.2)
    obtain ⟨k', hk'1, hk'2⟩ := rho_surj r k m hr hk.1 hne
    refine ⟨k', ?_, hk'2⟩
    rw [hS']
    exact ⟨by omega, (hPQ k' hk'1).mpr (hk'2 ▸ hk.2)⟩

lemma junk_eq (n : ℕ) (C C' : Circuit) (F : (Fin n → Bool) → Bool) (r : ℕ)
    (hr : r < C.gates.length)
    (hlen : C'.gates.length = C.gates.length)
    (hops : ∀ k', k' < C.gates.length - 1 → (gateAt C' k').op = (gateAt C (rho r k')).op)
    (htop : (gateAt C' (C.gates.length - 1)).op = GateOp.or)
    (hopr : (gateAt C r).op = GateOp.or)
    (hbelow : ∀ k', k' < C.gates.length - 1 →
        ((∀ x, wv n C' x (n + k') = true → F x = true) ↔
          (∀ x, wv n C x (n + rho r k') = true → F x = true)))
    (S S' : Finset ℕ)
    (hS : ∀ k, k ∈ S ↔ k < C.gates.length ∧ (gateAt C k).op = GateOp.and ∧
      ¬ ∀ x, wv n C x (n + k) = true → F x = true)
    (hS' : ∀ k, k ∈ S' ↔ k < C'.gates.length ∧ (gateAt C' k).op = GateOp.and ∧
      ¬ ∀ x, wv n C' x (n + k) = true → F x = true) :
    S'.card = S.card := by
  rw [hlen] at hS'
  apply card_mem_rho C.gates.length r hr _ _ S S' hS hS'
  · intro k' hk'
    rw [hops k' hk', hbelow k' hk']
  · rintro ⟨h, _⟩
    rw [hopr] at h
    exact absurd h (by simp)
  · rintro ⟨h, _⟩
    rw [htop] at h
    exact absurd h (by simp)

lemma gateAt_mem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  unfold gateAt
  rw [List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem hj

lemma mem_gateAt (C : Circuit) (g : Gate) (hg : g ∈ C.gates) :
    ∃ j, j < C.gates.length ∧ gateAt C j = g := by
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
  exact ⟨j, hj, by unfold gateAt; rw [List.getD_eq_getElem _ _ hj]⟩

lemma ao2_of (n : ℕ) (C : Circuit) (h : PEqualNP.TopForm.IsAO2 n C) : AO2 n C := by
  obtain ⟨h1, h2, h3⟩ := h
  intro j hj
  have hm := gateAt_mem C j hj
  exact ⟨h1 _ hm, List.length_eq_two.mp (h3 _ hm), h2 j hj⟩

lemma ao2_to (n : ℕ) (C : Circuit) (h : AO2 n C) : PEqualNP.TopForm.IsAO2 n C := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨j, hj, rfl⟩ := mem_gateAt C g hg
    exact (h j hj).1
  · intro j hj
    exact (h j hj).2.2
  · intro g hg
    obtain ⟨j, hj, rfl⟩ := mem_gateAt C g hg
    obtain ⟨a, b, hab⟩ := (h j hj).2.1
    rw [hab]
    rfl

lemma least_glue (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : PEqualNP.TopForm.IsLeastAO G C) :
    Least n C ∧ ∀ x, wv n C x C.output = graphFun G ∅ x := by
  obtain ⟨h1, h2, h3⟩ := hL
  have hF : ∀ x, wv n C x C.output = graphFun G ∅ x := fun x => congrFun h2 x
  refine ⟨⟨ao2_of n C h1, ?_⟩, hF⟩
  intro D hD hDf
  exact h3 D (ao2_to n D hD) (funext fun x => (hDf x).trans (hF x))

lemma least_glue' (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : Least n C) (hF : ∀ x, wv n C x C.output = graphFun G ∅ x) :
    PEqualNP.TopForm.IsLeastAO G C := by
  refine ⟨ao2_to n C hL.1, funext hF, ?_⟩
  intro D hD hDf
  exact hL.2 D (ao2_of n D hD) (fun x => (congrFun hDf x).trans (hF x).symm)

lemma exists_true (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : G.edgeFinset.Nonempty) : ∃ x : Fin n → Bool, graphFun G ∅ x = true := by
  refine ⟨fun _ => true, ?_⟩
  obtain ⟨e, he⟩ := hG
  rw [SimpleGraph.mem_edgeFinset] at he
  revert he
  refine Sym2.inductionOn e ?_
  intro u v he
  have hadj : G.Adj u v := he
  unfold graphFun
  have hd : decide (∃ u v, G.Adj u v ∧ (fun _ : Fin n => true) u = true ∧
      (fun _ : Fin n => true) v = true) = true := decide_eq_true ⟨u, v, hadj, rfl, rfl⟩
  rw [hd]
  simp

lemma mem_junk (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (k : ℕ) :
    k ∈ PEqualNP.TopForm.junk G C ↔ k < C.gates.length ∧ (gateAt C k).op = GateOp.and ∧
      ¬ ∀ x, wv n C x (n + k) = true → graphFun G ∅ x = true := by
  unfold PEqualNP.TopForm.junk PEqualNP.TopForm.gatesWhere
  rw [Finset.mem_filter, Finset.mem_range]
  unfold PEqualNP.CleanedNonEdge.IsDirtyAnd PEqualNP.CleanedNonEdge.IsDirty
  constructor
  · rintro ⟨h1, h2, _, x, hx1, hx2⟩
    refine ⟨h1, h2, fun h => ?_⟩
    have h3 := h x hx1
    rw [hx2] at h3
    exact absurd h3 (by simp)
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, h1, ?_⟩
    by_contra hne
    apply h3
    intro x hx
    by_contra hF
    exact hne ⟨x, hx, by simpa using hF⟩

open Classical in
lemma main_ind (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : G.edgeFinset.Nonempty) :
    ∀ k : ℕ, ∀ C : Circuit, PEqualNP.TopForm.IsLeastAO G C →
      ((Finset.range C.gates.length ×ˢ Finset.range C.gates.length).filter
        (fun p : ℕ × ℕ => (gateAt C p.1).op = GateOp.and ∧
          (gateAt C p.2).op = GateOp.and ∧ InCone n C p.1 p.2)).card = k →
      ∃ C' : Circuit, PEqualNP.TopForm.IsLeastAO G C' ∧ C'.size = C.size ∧
        (PEqualNP.TopForm.junk G C').card = (PEqualNP.TopForm.junk G C).card ∧
        PEqualNP.TopForm.TopForm G C' := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro C hC hk
    by_cases htop : PEqualNP.TopForm.TopForm G C
    · exact ⟨C, hC, rfl, rfl, htop⟩
    · have hex : ∃ i j, i < C.gates.length ∧ j < C.gates.length ∧
          (gateAt C i).op = GateOp.and ∧ PEqualNP.TopForm.BelowF G C i ∧
          (gateAt C j).op = GateOp.and ∧ InCone n C i j := by
        by_contra hne
        apply htop
        intro i hi j hj h1 h2 h3 h4
        exact hne ⟨i, j, hi, hj, h1, h2, h3, h4⟩
      obtain ⟨i, j, hi, hj, hopi, hbi, hopj, hcone⟩ := hex
      obtain ⟨hL, hF⟩ := least_glue n G C hC
      obtain ⟨x1, hx1⟩ := exists_true n G hG
      have hout : C.output < n + C.gates.length := out_lt n C x1 (by rw [hF]; exact hx1)
      obtain ⟨C', r, hr, hir, hL', hF', hlen, hops, htop', hopr, hbelow, hcn, hno⟩ :=
        step3_struct n C (graphFun G ∅) hL hF hout i j hbi hcone
      have hlt := pairs_lt n C C' r i j hr hir hlen hops htop' hcn hno hopi hopj hcone
      rw [hk] at hlt
      obtain ⟨C'', h1, h2, h3, h4⟩ := ih _ hlt C' (least_glue' n G C' hL' hF') rfl
      refine ⟨C'', h1, h2.trans hlen, h3.trans ?_, h4⟩
      refine junk_eq n C C' (graphFun G ∅) r hr hlen hops htop' hopr hbelow _ _ ?_ ?_
      · intro k
        exact mem_junk n G C k
      · intro k
        exact mem_junk n G C' k

end Part3

theorem Part3 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
  G.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO G C →
    ∃ C' : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsLeastAO G C' ∧ C'.size = C.size ∧
      (PEqualNP.TopForm.junk G C').card = (PEqualNP.TopForm.junk G C).card ∧ PEqualNP.TopForm.TopForm G C' := by
  intro n G _ C hG hC
  exact PEqualNP.Outside.L_meta_8323.Part3.main_ind n G hG _ C hC rfl

end PEqualNP.Outside.L_meta_8323

-- Source module: Pnp4201CleanOrCount
namespace PEqualNP.Outside.L_meta_8323

namespace Part4

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.CleanedNonEdge PEqualNP.TopForm
open PEqualNP.Outside.L_meta_8323.Part2

lemma disjoint_or_count (C : Circuit) (A B : Set ℕ)
    (hA : A ⊆ {i | i < C.gates.length ∧ (gateAt C i).op = GateOp.or})
    (hB : B ⊆ {i | i < C.gates.length ∧ (gateAt C i).op = GateOp.or})
    (hd : ∀ i ∈ A, i ∉ B) :
    A.ncard + B.ncard ≤ Set.ncard {i | i < C.gates.length ∧ (gateAt C i).op = GateOp.or} := by
  have hfin : Set.Finite {i | i < C.gates.length ∧ (gateAt C i).op = GateOp.or} :=
    (Set.finite_lt_nat C.gates.length).subset (fun _ hi => hi.1)
  have hdis : Disjoint A B := Set.disjoint_left.mpr hd
  rw [← Set.ncard_union_eq hdis (hfin.subset hA) (hfin.subset hB)]
  exact Set.ncard_le_ncard (Set.union_subset hA hB) hfin

theorem or_count_core (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (E : Finset (Fin n × Fin n))
    (hlt : ∀ e ∈ E, e.1 < e.2)
    (h30 : ∀ e ∈ E, ∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧
      OrReaches n C C.output j ∧
      ((e.1 ∈ side (n := n) C j 0 ∧ e.2 ∈ side (n := n) C j 1) ∨
        (e.2 ∈ side (n := n) C j 0 ∧ e.1 ∈ side (n := n) C j 1)))
    (h31a : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → OrReaches n C C.output j →
      (∀ w : Fin n, w ∈ side (n := n) C j 0 → w ∉ side (n := n) C j 1) ∧
      (∀ u : Fin n, u ∈ side (n := n) C j 0 → ∀ v : Fin n, v ∈ side (n := n) C j 1 → G.Adj u v) ∧
      ((side (n := n) C j 0).card ≤ 1 ∨ (side (n := n) C j 1).card ≤ 1))
    (h33 : ∀ F : Finset ℕ, (∀ j ∈ F, j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧
        OrReaches n C C.output j) →
      F.card ≤ Set.ncard {i : ℕ | i < C.gates.length ∧ (gateAt C i).op = GateOp.or ∧
        OrReaches n C C.output i} + 1)
    (h34 : ∀ (F : Finset ℕ) (ctr : ℕ → Fin n) (lf : ℕ → ℕ),
      (∀ j ∈ F, ∀ b : Fin n, b ∈ orIn n C (lf j) → G.Adj (ctr j) b) →
      (∀ i < C.gates.length, (gateAt C i).op = GateOp.or → 2 ≤ (orIn n C (n + i)).card →
        (∃ j1 ∈ F, OrReaches n C (lf j1) i) → ¬ OrReaches n C C.output i) ∧
      ∑ c : Fin n, (Finset.univ.filter (fun b2 : Fin n =>
        ∃ j2 ∈ F, ctr j2 = c ∧ b2 ∈ orIn n C (lf j2))).card ≤
        Set.ncard {i2 : ℕ | i2 < C.gates.length ∧ (gateAt C i2).op = GateOp.or ∧
          2 ≤ (orIn n C (n + i2)).card ∧ ∃ j3 ∈ F, OrReaches n C (lf j3) i2} + F.card) :
    E.card ≤ Set.ncard {i : ℕ | i < C.gates.length ∧ (gateAt C i).op = GateOp.or} + 1 := by
  classical
  by_cases hE : E = ∅
  · subst hE
    simp
  obtain ⟨e0, he0⟩ := Finset.nonempty_iff_ne_empty.mpr hE
  obtain ⟨F, hF⟩ : ∃ F : Finset ℕ, ∀ j, j ∈ F ↔ (j < C.gates.length ∧
      (gateAt C j).op = GateOp.and ∧ OrReaches n C C.output j ∧
      (side (n := n) C j 0).Nonempty ∧ (side (n := n) C j 1).Nonempty) :=
    ⟨(Finset.range C.gates.length).filter (fun j => (gateAt C j).op = GateOp.and ∧
      OrReaches n C C.output j ∧
      (side (n := n) C j 0).Nonempty ∧ (side (n := n) C j 1).Nonempty),
      fun j => by rw [Finset.mem_filter, Finset.mem_range]⟩
  have hper : ∀ j : ℕ, ∃ (c : Fin n) (l : ℕ), j ∈ F →
      (∀ b : Fin n, b ∈ orIn n C l → G.Adj c b) ∧
      (∀ u : Fin n, u ∈ side (n := n) C j 0 → ∀ v : Fin n, v ∈ side (n := n) C j 1 →
        (c = u ∧ v ∈ orIn n C l) ∨ (c = v ∧ u ∈ orIn n C l)) := by
    intro j
    by_cases hj : j ∈ F
    · obtain ⟨hjl, hand, hor, hn0, hn1⟩ := (hF j).mp hj
      obtain ⟨hdis, hadj, hcard⟩ := h31a j hjl hand hor
      rcases hcard with hc | hc
      · obtain ⟨c, hc0⟩ := hn0
        refine ⟨c, opnd C j 1, fun _ => ⟨?_, ?_⟩⟩
        · intro b hb
          exact hadj c hc0 b hb
        · intro u hu v hv
          exact Or.inl ⟨Finset.card_le_one.mp hc c hc0 u hu, hv⟩
      · obtain ⟨c, hc1⟩ := hn1
        refine ⟨c, opnd C j 0, fun _ => ⟨?_, ?_⟩⟩
        · intro b hb
          exact (hadj b hb c hc1).symm
        · intro u hu v hv
          exact Or.inr ⟨Finset.card_le_one.mp hc c hc1 v hv, hu⟩
    · exact ⟨e0.1, 0, fun h => absurd h hj⟩
  choose ctr lf hcl using hper
  have hw : ∀ e ∈ E, ∃ i ∈ F, i < C.gates.length ∧
      (gateAt C i).op = GateOp.and ∧ OrReaches n C C.output i ∧
      ((e.1 ∈ side (n := n) C i 0 ∧ e.2 ∈ side (n := n) C i 1) ∨
        (e.2 ∈ side (n := n) C i 0 ∧ e.1 ∈ side (n := n) C i 1)) := by
    intro e he
    obtain ⟨j, hjl, hand, hor, hs⟩ := h30 e he
    refine ⟨j, (hF j).mpr ⟨hjl, hand, hor, ?_, ?_⟩, hjl, hand, hor, hs⟩
    · rcases hs with hs | hs
      · exact ⟨e.1, hs.1⟩
      · exact ⟨e.2, hs.1⟩
    · rcases hs with hs | hs
      · exact ⟨e.2, hs.2⟩
      · exact ⟨e.1, hs.2⟩
  have hFand : ∀ j ∈ F, j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧
      OrReaches n C C.output j := by
    intro j hj
    obtain ⟨ha, hb, hc, _⟩ := (hF j).mp hj
    exact ⟨ha, hb, hc⟩
  have h3 := h33 F hFand
  obtain ⟨h4a, h4b⟩ := h34 F ctr lf (fun j hj => (hcl j hj).1)
  have hEsum := le_trans (sum_card_ge E (fun c => Finset.univ.filter (fun b2 : Fin n =>
      ∃ j2 ∈ F, ctr j2 = c ∧ b2 ∈ orIn n C (lf j2))) hlt (by
    intro e he
    obtain ⟨j, hjF, _, _, _, hs⟩ := hw e he
    rcases hs with hs | hs
    · rcases (hcl j hjF).2 e.1 hs.1 e.2 hs.2 with h | h
      · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, hjF, h.1, h.2⟩)
      · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, hjF, h.1, h.2⟩)
    · rcases (hcl j hjF).2 e.2 hs.1 e.1 hs.2 with h | h
      · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, hjF, h.1, h.2⟩)
      · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, hjF, h.1, h.2⟩))) h4b
  have hcount := disjoint_or_count C
    {i : ℕ | i < C.gates.length ∧ (gateAt C i).op = GateOp.or ∧ OrReaches n C C.output i}
    {i : ℕ | i < C.gates.length ∧ (gateAt C i).op = GateOp.or ∧
      2 ≤ (orIn n C (n + i)).card ∧ ∃ j ∈ F, OrReaches n C (lf j) i}
    (fun _ hi => ⟨hi.1, hi.2.1⟩) (fun _ hi => ⟨hi.1, hi.2.1⟩)
    (fun i hi hiB => h4a i hi.1 hi.2.1 hiB.2.2.1 hiB.2.2.2 hi.2.2)
  omega

theorem or_bound_of_edge_witness (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (E : Finset (Fin n × Fin n))
    (h4 : NoFourCycle G) (hAO : IsAO2 n C)
    (h1 : ∀ a : Fin n, circuitFun n C (fun k => decide (k = a)) = false)
    (h2 : ∀ a b : Fin n, a ≠ b → ¬ G.Adj a b →
      circuitFun n C (fun k => decide (k = a ∨ k = b)) = false)
    (hlt : ∀ e ∈ E, e.1 < e.2)
    (hedge : ∀ e ∈ E, ∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧
      OrReaches n C C.output j ∧
      ((e.1 ∈ side (n := n) C j 0 ∧ e.2 ∈ side (n := n) C j 1) ∨
        (e.2 ∈ side (n := n) C j 0 ∧ e.1 ∈ side (n := n) C j 1))) :
    E.card ≤ Set.ncard {i : ℕ | i < C.gates.length ∧ (gateAt C i).op = GateOp.or} + 1 := by
  exact or_count_core n G C E hlt hedge (s2231 n G C h4 hAO h1 h2).1
    (fun F => s2233 n C F hAO) (fun F ctr lf => s2234 n G C F ctr lf h4 hAO h1)

open PEqualNP.EdgeOwnership PEqualNP.Outside.L_meta_8323.Part3

lemma fire_trace (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (x : Fin n → Bool) :
    ∀ w : ℕ, wv n C x w = true →
      (∃ u ∈ orIn n C w, x u = true) ∨
      ∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧
        OrReaches n C w j ∧ gateVal n C j x = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hwn : w < n
    · left
      refine ⟨⟨w, hwn⟩, (s2234_qmem_orIn n C w _).mpr (Or.inl rfl), ?_⟩
      simpa only [wv_input n C x w hwn] using hw
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < C.gates.length := by
        have hl := out_lt n { C with output := n + j } x hw
        simpa using (show j < C.gates.length by simpa using hl)
      have haob := aob (ao2_of n C hAO)
      rcases (haob j hj).1 with hop | hop
      · exact Or.inr ⟨j, hj, hop, s2234_qreach_self n C j hj, hw⟩
      · rw [wv_rec n C x haob j hj, hop] at hw
        simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq] at hw
        obtain ⟨r, hr, hv⟩ := hw
        have hrlt := (haob j hj).2 r hr
        rcases ih r hrlt hv with ⟨u, hu, hxu⟩ | ⟨k, hk, hka, hkr, hkv⟩
        · exact Or.inl ⟨u, s2230_orIn_up n C j r u hj hop hr hrlt hu, hxu⟩
        · exact Or.inr ⟨k, hk, hka, s2230_orReaches_step n C j r k hj hop hr hrlt hkr, hkv⟩

lemma or_reach_cone (n : ℕ) (C : Circuit) (g : ℕ) :
    ∀ j : ℕ, j < C.gates.length → OrReaches n C (n + j) g → g = j ∨ InCone n C g j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj hr
    rcases (s2234_qreach_iff n C j g hj).mp hr with heq | ⟨_, w, hw, hwlt, hwr⟩
    · exact Or.inl heq
    · have hwn : n ≤ w := hwr.1
      have hk : w - n < j := by omega
      have he : n + (w - n) = w := by omega
      have hki := ih (w - n) hk (by omega) (by rwa [he])
      right
      apply (inCone_iff n C g j).mpr
      exact ⟨hj, w - n, hk, by rwa [he], hki⟩

lemma or_reach_into_input (n : ℕ) (C : Circuit) (j w g : ℕ)
    (hj : j < C.gates.length) (hw : w ∈ (gateAt C j).inputs) (hwlt : w < n + j)
    (hr : OrReaches n C w g) : InCone n C g j := by
  have hwn : n ≤ w := hr.1
  have hk : w - n < j := by omega
  have he : n + (w - n) = w := by omega
  exact (inCone_iff n C g j).mpr ⟨hj, w - n, hk, by rwa [he],
    or_reach_cone n C g (w - n) (by omega) (by rwa [he])⟩

lemma clean_top_operand (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (htop : TopForm G C)
    (hclean : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → BelowF G C j)
    (j : ℕ) (hj : j < C.gates.length) (hja : (gateAt C j).op = GateOp.and)
    (w : ℕ) (hw : w ∈ (gateAt C j).inputs) (x : Fin n → Bool)
    (hv : wv n C x w = true) : ∃ u ∈ orIn n C w, x u = true := by
  rcases fire_trace n C hAO x w hv with h | ⟨k, hk, hka, hr, _⟩
  · exact h
  · exact False.elim (htop k hk j hj hka (hclean k hk hka) hja
      (or_reach_into_input n C j w k hj hw (hAO.2.1 j hj w hw) hr))

theorem clean_top_edge_witness (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (h4 : NoFourCycle G)
    (h1 : ∀ a : Fin n, circuitFun n C (fun k => decide (k = a)) = false)
    (h2 : ∀ a b : Fin n, a ≠ b → ¬ G.Adj a b →
      circuitFun n C (fun k => decide (k = a ∨ k = b)) = false)
    (htop : TopForm G C)
    (hclean : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → BelowF G C j)
    (a b : Fin n) (hout : circuitFun n C (pairInput a b) = true) :
    ∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧ OrReaches n C C.output j ∧
      ((a ∈ side (n := n) C j 0 ∧ b ∈ side (n := n) C j 1) ∨
        (b ∈ side (n := n) C j 0 ∧ a ∈ side (n := n) C j 1)) := by
  rcases fire_trace n C hAO (pairInput a b) C.output hout with
    ⟨u, hu, _⟩ | ⟨j, hj, hja, hreach, hjval⟩
  · have hon := s2234_qval_orIn n C C.output u hu
    have hoff := h1 u
    change circuitFun n C (fun k => decide (k = u)) = true at hon
    rw [hoff] at hon
    cases hon
  · have hgm : gateAt C j ∈ C.gates := gateAt_mem C j hj
    obtain ⟨r, s, hrs⟩ := List.length_eq_two.mp (hAO.2.2 _ hgm)
    have hr : r ∈ (gateAt C j).inputs := by rw [hrs]; simp
    have hs : s ∈ (gateAt C j).inputs := by rw [hrs]; simp
    have hrval : wv n C (pairInput a b) r = true ∧ wv n C (pairInput a b) s = true := by
      change wv n C (pairInput a b) (n + j) = true at hjval
      rw [wv_rec n C _ (aob (ao2_of n C hAO)) j hj, hja, hrs] at hjval
      simpa [GateOp.eval] using hjval
    obtain ⟨u, hu, hxu⟩ := clean_top_operand n G C hAO htop hclean j hj hja r hr _ hrval.1
    obtain ⟨v, hv, hxv⟩ := clean_top_operand n G C hAO htop hclean j hj hja s hs _ hrval.2
    have e0 : opnd C j 0 = r := by simp [opnd, hrs]
    have e1 : opnd C j 1 = s := by simp [opnd, hrs]
    have hu0 : u ∈ side (n := n) C j 0 := by simpa only [side, e0] using hu
    have hv1 : v ∈ side (n := n) C j 1 := by simpa only [side, e1] using hv
    have huv : u ≠ v := by
      intro he
      subst v
      exact (s2231 n G C h4 hAO h1 h2).1 j hj hja hreach |>.1 u hu0 hv1
    have hua : u = a ∨ u = b := by simpa only [pairInput, decide_eq_true_eq] using hxu
    have hva : v = a ∨ v = b := by simpa only [pairInput, decide_eq_true_eq] using hxv
    refine ⟨j, hj, hja, hreach, ?_⟩
    rcases hua with rfl | rfl <;> rcases hva with rfl | rfl
    · exact False.elim (huv rfl)
    · exact Or.inl ⟨hu0, hv1⟩
    · exact Or.inr ⟨hu0, hv1⟩
    · exact False.elim (huv rfl)

lemma graph_unit_false (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a : Fin n) : graphFun G ∅ (fun k => decide (k = a)) = false := by
  simp [graphFun]

lemma graph_pair_false (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a b : Fin n) (hab : ¬ G.Adj a b) : graphFun G ∅ (pairInput a b) = false := by
  have hn : ¬ ∃ u v : Fin n, G.Adj u v ∧ pairInput a b u = true ∧ pairInput a b v = true := by
    rintro ⟨u, v, huv, hu, hv⟩
    have hu' : u = a ∨ u = b := by simpa only [pairInput, decide_eq_true_eq] using hu
    have hv' : v = a ∨ v = b := by simpa only [pairInput, decide_eq_true_eq] using hv
    rcases hu' with rfl | rfl <;> rcases hv' with rfl | rfl
    · exact G.irrefl huv
    · exact hab huv
    · exact hab huv.symm
    · exact G.irrefl huv
  simp [graphFun, hn]

lemma or_indices_eq_countP (C : Circuit) :
    Set.ncard {i : ℕ | i < C.gates.length ∧ (gateAt C i).op = GateOp.or} =
      C.gates.countP (fun g => GateOp.casesOn g.op false true false (fun _ => false) false) := by
  classical
  have hS : {i : ℕ | i < C.gates.length ∧ (gateAt C i).op = GateOp.or} =
      (↑((Finset.range C.gates.length).filter fun i => (gateAt C i).op = GateOp.or) : Set ℕ) := by
    ext i
    simp
  rw [hS, Set.ncard_coe_finset]
  have hmap : (List.range C.gates.length).map (gateAt C) = C.gates := by
    apply List.ext_getElem
    · simp
    · intro i hi hi'
      rw [List.getElem_map, List.getElem_range]
      exact s2231_gateAt_eq C i hi'
  have hc : ((Finset.range C.gates.length).filter fun i => (gateAt C i).op = GateOp.or).card =
      ((List.range C.gates.length).map (gateAt C)).countP (fun g => decide (g.op = GateOp.or)) := by
    simpa only [List.countP_map, Function.comp_def, List.toFinset_range] using
      (List.Nodup.card_eq_countP (P := fun i => (gateAt C i).op = GateOp.or)
        (List.nodup_range (n := C.gates.length)))
  rw [hmap] at hc
  rw [hc]
  congr 1
  funext g
  cases g.op <;> simp

theorem clean_top_or_bound (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (h4 : NoFourCycle G)
    (hf : circuitFun n C = graphFun G ∅) (htop : TopForm G C)
    (hclean : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → BelowF G C j) :
    (Finset.univ.filter (fun e : Fin n × Fin n => e.1 < e.2 ∧ G.Adj e.1 e.2)).card ≤
      C.gates.countP (fun g => GateOp.casesOn g.op false true false (fun _ => false) false) + 1 := by
  have h1 : ∀ a : Fin n, circuitFun n C (fun k => decide (k = a)) = false := by
    intro a
    rw [hf]
    exact graph_unit_false n G a
  have h2 : ∀ a b : Fin n, a ≠ b → ¬ G.Adj a b →
      circuitFun n C (fun k => decide (k = a ∨ k = b)) = false := by
    intro a b _ hab
    rw [hf]
    exact graph_pair_false n G a b hab
  have hcount := or_bound_of_edge_witness n G C
    (Finset.univ.filter (fun e : Fin n × Fin n => e.1 < e.2 ∧ G.Adj e.1 e.2))
    h4 hAO h1 h2 (fun e he => (Finset.mem_filter.mp he).2.1) (by
      intro e he
      apply clean_top_edge_witness n G C hAO h4 h1 h2 htop hclean e.1 e.2
      rw [hf]
      apply Bool.or_eq_true_iff.mpr
      right
      exact decide_eq_true ⟨e.1, e.2, (Finset.mem_filter.mp he).2.2,
        by simp [pairInput], by simp [pairInput]⟩)
  rwa [or_indices_eq_countP] at hcount

end Part4

end PEqualNP.Outside.L_meta_8323

-- Source module: Pnp2343Pruning
namespace PEqualNP.Outside.L_meta_8323

namespace Part5

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt2 (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
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
      rw [Nat.add_zero, foldl_getD_lt2 gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt2 gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
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

lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  exact List.getD_eq_getElem _ _ hj

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt2 _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

def OpMono (R : Bool → Bool → Prop) : Prop :=
  ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
    (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

lemma opMono_eq : OpMono Eq := by
  intro op _ l f g h
  rw [List.map_congr_left h]

lemma opMono_imp : OpMono (fun a b => a = true → b = true) := by
  intro op hop l f g h
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro h1 i hi; exact h i hi (h1 i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [ite_eq_right hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [ite_eq_left hlt]; exact h⟩

lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h'; exact ⟨hlt, h'⟩
    · rw [ite_eq_right hlt] at h'; cases h'
  · intro h i hi
    rw [ite_eq_left (h i hi).1]; exact (h i hi).2

lemma val_prefix {n : ℕ} {C D : Circuit} {x : List Bool} (hx : x.length = n) {m : ℕ}
    (hmC : m ≤ C.gates.length) (hmD : m ≤ D.gates.length)
    (hg : ∀ k < m, gateAt D k = gateAt C k) : ∀ u, u < n + m → val D x u = val C x u := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hu
    by_cases hun : u < n
    · rw [val_input hx hun, val_input hx hun]
    · obtain ⟨k, rfl⟩ : ∃ k, u = n + k := ⟨u - n, by omega⟩
      have hk : k < m := by omega
      rw [val_gate hx (by omega), val_gate hx (by omega), hg k hk]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < n + k
      · rw [ite_eq_left hi, ite_eq_left hi]; exact ih i hi (by omega)
      · rw [ite_eq_right hi, ite_eq_right hi]

def aliasWire (w i u : ℕ) : ℕ := if u = w then i else if w < u then u - 1 else u

def aliasGate (w i : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (aliasWire w i)⟩

def bypass (n : ℕ) (C : Circuit) (r i : ℕ) : Circuit :=
  ⟨(List.range (C.gates.length - 1)).map (fun k =>
      if k < r then gateAt C k else aliasGate (n + r) i (gateAt C (k + 1))),
    aliasWire (n + r) i C.output⟩

lemma bypass_length (n : ℕ) (C : Circuit) (r i : ℕ) :
    (bypass n C r i).gates.length = C.gates.length - 1 := by simp [bypass]

lemma bypass_output (n : ℕ) (C : Circuit) (r i : ℕ) :
    (bypass n C r i).output = aliasWire (n + r) i C.output := rfl

lemma gateAt_bypass {n : ℕ} {C : Circuit} {r i k : ℕ} (hk : k < C.gates.length - 1) :
    gateAt (bypass n C r i) k =
      if k < r then gateAt C k else aliasGate (n + r) i (gateAt C (k + 1)) := by
  have hk' : k < (bypass n C r i).gates.length := by rw [bypass_length]; exact hk
  rw [gateAt_eq hk']
  simp [bypass]

lemma bypass_val_lt {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r i : ℕ}
    (hr : r < C.gates.length) : ∀ u, u < n + r → val (bypass n C r i) x u = val C x u := by
  apply val_prefix hx (by omega) (by rw [bypass_length]; omega)
  intro k hk
  rw [gateAt_bypass (by omega), ite_eq_left hk]

lemma aliasWire_self (w i : ℕ) : aliasWire w i w = i := by simp [aliasWire]

lemma aliasWire_lt_self {w i u : ℕ} (hu : u < w) : aliasWire w i u = u := by
  unfold aliasWire; rw [ite_eq_right (by omega), ite_eq_right (by omega)]

lemma aliasWire_gt_self {w i u : ℕ} (hu : w < u) : aliasWire w i u = u - 1 := by
  unfold aliasWire; rw [ite_eq_right (by omega), ite_eq_left hu]

lemma bypass_rel {R : Bool → Bool → Prop} (hrefl : ∀ b, R b b) (hmono : OpMono R)
    {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
    {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
    (hR : (∃ k, r < k ∧ k < C.gates.length ∧ n + r ∈ (gateAt C k).inputs) →
      R (val C x (n + r)) (val C x i)) :
    ∀ u, u ≠ n + r → R (val C x u) (val (bypass n C r i) x (aliasWire (n + r) i u)) := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hne
    by_cases hlt : u < n + r
    · rw [aliasWire_lt_self hlt, bypass_val_lt hx hr u hlt]; exact hrefl _
    · rw [aliasWire_gt_self (by omega)]
      by_cases hge : n + C.gates.length ≤ u
      · rw [val_ge hx hge, val_ge hx (by rw [bypass_length]; omega)]; exact hrefl _
      · obtain ⟨k, rfl⟩ : ∃ k, u = n + (k + 1) := ⟨u - n - 1, by omega⟩
        have hk1 : k + 1 < C.gates.length := by omega
        have hkr : ¬ k < r := by omega
        have e : n + (k + 1) - 1 = n + k := by omega
        rw [e, val_gate hx hk1, val_gate hx (by rw [bypass_length]; omega),
          gateAt_bypass (by omega), ite_eq_right hkr]
        simp only [aliasGate, List.map_map]
        refine hmono _ (hAO _ hk1) _ _ _ ?_
        intro i' hi'
        simp only [Function.comp_apply]
        by_cases h1 : i' = n + r
        · subst h1
          rw [aliasWire_self, ite_eq_left (by omega)]
          have hgi : (if i < n + k then val (bypass n C r i) x i else false) = val C x i := by
            rcases hi with hi | hi
            · rw [ite_eq_left (by omega), bypass_val_lt hx hr i hi]
            · rw [ite_eq_right (by omega), val_ge hx hi]
          rw [hgi]
          exact hR ⟨k + 1, by omega, hk1, hi'⟩
        · by_cases h2 : i' < n + r
          · rw [aliasWire_lt_self h2, ite_eq_left (by omega), ite_eq_left (by omega),
              bypass_val_lt hx hr i' h2]
            exact hrefl _
          · by_cases h3 : i' < n + (k + 1)
            · have key := ih i' h3 h1
              rw [aliasWire_gt_self (by omega)] at key
              rw [aliasWire_gt_self (by omega), ite_eq_left h3, ite_eq_left (by omega)]
              exact key
            · rw [aliasWire_gt_self (by omega), ite_eq_right h3, ite_eq_right (by omega)]
              exact hrefl _

lemma bypass_eval_rel {R : Bool → Bool → Prop} (hrefl : ∀ b, R b b) (hmono : OpMono R)
    {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
    {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
    (hR : R (val C x (n + r)) (val C x i)) :
    R (C.eval x) ((bypass n C r i).eval x) := by
  rw [eval_eq_val, eval_eq_val, bypass_output]
  by_cases h : C.output = n + r
  · have hgi : val (bypass n C r i) x i = val C x i := by
      rcases hi with hi | hi
      · exact bypass_val_lt hx hr i hi
      · rw [val_ge hx hi, val_ge hx (by rw [bypass_length]; omega)]
    rw [h, aliasWire_self, hgi]; exact hR
  · exact bypass_rel hrefl hmono hx hAO hr hi (fun _ => hR) _ h

lemma bypass_eval_eq {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
    {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
    (hR : val C x (n + r) = val C x i) :
    (bypass n C r i).eval x = C.eval x :=
  (bypass_eval_rel (R := Eq) (fun _ => rfl) opMono_eq hx hAO hr hi hR).symm

lemma bypass_eval_unread {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
    {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
    (hout : C.output ≠ n + r)
    (hno : ∀ k, r < k → k < C.gates.length → n + r ∉ (gateAt C k).inputs) :
    (bypass n C r i).eval x = C.eval x := by
  rw [eval_eq_val, eval_eq_val, bypass_output]
  exact (bypass_rel (R := Eq) (fun _ => rfl) opMono_eq hx hAO hr hi
    (fun ⟨k, hrk, hk, hm⟩ => absurd hm (hno k hrk hk)) _ hout).symm

lemma bypass_AO {n : ℕ} {C : Circuit} {r i : ℕ} (hr : r < C.gates.length)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) :
    ∀ k < (bypass n C r i).gates.length,
      (gateAt (bypass n C r i) k).op = GateOp.and ∨
        (gateAt (bypass n C r i) k).op = GateOp.or := by
  intro k hk
  rw [bypass_length] at hk
  rw [gateAt_bypass hk]
  split_ifs with h
  · exact hAO k (by omega)
  · exact hAO (k + 1) (by omega)

lemma bypass_mem {n : ℕ} {C : Circuit} {r i : ℕ} :
    ∀ g ∈ (bypass n C r i).gates, ∃ g' ∈ C.gates, g.op = g'.op ∧
      g.inputs.length = g'.inputs.length := by
  intro g hg
  simp only [bypass, List.mem_map, List.mem_range] at hg
  obtain ⟨k, hk, rfl⟩ := hg
  split_ifs with h
  · exact ⟨gateAt C k, gateAt_mem (by omega), rfl, rfl⟩
  · exact ⟨gateAt C (k + 1), gateAt_mem (by omega), rfl, by simp [aliasGate]⟩

lemma aliasWire_lt {w i u m : ℕ} (hi : i < w) (hwm : w ≤ m) (hu : u < m + 1) :
    aliasWire w i u < m := by
  unfold aliasWire; split_ifs <;> omega

lemma bypass_readsBack {n : ℕ} {C : Circuit} {r i : ℕ} (hi : i < n + r)
    (hRB : ∀ k < C.gates.length, ∀ u ∈ (gateAt C k).inputs, u < n + k) :
    ∀ k < (bypass n C r i).gates.length,
      ∀ u ∈ (gateAt (bypass n C r i) k).inputs, u < n + k := by
  intro k hk u hu
  rw [bypass_length] at hk
  rw [gateAt_bypass hk] at hu
  split_ifs at hu with h
  · exact hRB k (by omega) u hu
  · simp only [aliasGate, List.mem_map] at hu
    obtain ⟨u', hu', rfl⟩ := hu
    have := hRB (k + 1) (by omega) u' hu'
    exact aliasWire_lt hi (by omega) (by omega)

lemma erase_eq_bypass (n : ℕ) (C : Circuit) (r i : ℕ) (hr : r < C.gates.length) :
    PEqualNP.CircuitMoves.eraseGate n C r i = bypass n C r i := by
  unfold PEqualNP.CircuitMoves.eraseGate
  rw [ite_eq_left hr]
  change Circuit.mk _ (aliasWire (n + r) i C.output) = Circuit.mk _ (aliasWire (n + r) i C.output)
  congr 1
  apply List.ext_getElem
  · simp [bypass]; omega
  · intro k hk hk'
    have hlen : (C.gates.take r).length = r := by simp; omega
    have hklen : k < C.gates.length - 1 := by simpa using hk'
    simp only [List.getElem_map, List.getElem_range]
    by_cases hkr : k < r
    · rw [ite_eq_left hkr, List.getElem_append_left (by omega), List.getElem_take,
        gateAt_eq (by omega)]
    · rw [ite_eq_right hkr, List.getElem_append_right (by omega), List.getElem_map,
        List.getElem_drop]
      simp only [hlen]
      have he : r + 1 + (k - r) = k + 1 := by omega
      simp only [he]
      rw [gateAt_eq (by omega : k + 1 < C.gates.length)]
      rfl

lemma mono_ops {C : Circuit} (hM : Monotone2 C) :
    ∀ k < C.gates.length, (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or := by
  intro k hk
  exact (hM _ (gateAt_mem hk)).1

lemma wire_monotone (n : ℕ) (C : Circuit) (hM : Monotone2 C) (x y : Fin n → Bool)
    (hxy : ∀ i, x i = true → y i = true) :
    ∀ u, val C (List.ofFn x) u = true → val C (List.ofFn y) u = true := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    by_cases hun : u < n
    · rw [val_input (n := n) (by simp) hun, val_input (n := n) (by simp) hun]
      simpa [hun] using hxy ⟨u, hun⟩
    · by_cases hge : n + C.gates.length ≤ u
      · rw [val_ge (n := n) (by simp) hge]
        intro h; cases h
      · obtain ⟨k, rfl⟩ : ∃ k, u = n + k := ⟨u - n, by omega⟩
        have hk : k < C.gates.length := by omega
        rw [val_gate (n := n) (by simp) hk, val_gate (n := n) (by simp) hk]
        apply opMono_imp _ (mono_ops hM k hk)
        intro i hi
        by_cases hil : i < n + k
        · rw [ite_eq_left hil, ite_eq_left hil]
          exact ih i hil
        · rw [ite_eq_right hil, ite_eq_right hil]
          exact id

lemma circuit_monotone (n : ℕ) (C : Circuit) (hM : Monotone2 C) (x y : Fin n → Bool)
    (hxy : ∀ i, x i = true → y i = true) : C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true :=
  wire_monotone n C hM x y hxy C.output

lemma opMono_reverse : OpMono (fun a b => b = true → a = true) := by
  intro op hop l f g h
  exact opMono_imp op hop l g f h

lemma bypass_mono {n : ℕ} {C : Circuit} {r i : ℕ} (hM : Monotone2 C) :
    Monotone2 (bypass n C r i) := by
  intro g hg
  obtain ⟨g', hg', hop, hlen⟩ := bypass_mem g hg
  rw [hop, hlen]
  exact hM g' hg'

def Fits {α β : Type} (positive : α → List Bool) (negative : β → List Bool) (C : Circuit) : Prop :=
  (∀ p, C.eval (positive p) = true) ∧ ∀ q, C.eval (negative q) = false

def LeastSamples {α β : Type} (n : ℕ) (positive : α → List Bool)
    (negative : β → List Bool) (C : Circuit) : Prop :=
  Monotone2 C ∧ ReadsBack n C ∧ Fits positive negative C ∧
    ∀ D : Circuit, Monotone2 D → ReadsBack n D → Fits positive negative D → C.size ≤ D.size

lemma bypass_samples {α β : Type} (n : ℕ) (positive : α → List Bool) (negative : β → List Bool)
    (hpLen : ∀ p, (positive p).length = n) (hnLen : ∀ q, (negative q).length = n)
    (C : Circuit) (hM : Monotone2 C) (hF : Fits positive negative C)
    (r i : ℕ) (hr : r < C.gates.length) (hi : i < n + r)
    (hp : ∀ p, val C (positive p) (n + r) = true → val C (positive p) i = true)
    (hn : ∀ q, val C (negative q) i = true → val C (negative q) (n + r) = true) :
    Fits positive negative (bypass n C r i) := by
  constructor
  · intro p
    exact bypass_eval_rel (R := fun a b => a = true → b = true) (fun _ => id) opMono_imp
      (hpLen p) (mono_ops hM) hr (Or.inl hi) (hp p) (hF.1 p)
  · intro q
    cases he : (bypass n C r i).eval (negative q) with
    | false => rfl
    | true =>
      have hc := bypass_eval_rel (R := fun a b => b = true → a = true) (fun _ => id) opMono_reverse
        (hnLen q) (mono_ops hM) hr (Or.inl hi) (hn q) he
      rw [hF.2 q] at hc
      cases hc

lemma erase_samples {α β : Type} (n : ℕ) (positive : α → List Bool) (negative : β → List Bool)
    (hpLen : ∀ p, (positive p).length = n) (hnLen : ∀ q, (negative q).length = n)
    (C : Circuit) (hM : Monotone2 C) (hR : ReadsBack n C) (hF : Fits positive negative C)
    (r i : ℕ) (hr : r < C.gates.length) (hi : i < n + r)
    (hp : ∀ p, val C (positive p) (n + r) = true → val C (positive p) i = true)
    (hn : ∀ q, val C (negative q) i = true → val C (negative q) (n + r) = true) :
    let D := PEqualNP.CircuitMoves.eraseGate n C r i
    Monotone2 D ∧ ReadsBack n D ∧ Fits positive negative D ∧ D.size + 1 = C.size := by
  dsimp only
  rw [erase_eq_bypass n C r i hr]
  refine ⟨bypass_mono hM, bypass_readsBack hi hR,
    bypass_samples n positive negative hpLen hnLen C hM hF r i hr hi hp hn, ?_⟩
  change (bypass n C r i).gates.length + 1 = C.gates.length
  rw [bypass_length]
  omega

lemma least_no_alias {α β : Type} (n : ℕ) (positive : α → List Bool) (negative : β → List Bool)
    (hpLen : ∀ p, (positive p).length = n) (hnLen : ∀ q, (negative q).length = n)
    (C : Circuit) (hmin : LeastSamples n positive negative C)
    (r i : ℕ) (hr : r < C.gates.length) (hi : i < n + r)
    (hp : ∀ p, val C (positive p) (n + r) = true → val C (positive p) i = true)
    (hn : ∀ q, val C (negative q) i = true → val C (negative q) (n + r) = true) : False := by
  obtain ⟨hM, hR, hF, hlen⟩ := erase_samples n positive negative hpLen hnLen C
    hmin.1 hmin.2.1 hmin.2.2.1 r i hr hi hp hn
  have hleast := hmin.2.2.2 _ hM hR hF
  omega

lemma and_negative_witness {α β : Type} (n : ℕ) (positive : α → List Bool) (negative : β → List Bool)
    (hpLen : ∀ p, (positive p).length = n) (hnLen : ∀ q, (negative q).length = n)
    (C : Circuit) (hmin : LeastSamples n positive negative C)
    (r a b : ℕ) (hr : r < C.gates.length)
    (hop : (gateAt C r).op = GateOp.and) (hins : (gateAt C r).inputs = [a,b]) :
    ∃ q, val C (negative q) a = true ∧ val C (negative q) b = false := by
  by_contra hex
  have ha : a < n + r := hmin.2.1 r hr a (by simp [hins])
  have hb : b < n + r := hmin.2.1 r hr b (by simp [hins])
  have hn (q : β) (hq : val C (negative q) a = true) : val C (negative q) b = true := by
    cases he : val C (negative q) b with
    | false => exact False.elim (hex ⟨q,hq,he⟩)
    | true => rfl
  apply least_no_alias n positive negative hpLen hnLen C hmin r a hr ha
  · intro p hp
    exact ((val_and (hpLen p) hr hop).mp hp) a (by simp [hins]) |>.2
  · intro q hq
    apply (val_and (hnLen q) hr hop).mpr
    intro i hi
    rw [hins] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact ⟨ha,hq⟩
    · exact ⟨hb,hn q hq⟩

lemma and_negative_incomparable {α β : Type} (n : ℕ) (positive : α → List Bool) (negative : β → List Bool)
    (hpLen : ∀ p, (positive p).length = n) (hnLen : ∀ q, (negative q).length = n)
    (C : Circuit) (hmin : LeastSamples n positive negative C)
    (r a b : ℕ) (hr : r < C.gates.length)
    (hop : (gateAt C r).op = GateOp.and) (hins : (gateAt C r).inputs = [a,b]) :
    (∃ q, val C (negative q) a = true ∧ val C (negative q) b = false) ∧
    (∃ q, val C (negative q) b = true ∧ val C (negative q) a = false) := by
  refine ⟨and_negative_witness n positive negative hpLen hnLen C hmin r a b hr hop hins, ?_⟩
  by_contra hex
  have ha : a < n + r := hmin.2.1 r hr a (by simp [hins])
  have hb : b < n + r := hmin.2.1 r hr b (by simp [hins])
  have hn (q : β) (hq : val C (negative q) b = true) : val C (negative q) a = true := by
    cases he : val C (negative q) a with
    | false => exact False.elim (hex ⟨q,hq,he⟩)
    | true => rfl
  apply least_no_alias n positive negative hpLen hnLen C hmin r b hr hb
  · intro p hp
    exact ((val_and (hpLen p) hr hop).mp hp) b (by simp [hins]) |>.2
  · intro q hq
    apply (val_and (hnLen q) hr hop).mpr
    intro i hi
    rw [hins] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact ⟨ha,hn q hq⟩
    · exact ⟨hb,hq⟩

lemma or_positive_incomparable {α β : Type} (n : ℕ) (positive : α → List Bool) (negative : β → List Bool)
    (hpLen : ∀ p, (positive p).length = n) (hnLen : ∀ q, (negative q).length = n)
    (C : Circuit) (hmin : LeastSamples n positive negative C)
    (r a b : ℕ) (hr : r < C.gates.length)
    (hop : (gateAt C r).op = GateOp.or) (hins : (gateAt C r).inputs = [a,b]) :
    (∃ p, val C (positive p) a = true ∧ val C (positive p) b = false) ∧
    (∃ p, val C (positive p) b = true ∧ val C (positive p) a = false) := by
  have ha : a < n + r := hmin.2.1 r hr a (by simp [hins])
  have hb : b < n + r := hmin.2.1 r hr b (by simp [hins])
  constructor
  · by_contra hex
    have hp (p : α) (h : val C (positive p) a = true) : val C (positive p) b = true := by
      cases he : val C (positive p) b with
      | false => exact False.elim (hex ⟨p,h,he⟩)
      | true => rfl
    apply least_no_alias n positive negative hpLen hnLen C hmin r b hr hb
    · intro p hg
      obtain ⟨i,hi,_,hv⟩ := (val_or (hpLen p) hr hop).mp hg
      rw [hins] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact hp p hv
      · exact hv
    · intro q hq
      exact (val_or (hnLen q) hr hop).mpr ⟨b,by simp [hins],hb,hq⟩
  · by_contra hex
    have hp (p : α) (h : val C (positive p) b = true) : val C (positive p) a = true := by
      cases he : val C (positive p) a with
      | false => exact False.elim (hex ⟨p,h,he⟩)
      | true => rfl
    apply least_no_alias n positive negative hpLen hnLen C hmin r a hr ha
    · intro p hg
      obtain ⟨i,hi,_,hv⟩ := (val_or (hpLen p) hr hop).mp hg
      rw [hins] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact hv
      · exact hp p hv
    · intro q hq
      exact (val_or (hnLen q) hr hop).mpr ⟨a,by simp [hins],ha,hq⟩

end Part5

namespace Part5.Normalize
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_start (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_start gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_start gs w
  rw [ht, List.getD_append _ _ _ _ h]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

variable {n : ℕ}

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

abbrev Stat : Type := Bool ⊕ ℕ

def Stat.val (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

theorem elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)

theorem elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega

theorem elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
    (∃ g ∈ gs, k ∈ g.inputs) → (elim n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _ h; obtain ⟨g, hg, _⟩ := h; simp at hg
  | cons g gs ih =>
    intro acc hok hk hc hex
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
        rw [hnone]; simp
      have := elim_len n gs (elimStep n acc g)
      omega
    · have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        obtain ⟨g', hg', hk'⟩ := hex
        rcases List.mem_cons.1 hg' with rfl | h
        · exact absurd hk' hkg
        · exact ⟨g', h, hk'⟩
      have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          refine ⟨c, ?_⟩
          simp only [elimStep]
          rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
        hex'
      have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      omega

theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Sum.inl false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Sum.inl false)).val (wiresFrom acc.2 y) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_start r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Sum.inl false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Sum.inl false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

theorem elim_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List Stat × List Gate) :
    elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl

theorem elim_append (n : ℕ) (pre post : List Gate) (acc : List Stat × List Gate) :
    elim n (pre ++ post) acc = elim n post (elim n pre acc) := by
  simp [elim, List.foldl_append]

def idStats (n : ℕ) : List Stat := List.ofFn (fun i : Fin n => Sum.inr i)

theorem inv_id (n : ℕ) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y) (idStats n, []) := by
  refine ⟨by simp [idStats], ?_⟩
  intro i
  by_cases hlt : i < n
  · simp [idStats, hlt, Stat.Valid, Stat.val, wiresFrom]
  · rw [List.getD_eq_default _ _ (by simp [idStats]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

theorem getD_ofFn {α : Type} (m : ℕ) (F : Fin m → α) (d : α) (j : Fin m) :
    (List.ofFn F).getD j d = F j := by
  simp
theorem split_at {α : Type} : ∀ (l : List α) (p : ℕ) (g : α), l[p]? = some g →
    ∃ pre post, l = pre ++ g :: post ∧ pre.length = p := by
  intro l
  induction l with
  | nil => intro p g h; simp at h
  | cons x l ih =>
    intro p g h
    cases p with
    | zero =>
      simp at h
      subst h
      exact ⟨[], l, rfl, rfl⟩
    | succ p =>
      simp at h
      obtain ⟨pre, post, rfl, rfl⟩ := ih p g h
      exact ⟨x :: pre, post, rfl, rfl⟩

theorem simplify_small (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (m : ℕ)
    (ins : List Stat) (hl : ins.length ≤ 1) : (simplify op m ins).1 = none := by
  rcases hop with rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩
    · simp [simplify, simpAnd]
    · cases a <;> simp [simplify, simpAnd]
    · simp at hl
  · rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩
    · simp [simplify, simpOr]
    · cases a <;> simp [simplify, simpOr]
    · simp at hl

theorem wire_at (n : ℕ) (pre post : List Gate) (g : Gate) (X : List Bool) (hX : X.length = n) :
    (wiresFrom (pre ++ g :: post) X).getD (n + pre.length) false
      = g.op.eval (g.inputs.map fun i => (wiresFrom pre X).getD i false) := by
  have h1 : wiresFrom (pre ++ g :: post) X = wiresFrom post
      (wiresFrom pre X ++ [g.op.eval (g.inputs.map fun i => (wiresFrom pre X).getD i false)]) := by
    rw [wiresFrom_append]; rfl
  have hl : (wiresFrom pre X).length = n + pre.length := by
    rw [length_wiresFrom]; omega
  rw [h1, getD_wiresFrom _ _ _ (by simp [hl]), getD_snoc_len _ _ _ _ hl]

def CleanGate (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ g.inputs = [j, k])

def CleanL (m : ℕ) (gs : List Gate) : Prop :=
  ∀ (p : ℕ) (g : Gate), gs[p]? = some g → CleanGate (m + p) g

theorem CleanGate.nok {m : ℕ} {g : Gate} (h : CleanGate m g) : NOk g := by
  rcases h with ⟨h1, j, _, h2⟩ | ⟨h1 | h1, j, k, _, _, h2⟩
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inr (Or.inr rfl)
    · rw [h2]; simp
    · intro _; rw [h2]; simp
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inl rfl
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inr (Or.inl rfl)
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h

theorem CleanGate.lt {m : ℕ} {g : Gate} (h : CleanGate m g) : ∀ a ∈ g.inputs, a < m := by
  intro a ha
  rcases h with ⟨_, j, hj, h2⟩ | ⟨_, j, k, hj, hk, h2⟩
  · rw [h2] at ha
    simp at ha
    subst ha; exact hj
  · rw [h2] at ha
    simp at ha
    rcases ha with rfl | rfl
    · exact hj
    · exact hk

theorem clean_nok (m : ℕ) (gs : List Gate) (h : CleanL m gs) : ∀ g ∈ gs, NOk g := by
  intro g hg
  obtain ⟨p, hp⟩ := List.mem_iff_getElem?.1 hg
  exact (h p g hp).nok

theorem simplify_clean (op : GateOp) (m : ℕ) (ins : List Stat) (hv : ∀ s ∈ ins, s.Valid m) :
    ∀ g ∈ (simplify op m ins).1, CleanGate m g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg
    refine Or.inr ⟨Or.inl rfl, _, _, ?_, ?_, rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg
    refine Or.inr ⟨Or.inr rfl, _, _, ?_, ?_, rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg
    refine Or.inl ⟨rfl, _, ?_, rfl⟩
    exact hv _ List.mem_cons_self
  · simp at hg
  · simp at hg

theorem toList_getElem? {α : Type} (o : Option α) (k : ℕ) (a : α)
    (h : o.toList[k]? = some a) : k = 0 ∧ a ∈ o := by
  cases o with
  | none => simp at h
  | some b =>
    cases k with
    | zero => simp at h; simp [h]
    | succ k => simp at h

theorem clean_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      CleanL n acc.2 → CleanL n (elim n gs acc).2 := by
  induction gs with
  | nil => intro w acc _ _ h; exact h
  | cons g gs ih =>
    intro w acc hok hinv hcl
    have hinv' : Inv n y (wiresFrom [g] w) (elimStep n acc g) :=
      inv_elim n y hy [g] w acc (fun g' hg' => hok g' (by simp at hg'; simp [hg'])) hinv
    refine ih _ (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) hinv' ?_
    intro p g' hp
    have hp' : (acc.2 ++ (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)[p]? = some g' := hp
    by_cases hlt : p < acc.2.length
    · rw [List.getElem?_append_left hlt] at hp'
      exact hcl p g' hp'
    · rw [List.getElem?_append_right (by omega)] at hp'
      obtain ⟨h0, hmem⟩ := toList_getElem? _ _ _ hp'
      have hpl : p = acc.2.length := by omega
      rw [hpl]
      exact simplify_clean _ _ _ (fun s hs => by
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        exact (hinv.2 a).1) g' hmem

theorem simplify_op (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, g.op = op := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; rfl)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; rfl)
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; rfl)
  · simp at hg
  · simp at hg

def AO (gs : List Gate) : Prop :=
  ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or

theorem elim_ao (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    AO gs → AO acc.2 → AO (elim n gs acc).2 := by
  induction gs with
  | nil => intro acc _ h; exact h
  | cons g gs ih =>
    intro acc hgs h
    apply ih (elimStep n acc g) (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · rw [simplify_op _ _ _ g' (by simpa using h1)]
      exact hgs g List.mem_cons_self

theorem ao_clean_isAO2 (n : ℕ) (gs : List Gate) (o : ℕ)
    (hao : AO gs) (hc : CleanL n gs) : PEqualNP.TopForm.IsAO2 n ⟨gs, o⟩ := by
  refine ⟨hao, ?_, ?_⟩
  · intro j hj w hw
    have hg : PEqualNP.MetaComplexity.NestedCover.gateAt ⟨gs, o⟩ j = gs[j] := by
      exact List.getD_eq_getElem _ _ hj
    rw [hg] at hw
    exact (hc j gs[j] (List.getElem?_eq_getElem hj)).lt w hw
  · intro g hg
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hg
    rcases hc j g hj with h | h
    · obtain ⟨hop, _⟩ := h
      rcases hao g hg with ha | ho <;> simp_all
    · obtain ⟨_, a, b, _, _, hi⟩ := h
      simp [hi]

theorem normalize_nonconstant (n : ℕ) (C : Circuit) (hM : Monotone2 C)
    (f : (Fin n → Bool) → Bool) (hf : circuitFun n C = f)
    (hnc : ∃ x y, f x ≠ f y) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧ circuitFun n D = f ∧ D.size ≤ C.size := by
  let acc := elim n C.gates (idStats n, [])
  have hok : ∀ g ∈ C.gates, Ok g := by
    intro g hg
    refine ⟨?_, (hM g hg).2⟩
    rcases (hM g hg).1 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  have hao : AO C.gates := fun g hg => (hM g hg).1
  have hinv : ∀ x : Fin n → Bool,
      Inv n (List.ofFn x) (wiresFrom C.gates (List.ofFn x)) acc :=
    fun x => inv_elim n _ (by simp) C.gates _ _ hok (inv_id n x)
  have hval : ∀ x : Fin n → Bool,
      (acc.1.getD C.output (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn x)) = f x := by
    intro x
    exact ((hinv x).2 C.output).2.trans (congrFun hf x)
  have hlen : acc.2.length ≤ C.size := by
    have h := elim_len n C.gates (idStats n, [])
    simpa only [acc, Circuit.size, List.length_nil, zero_add] using h
  cases hs : acc.1.getD C.output (Sum.inl false) with
  | inl b =>
    exfalso
    obtain ⟨x, y, hxy⟩ := hnc
    apply hxy
    rw [← hval x, ← hval y, hs]
    rfl
  | inr w =>
    refine ⟨⟨acc.2, w⟩, ?_, ?_, hlen⟩
    · apply ao_clean_isAO2
      · exact elim_ao n C.gates _ hao (by intro g hg; simp at hg)
      · exact clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) C.gates _ _ hok
          (inv_id n _) (by intro p g hp; simp at hp)
    · funext x
      have hx := hval x
      rw [hs] at hx
      exact hx

end Part5.Normalize

namespace Part5

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

lemma exists_least_samples {α β : Type} (n : ℕ) (positive : α → List Bool) (negative : β → List Bool)
    (C : Circuit) (hM : Monotone2 C) (hR : ReadsBack n C) (hF : Fits positive negative C) :
    ∃ D : Circuit, LeastSamples n positive negative D ∧ D.size ≤ C.size := by
  classical
  let A (k : ℕ) : Prop := ∃ D : Circuit,
    Monotone2 D ∧ ReadsBack n D ∧ Fits positive negative D ∧ D.size = k
  have hex : ∃ k, A k := ⟨C.size,C,hM,hR,hF,rfl⟩
  obtain ⟨D,hDm,hDr,hDf,hDsize⟩ := Nat.find_spec hex
  refine ⟨D,⟨hDm,hDr,hDf,?_⟩,?_⟩
  · intro E hEm hEr hEf
    rw [hDsize]
    exact Nat.find_min' hex ⟨E,hEm,hEr,hEf,rfl⟩
  · rw [hDsize]
    exact Nat.find_min' hex ⟨C,hM,hR,hF,rfl⟩

lemma ofFn_getD {n : ℕ} (x : List Bool) (hx : x.length = n) :
    List.ofFn (fun i : Fin n => x.getD i.val false) = x := by
  apply List.ext_getElem
  · simp [hx]
  · intro i hi hi'
    simp only [List.getElem_ofFn, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hi', Option.getD_some]

lemma eval_of_funEq {n : ℕ} {C D : Circuit} (h : circuitFun n D = circuitFun n C)
    (x : List Bool) (hx : x.length = n) : D.eval x = C.eval x := by
  have hh := congrFun h (fun i : Fin n => x.getD i.val false)
  simpa only [circuitFun, ofFn_getD x hx] using hh

lemma sample_nonconstant {α β : Type} (n : ℕ) (positive : α → List Bool) (negative : β → List Bool)
    (hpLen : ∀ p, (positive p).length = n) (hnLen : ∀ q, (negative q).length = n)
    (p0 : α) (q0 : β) (C : Circuit) (hF : Fits positive negative C) :
    ∃ x y : Fin n → Bool, circuitFun n C x ≠ circuitFun n C y := by
  refine ⟨fun i => (positive p0).getD i.val false,
    fun i => (negative q0).getD i.val false, ?_⟩
  simp only [circuitFun, ofFn_getD _ (hpLen p0), ofFn_getD _ (hnLen q0), hF.1 p0, hF.2 q0]
  decide

lemma least_normalized_samples {α β : Type} (n : ℕ) (positive : α → List Bool) (negative : β → List Bool)
    (hpLen : ∀ p, (positive p).length = n) (hnLen : ∀ q, (negative q).length = n)
    (p0 : α) (q0 : β) (C : Circuit) (hM : Monotone2 C) (hR : ReadsBack n C)
    (hF : Fits positive negative C) :
    ∃ D : Circuit, LeastSamples n positive negative D ∧ PEqualNP.TopForm.IsAO2 n D ∧ D.size ≤ C.size := by
  obtain ⟨B,hB,hBC⟩ := exists_least_samples n positive negative C hM hR hF
  obtain ⟨D,hD,hDB,hsize⟩ := Normalize.normalize_nonconstant n B hB.1 (circuitFun n B) rfl
    (sample_nonconstant n positive negative hpLen hnLen p0 q0 B hB.2.2.1)
  have hDm : Monotone2 D := by
    intro g hg
    exact ⟨hD.1 g hg,(hD.2.2 g hg).le⟩
  have hDf : Fits positive negative D := by
    constructor
    · intro p
      rw [eval_of_funEq hDB _ (hpLen p)]
      exact hB.2.2.1.1 p
    · intro q
      rw [eval_of_funEq hDB _ (hnLen q)]
      exact hB.2.2.1.2 q
  refine ⟨D,⟨hDm,hD.2.1,hDf,?_⟩,hD,hsize.trans hBC⟩
  intro E hEm hEr hEf
  exact hsize.trans (hB.2.2.2 E hEm hEr hEf)

lemma least_binary_inputs_distinct {α β : Type} (n : ℕ) (positive : α → List Bool) (negative : β → List Bool)
    (hpLen : ∀ p, (positive p).length = n) (hnLen : ∀ q, (negative q).length = n)
    (C : Circuit) (hmin : LeastSamples n positive negative C)
    (r a b : ℕ) (hr : r < C.gates.length) (hins : (gateAt C r).inputs = [a,b]) : a ≠ b := by
  rcases (hmin.1 (gateAt C r) (gateAt_mem hr)).1 with hand | hor
  · obtain ⟨q, hqa, hqb⟩ := and_negative_witness n positive negative hpLen hnLen C hmin r a b hr hand hins
    intro hab
    rw [hab,hqb] at hqa
    cases hqa
  · obtain ⟨⟨p,hpa,hpb⟩,_⟩ := or_positive_incomparable n positive negative hpLen hnLen C hmin r a b hr hor hins
    intro hab
    rw [hab,hpb] at hpa
    cases hpa

def diff : Finset (Fin 13) := {0,1,3,9}

def quad (Q : Finset (Fin 13)) : Prop :=
  Q.card = 4 ∧ ∀ l : Fin 13, (Q.filter (fun p => p - l ∈ diff)).card ≤ 2

abbrev Flag := {e : Fin 13 × Fin 13 // e.1 - e.2 ∈ diff}
abbrev Quad := {Q : Finset (Fin 13) // quad Q}

def augment (s : List ℕ) (x : List Bool) : List Bool :=
  x ++ [s.any (fun i => x.getD i false)]

def positive (s : List ℕ) (e : Flag) : List Bool :=
  augment s (List.ofFn (fun p : Fin 13 => decide (p = e.val.1)) ++
    List.ofFn (fun l : Fin 13 => decide (l = e.val.2)))

def negative (s : List ℕ) (Q : Quad) : List Bool :=
  augment s (List.ofFn (fun p : Fin 13 => decide (p ∈ Q.val)) ++
    List.ofFn (fun l : Fin 13 => decide (∀ p ∈ Q.val, p - l ∉ diff)))

lemma positive_length (s : List ℕ) (e : Flag) : (positive s e).length = 27 := by
  simp [positive,augment]

lemma negative_length (s : List ℕ) (Q : Quad) : (negative s Q).length = 27 := by
  simp [negative,augment]

def flag0 : Flag := ⟨(0,0),by decide⟩
def quad0 : Quad := ⟨{0,1,2,5},by unfold quad diff; decide⟩

theorem free_or_normal_form (C : Circuit) (s : List ℕ) (hM : Monotone2 C)
    (hR : ∀ i : Fin C.gates.length, ∀ w ∈ (C.gates.get i).inputs, w < 27 + i.val)
    (hF : Fits (positive s) (negative s) C) :
    ∃ D : Circuit, LeastSamples 27 (positive s) (negative s) D ∧
      PEqualNP.TopForm.IsAO2 27 D ∧ D.size ≤ C.size ∧
      ∀ r < D.gates.length, ∃ a b : ℕ, (gateAt D r).inputs = [a,b] ∧ a ≠ b := by
  have hR' : ReadsBack 27 C := by
    intro j hj w hw
    have hg : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj
    rw [hg] at hw
    exact hR ⟨j,hj⟩ w hw
  obtain ⟨D,hmin,hAO,hsize⟩ := least_normalized_samples 27 (positive s) (negative s)
    (positive_length s) (negative_length s) flag0 quad0 C hM hR' hF
  refine ⟨D,hmin,hAO,hsize,?_⟩
  intro r hr
  obtain ⟨a,b,hab⟩ := List.length_eq_two.mp (hAO.2.2 (gateAt D r) (gateAt_mem hr))
  exact ⟨a,b,hab,least_binary_inputs_distinct 27 (positive s) (negative s)
    (positive_length s) (negative_length s) D hmin r a b hr hab⟩

end Part5

end PEqualNP.Outside.L_meta_8323

-- Source module: Pnp4201OrBudget
namespace PEqualNP.Outside.L_meta_8323

namespace Part6

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_8323.Part5

def opCount (p : GateOp → Bool) (C : Circuit) : ℕ :=
  C.gates.countP (fun g => p g.op)

def isOr : GateOp → Bool
  | .or => true
  | _ => false

def orCount (C : Circuit) : ℕ := opCount isOr C

theorem orCount_eq_public (C : Circuit) :
    orCount C = C.gates.countP
      (fun g => GateOp.casesOn g.op false true false (fun _ => false) false) := by
  unfold orCount opCount
  congr 1
  funext g
  cases g.op <;> rfl

theorem bypass_opCount (p : GateOp → Bool) (n : ℕ) (C : Circuit) (r i : ℕ)
    (hr : r < C.gates.length) :
    opCount p (bypass n C r i) + (if p (gateAt C r).op then 1 else 0) = opCount p C := by
  rw [← erase_eq_bypass n C r i hr]
  unfold opCount PEqualNP.CircuitMoves.eraseGate
  rw [ite_eq_left hr]
  simp only [List.countP_append, List.countP_map, Function.comp_def]
  have hs : C.gates.take r ++ C.gates[r] :: C.gates.drop (r + 1) = C.gates := by
    rw [← List.drop_eq_getElem_cons hr, List.take_append_drop]
  have hc := congrArg (List.countP (fun g : Gate => p g.op)) hs
  simp only [List.countP_append, List.countP_cons] at hc
  rw [gateAt_eq hr]
  omega

theorem bypass_opCount_le (p : GateOp → Bool) (n : ℕ) (C : Circuit) (r i : ℕ)
    (hr : r < C.gates.length) : opCount p (bypass n C r i) ≤ opCount p C := by
  have := bypass_opCount p n C r i hr
  omega

namespace Normalize

open PEqualNP.Outside.L_meta_8323.Part5.Normalize

theorem simplify_countP (p : GateOp → Bool) (op : GateOp) (m : ℕ) (ins : List Stat) :
    (simplify op m ins).1.toList.countP (fun g => p g.op) ≤ if p op then 1 else 0 := by
  cases hs : (simplify op m ins).1 with
  | none => simp
  | some g =>
    have hg : g.op = op := simplify_op op m ins g (by rw [hs]; simp)
    simp [hg]

theorem elim_countP (p : GateOp → Bool) (n : ℕ) (gs : List Gate) :
    ∀ acc : List Stat × List Gate,
      (elim n gs acc).2.countP (fun g => p g.op) ≤
        acc.2.countP (fun g => p g.op) + gs.countP (fun g => p g.op) := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 := simplify_countP p g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
    rw [elim_cons]
    simp only [elimStep, List.countP_append] at h1
    rw [List.countP_cons]
    simp only [elimStep]
    omega

theorem normalize_nonconstant_budgets (n : ℕ) (C : Circuit) (hM : Monotone2 C)
    (f : (Fin n → Bool) → Bool) (hf : circuitFun n C = f)
    (hnc : ∃ x y, f x ≠ f y) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧ circuitFun n D = f ∧
      D.size ≤ C.size ∧ ∀ p : GateOp → Bool, opCount p D ≤ opCount p C := by
  let acc := elim n C.gates (idStats n, [])
  have hok : ∀ g ∈ C.gates, Ok g := by
    intro g hg
    refine ⟨?_, (hM g hg).2⟩
    rcases (hM g hg).1 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  have hao : AO C.gates := fun g hg => (hM g hg).1
  have hinv : ∀ x : Fin n → Bool,
      Inv n (List.ofFn x) (wiresFrom C.gates (List.ofFn x)) acc :=
    fun x => inv_elim n _ (by simp) C.gates _ _ hok (inv_id n x)
  have hval : ∀ x : Fin n → Bool,
      (acc.1.getD C.output (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn x)) = f x := by
    intro x
    exact ((hinv x).2 C.output).2.trans (congrFun hf x)
  have hlen : acc.2.length ≤ C.size := by
    have h := elim_len n C.gates (idStats n, [])
    simpa only [acc, Circuit.size, List.length_nil, zero_add] using h
  have hcount (p : GateOp → Bool) :
      acc.2.countP (fun g => p g.op) ≤ opCount p C := by
    have h := elim_countP p n C.gates (idStats n, [])
    simpa only [acc, opCount, List.countP_nil, zero_add] using h
  cases hs : acc.1.getD C.output (Sum.inl false) with
  | inl b =>
    exfalso
    obtain ⟨x, y, hxy⟩ := hnc
    apply hxy
    rw [← hval x, ← hval y, hs]
    rfl
  | inr w =>
    refine ⟨⟨acc.2, w⟩, ?_, ?_, hlen, hcount⟩
    · apply ao_clean_isAO2
      · exact elim_ao n C.gates _ hao (by intro g hg; simp at hg)
      · exact clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) C.gates _ _ hok
          (inv_id n _) (by intro p g hp; simp at hp)
    · funext x
      have hx := hval x
      rw [hs] at hx
      exact hx

end Normalize

def LeastBudget (n : ℕ) (f : (Fin n → Bool) → Bool) (p : GateOp → Bool)
    (K : ℕ) (C : Circuit) : Prop :=
  Monotone2 C ∧ circuitFun n C = f ∧ opCount p C ≤ K ∧
    ∀ D : Circuit, Monotone2 D → circuitFun n D = f → opCount p D ≤ K → C.size ≤ D.size

theorem exists_least_budget (n : ℕ) (f : (Fin n → Bool) → Bool) (p : GateOp → Bool)
    (K : ℕ) (C : Circuit) (hM : Monotone2 C) (hf : circuitFun n C = f)
    (hK : opCount p C ≤ K) :
    ∃ D : Circuit, LeastBudget n f p K D ∧ D.size ≤ C.size := by
  classical
  let A (k : ℕ) : Prop := ∃ D : Circuit,
    Monotone2 D ∧ circuitFun n D = f ∧ opCount p D ≤ K ∧ D.size = k
  have hex : ∃ k, A k := ⟨C.size, C, hM, hf, hK, rfl⟩
  obtain ⟨D, hDm, hDf, hDK, hDs⟩ := Nat.find_spec hex
  refine ⟨D, ⟨hDm, hDf, hDK, ?_⟩, ?_⟩
  · intro E hEm hEf hEK
    rw [hDs]
    exact Nat.find_min' hex ⟨E, hEm, hEf, hEK, rfl⟩
  · rw [hDs]
    exact Nat.find_min' hex ⟨C, hM, hf, hK, rfl⟩

theorem least_budget_normal_form (n : ℕ) (f : (Fin n → Bool) → Bool)
    (p : GateOp → Bool) (K : ℕ) (C : Circuit)
    (hM : Monotone2 C) (hf : circuitFun n C = f) (hK : opCount p C ≤ K)
    (hnc : ∃ x y, f x ≠ f y) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧ LeastBudget n f p K D ∧
      D.size ≤ C.size := by
  obtain ⟨B, hB, hBC⟩ := exists_least_budget n f p K C hM hf hK
  obtain ⟨D, hD, hDf, hDB, hDp⟩ :=
    Normalize.normalize_nonconstant_budgets n B hB.1 f hB.2.1 hnc
  have hDm : Monotone2 D := by
    intro g hg
    exact ⟨hD.1 g hg, (hD.2.2 g hg).le⟩
  refine ⟨D, hD, ⟨hDm, hDf, (hDp p).trans hB.2.2.1, ?_⟩, hDB.trans hBC⟩
  intro E hEm hEf hEK
  exact hDB.trans (hB.2.2.2 E hEm hEf hEK)

theorem least_budget_no_alias (n : ℕ) (f : (Fin n → Bool) → Bool)
    (p : GateOp → Bool) (K : ℕ) (C : Circuit) (hmin : LeastBudget n f p K C)
    (r i : ℕ) (hr : r < C.gates.length)
    (hi : i < n + r ∨ n + C.gates.length ≤ i)
    (he : ∀ x : Fin n → Bool, val C (List.ofFn x) (n + r) = val C (List.ofFn x) i) :
    False := by
  have hfun : circuitFun n (bypass n C r i) = f := by
    funext x
    exact (bypass_eval_eq (by simp) (mono_ops hmin.1) hr hi (he x)).trans
      (congrFun hmin.2.1 x)
  have hK := (bypass_opCount_le p n C r i hr).trans hmin.2.2.1
  have hle := hmin.2.2.2 (bypass n C r i) (bypass_mono hmin.1) hfun hK
  change C.gates.length ≤ (bypass n C r i).gates.length at hle
  rw [bypass_length] at hle
  omega

theorem least_budget_distinct_inputs (n : ℕ) (f : (Fin n → Bool) → Bool)
    (p : GateOp → Bool) (K : ℕ) (C : Circuit) (hmin : LeastBudget n f p K C)
    (hRB : ReadsBack n C) (r a b : ℕ) (hr : r < C.gates.length)
    (hins : (gateAt C r).inputs = [a, b]) : a ≠ b := by
  intro hab
  subst b
  have ha : a < n + r := hRB r hr a (by simp [hins])
  apply least_budget_no_alias n f p K C hmin r a hr (Or.inl ha)
  intro x
  rw [val_gate (by simp) hr, hins]
  rcases mono_ops hmin.1 r hr with hand | hor
  · rw [hand]
    simp [GateOp.eval, ha]
  · rw [hor]
    simp [GateOp.eval, ha]

theorem least_budget_no_alias_order (n : ℕ) (f : (Fin n → Bool) → Bool)
    (p : GateOp → Bool) (K : ℕ) (C : Circuit) (hmin : LeastBudget n f p K C)
    (r i : ℕ) (hr : r < C.gates.length)
    (hi : i < n + r ∨ n + C.gates.length ≤ i)
    (hp : ∀ x : Fin n → Bool, f x = true →
      val C (List.ofFn x) (n + r) = true → val C (List.ofFn x) i = true)
    (hn : ∀ x : Fin n → Bool, f x = false →
      val C (List.ofFn x) i = true → val C (List.ofFn x) (n + r) = true) :
    False := by
  have hfun : circuitFun n (bypass n C r i) = f := by
    funext x
    change (bypass n C r i).eval (List.ofFn x) = f x
    have hC : C.eval (List.ofFn x) = f x := congrFun hmin.2.1 x
    cases hfx : f x with
    | false =>
      cases hD : (bypass n C r i).eval (List.ofFn x) with
      | false => rfl
      | true =>
        have hbad := bypass_eval_rel (R := fun a b => b = true → a = true)
          (fun _ => id) opMono_reverse (by simp) (mono_ops hmin.1) hr hi (hn x hfx) hD
        rw [hC, hfx] at hbad
        cases hbad
    | true =>
      exact bypass_eval_rel (R := fun a b => a = true → b = true)
        (fun _ => id) opMono_imp (by simp) (mono_ops hmin.1) hr hi (hp x hfx) (hC.trans hfx)
  have hK := (bypass_opCount_le p n C r i hr).trans hmin.2.2.1
  have hle := hmin.2.2.2 (bypass n C r i) (bypass_mono hmin.1) hfun hK
  change C.gates.length ≤ (bypass n C r i).gates.length at hle
  rw [bypass_length] at hle
  omega

theorem least_budget_and_negative_witness (n : ℕ) (f : (Fin n → Bool) → Bool)
    (p : GateOp → Bool) (K : ℕ) (C : Circuit) (hmin : LeastBudget n f p K C)
    (hRB : ReadsBack n C) (r a b : ℕ) (hr : r < C.gates.length)
    (hop : (gateAt C r).op = GateOp.and) (hins : (gateAt C r).inputs = [a, b]) :
    ∃ x : Fin n → Bool, f x = false ∧
      val C (List.ofFn x) a = true ∧ val C (List.ofFn x) b = false := by
  by_contra hex
  have ha : a < n + r := hRB r hr a (by simp [hins])
  have hb : b < n + r := hRB r hr b (by simp [hins])
  have hn (x : Fin n → Bool) (hx : f x = false)
      (hxa : val C (List.ofFn x) a = true) : val C (List.ofFn x) b = true := by
    cases he : val C (List.ofFn x) b with
    | false => exact False.elim (hex ⟨x, hx, hxa, he⟩)
    | true => rfl
  apply least_budget_no_alias_order n f p K C hmin r a hr (Or.inl ha)
  · intro x _ hx
    exact ((val_and (by simp) hr hop).mp hx) a (by simp [hins]) |>.2
  · intro x hx hxa
    apply (val_and (by simp) hr hop).mpr
    intro i hi
    rw [hins] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact ⟨ha, hxa⟩
    · exact ⟨hb, hn x hx hxa⟩

theorem least_budget_and_negative_incomparable (n : ℕ) (f : (Fin n → Bool) → Bool)
    (p : GateOp → Bool) (K : ℕ) (C : Circuit) (hmin : LeastBudget n f p K C)
    (hRB : ReadsBack n C) (r a b : ℕ) (hr : r < C.gates.length)
    (hop : (gateAt C r).op = GateOp.and) (hins : (gateAt C r).inputs = [a, b]) :
    (∃ x : Fin n → Bool, f x = false ∧
      val C (List.ofFn x) a = true ∧ val C (List.ofFn x) b = false) ∧
    (∃ x : Fin n → Bool, f x = false ∧
      val C (List.ofFn x) b = true ∧ val C (List.ofFn x) a = false) := by
  refine ⟨least_budget_and_negative_witness n f p K C hmin hRB r a b hr hop hins, ?_⟩
  by_contra hex
  have ha : a < n + r := hRB r hr a (by simp [hins])
  have hb : b < n + r := hRB r hr b (by simp [hins])
  have hn (x : Fin n → Bool) (hx : f x = false)
      (hxb : val C (List.ofFn x) b = true) : val C (List.ofFn x) a = true := by
    cases he : val C (List.ofFn x) a with
    | false => exact False.elim (hex ⟨x, hx, hxb, he⟩)
    | true => rfl
  apply least_budget_no_alias_order n f p K C hmin r b hr (Or.inl hb)
  · intro x _ hx
    exact ((val_and (by simp) hr hop).mp hx) b (by simp [hins]) |>.2
  · intro x hx hxb
    apply (val_and (by simp) hr hop).mpr
    intro i hi
    rw [hins] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact ⟨ha, hn x hx hxb⟩
    · exact ⟨hb, hxb⟩

theorem least_budget_or_positive_incomparable (n : ℕ) (f : (Fin n → Bool) → Bool)
    (p : GateOp → Bool) (K : ℕ) (C : Circuit) (hmin : LeastBudget n f p K C)
    (hRB : ReadsBack n C) (r a b : ℕ) (hr : r < C.gates.length)
    (hop : (gateAt C r).op = GateOp.or) (hins : (gateAt C r).inputs = [a, b]) :
    (∃ x : Fin n → Bool, f x = true ∧
      val C (List.ofFn x) a = true ∧ val C (List.ofFn x) b = false) ∧
    (∃ x : Fin n → Bool, f x = true ∧
      val C (List.ofFn x) b = true ∧ val C (List.ofFn x) a = false) := by
  have ha : a < n + r := hRB r hr a (by simp [hins])
  have hb : b < n + r := hRB r hr b (by simp [hins])
  constructor
  · by_contra hex
    have hp (x : Fin n → Bool) (hx : f x = true)
        (hxa : val C (List.ofFn x) a = true) : val C (List.ofFn x) b = true := by
      cases he : val C (List.ofFn x) b with
      | false => exact False.elim (hex ⟨x, hx, hxa, he⟩)
      | true => rfl
    apply least_budget_no_alias_order n f p K C hmin r b hr (Or.inl hb)
    · intro x hx hg
      obtain ⟨i, hi, _, hv⟩ := (val_or (by simp) hr hop).mp hg
      rw [hins] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact hp x hx hv
      · exact hv
    · intro x _ hbtrue
      exact (val_or (by simp) hr hop).mpr ⟨b, by simp [hins], hb, hbtrue⟩
  · by_contra hex
    have hp (x : Fin n → Bool) (hx : f x = true)
        (hxb : val C (List.ofFn x) b = true) : val C (List.ofFn x) a = true := by
      cases he : val C (List.ofFn x) a with
      | false => exact False.elim (hex ⟨x, hx, hxb, he⟩)
      | true => rfl
    apply least_budget_no_alias_order n f p K C hmin r a hr (Or.inl ha)
    · intro x hx hg
      obtain ⟨i, hi, _, hv⟩ := (val_or (by simp) hr hop).mp hg
      rw [hins] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact hv
      · exact hp x hx hv
    · intro x _ hatrue
      exact (val_or (by simp) hr hop).mpr ⟨a, by simp [hins], ha, hatrue⟩

theorem least_budget_gate_productive (n : ℕ) (f : (Fin n → Bool) → Bool)
    (p : GateOp → Bool) (K : ℕ) (C : Circuit) (hmin : LeastBudget n f p K C)
    (r : ℕ) (hr : r < C.gates.length) :
    ∃ x : Fin n → Bool, f x = true ∧ val C (List.ofFn x) (n + r) = true := by
  by_contra hex
  apply least_budget_no_alias_order n f p K C hmin r (n + C.gates.length) hr (Or.inr le_rfl)
  · intro x hx hg
    exact False.elim (hex ⟨x, hx, hg⟩)
  · intro x _ hi
    rw [val_ge (by simp) le_rfl] at hi
    cases hi

end Part6

end PEqualNP.Outside.L_meta_8323

-- Source module: Pnp4201BudgetTopForm
namespace PEqualNP.Outside.L_meta_8323

namespace Part7

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.Outside.L_meta_8323.Part3
open PEqualNP.Outside.L_meta_8323.Part6

theorem opCount_of_same_ops (p : GateOp → Bool) (C D : Circuit)
    (hlen : C.gates.length = D.gates.length)
    (hops : ∀ k, k < C.gates.length → (gateAt C k).op = (gateAt D k).op) :
    opCount p C = opCount p D := by
  have hm : C.gates.map Gate.op = D.gates.map Gate.op := by
    apply List.ext_getElem
    · simpa using hlen
    · intro k hk hk'
      simp only [List.length_map] at hk hk'
      simp only [List.getElem_map]
      rw [← PEqualNP.Outside.L_meta_8323.Part5.gateAt_eq hk, ← PEqualNP.Outside.L_meta_8323.Part5.gateAt_eq hk']
      exact hops k hk
  have h := congrArg (List.countP p) hm
  simpa only [List.countP_map, Function.comp_def, opCount] using h

theorem V1_opCount (p : GateOp → Bool) (n : ℕ) (C : Circuit) (r b : ℕ)
    (hr : r < C.gates.length) :
    opCount p (V1 n C r b) + (if p (gateAt C r).op then 1 else 0) = opCount p C := by
  have he : opCount p (V1 n C r b) = opCount p (PEqualNP.Outside.L_meta_8323.Part5.bypass n C r b) := by
    apply opCount_of_same_ops
    · rw [V1_len, PEqualNP.Outside.L_meta_8323.Part5.bypass_length]
    · intro k hk
      rw [V1_len] at hk
      rw [V1_gate n C r b k hk, PEqualNP.Outside.L_meta_8323.Part5.gateAt_bypass hk]
      simp only [rho]
      split_ifs <;> rfl
  rw [he]
  exact bypass_opCount p n C r b hr

theorem V1_orCount_le (n : ℕ) (C : Circuit) (r b : ℕ)
    (hr : r < C.gates.length) : orCount (V1 n C r b) ≤ orCount C := by
  have h := V1_opCount isOr n C r b hr
  change opCount isOr (V1 n C r b) ≤ opCount isOr C
  omega

theorem V2_ops (n : ℕ) (C : Circuit) (r b i : ℕ) (hr : r < C.gates.length) :
    (V2 n C r b i).gates.map Gate.op = (V1 n C r b).gates.map Gate.op ++ [GateOp.or] := by
  apply List.ext_getElem
  · simp only [List.length_map, List.length_append, List.length_singleton, V1_len, V2_len]
    omega
  · intro k hk hk'
    have hkC : k < C.gates.length := by simpa only [List.length_map, V2_len] using hk
    by_cases hk0 : k < C.gates.length - 1
    · rw [List.getElem_append_left (by simp only [List.length_map, V1_len]; exact hk0)]
      simp only [List.getElem_map]
      rw [← PEqualNP.Outside.L_meta_8323.Part5.gateAt_eq (by rw [V2_len]; exact hkC),
        ← PEqualNP.Outside.L_meta_8323.Part5.gateAt_eq (by rw [V1_len]; exact hk0),
        V2_gate n C r b i k hk0, V1_gate n C r b k hk0]
    · have hk0' : k = C.gates.length - 1 := by omega
      subst k
      rw [List.getElem_append_right (by simp only [List.length_map, V1_len]; exact le_rfl)]
      simp only [List.length_map, V1_len, Nat.sub_self, List.getElem_cons_zero, List.getElem_map]
      rw [← PEqualNP.Outside.L_meta_8323.Part5.gateAt_eq (by rw [V2_len]; omega), V2_top n C r b i (by omega)]

theorem V2_opCount (p : GateOp → Bool) (n : ℕ) (C : Circuit) (r b i : ℕ)
    (hr : r < C.gates.length) :
    opCount p (V2 n C r b i) + (if p (gateAt C r).op then 1 else 0) =
      opCount p C + (if p GateOp.or then 1 else 0) := by
  have hv := congrArg (List.countP p) (V2_ops n C r b i hr)
  simp only [List.countP_append, List.countP_map, Function.comp_def,
    List.countP_cons, List.countP_nil, zero_add] at hv
  have hd := V1_opCount p n C r b hr
  change opCount p (V2 n C r b i) = opCount p (V1 n C r b) +
    (if p GateOp.or then 1 else 0) at hv
  omega

theorem V2_orCount (n : ℕ) (C : Circuit) (r b i : ℕ)
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    orCount (V2 n C r b i) = orCount C := by
  have h := V2_opCount isOr n C r b i hr
  rw [hop] at h
  exact Nat.add_right_cancel h

def BudgetLeast (n : ℕ) (C : Circuit) : Prop :=
  AO2 n C ∧ ∀ D : Circuit, AO2 n D →
    (∀ x, wv n D x D.output = wv n C x C.output) → orCount D ≤ orCount C →
    C.gates.length ≤ D.gates.length

lemma budget_reader_or (n : ℕ) (C : Circuit) (hL : BudgetLeast n C) (hout : C.output < n + C.gates.length)
    (i r : ℕ) (hr : r < C.gates.length)
    (hbel : ∀ x, wv n C x (n + i) = true → wv n C x C.output = true)
    (hin : n + i ∈ (gateAt C r).inputs) :
    (gateAt C r).op = GateOp.or ∧ ∃ c, c ≠ n + i ∧ c < n + r ∧
      ((gateAt C r).inputs = [n + i, c] ∨ (gateAt C r).inputs = [c, n + i]) := by
  obtain ⟨hop, ⟨a, c0, hab⟩, hlt⟩ := hL.1 r hr
  have hir : n + i < n + r := hlt _ hin
  have hin' : n + i = a ∨ n + i = c0 := by rw [hab] at hin; simpa using hin
  by_contra hcon
  have key : ∀ x, wv n C x (n + i) = false → wv n C x (n + r) = false := by
    intro x hx
    rw [wv_rec n C x (aob hL.1) r hr, hab]
    rcases hop with hop | hop
    · rw [hop, eval_and_pair]
      rcases hin' with h | h
      · rw [← h, hx]; rfl
      · rw [← h, hx]; simp
    · rw [hop, eval_or_pair]
      have ha : a = n + i := by
        by_contra hne
        apply hcon
        refine ⟨hop, a, hne, hlt a (by rw [hab]; simp), ?_⟩
        rcases hin' with h | h
        · exact absurd h.symm hne
        · right; rw [hab, h]
      have hc : c0 = n + i := by
        by_contra hne
        apply hcon
        refine ⟨hop, c0, hne, hlt c0 (by rw [hab]; simp), ?_⟩
        left; rw [hab, ha]
      rw [ha, hc, hx]; rfl
  have hfun : ∀ x, wv n (V1 n C r (n + i)) x (V1 n C r (n + i)).output = wv n C x C.output :=
    fun x => V1_fun n C r (n + i) x hL.1 hr hir hout (hbel x) (key x)
  have hle := hL.2 _ (V1_AO2 n C r (n + i) hL.1 hr hir) hfun (V1_orCount_le n C r (n + i) hr)
  rw [V1_len] at hle
  omega

lemma budget_reader_unique (n : ℕ) (C : Circuit) (hL : BudgetLeast n C)
    (hout : C.output < n + C.gates.length) (i r1 r2 : ℕ) (h12 : r1 < r2)
    (hr2 : r2 < C.gates.length)
    (hbel : ∀ x, wv n C x (n + i) = true → wv n C x C.output = true)
    (hin1 : n + i ∈ (gateAt C r1).inputs) (hin2 : n + i ∈ (gateAt C r2).inputs) : False := by
  have hr1 : r1 < C.gates.length := by omega
  obtain ⟨hop1, c1, hc1, hc1lt, hi1⟩ := budget_reader_or n C hL hout i r1 hr1 hbel hin1
  obtain ⟨hop2, c2, hc2, hc2lt, hi2⟩ := budget_reader_or n C hL hout i r2 hr2 hbel hin2
  have hir1 : i < r1 := by have := (hL.1 r1 hr1).2.2 _ hin1; omega
  have hir2 : i < r2 := by omega
  have k2 : ∀ x, wv n C x (n + i) = false → wv n C x (n + r2) = wv n C x c2 := by
    intro x hx
    rw [wv_rec n C x (aob hL.1) r2 hr2, hop2]
    rcases hi2 with h | h
    · rw [h, eval_or_pair, hx]; rfl
    · rw [h, eval_or_pair, hx]; simp
  have k1 : ∀ x, wv n C x (n + i) = false → wv n C x (n + r1) = wv n C x c1 := by
    intro x hx
    rw [wv_rec n C x (aob hL.1) r1 hr1, hop1]
    rcases hi1 with h | h
    · rw [h, eval_or_pair, hx]; rfl
    · rw [h, eval_or_pair, hx]; simp
  have hD : AO2 n (V2 n C r2 c2 i) := V2_AO2 n C r2 c2 i hL.1 hr2 hc2lt hir2 hout
  have hDlen := V2_len n C r2 c2 i
  have hDfun : ∀ x, wv n (V2 n C r2 c2 i) x (V2 n C r2 c2 i).output = wv n C x C.output :=
    fun x => V2_out n C r2 c2 i x hL.1 hr2 hc2lt hir2 hout (hbel x) (k2 x)
  have hDout : (V2 n C r2 c2 i).output = n + ((V2 n C r2 c2 i).gates.length - 1) := by
    rw [hDlen]
    show n + C.gates.length - 1 = n + (C.gates.length - 1)
    omega
  have hDtop : gateAt (V2 n C r2 c2 i) ((V2 n C r2 c2 i).gates.length - 1) =
      ⟨GateOp.or, [tau n r2 c2 C.output, n + i]⟩ := by
    rw [hDlen]
    exact V2_top n C r2 c2 i (by omega)
  have h0 : ∀ x, wv n (V2 n C r2 c2 i) x (n + i) = false →
      wv n (V2 n C r2 c2 i) x (n + r1) = wv n (V2 n C r2 c2 i) x c1 := by
    intro x hx
    rw [V2_low n C r2 c2 i x hL.1 hr2 hc2lt hir2 hout (n + i) (by omega)] at hx
    rw [V2_low n C r2 c2 i x hL.1 hr2 hc2lt hir2 hout (n + r1) (by omega),
      V2_low n C r2 c2 i x hL.1 hr2 hc2lt hir2 hout c1 (by omega)]
    exact k1 x hx
  have hEfun : ∀ x, wv n (V1 n (V2 n C r2 c2 i) r1 c1) x (V1 n (V2 n C r2 c2 i) r1 c1).output =
      wv n C x C.output := fun x =>
    (V1_fun_top n (V2 n C r2 c2 i) r1 c1 i (tau n r2 c2 C.output) x hD (by rw [hDlen]; omega)
      hc1lt hir1 hDout hDtop (h0 x)).trans (hDfun x)
  have hle := hL.2 _ (V1_AO2 n (V2 n C r2 c2 i) r1 c1 hD (by rw [hDlen]; omega) hc1lt) hEfun
    ((V1_orCount_le n (V2 n C r2 c2 i) r1 c1 (by rw [hDlen]; omega)).trans
      (le_of_eq (V2_orCount n C r2 c2 i hr2 hop2)))
  rw [V1_len, hDlen] at hle
  omega

lemma budget_step3_core (n : ℕ) (C : Circuit) (hL : BudgetLeast n C) (hout : C.output < n + C.gates.length)
    (i j : ℕ) (hbel : ∀ x, wv n C x (n + i) = true → wv n C x C.output = true)
    (hcone : InCone n C i j) :
    ∃ r c, r < C.gates.length ∧ i < r ∧ c < n + r ∧ c ≠ n + i ∧ c ∈ (gateAt C r).inputs ∧
      (gateAt C r).op = GateOp.or ∧
      (∀ k, k < C.gates.length → n + i ∈ (gateAt C k).inputs → k = r) ∧
      (∀ x, wv n C x (n + i) = false → wv n C x (n + r) = wv n C x c) := by
  obtain ⟨r, hr, hir, hrin, _⟩ := inCone_reader n C i j hcone
  obtain ⟨hop, c, hc, hclt, hi⟩ := budget_reader_or n C hL hout i r hr hbel hrin
  refine ⟨r, c, hr, hir, hclt, hc, ?_, hop, ?_, ?_⟩
  · rcases hi with h | h <;> rw [h] <;> simp
  · intro k hk hkin
    rcases Nat.lt_trichotomy k r with h | h | h
    · exact (budget_reader_unique n C hL hout i k r h hr hbel hkin hrin).elim
    · exact h
    · exact (budget_reader_unique n C hL hout i r k h hk hbel hrin hkin).elim
  · intro x hx
    rw [wv_rec n C x (aob hL.1) r hr, hop]
    rcases hi with h | h
    · rw [h, eval_or_pair, hx]; rfl
    · rw [h, eval_or_pair, hx]; simp

lemma budget_least_of_same (n : ℕ) (C D : Circuit) (hL : BudgetLeast n C) (hD : AO2 n D)
    (hfun : ∀ x, wv n D x D.output = wv n C x C.output)
    (hlen : D.gates.length = C.gates.length) (hcount : orCount D = orCount C) : BudgetLeast n D :=
  ⟨hD, fun E hE hEf hEc => by
    rw [hlen]
    exact hL.2 E hE (fun x => (hEf x).trans (hfun x)) (hEc.trans hcount.le)⟩

lemma budget_step3_struct (n : ℕ) (C : Circuit) (F : (Fin n → Bool) → Bool) (hL : BudgetLeast n C)
    (hF : ∀ x, wv n C x C.output = F x) (hout : C.output < n + C.gates.length)
    (i j : ℕ) (hbel : ∀ x, wv n C x (n + i) = true → F x = true)
    (hcone : InCone n C i j) :
    ∃ (C' : Circuit) (r : ℕ), r < C.gates.length ∧ i < r ∧ BudgetLeast n C' ∧
      (∀ x, wv n C' x C'.output = F x) ∧ C'.gates.length = C.gates.length ∧
      (∀ k', k' < C.gates.length - 1 → (gateAt C' k').op = (gateAt C (rho r k')).op) ∧
      (gateAt C' (C.gates.length - 1)).op = GateOp.or ∧ (gateAt C r).op = GateOp.or ∧
      (∀ k', k' < C.gates.length - 1 →
        ((∀ x, wv n C' x (n + k') = true → F x = true) ↔
          (∀ x, wv n C x (n + rho r k') = true → F x = true))) ∧
      (∀ a' b', b' < C.gates.length - 1 → InCone n C' a' b' →
        InCone n C (rho r a') (rho r b')) ∧
      (∀ j', j' < C.gates.length - 1 → ¬ InCone n C' i j') ∧ orCount C' = orCount C := by
  have hbel' : ∀ x, wv n C x (n + i) = true → wv n C x C.output = true :=
    fun x h => by rw [hF]; exact hbel x h
  obtain ⟨r, c, hr, hir, hclt, hci, hcin, hop, huniq, h0⟩ :=
    budget_step3_core n C hL hout i j hbel' hcone
  have hD := V2_AO2 n C r c i hL.1 hr hclt hir hout
  have hfun : ∀ x, wv n (V2 n C r c i) x (V2 n C r c i).output = wv n C x C.output :=
    fun x => V2_out n C r c i x hL.1 hr hclt hir hout (hbel' x) (h0 x)
  refine ⟨V2 n C r c i, r, hr, hir, budget_least_of_same n C _ hL hD hfun (V2_len n C r c i)
      (V2_orCount n C r c i hr hop),
    fun x => (hfun x).trans (hF x), V2_len n C r c i, ?_, ?_, hop, ?_, ?_, ?_, ?_⟩
  · intro k' hk'
    rw [V2_gate n C r c i k' hk']
  · rw [V2_top n C r c i (by omega)]
  · intro k' hk'
    exact V2_below n C r c i F hL.1 hr hclt hir hout hbel h0 k' hk'
  · intro a' b' hb' h
    exact V2_cone n C r c i hL.1 hr hclt hcin a' b' hb' h
  · exact V2_no_cone n C r c i hr hir hci huniq
  · exact V2_orCount n C r c i hr hop

open Classical in
lemma budget_main_ind (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : G.edgeFinset.Nonempty) :
    ∀ k : ℕ, ∀ C : Circuit, BudgetLeast n C →
      (∀ x, wv n C x C.output = graphFun G ∅ x) →
      ((Finset.range C.gates.length ×ˢ Finset.range C.gates.length).filter
        (fun p : ℕ × ℕ => (gateAt C p.1).op = GateOp.and ∧
          (gateAt C p.2).op = GateOp.and ∧ InCone n C p.1 p.2)).card = k →
      ∃ C' : Circuit, BudgetLeast n C' ∧
        (∀ x, wv n C' x C'.output = graphFun G ∅ x) ∧ C'.size = C.size ∧
        orCount C' = orCount C ∧
        (PEqualNP.TopForm.junk G C').card = (PEqualNP.TopForm.junk G C).card ∧
        PEqualNP.TopForm.TopForm G C' := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro C hC hF hk
    by_cases htop : PEqualNP.TopForm.TopForm G C
    · exact ⟨C, hC, hF, rfl, rfl, rfl, htop⟩
    · have hex : ∃ i j, i < C.gates.length ∧ j < C.gates.length ∧
          (gateAt C i).op = GateOp.and ∧ PEqualNP.TopForm.BelowF G C i ∧
          (gateAt C j).op = GateOp.and ∧ InCone n C i j := by
        by_contra hne
        apply htop
        intro i hi j hj h1 h2 h3 h4
        exact hne ⟨i, j, hi, hj, h1, h2, h3, h4⟩
      obtain ⟨i, j, hi, hj, hopi, hbi, hopj, hcone⟩ := hex
      obtain ⟨x1, hx1⟩ := exists_true n G hG
      have hout : C.output < n + C.gates.length := out_lt n C x1 (by rw [hF]; exact hx1)
      obtain ⟨C', r, hr, hir, hL', hF', hlen, hops, htop', hopr, hbelow, hcn, hno, hcount⟩ :=
        budget_step3_struct n C (graphFun G ∅) hC hF hout i j hbi hcone
      have hlt := pairs_lt n C C' r i j hr hir hlen hops htop' hcn hno hopi hopj hcone
      rw [hk] at hlt
      obtain ⟨C'', h1, h2, h3, h4, h5, h6⟩ := ih _ hlt C' hL' hF' rfl
      refine ⟨C'', h1, h2, h3.trans hlen, h4.trans hcount, h5.trans ?_, h6⟩
      refine junk_eq n C C' (graphFun G ∅) r hr hlen hops htop' hopr hbelow _ _ ?_ ?_
      · intro j
        exact mem_junk n G C j
      · intro j
        exact mem_junk n G C' j

theorem budget_top_form (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : G.edgeFinset.Nonempty) (C : Circuit) (hC : BudgetLeast n C)
    (hF : circuitFun n C = graphFun G ∅) :
    ∃ D : Circuit, BudgetLeast n D ∧ circuitFun n D = graphFun G ∅ ∧
      D.size = C.size ∧ orCount D = orCount C ∧
      (PEqualNP.TopForm.junk G D).card = (PEqualNP.TopForm.junk G C).card ∧
      PEqualNP.TopForm.TopForm G D := by
  obtain ⟨D, hD, hDf, hs, ho, hj, ht⟩ :=
    budget_main_ind n G hG _ C hC (fun x => congrFun hF x) rfl
  exact ⟨D, hD, funext hDf, hs, ho, hj, ht⟩

theorem budgetLeast_of_leastBudget (n : ℕ) (f : (Fin n → Bool) → Bool)
    (K : ℕ) (C : Circuit) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (hmin : LeastBudget n f isOr K C) : BudgetLeast n C := by
  refine ⟨ao2_of n C hAO, ?_⟩
  intro D hD hDf hcount
  have hAO' := ao2_to n D hD
  have hM : Monotone2 D := fun g hg => ⟨hAO'.1 g hg, (hAO'.2.2 g hg).le⟩
  have hF : circuitFun n D = f := by
    funext x
    exact (hDf x).trans (congrFun hmin.2.1 x)
  exact hmin.2.2.2 D hM hF (hcount.trans hmin.2.2.1)

theorem exists_top_form_with_or_budget (n : ℕ) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hG : G.edgeFinset.Nonempty) (C : Circuit)
    (hM : Monotone2 C) (hF : circuitFun n C = graphFun G ∅) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧ circuitFun n D = graphFun G ∅ ∧
      D.size ≤ C.size ∧ orCount D ≤ orCount C ∧ BudgetLeast n D ∧
      PEqualNP.TopForm.TopForm G D := by
  have hnc : ∃ x y : Fin n → Bool, graphFun G ∅ x ≠ graphFun G ∅ y := by
    obtain ⟨x, hx⟩ := exists_true n G hG
    refine ⟨x, fun _ => false, ?_⟩
    rw [hx]
    simp [graphFun]
  obtain ⟨B, hBA, hBmin, hBC⟩ := least_budget_normal_form n (graphFun G ∅)
    isOr (orCount C) C hM hF le_rfl hnc
  have hBL := budgetLeast_of_leastBudget n (graphFun G ∅) (orCount C) B hBA hBmin
  obtain ⟨D, hDL, hDF, hDS, hDO, _, hDT⟩ := budget_top_form n G hG B hBL hBmin.2.1
  exact ⟨D, ao2_to n D hDL.1, hDF, hDS.le.trans hBC,
    hDO.le.trans hBmin.2.2.1, hDL, hDT⟩

end Part7

end PEqualNP.Outside.L_meta_8323

-- Source module: Pnp4201CleanBudgetTopForm
namespace PEqualNP.Outside.L_meta_8323

namespace Part8

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.Outside.L_meta_8323.Part3
open PEqualNP.Outside.L_meta_8323.Part6 PEqualNP.Outside.L_meta_8323.Part7

def Clean (n : ℕ) (F : (Fin n → Bool) → Bool) (C : Circuit) : Prop :=
  ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
    ∀ x, F x = false → wv n C x (n + k) = false

def CleanLeast (n : ℕ) (F : (Fin n → Bool) → Bool) (C : Circuit) : Prop :=
  AO2 n C ∧ Clean n F C ∧ ∀ D : Circuit, AO2 n D →
    (∀ x, wv n D x D.output = wv n C x C.output) → orCount D ≤ orCount C →
    Clean n F D → C.gates.length ≤ D.gates.length

lemma below_off (n : ℕ) (C : Circuit) (F : (Fin n → Bool) → Bool)
    (hF : ∀ x, wv n C x C.output = F x) (i : ℕ)
    (hbel : ∀ x, wv n C x (n + i) = true → wv n C x C.output = true) :
    ∀ x, F x = false → wv n C x (n + i) = false := by
  intro x hx
  cases hi : wv n C x (n + i) with
  | false => rfl
  | true =>
    have hbad := hbel x hi
    rw [hF, hx] at hbad
    cases hbad

lemma V1_clean (n : ℕ) (C : Circuit) (F : (Fin n → Bool) → Bool)
    (r b : ℕ) (hC : AO2 n C) (hClean : Clean n F C)
    (hr : r < C.gates.length) (hb : b < n + r)
    (h0 : ∀ x, F x = false → wv n C x (n + r) = wv n C x b) :
    Clean n F (V1 n C r b) := by
  intro k hk hop x hx
  rw [V1_len] at hk
  have hkC := rho_lt r k C.gates.length hr hk
  have htr := transfer_eq n C (V1 n C r b) r b x (aob hC)
    (aob (V1_AO2 n C r b hC hr hb)) hr hb (by rw [V1_len]) (V1_red n C r b)
    (n + rho r k) (by omega) (fun _ => h0 x hx)
  rw [tau_rho] at htr
  rw [← htr]
  apply hClean (rho r k) hkC ?_ x hx
  rw [V1_gate n C r b k hk] at hop
  exact hop

lemma V2_clean (n : ℕ) (C : Circuit) (F : (Fin n → Bool) → Bool)
    (r b i : ℕ) (hC : AO2 n C) (hClean : Clean n F C)
    (hr : r < C.gates.length) (hb : b < n + r) (hi : i < r)
    (hout : C.output < n + C.gates.length)
    (h0 : ∀ x, F x = false → wv n C x (n + r) = wv n C x b) :
    Clean n F (V2 n C r b i) := by
  intro k hk hop x hx
  rw [V2_len] at hk
  by_cases hk0 : k < C.gates.length - 1
  · rw [V2_gateval n C r b i x hC hr hb hi hout (h0 x hx) k hk0]
    apply hClean (rho r k) (rho_lt r k _ hr hk0) ?_ x hx
    rw [V2_gate n C r b i k hk0] at hop
    exact hop
  · have he : k = C.gates.length - 1 := by omega
    rw [he, V2_top n C r b i (by omega)] at hop
    cases hop

lemma clean_reader_or (n : ℕ) (C : Circuit) (F : (Fin n → Bool) → Bool)
    (hF : ∀ x, wv n C x C.output = F x) (hL : CleanLeast n F C) (hout : C.output < n + C.gates.length)
    (i r : ℕ) (hr : r < C.gates.length)
    (hbel : ∀ x, wv n C x (n + i) = true → wv n C x C.output = true)
    (hin : n + i ∈ (gateAt C r).inputs) :
    (gateAt C r).op = GateOp.or ∧ ∃ c, c ≠ n + i ∧ c < n + r ∧
      ((gateAt C r).inputs = [n + i, c] ∨ (gateAt C r).inputs = [c, n + i]) := by
  obtain ⟨hop, ⟨a, c0, hab⟩, hlt⟩ := hL.1 r hr
  have hir : n + i < n + r := hlt _ hin
  have hin' : n + i = a ∨ n + i = c0 := by rw [hab] at hin; simpa using hin
  by_contra hcon
  have key : ∀ x, wv n C x (n + i) = false → wv n C x (n + r) = false := by
    intro x hx
    rw [wv_rec n C x (aob hL.1) r hr, hab]
    rcases hop with hop | hop
    · rw [hop, eval_and_pair]
      rcases hin' with h | h
      · rw [← h, hx]; rfl
      · rw [← h, hx]; simp
    · rw [hop, eval_or_pair]
      have ha : a = n + i := by
        by_contra hne
        apply hcon
        refine ⟨hop, a, hne, hlt a (by rw [hab]; simp), ?_⟩
        rcases hin' with h | h
        · exact absurd h.symm hne
        · right; rw [hab, h]
      have hc : c0 = n + i := by
        by_contra hne
        apply hcon
        refine ⟨hop, c0, hne, hlt c0 (by rw [hab]; simp), ?_⟩
        left; rw [hab, ha]
      rw [ha, hc, hx]; rfl
  have hfun : ∀ x, wv n (V1 n C r (n + i)) x (V1 n C r (n + i)).output = wv n C x C.output :=
    fun x => V1_fun n C r (n + i) x hL.1 hr hir hout (hbel x) (key x)
  have hsafe : Clean n F (V1 n C r (n + i)) :=
    V1_clean n C F r (n + i) hL.1 hL.2.1 hr hir (fun x hx => by
      have hi0 := below_off n C F hF i hbel x hx
      rw [key x hi0, hi0])
  have hle := hL.2.2 _ (V1_AO2 n C r (n + i) hL.1 hr hir) hfun (V1_orCount_le n C r (n + i) hr) hsafe
  rw [V1_len] at hle
  omega

lemma clean_reader_unique (n : ℕ) (C : Circuit) (F : (Fin n → Bool) → Bool)
    (hF : ∀ x, wv n C x C.output = F x) (hL : CleanLeast n F C)
    (hout : C.output < n + C.gates.length) (i r1 r2 : ℕ) (h12 : r1 < r2)
    (hr2 : r2 < C.gates.length)
    (hbel : ∀ x, wv n C x (n + i) = true → wv n C x C.output = true)
    (hin1 : n + i ∈ (gateAt C r1).inputs) (hin2 : n + i ∈ (gateAt C r2).inputs) : False := by
  have hr1 : r1 < C.gates.length := by omega
  obtain ⟨hop1, c1, hc1, hc1lt, hi1⟩ := clean_reader_or n C F hF hL hout i r1 hr1 hbel hin1
  obtain ⟨hop2, c2, hc2, hc2lt, hi2⟩ := clean_reader_or n C F hF hL hout i r2 hr2 hbel hin2
  have hir1 : i < r1 := by have := (hL.1 r1 hr1).2.2 _ hin1; omega
  have hir2 : i < r2 := by omega
  have k2 : ∀ x, wv n C x (n + i) = false → wv n C x (n + r2) = wv n C x c2 := by
    intro x hx
    rw [wv_rec n C x (aob hL.1) r2 hr2, hop2]
    rcases hi2 with h | h
    · rw [h, eval_or_pair, hx]; rfl
    · rw [h, eval_or_pair, hx]; simp
  have k1 : ∀ x, wv n C x (n + i) = false → wv n C x (n + r1) = wv n C x c1 := by
    intro x hx
    rw [wv_rec n C x (aob hL.1) r1 hr1, hop1]
    rcases hi1 with h | h
    · rw [h, eval_or_pair, hx]; rfl
    · rw [h, eval_or_pair, hx]; simp
  have hD : AO2 n (V2 n C r2 c2 i) := V2_AO2 n C r2 c2 i hL.1 hr2 hc2lt hir2 hout
  have hDlen := V2_len n C r2 c2 i
  have hDfun : ∀ x, wv n (V2 n C r2 c2 i) x (V2 n C r2 c2 i).output = wv n C x C.output :=
    fun x => V2_out n C r2 c2 i x hL.1 hr2 hc2lt hir2 hout (hbel x) (k2 x)
  have hDout : (V2 n C r2 c2 i).output = n + ((V2 n C r2 c2 i).gates.length - 1) := by
    rw [hDlen]
    show n + C.gates.length - 1 = n + (C.gates.length - 1)
    omega
  have hDtop : gateAt (V2 n C r2 c2 i) ((V2 n C r2 c2 i).gates.length - 1) =
      ⟨GateOp.or, [tau n r2 c2 C.output, n + i]⟩ := by
    rw [hDlen]
    exact V2_top n C r2 c2 i (by omega)
  have h0 : ∀ x, wv n (V2 n C r2 c2 i) x (n + i) = false →
      wv n (V2 n C r2 c2 i) x (n + r1) = wv n (V2 n C r2 c2 i) x c1 := by
    intro x hx
    rw [V2_low n C r2 c2 i x hL.1 hr2 hc2lt hir2 hout (n + i) (by omega)] at hx
    rw [V2_low n C r2 c2 i x hL.1 hr2 hc2lt hir2 hout (n + r1) (by omega),
      V2_low n C r2 c2 i x hL.1 hr2 hc2lt hir2 hout c1 (by omega)]
    exact k1 x hx
  have hEfun : ∀ x, wv n (V1 n (V2 n C r2 c2 i) r1 c1) x (V1 n (V2 n C r2 c2 i) r1 c1).output =
      wv n C x C.output := fun x =>
    (V1_fun_top n (V2 n C r2 c2 i) r1 c1 i (tau n r2 c2 C.output) x hD (by rw [hDlen]; omega)
      hc1lt hir1 hDout hDtop (h0 x)).trans (hDfun x)
  have hDclean := V2_clean n C F r2 c2 i hL.1 hL.2.1 hr2 hc2lt hir2 hout
    (fun x hx => k2 x (below_off n C F hF i hbel x hx))
  have hEclean : Clean n F (V1 n (V2 n C r2 c2 i) r1 c1) :=
    V1_clean n (V2 n C r2 c2 i) F r1 c1 hD hDclean (by rw [hDlen]; omega)
      hc1lt (fun x hx => h0 x (by
        rw [V2_low n C r2 c2 i x hL.1 hr2 hc2lt hir2 hout (n + i) (by omega)]
        exact below_off n C F hF i hbel x hx))
  have hle := hL.2.2 _ (V1_AO2 n (V2 n C r2 c2 i) r1 c1 hD (by rw [hDlen]; omega) hc1lt) hEfun
    ((V1_orCount_le n (V2 n C r2 c2 i) r1 c1 (by rw [hDlen]; omega)).trans
      (le_of_eq (V2_orCount n C r2 c2 i hr2 hop2))) hEclean
  rw [V1_len, hDlen] at hle
  omega

lemma clean_step3_core (n : ℕ) (C : Circuit) (F : (Fin n → Bool) → Bool)
    (hF : ∀ x, wv n C x C.output = F x) (hL : CleanLeast n F C) (hout : C.output < n + C.gates.length)
    (i j : ℕ) (hbel : ∀ x, wv n C x (n + i) = true → wv n C x C.output = true)
    (hcone : InCone n C i j) :
    ∃ r c, r < C.gates.length ∧ i < r ∧ c < n + r ∧ c ≠ n + i ∧ c ∈ (gateAt C r).inputs ∧
      (gateAt C r).op = GateOp.or ∧
      (∀ k, k < C.gates.length → n + i ∈ (gateAt C k).inputs → k = r) ∧
      (∀ x, wv n C x (n + i) = false → wv n C x (n + r) = wv n C x c) := by
  obtain ⟨r, hr, hir, hrin, _⟩ := inCone_reader n C i j hcone
  obtain ⟨hop, c, hc, hclt, hi⟩ := clean_reader_or n C F hF hL hout i r hr hbel hrin
  refine ⟨r, c, hr, hir, hclt, hc, ?_, hop, ?_, ?_⟩
  · rcases hi with h | h <;> rw [h] <;> simp
  · intro k hk hkin
    rcases Nat.lt_trichotomy k r with h | h | h
    · exact (clean_reader_unique n C F hF hL hout i k r h hr hbel hkin hrin).elim
    · exact h
    · exact (clean_reader_unique n C F hF hL hout i r k h hk hbel hrin hkin).elim
  · intro x hx
    rw [wv_rec n C x (aob hL.1) r hr, hop]
    rcases hi with h | h
    · rw [h, eval_or_pair, hx]; rfl
    · rw [h, eval_or_pair, hx]; simp

lemma clean_least_of_same (n : ℕ) (F : (Fin n → Bool) → Bool) (C D : Circuit)
    (hL : CleanLeast n F C) (hD : AO2 n D) (hClean : Clean n F D)
    (hfun : ∀ x, wv n D x D.output = wv n C x C.output)
    (hlen : D.gates.length = C.gates.length) (hcount : orCount D = orCount C) : CleanLeast n F D :=
  ⟨hD, hClean, fun E hE hEf hEc hEclean => by
    rw [hlen]
    exact hL.2.2 E hE (fun x => (hEf x).trans (hfun x)) (hEc.trans hcount.le) hEclean⟩

lemma clean_step3_struct (n : ℕ) (C : Circuit) (F : (Fin n → Bool) → Bool) (hL : CleanLeast n F C)
    (hF : ∀ x, wv n C x C.output = F x) (hout : C.output < n + C.gates.length)
    (i j : ℕ) (hbel : ∀ x, wv n C x (n + i) = true → F x = true)
    (hcone : InCone n C i j) :
    ∃ (C' : Circuit) (r : ℕ), r < C.gates.length ∧ i < r ∧ CleanLeast n F C' ∧
      (∀ x, wv n C' x C'.output = F x) ∧ C'.gates.length = C.gates.length ∧
      (∀ k', k' < C.gates.length - 1 → (gateAt C' k').op = (gateAt C (rho r k')).op) ∧
      (gateAt C' (C.gates.length - 1)).op = GateOp.or ∧ (gateAt C r).op = GateOp.or ∧
      (∀ k', k' < C.gates.length - 1 →
        ((∀ x, wv n C' x (n + k') = true → F x = true) ↔
          (∀ x, wv n C x (n + rho r k') = true → F x = true))) ∧
      (∀ a' b', b' < C.gates.length - 1 → InCone n C' a' b' →
        InCone n C (rho r a') (rho r b')) ∧
      (∀ j', j' < C.gates.length - 1 → ¬ InCone n C' i j') ∧ orCount C' = orCount C := by
  have hbel' : ∀ x, wv n C x (n + i) = true → wv n C x C.output = true :=
    fun x h => by rw [hF]; exact hbel x h
  obtain ⟨r, c, hr, hir, hclt, hci, hcin, hop, huniq, h0⟩ :=
    clean_step3_core n C F hF hL hout i j hbel' hcone
  have hD := V2_AO2 n C r c i hL.1 hr hclt hir hout
  have hfun : ∀ x, wv n (V2 n C r c i) x (V2 n C r c i).output = wv n C x C.output :=
    fun x => V2_out n C r c i x hL.1 hr hclt hir hout (hbel' x) (h0 x)
  have hDclean := V2_clean n C F r c i hL.1 hL.2.1 hr hclt hir hout
    (fun x hx => h0 x (below_off n C F hF i hbel' x hx))
  refine ⟨V2 n C r c i, r, hr, hir, clean_least_of_same n F C _ hL hD hDclean hfun (V2_len n C r c i)
      (V2_orCount n C r c i hr hop),
    fun x => (hfun x).trans (hF x), V2_len n C r c i, ?_, ?_, hop, ?_, ?_, ?_, ?_⟩
  · intro k' hk'
    rw [V2_gate n C r c i k' hk']
  · rw [V2_top n C r c i (by omega)]
  · intro k' hk'
    exact V2_below n C r c i F hL.1 hr hclt hir hout hbel h0 k' hk'
  · intro a' b' hb' h
    exact V2_cone n C r c i hL.1 hr hclt hcin a' b' hb' h
  · exact V2_no_cone n C r c i hr hir hci huniq
  · exact V2_orCount n C r c i hr hop

open Classical in
lemma clean_main_ind (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : G.edgeFinset.Nonempty) :
    ∀ k : ℕ, ∀ C : Circuit, CleanLeast n (graphFun G ∅) C →
      (∀ x, wv n C x C.output = graphFun G ∅ x) →
      ((Finset.range C.gates.length ×ˢ Finset.range C.gates.length).filter
        (fun p : ℕ × ℕ => (gateAt C p.1).op = GateOp.and ∧
          (gateAt C p.2).op = GateOp.and ∧ InCone n C p.1 p.2)).card = k →
      ∃ C' : Circuit, CleanLeast n (graphFun G ∅) C' ∧
        (∀ x, wv n C' x C'.output = graphFun G ∅ x) ∧ C'.size = C.size ∧
        orCount C' = orCount C ∧
        (PEqualNP.TopForm.junk G C').card = (PEqualNP.TopForm.junk G C).card ∧
        PEqualNP.TopForm.TopForm G C' := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro C hC hF hk
    by_cases htop : PEqualNP.TopForm.TopForm G C
    · exact ⟨C, hC, hF, rfl, rfl, rfl, htop⟩
    · have hex : ∃ i j, i < C.gates.length ∧ j < C.gates.length ∧
          (gateAt C i).op = GateOp.and ∧ PEqualNP.TopForm.BelowF G C i ∧
          (gateAt C j).op = GateOp.and ∧ InCone n C i j := by
        by_contra hne
        apply htop
        intro i hi j hj h1 h2 h3 h4
        exact hne ⟨i, j, hi, hj, h1, h2, h3, h4⟩
      obtain ⟨i, j, hi, hj, hopi, hbi, hopj, hcone⟩ := hex
      obtain ⟨x1, hx1⟩ := exists_true n G hG
      have hout : C.output < n + C.gates.length := out_lt n C x1 (by rw [hF]; exact hx1)
      obtain ⟨C', r, hr, hir, hL', hF', hlen, hops, htop', hopr, hbelow, hcn, hno, hcount⟩ :=
        clean_step3_struct n C (graphFun G ∅) hC hF hout i j hbi hcone
      have hlt := pairs_lt n C C' r i j hr hir hlen hops htop' hcn hno hopi hopj hcone
      rw [hk] at hlt
      obtain ⟨C'', h1, h2, h3, h4, h5, h6⟩ := ih _ hlt C' hL' hF' rfl
      refine ⟨C'', h1, h2, h3.trans hlen, h4.trans hcount, h5.trans ?_, h6⟩
      refine junk_eq n C C' (graphFun G ∅) r hr hlen hops htop' hopr hbelow _ _ ?_ ?_
      · intro j
        exact mem_junk n G C j
      · intro j
        exact mem_junk n G C' j

theorem clean_top_form (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : G.edgeFinset.Nonempty) (C : Circuit) (hC : CleanLeast n (graphFun G ∅) C)
    (hF : circuitFun n C = graphFun G ∅) :
    ∃ D : Circuit, CleanLeast n (graphFun G ∅) D ∧ circuitFun n D = graphFun G ∅ ∧
      D.size = C.size ∧ orCount D = orCount C ∧
      (PEqualNP.TopForm.junk G D).card = (PEqualNP.TopForm.junk G C).card ∧
      PEqualNP.TopForm.TopForm G D := by
  obtain ⟨D, hD, hDf, hs, ho, hj, ht⟩ :=
    clean_main_ind n G hG _ C hC (fun x => congrFun hF x) rfl
  exact ⟨D, hD, funext hDf, hs, ho, hj, ht⟩

theorem exists_clean_minimum (n : ℕ) (F : (Fin n → Bool) → Bool) (C : Circuit)
    (hAO : AO2 n C) (hClean : Clean n F C) (hF : circuitFun n C = F) :
    ∃ B : Circuit, CleanLeast n F B ∧ circuitFun n B = F ∧
      B.size ≤ C.size ∧ orCount B ≤ orCount C := by
  classical
  let A (k : ℕ) : Prop := ∃ B : Circuit,
    AO2 n B ∧ Clean n F B ∧ circuitFun n B = F ∧ orCount B ≤ orCount C ∧ B.size = k
  have hex : ∃ k, A k := ⟨C.size, C, hAO, hClean, hF, le_rfl, rfl⟩
  obtain ⟨B, hBA, hBClean, hBF, hBO, hBS⟩ := Nat.find_spec hex
  refine ⟨B, ⟨hBA, hBClean, ?_⟩, hBF, ?_, hBO⟩
  · intro D hD hDf hDO hDClean
    have hDF : circuitFun n D = F := funext fun x => (hDf x).trans (congrFun hBF x)
    change B.size ≤ D.size
    rw [hBS]
    exact Nat.find_min' hex ⟨D, hD, hDClean, hDF, hDO.trans hBO, rfl⟩
  · rw [hBS]
    exact Nat.find_min' hex ⟨C, hAO, hClean, hF, le_rfl, rfl⟩

theorem exists_clean_top_form_with_or_budget (n : ℕ) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hG : G.edgeFinset.Nonempty) (C : Circuit)
    (hAO : PEqualNP.TopForm.IsAO2 n C) (hF : circuitFun n C = graphFun G ∅)
    (hClean : Clean n (graphFun G ∅) C) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧ circuitFun n D = graphFun G ∅ ∧
      D.size ≤ C.size ∧ orCount D ≤ orCount C ∧ Clean n (graphFun G ∅) D ∧
      PEqualNP.TopForm.TopForm G D := by
  obtain ⟨B, hBL, hBF, hBS, hBO⟩ :=
    exists_clean_minimum n (graphFun G ∅) C (ao2_of n C hAO) hClean hF
  obtain ⟨D, hDL, hDF, hDS, hDO, _, hDT⟩ := clean_top_form n G hG B hBL hBF
  exact ⟨D, ao2_to n D hDL.1, hDF, hDS.le.trans hBS, hDO.le.trans hBO, hDL.2.1, hDT⟩

theorem clean_iff_all_and_below (n : ℕ) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) :
    Clean n (graphFun G ∅) C ↔
      ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → PEqualNP.TopForm.BelowF G C k := by
  constructor
  · intro h k hk hop x hx
    cases hf : graphFun G ∅ x with
    | true => rfl
    | false =>
      have hz := h k hk hop x hf
      change wv n C x (n + k) = true at hx
      rw [hz] at hx
      cases hx
  · intro h k hk hop x hx
    cases hv : wv n C x (n + k) with
    | false => rfl
    | true =>
      have hf := h k hk hop x hv
      rw [hx] at hf
      cases hf

end Part8

end PEqualNP.Outside.L_meta_8323

-- Source module: Pnp4201CleanNormalize
namespace PEqualNP.Outside.L_meta_8323

namespace Part9

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_8323.Part5.Normalize
open PEqualNP.Outside.L_meta_8323.Part6

def AndClean (n : ℕ) (f : (Fin n → Bool) → Bool) (C : Circuit) : Prop :=
  ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
    ∀ x, f x = false → (C.wires (List.ofFn x)).getD (n + j) false = false

def step (g : Gate) (w : List Bool) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def AndOff : List Gate → List Bool → Prop
  | [], _ => True
  | g :: gs, w =>
      (g.op = GateOp.and → g.op.eval (g.inputs.map fun i => w.getD i false) = false) ∧
        AndOff gs (step g w)

theorem wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w = wiresFrom gs (step g w) := rfl

theorem wiresFrom_head (g : Gate) (gs : List Gate) (w : List Bool) :
    (wiresFrom (g :: gs) w).getD w.length false =
      g.op.eval (g.inputs.map fun i => w.getD i false) := by
  rw [wiresFrom_cons, getD_wiresFrom gs (step g w) w.length (by simp [step])]
  exact getD_snoc_eq _ _ _

theorem andOff_iff (gs : List Gate) (w : List Bool) :
    AndOff gs w ↔ ∀ (j : ℕ) (hj : j < gs.length), gs[j].op = GateOp.and →
      (wiresFrom gs w).getD (w.length + j) false = false := by
  induction gs generalizing w with
  | nil => simp [AndOff]
  | cons g gs ih =>
    constructor
    · rintro ⟨hg, ht⟩ j hj hop
      cases j with
      | zero => simpa [wiresFrom_head] using (wiresFrom_head g gs w).trans (hg hop)
      | succ j =>
        have hj' : j < gs.length := by simpa using hj
        have h := (ih (step g w)).1 ht j hj' (by simpa using hop)
        simpa [wiresFrom_cons, step, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
    · intro h
      refine ⟨?_, (ih (step g w)).2 ?_⟩
      · intro hg
        have hz := h 0 (by simp) (by simpa using hg)
        simpa only [Nat.add_zero, wiresFrom_head] using hz
      · intro j hj hop
        have ht := h (j + 1) (by simpa using hj) (by simpa using hop)
        simpa [wiresFrom_cons, step, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht

theorem andOff_append (pre post : List Gate) (w : List Bool) :
    AndOff (pre ++ post) w ↔ AndOff pre w ∧ AndOff post (wiresFrom pre w) := by
  induction pre generalizing w with
  | nil => simp [AndOff, wiresFrom]
  | cons g pre ih =>
    simp only [List.cons_append, AndOff, wiresFrom_cons, ih]
    exact and_assoc.symm

theorem simplify_some_stat (op : GateOp) (m : ℕ) (ins : List Stat) (g : Gate)
    (hg : (simplify op m ins).1 = some g) :
    (simplify op m ins).2 = Sum.inr m := by
  cases op <;> simp only [simplify] at hg ⊢
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;>
      (try cases a) <;> (try cases b) <;> simp [simpAnd] at hg ⊢
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;>
      (try cases a) <;> (try cases b) <;> simp [simpOr] at hg ⊢
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg ⊢
  · simp at hg
  · simp at hg

theorem simplify_andOff (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length)
    (hoff : op = GateOp.and → op.eval (ins.map (Stat.val w)) = false) :
    AndOff (simplify op w.length ins).1.toList w := by
  cases hs : (simplify op w.length ins).1 with
  | none => trivial
  | some g =>
    refine ⟨?_, trivial⟩
    intro hg
    have hgop : g.op = op := simplify_op op w.length ins g (by rw [hs]; simp)
    have hstat := simplify_some_stat op w.length ins g hs
    have hval := (simplify_sound op hop w ins hlen hv).2
    rw [hstat, hs] at hval
    have hv' : g.op.eval (g.inputs.map fun i => w.getD i false) =
        op.eval (ins.map (Stat.val w)) := by
      simpa only [Option.toList_some, Stat.val, wiresFrom_head] using hval
    exact hv'.trans (hoff (hgop.symm.trans hg))

theorem elim_andOff (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate),
      (∀ g ∈ gs, Ok g) → Inv n y w acc → AndOff gs w → AndOff acc.2 y →
      AndOff (elim n gs acc).2 y := by
  induction gs with
  | nil => intro w acc _ _ _ hacc; exact hacc
  | cons g gs ih =>
    intro w acc hok hinv horig hacc
    have hinv' : Inv n y (wiresFrom [g] w) (elimStep n acc g) :=
      inv_elim n y hy [g] w acc
        (fun g' hg' => hok g' (by simp at hg'; simp [hg'])) hinv
    rw [elim_cons]
    apply ih (step g w) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) hinv' horig.2
    change AndOff (acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList) y
    apply (andOff_append _ _ _).2
    refine ⟨hacc, ?_⟩
    let w' := wiresFrom acc.2 y
    have lw' : w'.length = n + acc.2.length := by
      dsimp [w']; rw [length_wiresFrom, hy]
    rw [← lw']
    apply simplify_andOff g.op (hok g List.mem_cons_self).1 w'
    · simpa using (hok g List.mem_cons_self).2
    · intro s hs
      obtain ⟨i, _, rfl⟩ := List.mem_map.1 hs
      rw [lw']
      exact (hinv.2 i).1
    · intro hg
      have he : (g.inputs.map fun i => acc.1.getD i (Sum.inl false)).map
          (Stat.val w') = g.inputs.map fun i => w.getD i false := by
        rw [List.map_map]
        apply List.map_congr_left
        intro i _
        exact (hinv.2 i).2
      rw [he]
      exact horig.1 hg

theorem normalize_nonconstant_clean_budgets (n : ℕ) (C : Circuit) (hM : Monotone2 C)
    (f : (Fin n → Bool) → Bool) (hf : circuitFun n C = f)
    (hnc : ∃ x y, f x ≠ f y) (hclean : AndClean n f C) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧ circuitFun n D = f ∧
      D.size ≤ C.size ∧ (∀ p : GateOp → Bool, opCount p D ≤ opCount p C) ∧
      AndClean n f D := by
  let acc := elim n C.gates (idStats n, [])
  have hok : ∀ g ∈ C.gates, Ok g := by
    intro g hg
    refine ⟨?_, (hM g hg).2⟩
    rcases (hM g hg).1 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  have hao : AO C.gates := fun g hg => (hM g hg).1
  have hinv : ∀ x : Fin n → Bool,
      Inv n (List.ofFn x) (wiresFrom C.gates (List.ofFn x)) acc :=
    fun x => inv_elim n _ (by simp) C.gates _ _ hok (inv_id n x)
  have hval : ∀ x : Fin n → Bool,
      (acc.1.getD C.output (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn x)) = f x := by
    intro x
    exact ((hinv x).2 C.output).2.trans (congrFun hf x)
  have hlen : acc.2.length ≤ C.size := by
    have h := elim_len n C.gates (idStats n, [])
    simpa only [acc, Circuit.size, List.length_nil, zero_add] using h
  have hcount (p : GateOp → Bool) :
      acc.2.countP (fun g => p g.op) ≤ opCount p C := by
    have h := PEqualNP.Outside.L_meta_8323.Part6.Normalize.elim_countP p n C.gates (idStats n, [])
    simpa only [acc, opCount, List.countP_nil, zero_add] using h
  have haccClean : ∀ x : Fin n → Bool, f x = false → AndOff acc.2 (List.ofFn x) := by
    intro x hx
    apply elim_andOff n (List.ofFn x) (by simp) C.gates (List.ofFn x) (idStats n, [])
      hok (inv_id n x) ?_ trivial
    apply (andOff_iff C.gates (List.ofFn x)).2
    intro j hj hop
    have hg : (gateAt C j).op = GateOp.and := by
      rw [PEqualNP.Outside.L_meta_8323.Part5.gateAt_eq hj]
      exact hop
    simpa only [List.length_ofFn, wires_eq] using hclean j hj hg x hx
  cases hs : acc.1.getD C.output (Sum.inl false) with
  | inl b =>
    exfalso
    obtain ⟨x, y, hxy⟩ := hnc
    apply hxy
    rw [← hval x, ← hval y, hs]
    rfl
  | inr w =>
    refine ⟨⟨acc.2, w⟩, ?_, ?_, hlen, hcount, ?_⟩
    · apply ao_clean_isAO2
      · exact elim_ao n C.gates _ hao (by intro g hg; simp at hg)
      · exact clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) C.gates _ _ hok
          (inv_id n _) (by intro p g hp; simp at hp)
    · funext x
      have hx := hval x
      rw [hs] at hx
      exact hx
    · intro j hj hop x hx
      have hg : acc.2[j].op = GateOp.and := by
        have hgate : gateAt (⟨acc.2, w⟩ : Circuit) j = acc.2[j] :=
          List.getD_eq_getElem _ _ hj
        rwa [hgate] at hop
      simpa only [List.length_ofFn, wires_eq] using
        (andOff_iff acc.2 (List.ofFn x)).1 (haccClean x hx) j hj hg

end Part9

end PEqualNP.Outside.L_meta_8323

-- Source module: Pnp4201CleanCase
namespace PEqualNP.Outside.L_meta_8323

namespace Part10

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.Outside.L_meta_8323.Part1 PEqualNP.Outside.L_meta_8323.Part6
open PEqualNP.Outside.L_meta_8323.Part8 PEqualNP.Outside.L_meta_8323.Part4
open PEqualNP.Outside.L_meta_8323.Part9

lemma clean_ao2_lower_bound (C : Circuit) (hAO : IsAO2 42 C)
    (hf : circuitFun 42 C = graphFun pg4 ∅)
    (hclean : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → BelowF pg4 C j) :
    104 ≤ C.gates.countP
      (fun g => GateOp.casesOn g.op false true false (fun _ => false) false) := by
  have hG : pg4.edgeFinset.Nonempty := Finset.card_pos.mp (by rw [edgeFinset_card]; decide)
  obtain ⟨D, hDA, hDF, _, hDO, hDC, hDT⟩ :=
    exists_clean_top_form_with_or_budget 42 pg4 hG C hAO hf
      ((clean_iff_all_and_below 42 pg4 C).mpr hclean)
  have hb := clean_top_or_bound 42 pg4 D hDA noFourCycle hDF hDT
    ((clean_iff_all_and_below 42 pg4 D).mp hDC)
  change orderedEdges.card ≤ _ at hb
  rw [orderedEdges_card] at hb
  rw [orCount_eq_public D, orCount_eq_public C] at hDO
  omega

lemma clean_monotone_lower_bound (C : Circuit) (hM : Monotone2 C)
    (hf : circuitFun 42 C = graphFun pg4 ∅)
    (hclean : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → BelowF pg4 C j) :
    104 ≤ C.gates.countP
      (fun g => GateOp.casesOn g.op false true false (fun _ => false) false) := by
  have hC : Clean 42 (graphFun pg4 ∅) C := (clean_iff_all_and_below 42 pg4 C).mpr hclean
  obtain ⟨D, hDA, hDF, _, hDB, hDC⟩ :=
    normalize_nonconstant_clean_budgets 42 C hM (graphFun pg4 ∅) hf nonconstant hC
  have hDC' : Clean 42 (graphFun pg4 ∅) D := hDC
  have hb := clean_ao2_lower_bound D hDA hDF ((clean_iff_all_and_below 42 pg4 D).mp hDC')
  have hDO : orCount D ≤ orCount C := hDB isOr
  rw [orCount_eq_public D, orCount_eq_public C] at hDO
  exact hb.trans hDO

theorem exact_8323 : have x1 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x1 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x2 : Fin (42 : ℕ) → Bool), x1.eval (List.ofFn x2) = Bool.true ↔ ∃ (x3 : Fin (42 : ℕ)) (x4 : Fin (42 : ℕ)), (↑x3 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x4 ∧ (↑x4 + (21 : ℕ) - ↑x3) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x2 x3 = Bool.true ∧ x2 x4 = Bool.true; have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x3]? = Option.some x4 → x4.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x7 : Fin (42 : ℕ) → Bool), (x2.wires (List.ofFn x7)).getD ((42 : ℕ) + x3) Bool.false = Bool.true → x2.eval (List.ofFn x7) = Bool.true; have x3 : PEqualNP.CircuitLowerBounds.Circuit → ℕ := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => List.countP (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.casesOn x4.op Bool.false Bool.true Bool.false (fun (x5 : ℕ) => Bool.false) Bool.false) x3.gates; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → x1 x4 → x2 x4 → (104 : ℕ) ≤ x3 x4 := by
  dsimp only
  intro C hM hF hSafe
  have hf : circuitFun 42 C = graphFun pg4 ∅ := (computes_iff C).mp hF
  apply clean_monotone_lower_bound C hM hf
  intro j hj hop x hx
  have hg : C.gates[j]? = some (gateAt C j) := by
    rw [PEqualNP.Outside.L_meta_8323.Part2.s2231_gateAt_eq C j hj]
    simp [hj]
  have hout := hSafe j (gateAt C j) hg hop x hx
  change circuitFun 42 C x = true at hout
  rwa [hf] at hout

end Part10

end PEqualNP.Outside.L_meta_8323

theorem PEqualNP.Outside.L_meta_8323 : have x1 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x1 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x2 : Fin (42 : ℕ) → Bool), x1.eval (List.ofFn x2) = Bool.true ↔ ∃ (x3 : Fin (42 : ℕ)) (x4 : Fin (42 : ℕ)), (↑x3 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x4 ∧ (↑x4 + (21 : ℕ) - ↑x3) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x2 x3 = Bool.true ∧ x2 x4 = Bool.true; have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x3]? = Option.some x4 → x4.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x7 : Fin (42 : ℕ) → Bool), (x2.wires (List.ofFn x7)).getD ((42 : ℕ) + x3) Bool.false = Bool.true → x2.eval (List.ofFn x7) = Bool.true; have x3 : PEqualNP.CircuitLowerBounds.Circuit → ℕ := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => List.countP (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.casesOn x4.op Bool.false Bool.true Bool.false (fun (x5 : ℕ) => Bool.false) Bool.false) x3.gates; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → x1 x4 → x2 x4 → (104 : ℕ) ≤ x3 x4 := by
  exact PEqualNP.Outside.L_meta_8323.Part10.exact_8323
