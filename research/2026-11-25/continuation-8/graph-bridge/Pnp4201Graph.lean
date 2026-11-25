import PEqualNP.Defs
import Pnp4201Cover105

/-!
Concrete graph bridge for L-meta-4201. The same `SimpleGraph.fromRel` graph
already appears in upstream R_meta_2379_1 and L_meta_5058. This file adds the
geometry and semantic bridges needed by the OR-budget research. It reuses the
21-by-21 common-line certificate from Pnp4201Cover105; it does not enumerate
four independent Fin42 vertices or assert any all-clean normal-form existence.
-/
namespace PEqualNP.Outside.Pnp4201Graph

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
open PEqualNP.Outside.Pnp4201Cover105

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

-- These are only 21-by-21 adjacency tables, not a four-vertex C4 search.
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

-- A second finite count checks the standard undirected graph edge container.
-- Its domain is Sym2(Fin42), not four independently quantified vertices.
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

end PEqualNP.Outside.Pnp4201Graph
