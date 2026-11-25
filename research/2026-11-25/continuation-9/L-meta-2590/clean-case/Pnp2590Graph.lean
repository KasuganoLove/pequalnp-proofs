import PEqualNP.Defs

/-!
Exact Petersen graph for the held L-meta-2590 statement.
The fifteen listed edges are copied from that public statement. Finite geometry
certificates use kernel reduction. No circuit lower bound is assumed here.
-/

namespace PEqualNP.Outside.Pnp2590Graph

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

def edges : List (Fin 10 × Fin 10) :=
  [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),
    (5,7),(7,9),(9,6),(6,8),(8,5)]

def G : SimpleGraph (Fin 10) := SimpleGraph.fromRel (fun u v => (u,v) ∈ edges)

instance : DecidableRel G.Adj := by
  intro u v
  change Decidable (u ≠ v ∧ ((u,v) ∈ edges ∨ (v,u) ∈ edges))
  infer_instance

def target (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
  x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

lemma edge_distinct : ∀ e ∈ edges, e.1 ≠ e.2 := by decide +kernel

lemma target_eq_any (x : Fin 10 → Bool) :
    target x = edges.any (fun e => x e.1 && x e.2) := by
  simp [target, edges, Bool.or_assoc]

lemma target_eq_graphFun : target = graphFun G ∅ := by
  funext x
  apply Bool.eq_iff_iff.mpr
  rw [target_eq_any]
  have hg : graphFun G ∅ x = true ↔
      ∃ u v : Fin 10, G.Adj u v ∧ x u = true ∧ x v = true := by simp [graphFun]
  rw [hg]
  simp only [List.any_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨⟨u,v⟩, he, hu, hv⟩
    exact ⟨u,v,(SimpleGraph.fromRel_adj ..).mpr ⟨edge_distinct (u,v) he, Or.inl he⟩,hu,hv⟩
  · rintro ⟨u,v,h,hu,hv⟩
    rcases ((SimpleGraph.fromRel_adj ..).mp h).2 with he | he
    · exact ⟨(u,v),he,hu,hv⟩
    · exact ⟨(v,u),he,hv,hu⟩

def orderedEdges : Finset (Fin 10 × Fin 10) :=
  Finset.univ.filter fun e => e.1 < e.2 ∧ G.Adj e.1 e.2

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16000 in
theorem noFourCycle : NoFourCycle G := by decide +kernel

theorem edge_count : orderedEdges.card = 15 := by decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 16000 in
/-- Exact finite vertex-cover obstruction for Petersen's graph. -/
theorem cover_ge_six : ∀ T : Finset (Fin 10),
    (∀ e ∈ orderedEdges, e.1 ∈ T ∨ e.2 ∈ T) → 6 ≤ T.card := by
  decide +kernel

lemma nonempty_edges : G.edgeFinset.Nonempty := by
  refine ⟨s(0,1), ?_⟩
  exact SimpleGraph.mem_edgeFinset.mpr (by decide +kernel)

lemma target_nonconstant : ∃ x y, target x ≠ target y := by
  refine ⟨fun _ => false, fun _ => true, ?_⟩
  decide +kernel

end PEqualNP.Outside.Pnp2590Graph
