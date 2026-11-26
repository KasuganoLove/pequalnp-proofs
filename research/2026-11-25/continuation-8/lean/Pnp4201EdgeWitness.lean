import Pnp4201Graph

/-!
A direct nonempty-edge witness for PG4, avoiding the unrelated full Sym2
edgeFinset cardinality certificate. The proof uses only the graph definition
and the single adjacency between vertices 0 and 21.
-/

namespace PEqualNP.Outside.Pnp4201EdgeWitness

open PEqualNP.Outside.Pnp4201Graph

theorem zero_twentyOne_adj : pg4.Adj (0 : Fin 42) (21 : Fin 42) := by
  change (0 : Fin 42) ≠ 21 ∧ (Forward 0 21 ∨ Forward 21 0)
  decide

theorem edgeFinset_nonempty : pg4.edgeFinset.Nonempty := by
  refine ⟨s((0 : Fin 42), (21 : Fin 42)), ?_⟩
  rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
  exact zero_twentyOne_adj

end PEqualNP.Outside.Pnp4201EdgeWitness
