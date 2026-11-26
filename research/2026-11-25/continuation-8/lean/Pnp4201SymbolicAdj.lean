import Pnp4201Graph

/- Symbolic replacements for the three finite adjacency-table certificates.
No change to the frozen graph module is made here. -/
namespace PEqualNP.Outside.Pnp4201SymbolicAdj

open PEqualNP.Outside.Pnp4201Graph PEqualNP.Outside.Pnp4201Cover105

theorem not_adj_point_point (p q : Fin 21) : ¬ pg4.Adj (point p) (point q) := by
  intro h
  rcases (SimpleGraph.fromRel_adj ..).mp h with ⟨_, h | h⟩
  · have hq := q.isLt
    have hbad : 21 ≤ q.val := h.2.1
    omega
  · have hp := p.isLt
    have hbad : 21 ≤ p.val := h.2.1
    omega

theorem not_adj_line_line (p q : Fin 21) : ¬ pg4.Adj (line p) (line q) := by
  intro h
  rcases (SimpleGraph.fromRel_adj ..).mp h with ⟨_, h | h⟩
  · have hbad : 21 + p.val < 21 := h.1
    omega
  · have hbad : 21 + q.val < 21 := h.1
    omega

theorem adj_point_line (p l : Fin 21) : pg4.Adj (point p) (line l) ↔ Inc p l := by
  have hp := p.isLt
  have hshift : 21 + l.val + 21 - p.val = 21 + (l.val + 21 - p.val) := by omega
  have hmod : (21 + l.val + 21 - p.val) % 21 = (l.val + 21 - p.val) % 21 := by
    rw [hshift, Nat.add_mod]
    simp
  change (point p ≠ line l ∧ (Forward (point p) (line l) ∨
    Forward (line l) (point p))) ↔ Inc p l
  constructor
  · rintro ⟨_, h | h⟩
    · change (l.val + 21 - p.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)
      have hm := h.2.2
      change (21 + l.val + 21 - p.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ) at hm
      rwa [hmod] at hm
    · have hbad : 21 + l.val < 21 := h.1
      omega
  · intro h
    refine ⟨point_ne_line p l, Or.inl ⟨hp, by change 21 ≤ 21 + l.val; omega, ?_⟩⟩
    change (21 + l.val + 21 - p.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)
    rw [hmod]
    exact h

end PEqualNP.Outside.Pnp4201SymbolicAdj
