import Pnp5126TopForm
import Pnp5126OwnershipWitness

/-!
Checked preprocessing of a hypothetical two-junk circuit in L-meta-5126.
The remaining two-junk configurations are not proved impossible here.
-/

namespace Pnp5126Shape

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.SplitCount
open PEqualNP.Outside.Pnp5126OwnershipWitness Pnp5126TopForm

theorem normalized_pair_or_shared_triple {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hC : IsLeastAO G C)
    (hTwo : (junk G C).card = 2)
    (hOff : ∀ k ∈ junk G C, ∀ v : Fin n, gateVal n C k (unitInput v) = false) :
    ∃ D : Circuit, ∃ g t : ℕ,
      IsLeastAO G D ∧ D.size = C.size ∧ TopForm G D ∧ g < t ∧ junk G D = {g,t} ∧
      (∀ k ∈ junk G D, ∀ v : Fin n, gateVal n D k (unitInput v) = false) ∧
      (∃ S : Finset (Fin n), S.card = 2 ∧ graphFun G ∅ (setInput S) = false ∧
        gateVal n D g (setInput S) = true) ∧
      ((∃ S : Finset (Fin n), S.card = 2 ∧ graphFun G ∅ (setInput S) = false ∧
          gateVal n D t (setInput S) = true) ∨
        (∃ S : Finset (Fin n), S.card = 3 ∧ graphFun G ∅ (setInput S) = false ∧
          gateVal n D g (setInput S) = true ∧ gateVal n D t (setInput S) = true)) := by
  obtain ⟨D,hD,hsize,hcard,htop,hOffD⟩ := normalize_two_junk n G C hC hTwo hOff
  obtain ⟨a,b,hab,hJ⟩ := Finset.card_eq_two.mp hcard
  have horder : ∃ g t : ℕ, g < t ∧ junk G D = {g,t} := by
    rcases lt_or_gt_of_ne hab with h | h
    · exact ⟨a,b,h,hJ⟩
    · exact ⟨b,a,h,by simpa [Finset.pair_comm] using hJ⟩
  obtain ⟨g,t,hgt,hJ⟩ := horder
  refine ⟨D,g,t,hD,hsize,htop,hgt,hJ,hOffD,?_,?_⟩
  · apply two_junk_first_pair G D hD.1 g t hgt hJ
    exact hOffD g (by rw [hJ]; simp)
  · exact second_pair_or_shared_triple G D hD.1 g t hgt hJ hOffD

/-- A two-junk exclusion proved only in TopForm suffices for the original model.
The first-rung, bipartition, and four-cycle assumptions can be retained in the
caller; this normalization step does not require them. -/
theorem top_form_suffices {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hTop : ∀ D : Circuit, IsLeastAO G D → TopForm G D →
      (∀ k ∈ junk G D, ∀ v : Fin n, gateVal n D k (unitInput v) = false) →
      (junk G D).card ≠ 2) :
    ∀ C : Circuit, IsLeastAO G C →
      (∀ k ∈ junk G C, ∀ v : Fin n, gateVal n C k (unitInput v) = false) →
      (junk G C).card ≠ 2 := by
  intro C hC hOff hTwo
  obtain ⟨D,hD,_,hcard,htop,hOffD⟩ := normalize_two_junk n G C hC hTwo hOff
  exact hTop D hD htop hOffD hcard

end Pnp5126Shape
