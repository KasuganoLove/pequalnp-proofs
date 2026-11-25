import Pnp2343Pruning

/-!
Finite signature ranks for a least circuit fitting two sample families.
These are direct cardinal consequences of the two-sided erasure witnesses in
`Pnp2343Pruning`; its physical erasure helpers are attributed there to upstream
L_meta_2668 and L-meta-1499 / PR3112 (Apache-2.0).

The ranks are local: OR gates can increase negative signatures, and AND gates
can decrease positive signatures.  These inequalities alone do not sum to a
lower bound for a circuit with arbitrary sharing and mixed gate operations.
-/

namespace Pnp2343SignatureRanks

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover
  PEqualNP.Outside.Pnp2343Pruning

def firingSet {ι : Type} [Fintype ι] (samples : ι → List Bool)
    (C : Circuit) (w : ℕ) : Finset ι :=
  Finset.univ.filter (fun q => val C (samples q) w = true)

@[simp] theorem mem_firingSet {ι : Type} [Fintype ι] (samples : ι → List Bool)
    (C : Circuit) (w : ℕ) (q : ι) :
    q ∈ firingSet samples C w ↔ val C (samples q) w = true := by
  simp [firingSet]

theorem and_negative_strict {α β : Type} [Fintype β]
    (n : ℕ) (positive : α → List Bool) (negative : β → List Bool)
    (hpLen : ∀ p, (positive p).length = n) (hnLen : ∀ q, (negative q).length = n)
    (C : Circuit) (hmin : LeastSamples n positive negative C)
    (r a b : ℕ) (hr : r < C.gates.length)
    (hop : (gateAt C r).op = GateOp.and) (hins : (gateAt C r).inputs = [a,b]) :
    firingSet negative C (n+r) ⊂ firingSet negative C a ∧
    firingSet negative C (n+r) ⊂ firingSet negative C b := by
  obtain ⟨⟨qa,hqa,hqb⟩,⟨qb,hqb',hqa'⟩⟩ :=
    and_negative_incomparable n positive negative hpLen hnLen C hmin r a b hr hop hins
  have hsub (i : ℕ) (hi : i ∈ (gateAt C r).inputs) :
      firingSet negative C (n+r) ⊆ firingSet negative C i := by
    intro q hq
    apply (mem_firingSet negative C i q).2
    exact ((val_and (hnLen q) hr hop).1
      ((mem_firingSet negative C (n+r) q).1 hq) i hi).2
  constructor
  · refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub a (by simp [hins]), ?_⟩
    intro he
    have hgate : qa ∈ firingSet negative C (n+r) := by
      rw [he]
      exact (mem_firingSet negative C a qa).2 hqa
    have hb := ((val_and (hnLen qa) hr hop).1
      ((mem_firingSet negative C (n+r) qa).1 hgate) b (by simp [hins])).2
    rw [hqb] at hb
    contradiction
  · refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub b (by simp [hins]), ?_⟩
    intro he
    have hgate : qb ∈ firingSet negative C (n+r) := by
      rw [he]
      exact (mem_firingSet negative C b qb).2 hqb'
    have ha := ((val_and (hnLen qb) hr hop).1
      ((mem_firingSet negative C (n+r) qb).1 hgate) a (by simp [hins])).2
    rw [hqa'] at ha
    contradiction

theorem or_positive_strict {α β : Type} [Fintype α]
    (n : ℕ) (positive : α → List Bool) (negative : β → List Bool)
    (hpLen : ∀ p, (positive p).length = n) (hnLen : ∀ q, (negative q).length = n)
    (C : Circuit) (hmin : LeastSamples n positive negative C)
    (r a b : ℕ) (hr : r < C.gates.length)
    (hop : (gateAt C r).op = GateOp.or) (hins : (gateAt C r).inputs = [a,b]) :
    firingSet positive C a ⊂ firingSet positive C (n+r) ∧
    firingSet positive C b ⊂ firingSet positive C (n+r) := by
  obtain ⟨⟨pa,hpa,hpb⟩,⟨pb,hpb',hpa'⟩⟩ :=
    or_positive_incomparable n positive negative hpLen hnLen C hmin r a b hr hop hins
  have hsub (i : ℕ) (hi : i ∈ (gateAt C r).inputs) :
      firingSet positive C i ⊆ firingSet positive C (n+r) := by
    intro p hp
    apply (mem_firingSet positive C (n+r) p).2
    exact (val_or (hpLen p) hr hop).2
      ⟨i, hi, hmin.2.1 r hr i hi, (mem_firingSet positive C i p).1 hp⟩
  constructor
  · refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub a (by simp [hins]), ?_⟩
    intro he
    have hgate : pb ∈ firingSet positive C (n+r) :=
      hsub b (by simp [hins]) ((mem_firingSet positive C b pb).2 hpb')
    rw [← he] at hgate
    have ha := (mem_firingSet positive C a pb).1 hgate
    rw [hpa'] at ha
    contradiction
  · refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub b (by simp [hins]), ?_⟩
    intro he
    have hgate : pa ∈ firingSet positive C (n+r) :=
      hsub a (by simp [hins]) ((mem_firingSet positive C a pa).2 hpa)
    rw [← he] at hgate
    have hb := (mem_firingSet positive C b pa).1 hgate
    rw [hpb] at hb
    contradiction

theorem and_negative_rank {α β : Type} [Fintype β]
    (n : ℕ) (positive : α → List Bool) (negative : β → List Bool)
    (hpLen : ∀ p, (positive p).length = n) (hnLen : ∀ q, (negative q).length = n)
    (C : Circuit) (hmin : LeastSamples n positive negative C)
    (r a b : ℕ) (hr : r < C.gates.length)
    (hop : (gateAt C r).op = GateOp.and) (hins : (gateAt C r).inputs = [a,b]) :
    (firingSet negative C (n+r)).card + 1 ≤
      min (firingSet negative C a).card (firingSet negative C b).card := by
  obtain ⟨ha,hb⟩ := and_negative_strict n positive negative hpLen hnLen C hmin r a b hr hop hins
  exact le_min (Finset.card_lt_card ha) (Finset.card_lt_card hb)

theorem or_positive_rank {α β : Type} [Fintype α]
    (n : ℕ) (positive : α → List Bool) (negative : β → List Bool)
    (hpLen : ∀ p, (positive p).length = n) (hnLen : ∀ q, (negative q).length = n)
    (C : Circuit) (hmin : LeastSamples n positive negative C)
    (r a b : ℕ) (hr : r < C.gates.length)
    (hop : (gateAt C r).op = GateOp.or) (hins : (gateAt C r).inputs = [a,b]) :
    max (firingSet positive C a).card (firingSet positive C b).card + 1 ≤
      (firingSet positive C (n+r)).card := by
  obtain ⟨ha,hb⟩ := or_positive_strict n positive negative hpLen hnLen C hmin r a b hr hop hins
  have ha' := Finset.card_lt_card ha
  have hb' := Finset.card_lt_card hb
  omega

end Pnp2343SignatureRanks
