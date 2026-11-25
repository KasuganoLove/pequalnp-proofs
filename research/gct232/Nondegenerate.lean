import Mathlib

namespace SymmetricLevel.Nondegenerate

abbrev V := Fin 4 → ℂ

private def bilinearValue (u v w : V) : ℂ :=
  dotProduct u u * (dotProduct v w - (∑ i, v i) * ∑ i, w i) + dotProduct u v * dotProduct u w

private def form (u : V) : LinearMap.BilinForm ℂ V :=
  LinearMap.mk₂ ℂ (bilinearValue u)
    (by intro v v' w; simp only [bilinearValue,add_dotProduct,dotProduct_add,Pi.add_apply,Finset.sum_add_distrib]; ring)
    (by intro a v w; simp only [bilinearValue,smul_dotProduct,dotProduct_smul,Pi.smul_apply,smul_eq_mul,← Finset.mul_sum]; ring)
    (by intro v w w'; simp only [bilinearValue,dotProduct_add,Pi.add_apply,Finset.sum_add_distrib]; ring)
    (by intro a v w; simp only [bilinearValue,dotProduct_smul,Pi.smul_apply,smul_eq_mul,← Finset.mul_sum]; ring)

private theorem symmetric (u v w : V) : form u v w = form u w v := by
  change bilinearValue u v w = bilinearValue u w v
  unfold bilinearValue
  rw [dotProduct_comm v w]
  ring

/-- Testing a radical vector on the all-ones vector, u, and then each
    standard basis vector eliminates its coordinate sum, u-dot product, and coordinates. -/
private theorem radical {u : V} (sumZero : ∑ i, u i = 0) (cne : dotProduct u u ≠ 0)
    (v : V) (against : ∀ w, form u v w = 0) : v = 0 := by
  have h1 := against (1 : V)
  change bilinearValue u v 1 = 0 at h1
  simp [bilinearValue,dotProduct_one,sumZero] at h1
  have sumV : ∑ i, v i = 0 := by
    have linear := h1.resolve_left cne
    linear_combination -(1/3 : ℂ) * linear
  have h2 := against u
  change bilinearValue u v u = 0 at h2
  rw [bilinearValue,sumV,zero_mul,sub_zero,dotProduct_comm v u] at h2
  have dotV : dotProduct u v = 0 := by
    apply (mul_eq_zero.mp _).resolve_left cne
    linear_combination (1/2 : ℂ) * h2
  funext i
  have h := against (Pi.single i 1)
  change bilinearValue u v (Pi.single i 1) = 0 at h
  rw [bilinearValue,sumV,zero_mul,sub_zero,dotV,zero_mul,add_zero,dotProduct_single_one] at h
  exact (mul_eq_zero.mp h).resolve_left cne

private theorem nonsingular {u : V} (sumZero : ∑ i, u i = 0) (cne : dotProduct u u ≠ 0) :
    (form u).Nondegenerate :=
  ⟨radical sumZero cne,fun v h => radical sumZero cne v (fun w => (symmetric u v w).trans (h w))⟩

/-- The common-factor quadratic equation cuts out totally isotropic subspaces
    of a nondegenerate bilinear form whenever u has zero sum and nonzero self-dot. -/
theorem dimension_bound {u : V} (sumZero : ∑ i, u i = 0) (cne : dotProduct u u ≠ 0)
    (W : Submodule ℂ V)
    (vanish : ∀ v ∈ W, dotProduct u u * (dotProduct v v - (∑ i, v i)^2) + (dotProduct u v)^2 = 0) :
    Module.finrank ℂ W ≤ 2 := by
  have diagonal (v) (hv : v ∈ W) : form u v v = 0 := by
    change bilinearValue u v v = 0
    simpa only [bilinearValue,pow_two] using vanish v hv
  have within : W ≤ (form u).orthogonal W := by
    intro v hv
    apply LinearMap.BilinForm.mem_orthogonal_iff.mpr
    intro w hw
    have both := diagonal (w+v) (W.add_mem hw hv)
    simp only [map_add,LinearMap.add_apply,diagonal w hw,diagonal v hv] at both
    rw [symmetric u v w] at both
    linear_combination (1/2 : ℂ) * both
  have bound := Submodule.finrank_mono within
  have dimension := LinearMap.BilinForm.finrank_orthogonal (nonsingular sumZero cne) W
  have ambient : Module.finrank ℂ V = 4 := by simp [V]
  rw [ambient] at dimension
  have atMost := Submodule.finrank_le W
  rw [ambient] at atMost
  omega

end SymmetricLevel.Nondegenerate
