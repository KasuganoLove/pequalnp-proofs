import PEqualNP.Gct.Helpers.MincExpansion
import PEqualNP.Gct.Helpers.RankOne

namespace SymmetricLevel.RankOne

open Finset Polynomial
open PEqualNP.Gct.Helpers

noncomputable def elem {n : ℕ} (u : Fin n → ℂ) (k : ℕ) : ℂ :=
  ∑ S : RankOne.KSub n k, ∏ i ∈ S.1, u i

noncomputable def linePoly {n : ℕ} (u : Fin n → ℂ) : Polynomial ℂ :=
  ∑ k ∈ range (n+1), Polynomial.C (((n-k).factorial : ℂ) * (k.factorial : ℂ) * (elem u k)^2) *
    Polynomial.X^k

private theorem scale_elem {n : ℕ} (u : Fin n → ℂ) (z : ℂ) (k : ℕ) :
    elem (fun i => z*u i) k = z^k * elem u k := by
  unfold elem
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  simp [Finset.prod_mul_distrib,S.2]

/-- The complete univariate permanent on a symmetric outer-product line.
    The k-th coefficient is (n-k)! k! times the squared elementary symmetric sum. -/
theorem eval_linePoly {n : ℕ} (u : Fin n → ℂ) (z : ℂ) :
    (linePoly u).eval z =
      Matrix.permanent (Matrix.of fun i j : Fin n => 1 + z*u i*u j) := by
  let t := fun p : Fin n × Fin n => (z*u p.1)*u p.2
  have expansion := Minc.minc_Mk n t
  rw [PEqualNP.Gct.MethodCeiling.eval_permPoly] at expansion
  rw [show Matrix.permanent (Matrix.of fun i j : Fin n => 1 + z*u i*u j) = _ from expansion]
  simp only [linePoly,Polynomial.eval_finsetSum,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_pow,Polynomial.eval_X]
  apply Finset.sum_congr rfl
  intro k _
  have factor : Minc.Mk n k t = (k.factorial : ℂ) * elem (fun i => z*u i) k * elem u k :=
    PEqualNP.Gct.Helpers.RankOne.Mk_rankOne n k (fun i => z*u i) u
  rw [factor,scale_elem]
  ring

noncomputable def support {n : ℕ} (u : Fin n → ℂ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => u i ≠ 0)

private theorem support_only {n : ℕ} (u : Fin n → ℂ) :
    elem u (support u).card = ∏ i ∈ support u, u i := by
  classical
  let I := support u
  let s : PEqualNP.Gct.Helpers.RankOne.KSub n I.card := ⟨I,rfl⟩
  change (∑ S : PEqualNP.Gct.Helpers.RankOne.KSub n I.card, ∏ i ∈ S.1, u i) = _
  rw [Fintype.sum_eq_single s]
  · intro S different
    by_contra active
    have sub : S.1 ⊆ I := by
      intro a ha
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,fun zero => active (Finset.prod_eq_zero ha zero)⟩
    exact different (Subtype.ext (Finset.eq_of_subset_of_card_le sub S.2.ge))

theorem coeff_linePoly {n : ℕ} (u : Fin n → ℂ) (k : ℕ) (hk : k ≤ n) :
    (linePoly u).coeff k = ((n-k).factorial : ℂ) * (k.factorial : ℂ) * (elem u k)^2 := by
  classical
  simp only [linePoly,Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow]
  simp [Nat.lt_succ_of_le hk]

/-- For k equal to the support cardinality, exactly one k-element subset
    contributes. Its product is nonzero over the complex field. -/
theorem coeff_at_support {n : ℕ} (u : Fin n → ℂ) :
    (linePoly u).coeff (support u).card =
      ((n-(support u).card).factorial : ℂ) * ((support u).card.factorial : ℂ) *
        (∏ i ∈ support u, u i)^2 := by
  rw [coeff_linePoly _ _ (by simpa using Finset.card_le_univ (support u)),support_only]

theorem rankOne_not_constant {n : ℕ} (u : Fin n → ℂ) (nonzero : u ≠ 0) (c : ℂ) :
    ¬ ∀ z : ℂ, Matrix.permanent (Matrix.of fun i j : Fin n => 1 + z*u i*u j) = c := by
  classical
  intro constant
  have equal : linePoly u = Polynomial.C c :=
    Polynomial.funext fun z => (eval_linePoly u z).trans ((constant z).trans (Polynomial.eval_C ..).symm)
  have nonempty : (support u).Nonempty := by
    by_contra! empty
    apply nonzero
    funext i
    by_contra ne
    have mem : i ∈ support u := Finset.mem_filter.mpr ⟨Finset.mem_univ _,ne⟩
    rw [empty] at mem
    exact Finset.notMem_empty i mem
  have kpos := Finset.card_pos.mpr nonempty
  have prodNe : (∏ i ∈ support u, u i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i hi => (Finset.mem_filter.mp hi).2
  have coefficient := coeff_at_support u
  rw [equal,Polynomial.coeff_C_of_ne_zero kpos.ne'] at coefficient
  exact (mul_ne_zero (mul_ne_zero (by exact_mod_cast (Nat.factorial_pos _).ne')
    (by exact_mod_cast (Nat.factorial_pos _).ne')) (pow_ne_zero 2 prodNe)) coefficient.symm

/-- No nonzero scalar multiple of a symmetric outer product lies in any
    complex linear space on which the translated permanent is constant. -/
theorem scaled_not_mem {n : ℕ} (L : Submodule ℂ (Fin n × Fin n → ℂ)) (c : ℂ)
    (flat : ∀ t ∈ L, Matrix.permanent (Matrix.of fun i j => 1 + t (i,j)) = c)
    (u : Fin n → ℂ) (hu : u ≠ 0) (a : ℂ) (ha : a ≠ 0) :
    (fun p : Fin n × Fin n => a*u p.1*u p.2) ∉ L := by
  intro member
  apply rankOne_not_constant u hu c
  intro z
  have h := flat _ (L.smul_mem (z/a) member)
  convert h using 4
  simp [Pi.smul_apply,smul_eq_mul]
  field_simp

private theorem minors_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (low : A.rank ≤ 1)
    (i k j l : Fin n) : A i j * A k l = A i l * A k j := by
  let B : Matrix (Fin 2) (Fin 2) ℂ := A.submatrix ![i,k] ![j,l]
  have bound : B.rank ≤ 1 := (Matrix.rank_submatrix_le A _ _).trans low
  by_contra ne
  have nonsingular : B.det ≠ 0 := by
    rw [Matrix.det_fin_two]
    exact sub_ne_zero.mpr ne
  have full := Matrix.rank_of_det_ne_zero nonsingular
  simp only [Fintype.card_fin] at full
  omega

/-- Intrinsic matrix-rank version of the rank-one obstruction. -/
theorem rank_le_one_zero {n : ℕ} (L : Submodule ℂ (Fin n × Fin n → ℂ)) (c : ℂ)
    (flat : ∀ t ∈ L, Matrix.permanent (Matrix.of fun i j => 1 + t (i,j)) = c)
    {t : Fin n × Fin n → ℂ} (mem : t ∈ L) (symm : ∀ i j, t (i,j) = t (j,i))
    (low : (Matrix.of fun i j => t (i,j)).rank ≤ 1) : t = 0 := by
  classical
  let A := Matrix.of fun i j => t (i,j)
  have minor (i k j l) : t (i,j)*t (k,l) = t (i,l)*t (k,j) := minors_zero A low i k j l
  by_contra nonzero
  have existsDiag : ∃ i, t (i,i) ≠ 0 := by
    by_contra! zero
    apply nonzero
    funext p
    obtain ⟨i,j⟩ := p
    have m := minor i j i j
    rw [zero i,zero j,symm j i,zero_mul] at m
    exact (mul_self_eq_zero.mp m.symm)
  obtain ⟨k,diag⟩ := existsDiag
  let u := fun i => t (i,k)
  have hu : u ≠ 0 := fun eq => diag (congrFun eq k)
  apply scaled_not_mem L c flat u hu (t (k,k))⁻¹ (inv_ne_zero diag)
  have eq : (fun p : Fin n × Fin n => (t (k,k))⁻¹*u p.1*u p.2) = t := by
    funext p
    obtain ⟨i,j⟩ := p
    change (t (k,k))⁻¹*t (i,k)*t (j,k) = t (i,j)
    have m := minor i k j k
    rw [symm k j] at m
    field_simp
    linear_combination -m
  exact eq.symm ▸ mem

/-- The support coefficient is the actual leading coefficient, including
    when the support is empty and the polynomial is constant. -/
theorem natDegree_linePoly {n : ℕ} (u : Fin n → ℂ) : (linePoly u).natDegree = (support u).card := by
  classical
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro k large
    by_cases bound : k ≤ n
    · rw [coeff_linePoly u k bound]
      have none : elem u k = 0 := by
        unfold elem
        apply Finset.sum_eq_zero
        intro S _
        by_contra product
        have sub : S.1 ⊆ support u := fun i hi =>
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun z => product (Finset.prod_eq_zero hi z)⟩
        have card := Finset.card_le_card sub
        rw [S.2] at card
        omega
      simp [none]
    · simp only [linePoly,Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow]
      apply Finset.sum_eq_zero
      intro i hi
      have upper := Finset.mem_range.mp hi
      rw [ite_eq_right (by omega)]
  · rw [coeff_at_support]
    have product := Finset.prod_ne_zero_iff.mpr (fun i (hi : i ∈ support u) => (Finset.mem_filter.mp hi).2)
    exact mul_ne_zero (mul_ne_zero (by exact_mod_cast (Nat.factorial_pos _).ne')
      (by exact_mod_cast (Nat.factorial_pos _).ne')) (pow_ne_zero 2 product)

end SymmetricLevel.RankOne
