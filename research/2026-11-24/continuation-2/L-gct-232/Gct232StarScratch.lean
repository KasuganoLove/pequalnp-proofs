import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace Gct232StarScratch

-- The permanent expansion helper is adapted from upstream L_gct_222.lean.
lemma sum_perm_succ {n : ℕ} (f : Equiv.Perm (Fin (n + 1)) → ℂ) :
    ∑ σ, f σ = ∑ p : Fin (n + 1), ∑ τ : Equiv.Perm (Fin n), f (Equiv.Perm.decomposeFin.symm (p, τ)) := by
  rw [← Equiv.Perm.decomposeFin.symm.sum_comp, Fintype.sum_prod_type]

lemma perm4 (M : Matrix (Fin 4) (Fin 4) ℂ) : Matrix.permanent M =
    M 0 0 * M 1 1 * M 2 2 * M 3 3 + M 0 0 * M 1 1 * M 3 2 * M 2 3 + M 0 0 * M 2 1 * M 1 2 * M 3 3
  + M 0 0 * M 2 1 * M 3 2 * M 1 3 + M 0 0 * M 3 1 * M 1 2 * M 2 3 + M 0 0 * M 3 1 * M 2 2 * M 1 3
  + M 1 0 * M 0 1 * M 2 2 * M 3 3 + M 1 0 * M 0 1 * M 3 2 * M 2 3 + M 1 0 * M 2 1 * M 0 2 * M 3 3
  + M 1 0 * M 2 1 * M 3 2 * M 0 3 + M 1 0 * M 3 1 * M 0 2 * M 2 3 + M 1 0 * M 3 1 * M 2 2 * M 0 3
  + M 2 0 * M 0 1 * M 1 2 * M 3 3 + M 2 0 * M 0 1 * M 3 2 * M 1 3 + M 2 0 * M 1 1 * M 0 2 * M 3 3
  + M 2 0 * M 1 1 * M 3 2 * M 0 3 + M 2 0 * M 3 1 * M 0 2 * M 1 3 + M 2 0 * M 3 1 * M 1 2 * M 0 3
  + M 3 0 * M 0 1 * M 1 2 * M 2 3 + M 3 0 * M 0 1 * M 2 2 * M 1 3 + M 3 0 * M 1 1 * M 0 2 * M 2 3
  + M 3 0 * M 1 1 * M 2 2 * M 0 3 + M 3 0 * M 2 1 * M 0 2 * M 1 3 + M 3 0 * M 2 1 * M 1 2 * M 0 3 := by
  simp only [Matrix.permanent]
  rw [sum_perm_succ]
  simp only [sum_perm_succ (n := 2), sum_perm_succ (n := 1), sum_perm_succ (n := 0)]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.prod_univ_succ, Fin.prod_univ_zero,
    Equiv.Perm.decomposeFin_symm_apply_zero, Equiv.Perm.decomposeFin_symm_apply_succ,
    Fintype.sum_unique]
  simp +decide [Equiv.swap_apply_def]
  ring


def F (x y z a b c d e f g h i j : ℂ) : ℂ :=
  Matrix.permanent (Matrix.of (![
    ![1+z*a, 1+x+z*b, 1+y+z*c, 1-x-y+z*d],
    ![1+x+z*b, 1+z*e, 1+z*f, 1+z*g],
    ![1+y+z*c, 1+z*f, 1+z*h, 1+z*i],
    ![1-x-y+z*d, 1+z*g, 1+z*i, 1+z*j]] : Fin 4 → Fin 4 → ℂ))

def D (x y a b c d e f g h i j : ℂ) : ℂ :=
  6*(a+2*b+2*c+2*d+e+2*f+2*g+h+2*i+j)
  -4*(e+f-i-j)*x -4*(f-g+h-j)*y
  +(e-2*g+j)*x^2 +2*(f-g-i+j)*x*y +(h-2*i+j)*y^2

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma derivative_formula (x y a b c d e f g h i j : ℂ) :
    8*(F x y 1 a b c d e f g h i j-F x y (-1) a b c d e f g h i j)
    -(F x y 2 a b c d e f g h i j-F x y (-2) a b c d e f g h i j)
    = 12*D x y a b c d e f g h i j := by
  unfold F
  rw [perm4, perm4, perm4, perm4]
  simp only [Matrix.of_apply, Matrix.cons_val]
  dsimp [D]
  ring

lemma derivative_zero (a b c d e f g h i j : ℂ)
    (hF : ∀ x y z : ℂ, F x y z a b c d e f g h i j = 24)
    (x y : ℂ) : D x y a b c d e f g h i j = 0 := by
  have hh := derivative_formula x y a b c d e f g h i j
  rw [hF, hF, hF, hF] at hh
  linear_combination -hh/12

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma restricted_formula (z b c d r : ℂ) :
    F 0 0 z (-2*(b+c+d)-9*r) b c d r r r r r r =
    24+2*z^2*((b+c+d)^2-6*(b+c+d)*r-63*r^2)
    +4*r*z^3*((b+c+d)^2-6*(b+c+d)*r-39*r^2)
    +2*r^2*z^4*(b+c+d-9*r)*(b+c+d+3*r) := by
  unfold F
  rw [perm4]
  simp only [Matrix.of_apply, Matrix.cons_val]
  ring

set_option maxHeartbeats 2000000 in
lemma star_extension_rigidity (a b c d e f g h i j : ℂ)
    (hF : ∀ x y z : ℂ, F x y z a b c d e f g h i j = 24) :
    a = 0 ∧ b+c+d = 0 ∧ e = 0 ∧ f = 0 ∧ g = 0 ∧ h = 0 ∧ i = 0 ∧ j = 0 := by
  have h00 := derivative_zero a b c d e f g h i j hF 0 0
  have h10 := derivative_zero a b c d e f g h i j hF 1 0
  have hn0 := derivative_zero a b c d e f g h i j hF (-1) 0
  have h01 := derivative_zero a b c d e f g h i j hF 0 1
  have h0n := derivative_zero a b c d e f g h i j hF 0 (-1)
  have h11 := derivative_zero a b c d e f g h i j hF 1 1
  dsimp [D] at h00 h10 hn0 h01 h0n h11
  have heq : e-2*g+j = 0 := by linear_combination (h10+hn0-2*h00)/2
  have hhq : h-2*i+j = 0 := by linear_combination (h01+h0n-2*h00)/2
  have hfq : f-g-i+j = 0 := by linear_combination (h11-h10-h01+h00)/2
  have hel : e+f-i-j = 0 := by linear_combination -(h10-hn0)/8
  have hhl : f-g+h-j = 0 := by linear_combination -(h01-h0n)/8
  have hg : g=j := by linear_combination (hel-heq-hfq)/3
  have hi : i=j := by linear_combination (hhl-hhq-hfq)/3
  have he : e=j := by linear_combination heq+2*hg
  have hh : h=j := by linear_combination hhq+2*hi
  have hf : f=j := by linear_combination hfq+hg+hi
  have ha : a = -2*(b+c+d)-9*j := by
    linear_combination h00/6-he-2*hf-2*hg-hh-2*hi
  rw [ha, he, hf, hg, hh, hi] at hF
  have p1 := hF 0 0 1
  have pn1 := hF 0 0 (-1)
  have p2 := hF 0 0 2
  have pn2 := hF 0 0 (-2)
  rw [restricted_formula] at p1 pn1 p2 pn2
  have hq : (b+c+d)^2-6*(b+c+d)*j-63*j^2 = 0 := by
    linear_combination (16*(p1+pn1)-(p2+pn2))/48
  have hc : j*((b+c+d)^2-6*(b+c+d)*j-39*j^2) = 0 := by
    linear_combination (p1-pn1)/8
  have hj3 : j^3=0 := by linear_combination (hc-j*hq)/24
  have hj : j=0 := (pow_eq_zero_iff (by decide : (3:ℕ) ≠ 0)).mp hj3
  have hs2 : (b+c+d)^2=0 := by simpa [hj] using hq
  have hs : b+c+d=0 := (pow_eq_zero_iff (by decide : (2:ℕ) ≠ 0)).mp hs2
  refine ⟨?_, hs, ?_, ?_, ?_, ?_, ?_, hj⟩
  · simpa [hj, hs] using ha
  · exact he.trans hj
  · exact hf.trans hj
  · exact hg.trans hj
  · exact hh.trans hj
  · exact hi.trans hj

end Gct232StarScratch
