import PEqualNP.Outside.L_gct_220

namespace Gct232.EqualDiagonal

abbrev V := Fin 4 × Fin 4 → ℂ
abbrev W := Fin 5 → ℂ
def level (U : V) : Prop := ∀ z : ℂ, Matrix.permanent
  (Matrix.of fun i j : Fin 4 => 1 + z * U (i,j)) = 24

def label (a b c d e f : ℂ) := a+b+c+d+e+f
def haf (a b c d e f : ℂ) := a*f+b*e+c*d
def formula (s a b c d e f : ℂ) : ℂ :=
  s^4 + s^2*(a^2+b^2+c^2+d^2+e^2+f^2) + 2*s*(a*b*d+a*c*e+b*c*f+d*e*f) +
    (haf a b c d e f)^2

private theorem symEval (U : V) (sym : ∀ i j : Fin 4, U (i,j)=U (j,i))
    (s : ℂ) (diag : ∀ i : Fin 4, U (i,i)=s) (z : ℂ) :
    Matrix.permanent (Matrix.of fun i j : Fin 4 => 1+z*U (i,j)) =
      formula (1+z*s) (1+z*U (0,1)) (1+z*U (0,2)) (1+z*U (0,3))
        (1+z*U (1,2)) (1+z*U (1,3)) (1+z*U (2,3)) := by
  rw [PEqualNP.Outside.L_gct_220.perm4]
  simp only [Matrix.of_apply,diag,sym 1 0,sym 2 0,sym 3 0,sym 2 1,sym 3 1,sym 3 2]
  unfold formula haf
  ring

private theorem constraints (s a b c d e f : ℂ)
    (line : ∀ z : ℂ, formula (1+z*s) (1+z*a) (1+z*b) (1+z*c) (1+z*d) (1+z*e) (1+z*f) = 24) :
    s=0 ∧ label a b c d e f=0 ∧ haf a b c d e f=0 := by
  have t₁ := line 1
  have negOne := line (-1)
  have t₂ := line 2
  have negTwo := line (-2)
  unfold formula haf at t₁ negOne t₂ negTwo
  have linear : 2*s+label a b c d e f = 0 := by
    unfold label
    linear_combination (8*(t₁-negOne)-(t₂-negTwo))/144
  have quad : s^2 + haf a b c d e f = 0 := by
    have h : 2*(2*s+label a b c d e f)^2 + 4*(s^2+haf a b c d e f) = 0 := by
      unfold label haf
      linear_combination (16*(t₁+negOne)-(t₂+negTwo))/24
    rw [linear] at h
    linear_combination h/4
  have zero : s=0 := by
    by_contra ne
    have z := line (-(1/s))
    have diag : 1 + -(1/s)*s = 0 := by field_simp; ring
    simp only [diag,formula,zero_pow (by decide : 4 ≠ 0),zero_pow (by decide : 2 ≠ 0),
      zero_mul,mul_zero,add_zero,zero_add] at z
    have scaleH :
        s^2 * haf (1+ -(1/s)*a) (1+ -(1/s)*b) (1+ -(1/s)*c) (1+ -(1/s)*d)
          (1+ -(1/s)*e) (1+ -(1/s)*f) = 4*s^2 := by
      have scale : s^2 * haf (1+ -(1/s)*a) (1+ -(1/s)*b) (1+ -(1/s)*c) (1+ -(1/s)*d)
          (1+ -(1/s)*e) (1+ -(1/s)*f) = 3*s^2 - s*label a b c d e f + haf a b c d e f := by
        unfold haf label
        field_simp
        ring
      rw [scale]
      linear_combination -s*linear + quad
    have val : haf (1+ -(1/s)*a) (1+ -(1/s)*b) (1+ -(1/s)*c) (1+ -(1/s)*d)
          (1+ -(1/s)*e) (1+ -(1/s)*f) = 4 := by
      rw [mul_comm 4] at scaleH
      exact mul_left_cancel₀ (pow_ne_zero 2 ne) scaleH
    rw [val] at z
    norm_num at z
  exact ⟨zero, by simpa only [zero,mul_zero,zero_add] using linear,
    by simpa only [zero,zero_pow (by decide : 2 ≠ 0),zero_add] using quad⟩

/-- Every equal-diagonal direction on the level through J has zero diagonal,
zero off-diagonal sum and zero hafnian. -/
theorem equal_diagonal (U : V) (sym : ∀ i j : Fin 4, U (i,j)=U (j,i))
    (s : ℂ) (diag : ∀ i : Fin 4, U (i,i)=s) (flat : level U) :
    s=0 ∧ label (U (0,1)) (U (0,2)) (U (0,3)) (U (1,2)) (U (1,3)) (U (2,3))=0 ∧
      haf (U (0,1)) (U (0,2)) (U (0,3)) (U (1,2)) (U (1,3)) (U (2,3))=0 :=
  constraints _ _ _ _ _ _ _ (fun z => (symEval U sym s diag z).symm.trans (flat z))

end Gct232.EqualDiagonal
