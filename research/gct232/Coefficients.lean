import PEqualNP.Outside.L_gct_220

namespace Gct232.Coefficients

abbrev V := Fin 4 → ℂ
abbrev Mat := Fin 4 × Fin 4 → ℂ

def total (u : V) := ∑ i, u i
def dot (u v : V) := ∑ i, u i * v i
def dyad (u v : V) (p : Fin 4 × Fin 4) := u p.1 * v p.2 + v p.1 * u p.2
def permAt (t : Mat) (z : ℂ) :=
  Matrix.permanent (Matrix.of fun i j : Fin 4 => (1 : ℂ) + z*t (i,j))
def level (t : Mat) : Prop := ∀ z, permAt t z=24

def linear (t : Mat) : ℂ := ∑ i : Fin 4, ∑ j : Fin 4, t (i,j)
def quadratic (t : Mat) : ℂ :=
  (linear t)^2 - (∑ i : Fin 4, (∑ j : Fin 4, t (i,j))^2) -
    (∑ j : Fin 4, (∑ i : Fin 4, t (i,j))^2) + ∑ i : Fin 4, ∑ j : Fin 4, t (i,j)^2

-- Central differences at four scalar points isolate the first two terms of
-- this quartic without any numerical differentiation.
set_option maxHeartbeats 7000000 in
private theorem first_difference (t : Mat) :
    8*(permAt t 1-permAt t (-1))-(permAt t 2-permAt t (-2))=72*linear t := by
  simp only [permAt,PEqualNP.Outside.L_gct_220.perm4,Matrix.of_apply,linear,Fin.sum_univ_four]
  ring

set_option maxHeartbeats 7000000 in
private theorem second_difference (t : Mat) :
    16*(permAt t 1+permAt t (-1)-48)-(permAt t 2+permAt t (-2)-48)=24*quadratic t := by
  simp only [permAt,PEqualNP.Outside.L_gct_220.perm4,Matrix.of_apply,quadratic,linear,Fin.sum_univ_four]
  ring

theorem vanish {t : Mat} (h : level t) : linear t=0 ∧ quadratic t=0 := by
  have a := first_difference t
  have b := second_difference t
  rw [h,h,h,h] at a b
  constructor
  · linear_combination -a/72
  · linear_combination -b/24

theorem dyad_first (u v : V) : linear (dyad u v) = 2*total u*total v := by
  simp only [linear,dyad,total,Fin.sum_univ_four]
  ring

set_option maxHeartbeats 3000000 in
theorem dyad_second (u v : V) : quadratic (dyad u v) =
    4*(total u)^2*(total v)^2 + 2*(dot u u*dot v v + (dot u v)^2 -
    (total v)^2*dot u u - 2*total u*total v*dot u v - (total u)^2*dot v v) := by
  simp only [quadratic,linear,dyad,dot,total,Fin.sum_univ_four]
  ring

theorem necessary {u v : V} (h : level (dyad u v)) :
    total u * total v = 0 ∧
      dot u u*dot v v + (dot u v)^2 - (total v)^2*dot u u - (total u)^2*dot v v=0 := by
  obtain ⟨a,b⟩ := vanish h
  rw [dyad_first] at a
  rw [dyad_second] at b
  have first : total u * total v = 0 := by linear_combination a/2
  refine ⟨first,?_⟩
  linear_combination b/2 - 2*(total u*total v-dot u v)*first

end Gct232.Coefficients
