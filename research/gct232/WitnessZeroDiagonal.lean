import WitnessEqualDiagonal
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

namespace Gct232.EqualDiagonal

noncomputable section

private def remEdge (x : W) := -(x 0+x 1+x 2+x 3+x 4)
private def quadForm (x : W) := x 0 * remEdge x + x 1 * x 4 + x 2 * x 3
private def polar (x y : W) :=
  x 0 * remEdge y + y 0 * remEdge x + x 1*y 4 + y 1*x 4 + x 2*y 3 + y 2*x 3

private def B : LinearMap.BilinForm ℂ W :=
  LinearMap.mk₂ ℂ polar
    (by intro x y z; simp [polar,remEdge]; ring)
    (by intro a x y; simp [polar,remEdge]; ring)
    (by intro x y z; simp [polar,remEdge]; ring)
    (by intro a x y; simp [polar,remEdge]; ring)

private theorem polarization (x y : W) : B x y = quadForm (x+y)-quadForm x-quadForm y := by
  simp [B,polar,quadForm,remEdge]
  ring

private theorem nonsingular : B.Nondegenerate := by
  have separates (x : W) (h : ∀ y, B x y = 0) : x=0 := by
    have e0 := h ![1,0,0,0,0]
    have e1 := h ![0,1,0,0,0]
    have e2 := h ![0,0,1,0,0]
    have e3 := h ![0,0,0,1,0]
    have e4 := h ![0,0,0,0,1]
    norm_num [B,polar,remEdge] at e0 e1 e2 e3 e4
    have z : x 0 = 0 := by linear_combination -(e0+e1+e2+e3+e4)/6
    funext i
    fin_cases i
    · exact z
    · change x 1 = 0; linear_combination e4+z
    · change x 2 = 0; linear_combination e3+z
    · change x 3 = 0; linear_combination e2+z
    · change x 4 = 0; linear_combination e1+z
  refine ⟨separates, fun y h => separates y (fun x => ?_)⟩
  have swap : B y x = B x y := by simp [B,polar]; ring
  exact swap.trans (h x)

private def project : V →ₗ[ℂ] W where
  toFun U := ![U (0,1), U (0,2), U (0,3), U (1,2), U (1,3)]
  map_add' := by intro x y; funext i; fin_cases i <;> rfl
  map_smul' := by intro a x; funext i; fin_cases i <;> rfl

private def restore (x : W) : V := fun ij =>
  (![![0,x 0,x 1,x 2], ![x 0,0,x 3,x 4], ![x 1,x 3,0,remEdge x],
     ![x 2,x 4,remEdge x,0]] : Fin 4 → Fin 4 → ℂ) ij.1 ij.2

/-- On the zero-diagonal tangent hyperplane the hafnian is a nondegenerate
quadratic form in five coordinates. A totally isotropic subspace has dimension at most two. -/
theorem zero_diagonal_bound (L : Submodule ℂ V)
    (sym : ∀ U ∈ L, ∀ i j : Fin 4, U (i,j) = U (j,i))
    (diag : ∀ U ∈ L, ∀ i : Fin 4, U (i,i) = 0)
    (flat : ∀ U ∈ L, Matrix.permanent (Matrix.of fun i j : Fin 4 => 1 + U (i,j)) = 24) :
    Module.finrank ℂ L ≤ 2 := by
  let f := project.comp L.subtype
  have full (u : L) : level u.val := by
    intro z
    simpa only [Pi.smul_apply,smul_eq_mul] using flat (z • u.val) (L.smul_mem z u.property)
  have eqs (u : L) := (equal_diagonal _ (sym u.val u.property) 0 (diag u.val u.property) (full u)).2
  have last (u : L) : u.val (2,3) = remEdge (f u) := by
    change u.val (2,3) = -(u.val (0,1)+u.val (0,2)+u.val (0,3)+u.val (1,2)+u.val (1,3))
    have total := (eqs u).1
    unfold label at total
    linear_combination total
  have recover (u : L) : u.val = restore (f u) := by
    funext ij
    rcases ij with ⟨i,j⟩
    fin_cases i <;> fin_cases j <;>
      first | rfl | exact diag u.val u.property _ | exact sym u.val u.property _ _ |
        exact last u | exact (sym u.val u.property 3 2).trans (last u)
  have inj : Function.Injective f := by
    intro x y eq
    apply Subtype.ext
    exact (recover x).trans ((congrArg restore eq).trans (recover y).symm)
  have nullQ (u : L) : quadForm (f u)=0 := by
    unfold quadForm
    rw [←last]
    exact (eqs u).2
  let S := LinearMap.range f
  have inOrth : S ≤ B.orthogonal S := by
    rintro _ ⟨y,rfl⟩ _ ⟨x,rfl⟩
    rw [polarization,←map_add,nullQ,nullQ,nullQ]
    ring
  have bound := Submodule.finrank_mono inOrth
  rw [LinearMap.BilinForm.finrank_orthogonal nonsingular,Module.finrank_fin_fun] at bound
  have rank : Module.finrank ℂ S = Module.finrank ℂ L := LinearMap.finrank_range_of_inj inj
  omega

/-- A subspace with constant diagonal along each direction obeys the same bound. -/
theorem equal_diagonal_bound (L : Submodule ℂ V)
    (sym : ∀ U ∈ L, ∀ i j : Fin 4, U (i,j) = U (j,i))
    (same : ∀ U ∈ L, ∀ i : Fin 4, U (i,i) = U (0,0))
    (flat : ∀ U ∈ L, Matrix.permanent (Matrix.of fun i j : Fin 4 => 1 + U (i,j)) = 24) :
    Module.finrank ℂ L ≤ 2 := by
  apply zero_diagonal_bound L sym _ flat
  intro U h i
  apply (same U h i).trans
  apply (equal_diagonal U (sym U h) _ (same U h) ?_).1
  intro z
  simpa only [Pi.smul_apply,smul_eq_mul] using flat (z • U) (L.smul_mem z h)

end
end Gct232.EqualDiagonal
