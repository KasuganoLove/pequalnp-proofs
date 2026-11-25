import Coefficients
import RankOne
import Nondegenerate
import Mathlib.LinearAlgebra.Dual.Lemmas

namespace Gct232.CommonFactor

open Gct232.Coefficients

private def form (u : V) : V →ₗ[ℂ] ℂ where
  toFun := dot u
  map_add' v w := by simp [dot,Pi.add_apply,mul_add,Finset.sum_add_distrib]
  map_smul' c v := by simp [dot,Pi.smul_apply,smul_eq_mul,Finset.mul_sum,mul_left_comm]

private theorem form_ne {u : V} (hu : u ≠ 0) : form u ≠ 0 := by
  intro eq
  apply hu
  funext i
  have e := LinearMap.congr_fun eq (Pi.single i 1)
  change dotProduct u (Pi.single i 1) = 0 at e
  simpa using e

private theorem ker_span (W : Submodule ℂ V) (u : V) (u0 : u ≠ 0)
    (sub : ∀ v ∈ W, dot u v=0) (dimW : 3 ≤ Module.finrank ℂ W) :
    W = LinearMap.ker (form u) := by
  have dim := Module.Dual.finrank_ker_add_one_of_ne_zero (form_ne u0)
  have dimV : Module.finrank ℂ V = 4 := by simp [V]
  exact Submodule.eq_of_le_of_finrank_le (fun v hv => sub v hv) (by omega)

private def e : V := fun _ => 1
private def x : V := ![1,-1,0,0]
private def y : V := ![0,0,1,-1]

theorem sum_nonzero_bound {u : V} (nonzero : total u ≠ 0) (W : Submodule ℂ V)
    (flat : ∀ v ∈ W, level (dyad u v)) : Module.finrank ℂ W ≤ 2 := by
  by_contra! large
  have sub (v : V) (hv : v ∈ W) : total v=0 :=
    (mul_eq_zero.mp (necessary (flat _ hv)).1).resolve_left nonzero
  have e_ne : e ≠ 0 := by intro h; have := congrFun h 0; norm_num [e] at this
  have kern := ker_span W e e_ne (fun v hv => by simpa [dot,e,total] using sub v hv) (by omega)
  have closed (v : V) (z : total v=0) : v ∈ W := by
    rw [kern,LinearMap.mem_ker]
    change dot e v = 0
    simpa [dot,e,total] using z
  let c := dot u u - (total u)^2
  have eq (v : V) (z : total v=0) : c*dot v v + (dot u v)^2=0 := by
    have h := (necessary (flat _ (closed _ z))).2
    rw [z] at h
    dsimp [c]
    linear_combination h
  have hx := eq x (by norm_num [x,total,Fin.sum_univ_four])
  have hy := eq y (by norm_num [y,total,Fin.sum_univ_four])
  have hxy := eq (x+y) (by norm_num [x,y,total,Fin.sum_univ_four,Pi.add_apply])
  simp [x,y,dot,Fin.sum_univ_four,Pi.add_apply] at hx hy hxy
  have cross : (u 0-u 1)*(u 2-u 3)=0 := by linear_combination (hxy-hx-hy)/2
  have cz : c=0 := by
    rcases mul_eq_zero.mp cross with h | h
    · have same : u 0=u 1 := sub_eq_zero.mp h
      rw [same] at hx
      linear_combination hx/2
    · have same : u 2=u 3 := sub_eq_zero.mp h
      rw [same] at hy
      linear_combination hy/2
  have const (i : Fin 4) : u i = u 0 := by
    let v : V := Pi.single i 1 - Pi.single 0 1
    have z : total v=0 := by simp [v,total,Pi.sub_apply,Pi.single_apply,Finset.sum_sub_distrib]
    have zero := eq v z
    rw [cz,zero_mul,zero_add] at zero
    have h : dot u v=0 := (sq_eq_zero_iff).mp zero
    apply sub_eq_zero.mp
    simpa [dot,v,Pi.sub_apply,Pi.single_apply,mul_sub,Finset.sum_sub_distrib] using h
  have b : (u 0)^2 = 0 := by
    have cdef : dot u u - (total u)^2=0 := cz
    simp only [dot,total,Fin.sum_univ_four,const] at cdef
    linear_combination -cdef/12
  apply nonzero
  simp [total,const,sq_eq_zero_iff.mp b]

theorem common_factor_bound {u : V} (u0 : u ≠ 0) (W : Submodule ℂ V)
    (flat : ∀ v ∈ W, level (dyad u v)) : Module.finrank ℂ W ≤ 2 := by
  by_cases su : total u=0
  · by_cases cu : dot u u=0
    · by_contra! large
      have sub (v : V) (hv : v∈W) : dot u v = 0 := by
        have h := (necessary (flat _ hv)).2
        simpa [cu,su] using h
      have kern := ker_span W u u0 sub (by omega)
      have member : u ∈ W := by rw [kern]; exact cu
      apply SymmetricLevel.RankOne.rankOne_not_constant u u0 24
      intro z
      have matrix_eq :
          (Matrix.of fun i j : Fin 4 => (1 : ℂ) + z*u i*u j) =
          Matrix.of (fun i j : Fin 4 => (1 : ℂ) + (z/2)*dyad u u (i,j)) := by
        ext i j
        simp only [Matrix.of_apply,dyad]
        ring
      rw [matrix_eq]
      exact flat u member (z/2)
    · apply SymmetricLevel.Nondegenerate.dimension_bound su cu W
      intro v hv
      have h := (necessary (flat _ hv)).2
      rw [su] at h
      change dot u u*(dot v v-(total v)^2)+(dot u v)^2=0
      linear_combination h
  · exact sum_nonzero_bound su W flat

def dyadMap (u : V) : V →ₗ[ℂ] Mat where
  toFun := dyad u
  map_add' v w := by
    funext p
    simp only [dyad,Pi.add_apply]
    ring
  map_smul' a v := by
    funext p
    simp only [dyad,Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
    ring

/-- If every matrix in the flat has a shared linear factor as a quadratic
    form, the flat has dimension at most two. -/
theorem dimension_of_common_factor {u : V} (hu : u ≠ 0) (L : Submodule ℂ Mat)
    (factor : L ≤ LinearMap.range (dyadMap u))
    (flat : ∀ t ∈ L, Matrix.permanent (Matrix.of fun i j : Fin 4 => (1 : ℂ)+t (i,j))=24) :
    Module.finrank ℂ L ≤ 2 := by
  let W := L.comap (dyadMap u)
  have eq : W.map (dyadMap u) = L := Submodule.map_comap_eq_of_le factor
  have bound : Module.finrank ℂ W ≤ 2 := common_factor_bound hu W (by
    intro v hv z
    have member : dyad u v ∈ L := hv
    have scaled := flat _ (L.smul_mem z member)
    simpa only [permAt,Pi.smul_apply,smul_eq_mul] using scaled)
  rw [← eq]
  exact (Submodule.finrank_map_le _ _).trans bound

end Gct232.CommonFactor
