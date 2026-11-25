import PEqualNP.Outside.L_gct_220

namespace Gct232.StarMaximal

abbrev V := Fin 4 × Fin 4 → ℂ

def coords (t x y z a b c d e f : ℂ) : V := fun ij =>
  (![![t,x,y,z], ![x,a,b,c], ![y,b,d,e], ![z,c,e,f]] : Fin 4 → Fin 4 → ℂ) ij.1 ij.2

def star (p q : ℂ) : V := coords 0 p q (-p-q) 0 0 0 0 0 0

def four (t x y z a b c d e f : ℂ) : ℂ :=
  t * (a*d*f + a*e^2 + b^2*f + 2*b*c*e + c^2*d) +
  x^2 * (d*f+e^2) + y^2 * (a*f+c^2) + z^2 * (a*d+b^2) +
  2*x*y*(b*f+c*e) + 2*x*z*(b*e+c*d) + 2*y*z*(a*e+b*c)

private theorem blockPermanent (t x y z a b c d e f : ℂ) :
    Matrix.permanent (Matrix.of fun i j : Fin 4 => coords t x y z a b c d e f (i,j)) =
    four t x y z a b c d e f := by
  rw [PEqualNP.Outside.L_gct_220.perm4]
  simp [coords,four,Matrix.of_apply]
  ring

private theorem permSym (U : V) (sym : ∀ i j : Fin 4, U (i,j)=U (j,i)) :
    Matrix.permanent (Matrix.of fun i j : Fin 4 => U (i,j)) =
      four (U (0,0)) (U (0,1)) (U (0,2)) (U (0,3)) (U (1,1)) (U (1,2))
        (U (1,3)) (U (2,2)) (U (2,3)) (U (3,3)) := by
  rw [←blockPermanent]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> first | rfl | exact sym _ _

private theorem threeDifferences (t x y z a b c d e f : ℂ)
    (level : ∀ p q : ℂ, four t (x+p) (y+q) (z-p-q) a b c d e f = 24) :
    (a+d-2*b)*f+(c-e)^2=0 ∧ (a+f-2*c)*d+(b-e)^2=0 ∧ (d+f-2*e)*a+(b-c)^2=0 := by
  unfold four at level
  constructor
  · linear_combination (level 1 (-1))/2 + (level (-1) 1)/2 - level 0 0
  constructor
  · linear_combination (level 1 0)/2 + (level (-1) 0)/2 - level 0 0
  · linear_combination (level 0 1)/2 + (level 0 (-1))/2 - level 0 0

private theorem extract (U V W : ℂ)
    (h : ∀ s : ℂ, (s*U)*(1+s*V)+(s*W)^2=0) : U=0 ∧ W=0 := by
  have zero : U=0 := by linear_combination (h 1)/2 - (h (-1))/2
  refine ⟨zero,?_⟩
  have sq := h 1
  rw [zero] at sq
  simpa using sq

/-- If the four-by-four symmetric permanent is unchanged by every star
    perturbation, the lower-right block of any extension direction vanishes.
    Its diagonal at the center vanishes and its three arms sum to zero. -/
theorem scalarMaximal (t x y z a b c d e f : ℂ)
    (level : ∀ s p q : ℂ, four (1+s*t) (1+s*x+p) (1+s*y+q) (1+s*z-p-q)
      (1+s*a) (1+s*b) (1+s*c) (1+s*d) (1+s*e) (1+s*f) = 24) :
    a=0 ∧ b=0 ∧ c=0 ∧ d=0 ∧ e=0 ∧ f=0 ∧ t=0 ∧ x+y+z=0 := by
  have relations (s : ℂ) := threeDifferences _ _ _ _ _ _ _ _ _ _ (level s)
  have ad := extract (a+d-2*b) f (c-e) (by intro s; linear_combination (relations s).1)
  have af := extract (a+f-2*c) d (b-e) (by intro s; linear_combination (relations s).2.1)
  have df := extract (d+f-2*e) a (b-c) (by intro s; linear_combination (relations s).2.2)
  obtain ⟨ad,ce⟩ := ad; obtain ⟨af,be⟩ := af; obtain ⟨df,bc⟩ := df
  have aa : a=b := by linear_combination (ad+af-df)/2 + ce
  have dd : d=b := by linear_combination ad - aa
  have ff : f=b := by linear_combination af - aa - 2*bc
  have cc : c=b := by linear_combination -bc
  have ee : e=b := by linear_combination -be
  subst a; subst c; subst d; subst e; subst f
  by_cases nz : b=0
  · subst b
    have hp := level 1 0 0
    have hm := level (-1) 0 0
    unfold four at hp hm
    have arms2 : (x+y+z)^2=0 := by linear_combination (hp+hm)/4
    have arms : x+y+z=0 := by simpa using arms2
    have diag : t=0 := by linear_combination hp/6 - arms2/3 - 2*arms
    exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,diag,arms⟩
  · have cancel : 1+(-b⁻¹)*b=0 := by field_simp; ring
    have bad := level (-b⁻¹) 0 0
    simp only [cancel] at bad
    norm_num [four] at bad

private theorem symmetricStar (p q : ℂ) (i j : Fin 4) : star p q (i,j)=star p q (j,i) := by
  fin_cases i <;> fin_cases j <;> rfl

theorem allStar {L : Submodule ℂ V}
    (inside : ∀ p q : ℂ, star p q ∈ L)
    (symmetric : ∀ v ∈ L, ∀ i j : Fin 4, v (i,j)=v (j,i))
    (level : ∀ v ∈ L, Matrix.permanent (Matrix.of fun i j : Fin 4 => 1+v (i,j))=24)
    (v : V) (hv : v ∈ L) : ∃ p q : ℂ, v=star p q := by
  have eqs := symmetric v hv
  have params (s p q : ℂ) := level (s • v + star p q) (L.add_mem (L.smul_mem s hv) (inside p q))
  have formula (s p q : ℂ) :
      four (1+s*v (0,0)) (1+s*v (0,1)+p) (1+s*v (0,2)+q) (1+s*v (0,3)-p-q)
        (1+s*v (1,1)) (1+s*v (1,2)) (1+s*v (1,3))
        (1+s*v (2,2)) (1+s*v (2,3)) (1+s*v (3,3)) = 24 := by
    let U : V := fun ij => 1+(s • v + star p q) ij
    have sym (i j : Fin 4) : U (i,j) = U (j,i) := by
      simp only [U,Pi.add_apply,Pi.smul_apply,smul_eq_mul,eqs i j,symmetricStar p q i j]
    have h : Matrix.permanent (Matrix.of fun i j : Fin 4 => U (i,j))=24 := params s p q
    rw [permSym U sym] at h
    simpa [U,star,coords,add_assoc,sub_eq_add_neg] using h
  obtain ⟨a,b,c,d,e,f,t,sum⟩ := scalarMaximal _ _ _ _ _ _ _ _ _ _ formula
  refine ⟨v (0,1), v (0,2), ?_⟩
  have z : v (0,3) = -v (0,1) - v (0,2) := by linear_combination sum
  funext ⟨i,j⟩
  fin_cases i <;> fin_cases j <;> dsimp [star,coords] <;>
    first | assumption | exact eqs _ _ | (rwa [eqs])

def starMap : (Fin 2 → ℂ) →ₗ[ℂ] V where
  toFun u := star (u 0) (u 1)
  map_add' a b := by
    funext ⟨i,j⟩; fin_cases i <;> fin_cases j <;> simp [star,coords] <;> ring
  map_smul' c a := by
    funext ⟨i,j⟩; fin_cases i <;> fin_cases j <;> simp [star,coords] <;> ring

theorem starMap_injective : Function.Injective starMap := by
  intro a b h
  funext i
  fin_cases i
  · exact congrFun h (0,1)
  · exact congrFun h (0,2)

theorem rank_starPlane : Module.finrank ℂ (LinearMap.range starMap) = 2 := by
  rw [LinearMap.finrank_range_of_inj starMap_injective]
  simp

theorem star_level (p q : ℂ) :
    Matrix.permanent (Matrix.of fun i j : Fin 4 => 1 + star p q (i,j)) = 24 := by
  let U : V := fun ij => 1+star p q ij
  have sym (i j : Fin 4) : U (i,j)=U (j,i) := congrArg (1+·) (symmetricStar p q i j)
  change Matrix.permanent (Matrix.of fun i j : Fin 4 => U (i,j)) = _
  rw [permSym U sym]
  simp [U,star,coords,four]
  ring

/-- The standard symmetric star plane is a maximal level space under
    inclusion. This does not assume that a general level space contains it. -/
theorem maximality {L : Submodule ℂ V} (includeStar : LinearMap.range starMap ≤ L)
    (symmetric : ∀ v ∈ L, ∀ i j : Fin 4, v (i,j)=v (j,i))
    (level : ∀ v ∈ L, Matrix.permanent (Matrix.of fun i j : Fin 4 => 1+v (i,j))=24) :
    L = LinearMap.range starMap := by
  apply le_antisymm _ includeStar
  intro v hv
  have contains (p q : ℂ) : star p q ∈ L := includeStar ⟨![p,q],rfl⟩
  obtain ⟨p,q,eq⟩ := allStar contains symmetric level v hv
  exact ⟨![p,q],eq.symm⟩

theorem rank_if_contains_star {L : Submodule ℂ V} (includeStar : LinearMap.range starMap ≤ L)
    (symmetric : ∀ v ∈ L, ∀ i j : Fin 4, v (i,j)=v (j,i))
    (level : ∀ v ∈ L, Matrix.permanent (Matrix.of fun i j : Fin 4 => 1+v (i,j))=24) :
    Module.finrank ℂ L = 2 := maximality includeStar symmetric level ▸ rank_starPlane

/-- Coordinate subspace supported on the distinguished row and column. -/
def supportedAt (k : Fin 4) : Submodule ℂ V where
  carrier := {v | ∀ i j : Fin 4, i ≠ k → j ≠ k → v (i,j) = 0}
  zero_mem' := by simp
  add_mem' {v w} hv hw := by intro i j hi hj; simp [hv i j hi hj,hw i j hi hj]
  smul_mem' s v hv := by intro i j hi hj; simp [hv i j hi hj]

private theorem sparse {L : Submodule ℂ V}
    (symmetric : ∀ v ∈ L, ∀ i j : Fin 4, v (i,j)=v (j,i))
    (level : ∀ v ∈ L, Matrix.permanent (Matrix.of fun i j : Fin 4 => 1+v (i,j))=24)
    {v : V} (hv : v ∈ L ⊓ supportedAt 0) : v ∈ LinearMap.range starMap := by
  have sym := symmetric v hv.1
  have zeros (i j : Fin 4) (hi : i ≠ 0) (hj : j ≠ 0) : v (i,j)=0 := hv.2 i j hi hj
  have sample (s : ℂ) :
      four (1+s*v (0,0)) (1+s*v (0,1)) (1+s*v (0,2)) (1+s*v (0,3)) 1 1 1 1 1 1 = 24 := by
    let U : V := fun ij => 1+s*v ij
    have symmetric' (i j : Fin 4) : U (i,j)=U (j,i) := by simp [U,sym i j]
    have h : Matrix.permanent (Matrix.of fun i j : Fin 4 => U (i,j))=24 :=
      level (s • v) (L.smul_mem s hv.1)
    rw [permSym U symmetric'] at h
    simp only [U,zeros 1 1 (by decide) (by decide),zeros 1 2 (by decide) (by decide),
      zeros 1 3 (by decide) (by decide),zeros 2 2 (by decide) (by decide),
      zeros 2 3 (by decide) (by decide),zeros 3 3 (by decide) (by decide),mul_zero,add_zero] at h
    exact h
  have plus := sample 1
  have minus := sample (-1)
  unfold four at plus minus
  have sq : (v (0,1)+v (0,2)+v (0,3))^2=0 := by linear_combination (plus+minus)/4
  have arms : v (0,1)+v (0,2)+v (0,3)=0 := by simpa using sq
  have diag : v (0,0) = 0 := by linear_combination plus/6-sq/3-2*arms
  have third : v (0,3) = -v (0,1)-v (0,2) := by linear_combination arms
  refine ⟨![v (0,1),v (0,2)],?_⟩
  change star (v (0,1)) (v (0,2)) = v
  symm
  funext ⟨i,j⟩
  fin_cases i <;> fin_cases j <;> dsimp [star,coords] <;>
    first | assumption | exact sym _ _ | exact zeros _ _ (by decide) (by decide) |
      exact (sym 3 0).trans third

theorem atMostOneSparse {L : Submodule ℂ V}
    (symmetric : ∀ v ∈ L, ∀ i j : Fin 4, v (i,j)=v (j,i))
    (level : ∀ v ∈ L, Matrix.permanent (Matrix.of fun i j : Fin 4 => 1+v (i,j))=24)
    (rank : 3 ≤ Module.finrank ℂ L) : Module.finrank ℂ (L ⊓ supportedAt 0 : Submodule ℂ V) ≤ 1 := by
  by_contra! high
  have hsub : L ⊓ supportedAt 0 ≤ LinearMap.range starMap := fun _ hv => sparse symmetric level hv
  have same := Submodule.eq_of_le_of_finrank_le hsub (by rw [rank_starPlane]; omega)
  have inside : LinearMap.range starMap ≤ L := same ▸ inf_le_left
  have two := rank_if_contains_star inside symmetric level
  omega


def relabel (σ : Equiv.Perm (Fin 4)) : V ≃ₗ[ℂ] V where
  toFun x := fun ij => x (σ ij.1,σ ij.2)
  invFun x := fun ij => x (σ.symm ij.1,σ.symm ij.2)
  left_inv x := by funext ⟨i,j⟩; simp
  right_inv x := by funext ⟨i,j⟩; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A simultaneous permutation of rows and columns gives the same
    sparse-kernel obstruction at every principal three-by-three block. -/
theorem atMostOneSparseAt {L : Submodule ℂ V}
    (symmetric : ∀ v ∈ L, ∀ i j : Fin 4, v (i,j)=v (j,i))
    (level : ∀ v ∈ L, Matrix.permanent (Matrix.of fun i j : Fin 4 => 1+v (i,j))=24)
    (rank : 3 ≤ Module.finrank ℂ L) (k : Fin 4) :
    Module.finrank ℂ (L ⊓ supportedAt k : Submodule ℂ V) ≤ 1 := by
  let σ := Equiv.swap (0 : Fin 4) k
  let e := relabel σ
  let M := L.map e.toLinearMap
  have sym (v) (hv : v ∈ M) (i j : Fin 4) : v (i,j)=v (j,i) := by
    obtain ⟨x,hx,rfl⟩ := hv; exact symmetric x hx (σ i) (σ j)
  have same (v) (hv : v ∈ M) :
      Matrix.permanent (Matrix.of fun i j : Fin 4 => 1+v (i,j)) = 24 := by
    obtain ⟨x,hx,rfl⟩ := hv
    let A := Matrix.of fun i j : Fin 4 => 1+x (i,j)
    change ((A.submatrix σ id).submatrix id σ).permanent = _
    rw [Matrix.permanent_permute_rows,Matrix.permanent_permute_cols]
    exact level x hx
  have dim : Module.finrank ℂ M = Module.finrank ℂ L := LinearEquiv.finrank_map_eq e L
  have low := atMostOneSparse sym same (by omega)
  have im : (L ⊓ supportedAt k : Submodule ℂ V).map e.toLinearMap ≤ M ⊓ supportedAt 0 := by
    rintro y ⟨x,hx,rfl⟩
    refine ⟨⟨x,hx.1,rfl⟩,?_⟩
    intro i j hi hj
    have zero : σ 0 = k := Equiv.swap_apply_left ..
    exact hx.2 (σ i) (σ j) (fun eq => hi (σ.injective (eq.trans zero.symm)))
      (fun eq => hj (σ.injective (eq.trans zero.symm)))
  have bound := Submodule.finrank_mono im
  rw [LinearEquiv.finrank_map_eq] at bound
  omega


/-- Delete row and column k. -/
def principal (k : Fin 4) : V →ₗ[ℂ] (Fin 3 × Fin 3 → ℂ) where
  toFun v := fun ij => v (k.succAbove ij.1,k.succAbove ij.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem principalKer (k : Fin 4) : (principal k).ker = supportedAt k := by
  ext v
  constructor
  · intro h i j ni nj
    have pre : ∀ p u : Fin 4, u ≠ p → ∃ a : Fin 3, p.succAbove a = u := by decide
    obtain ⟨a,rfl⟩ := pre k i ni
    obtain ⟨b,rfl⟩ := pre k j nj
    exact congrFun (LinearMap.mem_ker.mp h) (a,b)
  · intro h
    apply LinearMap.mem_ker.mpr
    funext ⟨i,j⟩
    exact h _ _ (k.succAbove_ne i) (k.succAbove_ne j)

/-- Deleting any one row and its matching column from a hypothetical
    three-dimensional witness still leaves at least two independent matrices. -/
theorem principalRank {L : Submodule ℂ V}
    (symmetric : ∀ v ∈ L, ∀ i j : Fin 4, v (i,j)=v (j,i))
    (level : ∀ v ∈ L, Matrix.permanent (Matrix.of fun i j : Fin 4 => 1+v (i,j))=24)
    (rank : 3 ≤ Module.finrank ℂ L) (k : Fin 4) :
    2 ≤ Module.finrank ℂ (LinearMap.range ((principal k).comp L.subtype)) := by
  let f := (principal k).comp L.subtype
  have dim := f.finrank_range_add_finrank_ker
  have iso := (L.equivSubtypeMap f.ker).finrank_eq
  have eq : f.ker.map L.subtype = L ⊓ supportedAt k := by
    rw [show f.ker = ((principal k).ker).comap L.subtype from LinearMap.ker_comp ..,
      Submodule.map_comap_subtype,principalKer]
  rw [eq] at iso
  have small := atMostOneSparseAt symmetric level rank k
  change 2 ≤ Module.finrank ℂ f.range
  omega

end Gct232.StarMaximal
