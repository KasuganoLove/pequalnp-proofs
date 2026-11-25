import Pnp5126OwnershipWitness

/-!
Fixed raw-input supports plus one shared dirty-gate atom give an exact semantic
form on graph-negative inputs. This does not assume that the later dirty gate
is globally a pure rectangle. The imported wire helpers are attributed in the
witness module; all profile constructions below are new research declarations.
-/
namespace PEqualNP.Outside.Pnp5126OwnershipProfile

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.SplitCount
  PEqualNP.Outside.Pnp5126OwnershipWitness

attribute [local instance] gateOpDecEq

structure Profile (n : ℕ) where
  raw : Finset (Fin n)
  flag : Bool

def emptyProfile (n : ℕ) : Profile n := ⟨∅,false⟩
def joinProfile {n : ℕ} (a b : Profile n) : Profile n := ⟨a.raw ∪ b.raw,a.flag || b.flag⟩
def rawOr {n : ℕ} (A : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  decide (∃ v ∈ A, x v = true)
def reflect {n : ℕ} (p : Profile n) (x : Fin n → Bool) (z : Bool) : Bool :=
  rawOr p.raw x || (p.flag && z)

lemma rawOr_union {n : ℕ} (A B : Finset (Fin n)) (x : Fin n → Bool) :
    rawOr (A ∪ B) x = (rawOr A x || rawOr B x) := by
  simp [rawOr,or_and_right,exists_or]

lemma reflect_join {n : ℕ} (a b : Profile n) (x : Fin n → Bool) (z : Bool) :
    reflect (joinProfile a b) x z = (reflect a x z || reflect b x z) := by
  simp only [reflect,joinProfile,rawOr_union]
  cases rawOr a.raw x <;> cases rawOr b.raw x <;> cases a.flag <;> cases b.flag <;> cases z <;> rfl

/-- Stop at all AND gates, except for the selected shared atom g. -/
def profile (n : ℕ) (C : Circuit) (g w : ℕ) : Profile n :=
  if hw : w < n then ⟨{⟨w,hw⟩},false⟩
  else if w = n+g then ⟨∅,true⟩
  else if w-n < C.gates.length ∧ (gateAt C (w-n)).op = GateOp.or then
    joinProfile
      (if ha : opnd C (w-n) 0 < w then profile n C g (opnd C (w-n) 0) else emptyProfile n)
      (if hb : opnd C (w-n) 1 < w then profile n C g (opnd C (w-n) 1) else emptyProfile n)
  else emptyProfile n
termination_by w

lemma gate_inputs {n : ℕ} {C : Circuit} (hA : IsAO2 n C) {k : ℕ} (hk : k < C.gates.length) :
    (gateAt C k).inputs = [opnd C k 0,opnd C k 1] := by
  obtain ⟨a,b,hab⟩ := List.length_eq_two.mp (hA.2.2 _ (gateAt_mem hk))
  simp [opnd,hab]

lemma opnd_lt {n : ℕ} {C : Circuit} (hA : IsAO2 n C) {k : ℕ}
    (hk : k < C.gates.length) (b : Fin 2) : opnd C k b < n+k := by
  have hin : opnd C k b ∈ (gateAt C k).inputs := by
    rw [gate_inputs hA hk]
    fin_cases b <;> simp
  exact hA.2.1 k hk _ hin

lemma val_binary {n : ℕ} {C : Circuit} (hA : IsAO2 n C) {k : ℕ}
    (hk : k < C.gates.length) (x : Fin n → Bool) :
    gateVal n C k x = (gateAt C k).op.eval
      [val C (List.ofFn x) (opnd C k 0),val C (List.ofFn x) (opnd C k 1)] := by
  change val C (List.ofFn x) (n+k) = _
  rw [val_gate (n := n) (by simp) hk,gate_inputs hA hk]
  simp only [List.map_cons,List.map_nil,ite_eq_left (opnd_lt hA hk 0),
    ite_eq_left (opnd_lt hA hk 1)]

lemma profile_raw {n : ℕ} {C : Circuit} {g w : ℕ} (hw : w < n) :
    profile n C g w = ⟨{⟨w,hw⟩},false⟩ := by
  rw [profile]
  exact dite_eq_left hw

lemma profile_atom {n : ℕ} (C : Circuit) (g : ℕ) :
    profile n C g (n+g) = ⟨∅,true⟩ := by
  rw [profile,dite_eq_right (show ¬n+g < n by omega),ite_eq_left rfl]

lemma profile_and {n : ℕ} {C : Circuit} {g k : ℕ}
    (hkg : k ≠ g) (hop : (gateAt C k).op = GateOp.and) :
    profile n C g (n+k) = emptyProfile n := by
  have hne : n+k ≠ n+g := by omega
  rw [profile,dite_eq_right (show ¬n+k < n by omega),ite_eq_right hne,Nat.add_sub_cancel_left]
  have hno : ¬(k < C.gates.length ∧ (gateAt C k).op = GateOp.or) := by
    rintro ⟨_,ho⟩
    rw [hop] at ho
    cases ho
  exact ite_eq_right hno

lemma profile_or {n : ℕ} {C : Circuit} (hA : IsAO2 n C) {g k : ℕ}
    (hk : k < C.gates.length) (hkg : k ≠ g) (hop : (gateAt C k).op = GateOp.or) :
    profile n C g (n+k) =
      joinProfile (profile n C g (opnd C k 0)) (profile n C g (opnd C k 1)) := by
  have hne : n+k ≠ n+g := by omega
  rw [profile,dite_eq_right (show ¬n+k < n by omega),ite_eq_right hne,Nat.add_sub_cancel_left,
    ite_eq_left ⟨hk,hop⟩,dite_eq_left (opnd_lt hA hk 0),dite_eq_left (opnd_lt hA hk 1)]

/-- The shared atom cannot occur before its own gate. -/
lemma flag_before {n : ℕ} {C : Circuit} (hA : IsAO2 n C) {g : ℕ}
    (hg : g < C.gates.length) : ∀ w < n+g, (profile n C g w).flag = false := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hraw : w < n
    · rw [profile_raw hraw]
    obtain ⟨k,rfl⟩ : ∃ k, w = n+k := ⟨w-n,by omega⟩
    have hkg : k < g := by omega
    have hk : k < C.gates.length := by omega
    rcases hA.1 _ (gateAt_mem hk) with hop | hop
    · rw [profile_and (by omega) hop]
      rfl
    · rw [profile_or hA hk (by omega) hop]
      change ((profile n C g (opnd C k 0)).flag || (profile n C g (opnd C k 1)).flag) = false
      rw [ih _ (opnd_lt hA hk 0) (by have := opnd_lt hA hk 0; omega),
        ih _ (opnd_lt hA hk 1) (by have := opnd_lt hA hk 1; omega)]
      rfl

lemma two_junk_other_false {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) {g t k : ℕ} (hJ : junk G C = {g,t})
    (hk : k < C.gates.length) (hkg : k ≠ g) (hkt : k ≠ t)
    (hop : (gateAt C k).op = GateOp.and) (x : Fin n → Bool)
    (hx : graphFun G ∅ x = false) : gateVal n C k x = false := by
  cases he : gateVal n C k x with
  | false => rfl
  | true =>
    have hkJ : k ∈ junk G C := (mem_junk_iff G C k).mpr ⟨hk,hop,x,he,hx⟩
    rw [hJ] at hkJ
    simp only [Finset.mem_insert,Finset.mem_singleton] at hkJ
    exact False.elim (hkJ.elim hkg hkt)

/-- Exact profile semantics on negative inputs, before the second dirty gate. -/
lemma profile_correct {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hA : IsAO2 n C) (g t : ℕ) (ht : t < C.gates.length)
    (hJ : junk G C = {g,t}) (x : Fin n → Bool) (hx : graphFun G ∅ x = false) :
    ∀ w < n+t, val C (List.ofFn x) w = reflect (profile n C g w) x (gateVal n C g x) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hraw : w < n
    · rw [val_fn_input C x w hraw,profile_raw hraw]
      simp [reflect,rawOr]
    obtain ⟨k,rfl⟩ : ∃ k, w = n+k := ⟨w-n,by omega⟩
    have hkt : k < t := by omega
    have hk : k < C.gates.length := by omega
    by_cases hkg : k = g
    · subst k
      rw [profile_atom]
      simp [reflect,rawOr]
      rfl
    rcases hA.1 _ (gateAt_mem hk) with hop | hop
    · change gateVal n C k x = _
      rw [two_junk_other_false G C hJ hk hkg (by omega) hop x hx,profile_and hkg hop]
      simp [reflect,emptyProfile,rawOr]
    · change gateVal n C k x = _
      rw [val_binary hA hk x,hop,profile_or hA hk hkg hop,reflect_join]
      simp only [GateOp.eval,List.any_cons,List.any_nil,id_eq,Bool.or_false]
      rw [ih _ (opnd_lt hA hk 0) (by have := opnd_lt hA hk 0; omega),
        ih _ (opnd_lt hA hk 1) (by have := opnd_lt hA hk 1; omega)]

end PEqualNP.Outside.Pnp5126OwnershipProfile
