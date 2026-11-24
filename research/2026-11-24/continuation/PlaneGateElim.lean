import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.Helpers.PermInputs
import PEqualNP.MetaComplexity.Helpers.LowMergeWires

namespace PEqualNP.Outside.PlaneGateElim

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.TopForm PEqualNP.GenericRejection

theorem size_after_one {m s : ℕ} (hm : 1 < m) (f : (Fin m → Bool) → Bool)
    (p : Fin m) (dep : ∃ x, f (Function.update x p (!x p)) ≠ f x)
    (rest : ∀ (b : Bool) (i : Fin m), i ≠ p →
       ∃ x, x p = b ∧ f (Function.update x i (!x i)) ≠ f x)
    (bound : HasCircuitSize m f s) : m ≤ s := by
  let T : Finset (Fin m) := Finset.univ.erase p
  have hcard : T.card = m-1 := by simp [T]
  have h := Helpers.PermInputs.fix_many T (Finset.card_pos.mp (by omega)) [p] f (by simp)
    (by intro v hv; simp at hv; subst v; simp [T]) (by
      intro a pre post i eqn
      have hlen := congrArg List.length eqn
      simp at hlen
      have ep : pre = [] := List.length_eq_zero_iff.mp (by omega)
      have es : post = [] := List.length_eq_zero_iff.mp (by omega)
      subst pre; subst post
      simp at eqn
      subst i
      obtain ⟨x, hx⟩ := dep
      exact ⟨x, by simp, hx⟩) (by
      intro a i hi
      have hip : i ≠ p := (Finset.mem_erase.mp hi).1
      obtain ⟨x, hxp, hx⟩ := rest (a p) i hip
      exact ⟨x, by simpa using hxp, hx⟩) s bound
  simp only [List.length_cons, List.length_nil] at h
  omega

def vec {n : ℕ} (X Y : Finset (Fin n)) : Fin (n+n) → Bool :=
  Fin.addCases (fun p => decide (p ∈ X)) (fun l => decide (l ∈ Y))

theorem vec_list {n : ℕ} (X Y : Finset (Fin n)) : List.ofFn (vec X Y) = incidenceInput X Y :=
  List.ofFn_fin_append _ _

theorem pt {n : ℕ} (X Y : Finset (Fin n)) (p : Fin n) :
    vec X Y (Fin.castAdd n p) = decide (p ∈ X) := Fin.addCases_left ..

theorem ln {n : ℕ} (X Y : Finset (Fin n)) (l : Fin n) :
    vec X Y (Fin.natAdd n l) = decide (l ∈ Y) := Fin.addCases_right ..

theorem separate {n : ℕ} (p l : Fin n) : Fin.castAdd n p ≠ Fin.natAdd n l := by
  intro eqn
  have h := congrArg Fin.val eqn
  simp only [Fin.val_castAdd, Fin.val_natAdd] at h
  have := p.isLt
  omega

theorem flipP {n : ℕ} (p : Fin n) (X Y : Finset (Fin n)) (hp : p ∉ X) :
    Function.update (vec X Y) (Fin.castAdd n p) (!(vec X Y (Fin.castAdd n p))) =
      vec (insert p X) Y := by
  funext k
  revert k
  apply Fin.addCases
  · intro a
    by_cases ha : a = p
    · subst a
      rw [Function.update_self, pt, pt]
      simp [hp]
    · have hd : Fin.castAdd n a ≠ Fin.castAdd n p := fun h => ha (Fin.castAdd_inj.mp h)
      rw [Function.update_of_ne hd, pt, pt]
      simp [ha]
  · intro l
    rw [Function.update_of_ne (separate p l).symm, ln, ln]

theorem flipL {n : ℕ} (l : Fin n) (X Y : Finset (Fin n)) (hl : l ∉ Y) :
    Function.update (vec X Y) (Fin.natAdd n l) (!(vec X Y (Fin.natAdd n l))) =
      vec X (insert l Y) := by
  funext k
  revert k
  apply Fin.addCases
  · intro p
    rw [Function.update_of_ne (separate p l), pt, pt]
  · intro a
    by_cases ha : a = l
    · subst a
      rw [Function.update_self, ln, ln]
      simp [hl]
    · have hd : Fin.natAdd n a ≠ Fin.natAdd n l := fun h => ha ((Fin.natAdd_inj n).mp h)
      rw [Function.update_of_ne hd, ln, ln]
      simp [ha]

theorem hit {n : ℕ} (S : Fin n → Finset (Fin n)) (C : Circuit)
    (hm : IsAO2 (n+n) C) (acc : RightOnIncidentPairs S C)
    (X Y : Finset (Fin n)) {p l : Fin n} (hpi : p ∈ S l) (hp : p ∈ X) (hl : l ∈ Y) :
    C.eval (incidenceInput X Y) = true := by
  have lift : ∀ v, vec {p} {l} v = true → vec X Y v = true := by
    apply Fin.addCases
    · intro a; rw [pt, pt]; simpa using (show a = p → a ∈ X from fun h => h ▸ hp)
    · intro b; rw [ln, ln]; simpa using (show b = l → b ∈ Y from fun h => h ▸ hl)
  have hpw : LowMergeProof.LeL (List.ofFn (vec {p} {l})) (List.ofFn (vec X Y)) := by
    intro i
    by_cases hi : i < n+n
    · simpa [hi] using lift ⟨i, hi⟩
    · simp [hi]
  have hv := LowMergeProof.wires_mono C hm.1 (List.ofFn (vec {p} {l})) (List.ofFn (vec X Y))
    (by simp) hpw C.output
  rw [vec_list, vec_list] at hv
  exact hv (acc l p hpi)

theorem sensitive_lower {q n : ℕ} (S : Fin n → Finset (Fin n)) (C : Circuit)
    (a : Fin n) (hm : IsAO2 (n+n) C) (acc : RightOnIncidentPairs S C)
    (rej : ∀ (X Y : Finset (Fin n)), Y.card ≤ q → IsFalseInput S X Y →
      C.eval (incidenceInput X Y) = false)
    (hq : 1 ≤ q) (a_meets : ∃ l, a ∈ S l)
    (point_separates : ∀ r : Fin n, r ≠ a → ∃ l, r ∈ S l ∧ a ∉ S l)
    (line_survives : ∀ l, ∃ r ∈ S l, r ≠ a) : n+n ≤ C.size := by
  let f : (Fin (n+n) → Bool) → Bool := circuitFun (n+n) C
  let fixed (b : Bool) : Finset (Fin n) := if b then {a} else ∅
  have only (b : Bool) (r : Fin n) : r ∈ fixed b → r = a := by cases b <;> simp [fixed]
  have flag (b : Bool) : decide (a ∈ fixed b) = b := by cases b <;> simp [fixed]
  have hs : HasCircuitSize (n+n) f C.size := by
    refine ⟨C, ?_, le_rfl, fun _ => rfl⟩
    intro g hg
    refine ⟨?_, (hm.2.2 g hg).le⟩
    rcases hm.1 g hg with hop | hop <;> simp [hop]
  have npos := a.isLt
  apply size_after_one (by omega) f (Fin.castAdd n a) ?_ ?_ hs
  · obtain ⟨l, ha⟩ := a_meets
    use vec ∅ {l}
    have neg := rej ∅ {l} (by simpa using hq) (by intro t ht; simp)
    change C.eval (List.ofFn _) ≠ C.eval (List.ofFn _)
    rw [flipP _ _ _ (by simp), vec_list, vec_list]
    simpa [acc l a ha, neg]
  · intro b
    apply Fin.addCases
    · intro r hd
      have hra : r ≠ a := fun eqn => hd (congrArg (Fin.castAdd n) eqn)
      obtain ⟨l, hrl, hal⟩ := point_separates r hra
      have hr : r ∉ fixed b := fun h => hra (only b r h)
      refine ⟨vec (fixed b) {l}, ?_, ?_⟩
      · rw [pt, flag]
      · have neg := rej (fixed b) {l} (by simpa using hq) (by
          intro t ht
          obtain rfl := Finset.mem_singleton.mp ht
          apply Finset.disjoint_left.mpr
          intro k hk hkb
          exact hal ((only b k hkb) ▸ hk))
        have pos := hit S C hm acc (insert r (fixed b)) {l} hrl (by simp) (by simp)
        change C.eval (List.ofFn _) ≠ C.eval (List.ofFn _)
        rw [flipP _ _ _ hr, vec_list, vec_list, pos, neg]
        decide
    · intro l _
      obtain ⟨r, hrl, hra⟩ := line_survives l
      refine ⟨vec (insert r (fixed b)) ∅, ?_, ?_⟩
      · rw [pt]
        simpa [Ne.symm hra] using flag b
      · have neg := rej (insert r (fixed b)) ∅ (by simp) (by intro t ht; simp at ht)
        have pos := hit S C hm acc (insert r (fixed b)) {l} hrl (by simp) (by simp)
        change C.eval (List.ofFn _) ≠ C.eval (List.ofFn _)
        rw [flipL _ _ _ (by simp), vec_list, vec_list]
        simpa [pos, neg]

theorem plane_linear {q n : ℕ} (S : Fin n → Finset (Fin n)) (C : Circuit)
    (hq : 1 ≤ q) (hn : n = q^2+q+1)
    (degree : ∀ l, (S l).card = q+1)
    (join : ∀ p r : Fin n, p ≠ r → ∃! l, p ∈ S l ∧ r ∈ S l)
    (hm : IsAO2 (n+n) C) (acc : RightOnIncidentPairs S C)
    (rej : ∀ (X Y : Finset (Fin n)), Y.card ≤ q → IsFalseInput S X Y →
      C.eval (incidenceInput X Y) = false) : n+n ≤ C.size := by
  let l0 : Fin n := ⟨0, by omega⟩
  obtain ⟨a, ha⟩ : (S l0).Nonempty := Finset.card_pos.mp (by rw [degree]; omega)
  apply sensitive_lower S C a hm acc rej hq ⟨l0, ha⟩
  · intro p hpa
    obtain ⟨l, ⟨hpl, hal⟩, uniq⟩ := join p a hpa
    obtain ⟨r, hr⟩ : ∃ r, r ∉ S l := by
      by_contra! h
      have all : S l = Finset.univ := Finset.eq_univ_of_forall h
      have eqn := degree l
      rw [all, Finset.card_univ, Fintype.card_fin] at eqn
      have pos : 0 < q^2 := pow_pos (by omega) 2
      omega
    have hpr : p ≠ r := fun e => hr (e ▸ hpl)
    obtain ⟨k, ⟨hpk, hrk⟩, _⟩ := join p r hpr
    refine ⟨k, hpk, ?_⟩
    intro hak
    have ke := uniq k ⟨hpk, hak⟩
    exact hr (ke ▸ hrk)
  · intro l
    by_contra! h
    have sub : S l ⊆ {a} := fun r hr => Finset.mem_singleton.mpr (h r hr)
    have card := Finset.card_le_card sub
    rw [Finset.card_singleton, degree] at card
    omega

theorem range_to_two_hundred {q n : ℕ} (S : Fin n → Finset (Fin n)) (C : Circuit)
    (hq : 1 ≤ q) (cap : q ≤ 200) (hn : n = q^2+q+1)
    (degree : ∀ l, (S l).card = q+1)
    (join : ∀ p r : Fin n, p ≠ r → ∃! l, p ∈ S l ∧ r ∈ S l)
    (hm : IsAO2 (n+n) C) (acc : RightOnIncidentPairs S C)
    (rej : ∀ (X Y : Finset (Fin n)), Y.card ≤ q → IsFalseInput S X Y →
      C.eval (incidenceInput X Y) = false) : n*q ≤ 100*C.size := by
  have bound := plane_linear S C hq hn degree join hm acc rej
  have multi := Nat.mul_le_mul_left n cap
  omega

end PEqualNP.Outside.PlaneGateElim
