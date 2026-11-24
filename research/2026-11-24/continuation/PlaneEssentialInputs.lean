import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.PlaneEssentialInputs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.TopForm PEqualNP.GenericRejection

-- The support count below is adapted from the project's
-- PEqualNP.MetaComplexity.Helpers.Support and L011.
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

variable {n : ℕ}

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

/-- The support of a gate: the union of the supports of the wires it reads. -/
def gateSupp (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

theorem mem_foldr_union (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

theorem mem_gateSupp (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _

/-- The supports of all wires, starting from the supports `L` of the wires present. -/
def suppsFrom (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

/-- The supports of the input wires: input `i` has support `{i}`. -/
def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

/-- Wire lists `w`, `w'` (for the inputs `x`, `y`) agree on every wire whose support `x` and
`y` agree on. -/
def Agree (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

theorem agree_wiresFrom (x y : Fin n → Bool) (gs : List Gate) :
    ∀ (L : List (Finset (Fin n))) (w w' : List Bool), Agree x y L w w' →
      Agree x y (suppsFrom gs L) (wiresFrom gs w) (wiresFrom gs w') := by
  induction gs with
  | nil => intro L w w' h; exact h
  | cons g gs ih =>
    intro L w w' h
    obtain ⟨h1, h2, h3⟩ := h
    apply ih (L ++ [gateSupp L g])
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
    refine ⟨by simp [h1], by simp [h2], ?_⟩
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq] at hj
      rw [h1, getD_snoc_eq, h2, getD_snoc_eq]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun i hi => hj i ((mem_gateSupp L g i).2 ⟨a, ha, hi⟩))
    · rw [getD_snoc_ne _ _ _ _ hjl] at hj
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact h3 j hj

theorem agree_inputs (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

/-- Any set `W` of wires has a joint support of size at most `t + |W|`. -/
def Cnt (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

theorem cnt_inputs : Cnt 0 (inputSupps n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < n
  · simp [inputSupps, hjn]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem cnt_step (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2)
    (h : Cnt t L) : Cnt (t + 1) (L ++ [gateSupp L g]) := by
  intro W
  by_cases hW : L.length ∈ W
  · have hsub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        ⊆ ((W.erase L.length ∪ g.inputs.toFinset).biUnion fun j => L.getD j ∅) := by
      intro i hi
      rw [Finset.mem_biUnion] at hi ⊢
      obtain ⟨j, hjW, hij⟩ := hi
      by_cases hjl : j = L.length
      · subst hjl
        rw [getD_snoc_eq] at hij
        obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).1 hij
        exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.2 ha), hia⟩
      · rw [getD_snoc_ne _ _ _ _ hjl] at hij
        exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
    have hc1 : (W.erase L.length ∪ g.inputs.toFinset).card ≤ (W.card - 1) + 2 := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) hg) _
    have hWpos : 1 ≤ W.card := Finset.card_pos.2 ⟨_, hW⟩
    have := h (W.erase L.length ∪ g.inputs.toFinset)
    have := Finset.card_le_card hsub
    omega
  · have heq : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        = (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (fun e => hW (e ▸ hj))
    rw [heq]
    have := h W
    omega

theorem cnt_suppsFrom (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
    (∀ g ∈ gs, Ok g) → Cnt t L → Cnt (t + gs.length) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L _ h; exact h
  | cons g gs ih =>
    intro t L hok h
    have := ih (t + 1) (L ++ [gateSupp L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (cnt_step t L g (hok g List.mem_cons_self).2 h)
    rw [List.length_cons, show t + (gs.length + 1) = t + 1 + gs.length by omega]
    exact this

/-- A function that depends on each of its `n` inputs has no circuit with fewer than `n - 1`
gates. -/
theorem dep_lower (n : ℕ) (f : (Fin n → Bool) → Bool)
    (hdep : ∀ i : Fin n, ∃ x : Fin n → Bool, f (Function.update x i (!x i)) ≠ f x)
    (s : ℕ) (h : HasCircuitSize n f s) : n ≤ s + 1 := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set S := (suppsFrom C.gates (inputSupps n)).getD C.output ∅ with hS
  have hall : ∀ i : Fin n, i ∈ S := by
    intro i
    by_contra hi
    obtain ⟨x, hx⟩ := hdep i
    apply hx
    have hag := (agree_wiresFrom (Function.update x i (!x i)) x C.gates _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ i := fun e => hi (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hev, ← hev]
    exact hag
  have hcard : S.card = n := by
    rw [Finset.eq_univ_of_forall hall]; simp
  have hc := cnt_suppsFrom C.gates 0 (inputSupps n) ok cnt_inputs {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hc
  rw [← hS, hcard] at hc
  omega

theorem nonisolated_lower (n : ℕ) (S : Fin n → Finset (Fin n)) (C : Circuit)
    (line_meets : ∀ l, (S l).Nonempty) (point_meets : ∀ p, ∃ l, p ∈ S l)
    (model : IsAO2 (n+n) C) (accepts : RightOnIncidentPairs S C)
    (singles : ∀ X Y : Finset (Fin n), X.card + Y.card = 1 → C.eval (incidenceInput X Y) = false) :
    n + n ≤ C.size + 1 := by
  have empty_line (p : Fin n) := singles {p} ∅ (by simp)
  have empty_point (l : Fin n) := singles ∅ {l} (by simp)
  let vec (X Y : Finset (Fin n)) : Fin (n+n) → Bool :=
    Fin.addCases (fun p => decide (p ∈ X)) (fun l => decide (l ∈ Y))
  have vec_list (X Y : Finset (Fin n)) : List.ofFn (vec X Y) = incidenceInput X Y :=
    List.ofFn_fin_append _ _
  have pt (X Y : Finset (Fin n)) (p : Fin n) :
      vec X Y (Fin.castAdd n p) = decide (p ∈ X) := Fin.addCases_left ..
  have ln (X Y : Finset (Fin n)) (l : Fin n) :
      vec X Y (Fin.natAdd n l) = decide (l ∈ Y) := Fin.addCases_right ..
  have separate (p l : Fin n) : Fin.castAdd n p ≠ Fin.natAdd n l := by
    intro he
    have hv := congrArg Fin.val he
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
    have hp := p.isLt
    omega
  have turnOnPoint (p l : Fin n) :
      Function.update (vec ∅ {l}) (Fin.castAdd n p) (!(vec ∅ {l} (Fin.castAdd n p)))
        = vec {p} {l} := by
    funext k
    revert k
    apply Fin.addCases
    · intro a
      by_cases ha : a = p
      · subst a
        simp [pt]
      · have hne : Fin.castAdd n a ≠ Fin.castAdd n p := fun h => ha (Fin.castAdd_inj.mp h)
        rw [Function.update_of_ne hne, pt, pt]; simp [ha]
    · intro b
      rw [Function.update_of_ne (separate p b).symm, ln, ln]
  have turnOnLine (p l : Fin n) :
      Function.update (vec {p} ∅) (Fin.natAdd n l) (!(vec {p} ∅ (Fin.natAdd n l)))
        = vec {p} {l} := by
    funext k
    revert k
    apply Fin.addCases
    · intro a
      rw [Function.update_of_ne (separate a l), pt, pt]
    · intro b
      by_cases hb : b = l
      · subst b
        rw [Function.update_self, ln, ln]; simp
      · have hne : Fin.natAdd n b ≠ Fin.natAdd n l := fun h => hb ((Fin.natAdd_inj n).mp h)
        rw [Function.update_of_ne hne, ln, ln]; simp [hb]
  let f (x : Fin (n+n) → Bool) := C.eval (List.ofFn x)
  have hs : HasCircuitSize (n+n) f C.size := by
    refine ⟨C, ?_, le_rfl, fun _ => rfl⟩
    intro g hg
    refine ⟨?_, (model.2.2 g hg).le⟩
    rcases model.1 g hg with hop | hop <;> simp [hop]
  apply dep_lower (n+n) f ?_ C.size hs
  apply Fin.addCases
  · intro p
    obtain ⟨l, hp⟩ := point_meets p
    refine ⟨vec ∅ {l}, ?_⟩
    change C.eval (List.ofFn _) ≠ C.eval (List.ofFn _)
    rw [turnOnPoint, vec_list, vec_list, accepts l p hp, empty_point l]
    decide
  · intro l
    obtain ⟨p, hp⟩ := line_meets l
    refine ⟨vec {p} ∅, ?_⟩
    change C.eval (List.ofFn _) ≠ C.eval (List.ofFn _)
    rw [turnOnLine, vec_list, vec_list, accepts l p hp, empty_line p]
    decide

end PEqualNP.Outside.PlaneEssentialInputs

theorem PEqualNP.Outside.PlaneEssentialInputs : ∀ (x1 : ℕ) (x2 : Fin x1 → Finset (Fin x1)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x4 : Fin x1), (x2 x4).Nonempty) → (∀ (x5 : Fin x1), ∃ (x6 : Fin x1), x5 ∈ x2 x6) → PEqualNP.TopForm.IsAO2 (x1 + x1) x3 → PEqualNP.GenericRejection.RightOnIncidentPairs x2 x3 → (∀ (x8 x9 : Finset (Fin x1)), x8.card + x9.card = (1 : ℕ) → x3.eval (PEqualNP.GenericRejection.incidenceInput x8 x9) = Bool.false) → x1 + x1 ≤ x3.size + (1 : ℕ) :=
  PEqualNP.Outside.PlaneEssentialInputs.nonisolated_lower
