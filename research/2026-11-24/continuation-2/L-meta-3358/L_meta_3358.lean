import Mathlib.Data.Finset.Card
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3358

open PEqualNP.CircuitLowerBounds

def parents (g : Gate) : List ℕ :=
  match g.op with
  | .not => g.inputs.take 1
  | _ => g.inputs

def binaryCost (g : Gate) : ℕ :=
  match g.op with
  | .not => 0
  | _ => 1

lemma arity (g : Gate) (fan : g.inputs.length ≤ 2) :
    (parents g).length ≤ 1 + binaryCost g := by
  obtain ⟨op, ins⟩ := g
  cases op <;> simp_all [parents,binaryCost]

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]) w

lemma eval_congr (g : Gate) (p q : ℕ → Bool) (eqv : ∀ i ∈ parents g, p i = q i) :
    g.op.eval (g.inputs.map p) = g.op.eval (g.inputs.map q) := by
  obtain ⟨op, ins⟩ := g
  cases op with
  | not =>
    cases ins with
    | nil => rfl
    | cons a l => simpa [GateOp.eval] using congrArg Bool.not (eqv a (by simp [parents]))
  | _ => exact congrArg _ (List.map_congr_left (l := ins) eqv)

lemma bounded_agreement (w v : List Bool) (n i : ℕ) (hw : w.length = n) (hv : v.length = n)
    (h : i < n → w.getD i false = v.getD i false) : w.getD i false = v.getD i false := by
  by_cases hl : i < n
  · exact h hl
  · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]

theorem suffix_ports (gs : List Gate) (n o : ℕ) (fan : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    ∃ U : Finset ℕ, U ⊆ Finset.range n ∧ U.card ≤ 1 + (gs.map binaryCost).sum ∧
      ∀ w v : List Bool, w.length = n → v.length = n →
        (∀ i ∈ U, w.getD i false = v.getD i false) →
        (run gs w).getD o false = (run gs v).getD o false := by
  induction gs generalizing n with
  | nil =>
    refine ⟨{o} ∩ Finset.range n, Finset.inter_subset_right, ?_, ?_⟩
    · simpa using Finset.card_le_card (Finset.inter_subset_left (s₁ := {o}) (s₂ := Finset.range n))
    · intro w v hw hv h
      exact bounded_agreement w v n o hw hv (fun ho => h o (by simp [ho]))
  | cons g gs ih =>
    obtain ⟨V, vrange, budget, agrees⟩ := ih (n+1) (fun g' hg => fan g' (by simp [hg]))
    let deps := (parents g).toFinset ∩ Finset.range n
    let U := if n ∈ V then V.erase n ∪ deps else V
    have old (i : ℕ) (vi : i ∈ V) (ne : i ≠ n) : i ∈ U := by
      by_cases used : n ∈ V <;> simp [U, used, vi, ne]
    refine ⟨U, ?_, ?_, ?_⟩
    · intro i hi
      by_cases used : n ∈ V
      · rw [show U = V.erase n ∪ deps from if_pos used] at hi
        rcases Finset.mem_union.mp hi with earlier | read
        · obtain ⟨ne, mem⟩ := Finset.mem_erase.mp earlier
          have lt := Finset.mem_range.mp (vrange mem)
          exact Finset.mem_range.mpr (by omega)
        · exact (Finset.mem_inter.mp read).2
      · rw [show U = V from if_neg used] at hi
        have lt := Finset.mem_range.mp (vrange hi)
        have ne : i ≠ n := fun eq => used (eq ▸ hi)
        exact Finset.mem_range.mpr (by omega)
    · simp only [List.map_cons, List.sum_cons]
      by_cases used : n ∈ V
      · have hd : deps.card ≤ (parents g).length :=
          (Finset.card_le_card Finset.inter_subset_left).trans (List.toFinset_card_le _)
        have ha := arity g (fan g List.mem_cons_self)
        have he := Finset.card_erase_add_one used
        have hu := Finset.card_union_le (V.erase n) deps
        rw [show U = V.erase n ∪ deps from if_pos used]
        omega
      · rw [show U = V from if_neg used]
        omega
    · intro w v hw hv h
      let val (s : List Bool) := g.op.eval (g.inputs.map fun i => s.getD i false)
      apply agrees (w ++ [val w]) (v ++ [val v]) (by simp [hw]) (by simp [hv])
      intro i hi
      by_cases eq : i = n
      · subst i
        have vg : val w = val v := by
          apply eval_congr
          intro j read
          apply bounded_agreement w v n j hw hv
          intro jn
          apply h
          rw [show U = V.erase n ∪ deps from if_pos hi]
          exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨List.mem_toFinset.mpr read, Finset.mem_range.mpr jn⟩)
        rw [List.getD_append_right _ _ _ _ hw.le, List.getD_append_right _ _ _ _ hv.le,
          hw, hv, Nat.sub_self]
        exact vg
      · have lt := Finset.mem_range.mp (vrange hi)
        rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
        exact h i (old i hi eq)

lemma binaryCost_le (g : Gate) : binaryCost g ≤ 1 := by
  cases g with
  | mk op ins => cases op <;> simp [binaryCost]

lemma sum_le_length (gs : List Gate) : (gs.map binaryCost).sum ≤ gs.length := by
  induction gs with
  | nil => decide
  | cons g gs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have := binaryCost_le g
    omega

lemma lossOne (gs : List Gate) : ∀ (i : ℕ) (hi : i < gs.length),
    gs[i].op = .not → (gs.map binaryCost).sum + 1 ≤ gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    intro i hi hnot
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    cases i with
    | zero =>
      change g.op = .not at hnot
      simpa [binaryCost,hnot] using sum_le_length gs
    | succ i =>
      have hh := ih i (by simpa using hi) hnot
      have := binaryCost_le g
      omega

lemma lossTwo (gs : List Gate) : ∀ (i j : ℕ) (hi : i < gs.length) (hj : j < gs.length),
    i < j → gs[i].op = .not → gs[j].op = .not →
    (gs.map binaryCost).sum + 2 ≤ gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    intro i j hi hj ord ni nj
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    cases j with
    | zero => omega
    | succ j =>
      cases i with
      | zero =>
        change g.op = .not at ni
        have := lossOne gs j (by simpa using hj) nj
        simp [binaryCost,ni]
        omega
      | succ i =>
        have := ih i j (by simpa using hi) (by simpa using hj) (by omega) ni nj
        have := binaryCost_le g
        omega

theorem suffix_child (D : Circuit) (fan : PEqualNP.MetaComplexity.FanInTwo D)
    (size : D.size ≤ 7) (i j : Fin D.gates.length) (ord : i < j)
    (ni : (D.gates.get i).op = .not) (nj : (D.gates.get j).op = .not) :
    ∃ U : Finset ℕ, U ⊆ Finset.range 17 ∧ U.card ≤ 6 ∧
      ∀ w v : List Bool, w.length = 17 → v.length = 17 →
        (∀ k ∈ U, w.getD k false = v.getD k false) → D.eval w = D.eval v := by
  have losses := lossTwo D.gates i.val j.val i.isLt j.isLt ord ni nj
  obtain ⟨U,range,bound,agree⟩ := suffix_ports D.gates 17 D.output (fun g h => (fan g h).2)
  change D.gates.length ≤ 7 at size
  exact ⟨U,range,by omega,agree⟩

end PEqualNP.Outside.L_meta_3358

theorem PEqualNP.Outside.L_meta_3358 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (7 : ℕ) → ∀ (x4 x5 : Fin x1.gates.length), x4 < x5 → (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.not → (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ x9 ⊆ Finset.range (17 : ℕ), x9.card ≤ (6 : ℕ) ∧ ∀ (x10 x11 : List Bool), x10.length = (17 : ℕ) → x11.length = (17 : ℕ) → (∀ x14 ∈ x9, x10.getD x14 Bool.false = x11.getD x14 Bool.false) → x1.eval x10 = x1.eval x11 := PEqualNP.Outside.L_meta_3358.suffix_child
