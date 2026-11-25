import Pnp4201OrBudget

/-
Research bridge for L-meta-4201 / L-meta-8323.
Constant propagation preserves the value of each retained AND, and therefore
preserves AND soundness on every negative input of the represented function.
The construction and its operation budgets are reused from Pnp2343Pruning and
Pnp4201OrBudget (with their upstream attribution); the semantic cleanliness
invariant below is the additional result. No clean representation is asserted
for a circuit whose ANDs were not already clean.
-/

namespace PEqualNP.Outside.Pnp4201CleanNormalize

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.Pnp2343Pruning.Normalize
open PEqualNP.Outside.Pnp4201OrBudget

def AndClean (n : ℕ) (f : (Fin n → Bool) → Bool) (C : Circuit) : Prop :=
  ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
    ∀ x, f x = false → (C.wires (List.ofFn x)).getD (n + j) false = false

def step (g : Gate) (w : List Bool) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def AndOff : List Gate → List Bool → Prop
  | [], _ => True
  | g :: gs, w =>
      (g.op = GateOp.and → g.op.eval (g.inputs.map fun i => w.getD i false) = false) ∧
        AndOff gs (step g w)

theorem wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w = wiresFrom gs (step g w) := rfl

theorem wiresFrom_head (g : Gate) (gs : List Gate) (w : List Bool) :
    (wiresFrom (g :: gs) w).getD w.length false =
      g.op.eval (g.inputs.map fun i => w.getD i false) := by
  rw [wiresFrom_cons, getD_wiresFrom gs (step g w) w.length (by simp [step])]
  exact getD_snoc_eq _ _ _

theorem andOff_iff (gs : List Gate) (w : List Bool) :
    AndOff gs w ↔ ∀ (j : ℕ) (hj : j < gs.length), gs[j].op = GateOp.and →
      (wiresFrom gs w).getD (w.length + j) false = false := by
  induction gs generalizing w with
  | nil => simp [AndOff]
  | cons g gs ih =>
    constructor
    · rintro ⟨hg, ht⟩ j hj hop
      cases j with
      | zero => simpa [wiresFrom_head] using (wiresFrom_head g gs w).trans (hg hop)
      | succ j =>
        have hj' : j < gs.length := by simpa using hj
        have h := (ih (step g w)).1 ht j hj' (by simpa using hop)
        simpa [wiresFrom_cons, step, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
    · intro h
      refine ⟨?_, (ih (step g w)).2 ?_⟩
      · intro hg
        have hz := h 0 (by simp) (by simpa using hg)
        simpa only [Nat.add_zero, wiresFrom_head] using hz
      · intro j hj hop
        have ht := h (j + 1) (by simpa using hj) (by simpa using hop)
        simpa [wiresFrom_cons, step, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht

theorem andOff_append (pre post : List Gate) (w : List Bool) :
    AndOff (pre ++ post) w ↔ AndOff pre w ∧ AndOff post (wiresFrom pre w) := by
  induction pre generalizing w with
  | nil => simp [AndOff, wiresFrom]
  | cons g pre ih =>
    simp only [List.cons_append, AndOff, wiresFrom_cons, ih]
    exact and_assoc.symm

theorem simplify_some_stat (op : GateOp) (m : ℕ) (ins : List Stat) (g : Gate)
    (hg : (simplify op m ins).1 = some g) :
    (simplify op m ins).2 = Sum.inr m := by
  cases op <;> simp only [simplify] at hg ⊢
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;>
      (try cases a) <;> (try cases b) <;> simp [simpAnd] at hg ⊢
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;>
      (try cases a) <;> (try cases b) <;> simp [simpOr] at hg ⊢
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg ⊢
  · simp at hg
  · simp at hg

theorem simplify_andOff (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length)
    (hoff : op = GateOp.and → op.eval (ins.map (Stat.val w)) = false) :
    AndOff (simplify op w.length ins).1.toList w := by
  cases hs : (simplify op w.length ins).1 with
  | none => trivial
  | some g =>
    refine ⟨?_, trivial⟩
    intro hg
    have hgop : g.op = op := simplify_op op w.length ins g (by rw [hs]; simp)
    have hstat := simplify_some_stat op w.length ins g hs
    have hval := (simplify_sound op hop w ins hlen hv).2
    rw [hstat, hs] at hval
    have hv' : g.op.eval (g.inputs.map fun i => w.getD i false) =
        op.eval (ins.map (Stat.val w)) := by
      simpa only [Option.toList_some, Stat.val, wiresFrom_head] using hval
    exact hv'.trans (hoff (hgop.symm.trans hg))

theorem elim_andOff (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate),
      (∀ g ∈ gs, Ok g) → Inv n y w acc → AndOff gs w → AndOff acc.2 y →
      AndOff (elim n gs acc).2 y := by
  induction gs with
  | nil => intro w acc _ _ _ hacc; exact hacc
  | cons g gs ih =>
    intro w acc hok hinv horig hacc
    have hinv' : Inv n y (wiresFrom [g] w) (elimStep n acc g) :=
      inv_elim n y hy [g] w acc
        (fun g' hg' => hok g' (by simp at hg'; simp [hg'])) hinv
    rw [elim_cons]
    apply ih (step g w) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) hinv' horig.2
    change AndOff (acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList) y
    apply (andOff_append _ _ _).2
    refine ⟨hacc, ?_⟩
    let w' := wiresFrom acc.2 y
    have lw' : w'.length = n + acc.2.length := by
      dsimp [w']; rw [length_wiresFrom, hy]
    rw [← lw']
    apply simplify_andOff g.op (hok g List.mem_cons_self).1 w'
    · simpa using (hok g List.mem_cons_self).2
    · intro s hs
      obtain ⟨i, _, rfl⟩ := List.mem_map.1 hs
      rw [lw']
      exact (hinv.2 i).1
    · intro hg
      have he : (g.inputs.map fun i => acc.1.getD i (Sum.inl false)).map
          (Stat.val w') = g.inputs.map fun i => w.getD i false := by
        rw [List.map_map]
        apply List.map_congr_left
        intro i _
        exact (hinv.2 i).2
      rw [he]
      exact horig.1 hg

theorem normalize_nonconstant_clean_budgets (n : ℕ) (C : Circuit) (hM : Monotone2 C)
    (f : (Fin n → Bool) → Bool) (hf : circuitFun n C = f)
    (hnc : ∃ x y, f x ≠ f y) (hclean : AndClean n f C) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧ circuitFun n D = f ∧
      D.size ≤ C.size ∧ (∀ p : GateOp → Bool, opCount p D ≤ opCount p C) ∧
      AndClean n f D := by
  let acc := elim n C.gates (idStats n, [])
  have hok : ∀ g ∈ C.gates, Ok g := by
    intro g hg
    refine ⟨?_, (hM g hg).2⟩
    rcases (hM g hg).1 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  have hao : AO C.gates := fun g hg => (hM g hg).1
  have hinv : ∀ x : Fin n → Bool,
      Inv n (List.ofFn x) (wiresFrom C.gates (List.ofFn x)) acc :=
    fun x => inv_elim n _ (by simp) C.gates _ _ hok (inv_id n x)
  have hval : ∀ x : Fin n → Bool,
      (acc.1.getD C.output (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn x)) = f x := by
    intro x
    exact ((hinv x).2 C.output).2.trans (congrFun hf x)
  have hlen : acc.2.length ≤ C.size := by
    have h := elim_len n C.gates (idStats n, [])
    simpa only [acc, Circuit.size, List.length_nil, zero_add] using h
  have hcount (p : GateOp → Bool) :
      acc.2.countP (fun g => p g.op) ≤ opCount p C := by
    have h := PEqualNP.Outside.Pnp4201OrBudget.Normalize.elim_countP p n C.gates (idStats n, [])
    simpa only [acc, opCount, List.countP_nil, zero_add] using h
  have haccClean : ∀ x : Fin n → Bool, f x = false → AndOff acc.2 (List.ofFn x) := by
    intro x hx
    apply elim_andOff n (List.ofFn x) (by simp) C.gates (List.ofFn x) (idStats n, [])
      hok (inv_id n x) ?_ trivial
    apply (andOff_iff C.gates (List.ofFn x)).2
    intro j hj hop
    have hg : (gateAt C j).op = GateOp.and := by
      rw [PEqualNP.Outside.Pnp2343Pruning.gateAt_eq hj]
      exact hop
    simpa only [List.length_ofFn, wires_eq] using hclean j hj hg x hx
  cases hs : acc.1.getD C.output (Sum.inl false) with
  | inl b =>
    exfalso
    obtain ⟨x, y, hxy⟩ := hnc
    apply hxy
    rw [← hval x, ← hval y, hs]
    rfl
  | inr w =>
    refine ⟨⟨acc.2, w⟩, ?_, ?_, hlen, hcount, ?_⟩
    · apply ao_clean_isAO2
      · exact elim_ao n C.gates _ hao (by intro g hg; simp at hg)
      · exact clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) C.gates _ _ hok
          (inv_id n _) (by intro p g hp; simp at hp)
    · funext x
      have hx := hval x
      rw [hs] at hx
      exact hx
    · intro j hj hop x hx
      have hg : acc.2[j].op = GateOp.and := by
        have hgate : gateAt (⟨acc.2, w⟩ : Circuit) j = acc.2[j] :=
          List.getD_eq_getElem _ _ hj
        rwa [hgate] at hop
      simpa only [List.length_ofFn, wires_eq] using
        (andOff_iff acc.2 (List.ofFn x)).1 (haccClean x hx) j hj hg

end PEqualNP.Outside.Pnp4201CleanNormalize
