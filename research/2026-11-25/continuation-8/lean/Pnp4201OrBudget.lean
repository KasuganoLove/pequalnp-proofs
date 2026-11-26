import Pnp2343Pruning

/-
Research support for L-meta-4201. The task counts OR gates, not all gates.
Consequently an unrestricted minimum-size circuit is not a justified replacement.
This file proves operation-budget preservation and minimizes total size *within*
an operation budget. It does not assert the 104-OR lower bound.

The erasure and constant-propagation constructions are imported from our checked
Pnp2343Pruning research, whose attribution includes L-meta-1499 / PR3112,
L-meta-2668, L-meta-1680 and L-meta-1425. The budget invariants here are new.
-/

namespace PEqualNP.Outside.Pnp4201OrBudget

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.Pnp2343Pruning

def opCount (p : GateOp → Bool) (C : Circuit) : ℕ :=
  C.gates.countP (fun g => p g.op)

def isOr : GateOp → Bool
  | .or => true
  | _ => false

def orCount (C : Circuit) : ℕ := opCount isOr C

theorem orCount_eq_public (C : Circuit) :
    orCount C = C.gates.countP
      (fun g => GateOp.casesOn g.op false true false (fun _ => false) false) := by
  unfold orCount opCount
  congr 1
  funext g
  cases g.op <;> rfl

theorem bypass_opCount (p : GateOp → Bool) (n : ℕ) (C : Circuit) (r i : ℕ)
    (hr : r < C.gates.length) :
    opCount p (bypass n C r i) + (if p (gateAt C r).op then 1 else 0) = opCount p C := by
  rw [← erase_eq_bypass n C r i hr]
  unfold opCount PEqualNP.CircuitMoves.eraseGate
  rw [ite_eq_left hr]
  simp only [List.countP_append, List.countP_map, Function.comp_def]
  have hs : C.gates.take r ++ C.gates[r] :: C.gates.drop (r + 1) = C.gates := by
    rw [← List.drop_eq_getElem_cons hr, List.take_append_drop]
  have hc := congrArg (List.countP (fun g : Gate => p g.op)) hs
  simp only [List.countP_append, List.countP_cons] at hc
  rw [gateAt_eq hr]
  omega

theorem bypass_opCount_le (p : GateOp → Bool) (n : ℕ) (C : Circuit) (r i : ℕ)
    (hr : r < C.gates.length) : opCount p (bypass n C r i) ≤ opCount p C := by
  have := bypass_opCount p n C r i hr
  omega

namespace Normalize

open PEqualNP.Outside.Pnp2343Pruning.Normalize

theorem simplify_countP (p : GateOp → Bool) (op : GateOp) (m : ℕ) (ins : List Stat) :
    (simplify op m ins).1.toList.countP (fun g => p g.op) ≤ if p op then 1 else 0 := by
  cases hs : (simplify op m ins).1 with
  | none => simp
  | some g =>
    have hg : g.op = op := simplify_op op m ins g (by rw [hs]; simp)
    simp [hg]

theorem elim_countP (p : GateOp → Bool) (n : ℕ) (gs : List Gate) :
    ∀ acc : List Stat × List Gate,
      (elim n gs acc).2.countP (fun g => p g.op) ≤
        acc.2.countP (fun g => p g.op) + gs.countP (fun g => p g.op) := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 := simplify_countP p g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
    rw [elim_cons]
    simp only [elimStep, List.countP_append] at h1
    rw [List.countP_cons]
    simp only [elimStep]
    omega

theorem normalize_nonconstant_budgets (n : ℕ) (C : Circuit) (hM : Monotone2 C)
    (f : (Fin n → Bool) → Bool) (hf : circuitFun n C = f)
    (hnc : ∃ x y, f x ≠ f y) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧ circuitFun n D = f ∧
      D.size ≤ C.size ∧ ∀ p : GateOp → Bool, opCount p D ≤ opCount p C := by
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
    have h := elim_countP p n C.gates (idStats n, [])
    simpa only [acc, opCount, List.countP_nil, zero_add] using h
  cases hs : acc.1.getD C.output (Sum.inl false) with
  | inl b =>
    exfalso
    obtain ⟨x, y, hxy⟩ := hnc
    apply hxy
    rw [← hval x, ← hval y, hs]
    rfl
  | inr w =>
    refine ⟨⟨acc.2, w⟩, ?_, ?_, hlen, hcount⟩
    · apply ao_clean_isAO2
      · exact elim_ao n C.gates _ hao (by intro g hg; simp at hg)
      · exact clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) C.gates _ _ hok
          (inv_id n _) (by intro p g hp; simp at hp)
    · funext x
      have hx := hval x
      rw [hs] at hx
      exact hx

end Normalize

def LeastBudget (n : ℕ) (f : (Fin n → Bool) → Bool) (p : GateOp → Bool)
    (K : ℕ) (C : Circuit) : Prop :=
  Monotone2 C ∧ circuitFun n C = f ∧ opCount p C ≤ K ∧
    ∀ D : Circuit, Monotone2 D → circuitFun n D = f → opCount p D ≤ K → C.size ≤ D.size

theorem exists_least_budget (n : ℕ) (f : (Fin n → Bool) → Bool) (p : GateOp → Bool)
    (K : ℕ) (C : Circuit) (hM : Monotone2 C) (hf : circuitFun n C = f)
    (hK : opCount p C ≤ K) :
    ∃ D : Circuit, LeastBudget n f p K D ∧ D.size ≤ C.size := by
  classical
  let A (k : ℕ) : Prop := ∃ D : Circuit,
    Monotone2 D ∧ circuitFun n D = f ∧ opCount p D ≤ K ∧ D.size = k
  have hex : ∃ k, A k := ⟨C.size, C, hM, hf, hK, rfl⟩
  obtain ⟨D, hDm, hDf, hDK, hDs⟩ := Nat.find_spec hex
  refine ⟨D, ⟨hDm, hDf, hDK, ?_⟩, ?_⟩
  · intro E hEm hEf hEK
    rw [hDs]
    exact Nat.find_min' hex ⟨E, hEm, hEf, hEK, rfl⟩
  · rw [hDs]
    exact Nat.find_min' hex ⟨C, hM, hf, hK, rfl⟩

theorem least_budget_normal_form (n : ℕ) (f : (Fin n → Bool) → Bool)
    (p : GateOp → Bool) (K : ℕ) (C : Circuit)
    (hM : Monotone2 C) (hf : circuitFun n C = f) (hK : opCount p C ≤ K)
    (hnc : ∃ x y, f x ≠ f y) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧ LeastBudget n f p K D ∧
      D.size ≤ C.size := by
  obtain ⟨B, hB, hBC⟩ := exists_least_budget n f p K C hM hf hK
  obtain ⟨D, hD, hDf, hDB, hDp⟩ :=
    Normalize.normalize_nonconstant_budgets n B hB.1 f hB.2.1 hnc
  have hDm : Monotone2 D := by
    intro g hg
    exact ⟨hD.1 g hg, (hD.2.2 g hg).le⟩
  refine ⟨D, hD, ⟨hDm, hDf, (hDp p).trans hB.2.2.1, ?_⟩, hDB.trans hBC⟩
  intro E hEm hEf hEK
  exact hDB.trans (hB.2.2.2 E hEm hEf hEK)

theorem least_budget_no_alias (n : ℕ) (f : (Fin n → Bool) → Bool)
    (p : GateOp → Bool) (K : ℕ) (C : Circuit) (hmin : LeastBudget n f p K C)
    (r i : ℕ) (hr : r < C.gates.length)
    (hi : i < n + r ∨ n + C.gates.length ≤ i)
    (he : ∀ x : Fin n → Bool, val C (List.ofFn x) (n + r) = val C (List.ofFn x) i) :
    False := by
  have hfun : circuitFun n (bypass n C r i) = f := by
    funext x
    exact (bypass_eval_eq (by simp) (mono_ops hmin.1) hr hi (he x)).trans
      (congrFun hmin.2.1 x)
  have hK := (bypass_opCount_le p n C r i hr).trans hmin.2.2.1
  have hle := hmin.2.2.2 (bypass n C r i) (bypass_mono hmin.1) hfun hK
  change C.gates.length ≤ (bypass n C r i).gates.length at hle
  rw [bypass_length] at hle
  omega

theorem least_budget_distinct_inputs (n : ℕ) (f : (Fin n → Bool) → Bool)
    (p : GateOp → Bool) (K : ℕ) (C : Circuit) (hmin : LeastBudget n f p K C)
    (hRB : ReadsBack n C) (r a b : ℕ) (hr : r < C.gates.length)
    (hins : (gateAt C r).inputs = [a, b]) : a ≠ b := by
  intro hab
  subst b
  have ha : a < n + r := hRB r hr a (by simp [hins])
  apply least_budget_no_alias n f p K C hmin r a hr (Or.inl ha)
  intro x
  rw [val_gate (by simp) hr, hins]
  rcases mono_ops hmin.1 r hr with hand | hor
  · rw [hand]
    simp [GateOp.eval, ha]
  · rw [hor]
    simp [GateOp.eval, ha]

theorem least_budget_no_alias_order (n : ℕ) (f : (Fin n → Bool) → Bool)
    (p : GateOp → Bool) (K : ℕ) (C : Circuit) (hmin : LeastBudget n f p K C)
    (r i : ℕ) (hr : r < C.gates.length)
    (hi : i < n + r ∨ n + C.gates.length ≤ i)
    (hp : ∀ x : Fin n → Bool, f x = true →
      val C (List.ofFn x) (n + r) = true → val C (List.ofFn x) i = true)
    (hn : ∀ x : Fin n → Bool, f x = false →
      val C (List.ofFn x) i = true → val C (List.ofFn x) (n + r) = true) :
    False := by
  have hfun : circuitFun n (bypass n C r i) = f := by
    funext x
    change (bypass n C r i).eval (List.ofFn x) = f x
    have hC : C.eval (List.ofFn x) = f x := congrFun hmin.2.1 x
    cases hfx : f x with
    | false =>
      cases hD : (bypass n C r i).eval (List.ofFn x) with
      | false => rfl
      | true =>
        have hbad := bypass_eval_rel (R := fun a b => b = true → a = true)
          (fun _ => id) opMono_reverse (by simp) (mono_ops hmin.1) hr hi (hn x hfx) hD
        rw [hC, hfx] at hbad
        cases hbad
    | true =>
      exact bypass_eval_rel (R := fun a b => a = true → b = true)
        (fun _ => id) opMono_imp (by simp) (mono_ops hmin.1) hr hi (hp x hfx) (hC.trans hfx)
  have hK := (bypass_opCount_le p n C r i hr).trans hmin.2.2.1
  have hle := hmin.2.2.2 (bypass n C r i) (bypass_mono hmin.1) hfun hK
  change C.gates.length ≤ (bypass n C r i).gates.length at hle
  rw [bypass_length] at hle
  omega

theorem least_budget_and_negative_witness (n : ℕ) (f : (Fin n → Bool) → Bool)
    (p : GateOp → Bool) (K : ℕ) (C : Circuit) (hmin : LeastBudget n f p K C)
    (hRB : ReadsBack n C) (r a b : ℕ) (hr : r < C.gates.length)
    (hop : (gateAt C r).op = GateOp.and) (hins : (gateAt C r).inputs = [a, b]) :
    ∃ x : Fin n → Bool, f x = false ∧
      val C (List.ofFn x) a = true ∧ val C (List.ofFn x) b = false := by
  by_contra hex
  have ha : a < n + r := hRB r hr a (by simp [hins])
  have hb : b < n + r := hRB r hr b (by simp [hins])
  have hn (x : Fin n → Bool) (hx : f x = false)
      (hxa : val C (List.ofFn x) a = true) : val C (List.ofFn x) b = true := by
    cases he : val C (List.ofFn x) b with
    | false => exact False.elim (hex ⟨x, hx, hxa, he⟩)
    | true => rfl
  apply least_budget_no_alias_order n f p K C hmin r a hr (Or.inl ha)
  · intro x _ hx
    exact ((val_and (by simp) hr hop).mp hx) a (by simp [hins]) |>.2
  · intro x hx hxa
    apply (val_and (by simp) hr hop).mpr
    intro i hi
    rw [hins] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact ⟨ha, hxa⟩
    · exact ⟨hb, hn x hx hxa⟩

theorem least_budget_and_negative_incomparable (n : ℕ) (f : (Fin n → Bool) → Bool)
    (p : GateOp → Bool) (K : ℕ) (C : Circuit) (hmin : LeastBudget n f p K C)
    (hRB : ReadsBack n C) (r a b : ℕ) (hr : r < C.gates.length)
    (hop : (gateAt C r).op = GateOp.and) (hins : (gateAt C r).inputs = [a, b]) :
    (∃ x : Fin n → Bool, f x = false ∧
      val C (List.ofFn x) a = true ∧ val C (List.ofFn x) b = false) ∧
    (∃ x : Fin n → Bool, f x = false ∧
      val C (List.ofFn x) b = true ∧ val C (List.ofFn x) a = false) := by
  refine ⟨least_budget_and_negative_witness n f p K C hmin hRB r a b hr hop hins, ?_⟩
  by_contra hex
  have ha : a < n + r := hRB r hr a (by simp [hins])
  have hb : b < n + r := hRB r hr b (by simp [hins])
  have hn (x : Fin n → Bool) (hx : f x = false)
      (hxb : val C (List.ofFn x) b = true) : val C (List.ofFn x) a = true := by
    cases he : val C (List.ofFn x) a with
    | false => exact False.elim (hex ⟨x, hx, hxb, he⟩)
    | true => rfl
  apply least_budget_no_alias_order n f p K C hmin r b hr (Or.inl hb)
  · intro x _ hx
    exact ((val_and (by simp) hr hop).mp hx) b (by simp [hins]) |>.2
  · intro x hx hxb
    apply (val_and (by simp) hr hop).mpr
    intro i hi
    rw [hins] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact ⟨ha, hn x hx hxb⟩
    · exact ⟨hb, hxb⟩

theorem least_budget_or_positive_incomparable (n : ℕ) (f : (Fin n → Bool) → Bool)
    (p : GateOp → Bool) (K : ℕ) (C : Circuit) (hmin : LeastBudget n f p K C)
    (hRB : ReadsBack n C) (r a b : ℕ) (hr : r < C.gates.length)
    (hop : (gateAt C r).op = GateOp.or) (hins : (gateAt C r).inputs = [a, b]) :
    (∃ x : Fin n → Bool, f x = true ∧
      val C (List.ofFn x) a = true ∧ val C (List.ofFn x) b = false) ∧
    (∃ x : Fin n → Bool, f x = true ∧
      val C (List.ofFn x) b = true ∧ val C (List.ofFn x) a = false) := by
  have ha : a < n + r := hRB r hr a (by simp [hins])
  have hb : b < n + r := hRB r hr b (by simp [hins])
  constructor
  · by_contra hex
    have hp (x : Fin n → Bool) (hx : f x = true)
        (hxa : val C (List.ofFn x) a = true) : val C (List.ofFn x) b = true := by
      cases he : val C (List.ofFn x) b with
      | false => exact False.elim (hex ⟨x, hx, hxa, he⟩)
      | true => rfl
    apply least_budget_no_alias_order n f p K C hmin r b hr (Or.inl hb)
    · intro x hx hg
      obtain ⟨i, hi, _, hv⟩ := (val_or (by simp) hr hop).mp hg
      rw [hins] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact hp x hx hv
      · exact hv
    · intro x _ hbtrue
      exact (val_or (by simp) hr hop).mpr ⟨b, by simp [hins], hb, hbtrue⟩
  · by_contra hex
    have hp (x : Fin n → Bool) (hx : f x = true)
        (hxb : val C (List.ofFn x) b = true) : val C (List.ofFn x) a = true := by
      cases he : val C (List.ofFn x) a with
      | false => exact False.elim (hex ⟨x, hx, hxb, he⟩)
      | true => rfl
    apply least_budget_no_alias_order n f p K C hmin r a hr (Or.inl ha)
    · intro x hx hg
      obtain ⟨i, hi, _, hv⟩ := (val_or (by simp) hr hop).mp hg
      rw [hins] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact hv
      · exact hp x hx hv
    · intro x _ hatrue
      exact (val_or (by simp) hr hop).mpr ⟨a, by simp [hins], ha, hatrue⟩

theorem least_budget_gate_productive (n : ℕ) (f : (Fin n → Bool) → Bool)
    (p : GateOp → Bool) (K : ℕ) (C : Circuit) (hmin : LeastBudget n f p K C)
    (r : ℕ) (hr : r < C.gates.length) :
    ∃ x : Fin n → Bool, f x = true ∧ val C (List.ofFn x) (n + r) = true := by
  by_contra hex
  apply least_budget_no_alias_order n f p K C hmin r (n + C.gates.length) hr (Or.inr le_rfl)
  · intro x hx hg
    exact False.elim (hex ⟨x, hx, hg⟩)
  · intro x _ hi
    rw [val_ge (by simp) le_rfl] at hi
    cases hi

end PEqualNP.Outside.Pnp4201OrBudget
