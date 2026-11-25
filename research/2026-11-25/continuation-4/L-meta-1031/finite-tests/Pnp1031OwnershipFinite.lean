import PEqualNP.Defs

-- Wire evaluation facts are copied from upstream L_meta_1906 at 72c6f42af03b1.
-- The finite-test equivalence below is the new research result for L-meta-1031.
-- It concerns all AND gates of the same fan-in-two AND/OR circuit.

namespace Pnp1031OwnershipFinite

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.EdgeOwnership

namespace Wire

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (wf gs x).getD o false := rfl

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega


theorem wire_take (gates : List Gate) (X : List Bool) (k i : ℕ) (hi : i < X.length + k)
    (hk : k ≤ gates.length) :
    (wf gates X).getD i false = (wf (gates.take k) X).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gates]
  exact wf_prefix _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

theorem gate_val (gates : List Gate) (X : List Bool) (k : ℕ) (hk : k < gates.length) :
    (wf gates X).getD (X.length + k) false
      = gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false) := by
  rw [wire_take gates X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, wf_snoc]
  have := getD_snoc_eq (wf (gates.take k) X)
    (gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false))
  rw [wf_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at this
  exact this

def val (gates : List Gate) {n : ℕ} (w : ℕ) (x : Fin n → Bool) : Bool :=
  (wf gates (List.ofFn x)).getD w false

theorem iv_eq (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k ≤ gates.length)
    (i : ℕ) : (wf (gates.take k) (List.ofFn x)).getD i false = true ↔
      i < n + k ∧ val gates i x = true := by
  by_cases hi : i < n + k
  · rw [val, wire_take gates (List.ofFn x) k i (by simpa using hi) hk]
    simp [hi]
  · rw [List.getD_eq_default _ _ (by rw [wf_len, List.length_take, Nat.min_eq_left hk]; simp; omega)]
    simp [hi]

theorem val_and (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.and) :
    val gates (n + k) x = true ↔ ∀ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
  constructor
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).1 (h i hi)
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).2 (h i hi)

theorem val_or (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.or) :
    val gates (n + k) x = true ↔ ∃ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
  constructor
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).1 h⟩
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).2 h⟩

theorem val_input (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val gates w x = x ⟨w, hw⟩ := by
  rw [val, wf_keep gates _ w (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

theorem val_big (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ)
    (hw : n + gates.length ≤ w) : val gates w x = false := by
  rw [val, List.getD_eq_default _ _ (by rw [wf_len]; simpa using hw)]

theorem val_mono (gates : List Gate) {n : ℕ}
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x x' : Fin n → Bool) (hx : ∀ v, x v = true → x' v = true) :
    ∀ w, val gates w x = true → val gates w x' = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro h
    by_cases hwn : w < n
    · rw [val_input gates _ w hwn] at h ⊢
      exact hx _ h
    · by_cases hbig : n + gates.length ≤ w
      · rw [val_big gates x w hbig] at h
        exact Bool.noConfusion h
      · have hi : w - n < gates.length := by omega
        have he : n + (w - n) = w := by omega
        rw [← he] at h ⊢
        rcases (legal gates[w - n] (List.getElem_mem hi)).1 with ha | ho
        · apply (val_and gates x' (w - n) hi ha).2
          intro j hj
          obtain ⟨hjlt, hjv⟩ := (val_and gates x (w - n) hi ha).1 h j hj
          exact ⟨hjlt, ih j (by omega) hjv⟩
        · obtain ⟨j, hj, hjlt, hv⟩ := (val_or gates x (w - n) hi ho).1 h
          exact (val_or gates x' (w - n) hi ho).2 ⟨j, hj, hjlt, ih j (by omega) hv⟩


end Wire

def EdgeTrue {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → Bool) : Prop :=
  ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true

def RejectsNonedgePairs {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) : Prop :=
  ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → g.op = GateOp.and →
    gateVal n C j (fun _ => false) = false ∧
    ∀ u v : Fin n, ¬ G.Adj u v → gateVal n C j (pairInput u v) = false

def AllAndSound {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) : Prop :=
  ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → g.op = GateOp.and →
    ∀ x : Fin n → Bool, gateVal n C j x = true → EdgeTrue G x

-- On an independent input every true wire has a single active input as an OR witness.
-- A true AND would instead give a forbidden zero, singleton, or nonedge-pair test.
theorem edgefree_wire_witness {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit)
    (hmono : Monotone2 C) (htests : RejectsNonedgePairs G C)
    (x : Fin n → Bool) (hfree : ¬ EdgeTrue G x) :
    ∀ w : ℕ, Wire.val C.gates w x = true →
      ∃ u : Fin n, x u = true ∧
        ∀ y : Fin n → Bool, y u = true → Wire.val C.gates w y = true := by
  classical
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hv
    by_cases hwn : w < n
    · refine ⟨⟨w, hwn⟩, ?_, ?_⟩
      · rwa [Wire.val_input C.gates x w hwn] at hv
      · intro y hy
        rwa [Wire.val_input C.gates y w hwn]
    · by_cases hbig : n + C.gates.length ≤ w
      · rw [Wire.val_big C.gates x w hbig] at hv
        contradiction
      · have hj : w - n < C.gates.length := by omega
        have hw : n + (w - n) = w := by omega
        have hgv : Wire.val C.gates (n + (w - n)) x = true := by rwa [hw]
        have hlegal := hmono C.gates[w - n] (List.getElem_mem hj)
        rcases hlegal.1 with hand | hor
        · exfalso
          have hreject := htests (w - n) C.gates[w - n]
            (List.getElem?_eq_getElem hj) hand
          have hlen := hlegal.2
          rcases hin : C.gates[w - n].inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
          · have hz : Wire.val C.gates (n + (w - n)) (fun _ : Fin n => false) = true :=
              (Wire.val_and C.gates _ (w - n) hj hand).2 (by
                intro i hi
                simp [hin] at hi)
            have hf : Wire.val C.gates (n + (w - n)) (fun _ : Fin n => false) = false :=
              hreject.1
            rw [hf] at hz
            contradiction
          · obtain ⟨ha, hva⟩ := (Wire.val_and C.gates x (w - n) hj hand).1 hgv a
              (by simp [hin])
            obtain ⟨u, hxu, hu⟩ := ih a (by omega) hva
            have hp : Wire.val C.gates (n + (w - n)) (pairInput u u) = true := by
              apply (Wire.val_and C.gates _ (w - n) hj hand).2
              intro i hi
              have hi' : i = a := by simpa [hin] using hi
              subst i
              exact ⟨ha, hu _ (by simp [pairInput])⟩
            have hf : Wire.val C.gates (n + (w - n)) (pairInput u u) = false :=
              hreject.2 u u G.irrefl
            rw [hf] at hp
            contradiction
          · obtain ⟨ha, hva⟩ := (Wire.val_and C.gates x (w - n) hj hand).1 hgv a
              (by simp [hin])
            obtain ⟨hb, hvb⟩ := (Wire.val_and C.gates x (w - n) hj hand).1 hgv b
              (by simp [hin])
            obtain ⟨u, hxu, hu⟩ := ih a (by omega) hva
            obtain ⟨v, hxv, hv'⟩ := ih b (by omega) hvb
            have hnonedge : ¬ G.Adj u v := fun hadj => hfree ⟨u, v, hadj, hxu, hxv⟩
            have hp : Wire.val C.gates (n + (w - n)) (pairInput u v) = true := by
              apply (Wire.val_and C.gates _ (w - n) hj hand).2
              intro i hi
              have hi' : i = a ∨ i = b := by simpa [hin] using hi
              rcases hi' with rfl | rfl
              · exact ⟨ha, hu _ (by simp [pairInput])⟩
              · exact ⟨hb, hv' _ (by simp [pairInput])⟩
            have hf : Wire.val C.gates (n + (w - n)) (pairInput u v) = false :=
              hreject.2 u v hnonedge
            rw [hf] at hp
            contradiction
          · rw [hin] at hlen
            simp only [List.length_cons] at hlen
            omega
        · obtain ⟨a, ha, halt, hva⟩ := (Wire.val_or C.gates x (w - n) hj hor).1 hgv
          obtain ⟨u, hxu, hu⟩ := ih a (by omega) hva
          refine ⟨u, hxu, ?_⟩
          intro y hy
          rw [← hw]
          exact (Wire.val_or C.gates y (w - n) hj hor).2 ⟨a, ha, halt, hu y hy⟩

theorem finite_tests_imply_all_and_sound {n : ℕ} (G : SimpleGraph (Fin n))
    (C : Circuit) (hmono : Monotone2 C) (htests : RejectsNonedgePairs G C) :
    AllAndSound G C := by
  classical
  intro j g hg hand x hx
  by_contra hfree
  obtain ⟨u, _, hu⟩ := edgefree_wire_witness G C hmono htests x hfree (n + j) hx
  have hp : gateVal n C j (pairInput u u) = true := hu _ (by simp [pairInput])
  rw [(htests j g hg hand).2 u u G.irrefl] at hp
  contradiction

theorem all_and_sound_implies_finite_tests {n : ℕ} (G : SimpleGraph (Fin n))
    (C : Circuit) (hsound : AllAndSound G C) : RejectsNonedgePairs G C := by
  intro j g hg hand
  refine ⟨?_, ?_⟩
  · apply Bool.eq_false_iff.mpr
    intro hv
    obtain ⟨u, v, _, hu, _⟩ := hsound j g hg hand (fun _ => false) hv
    exact Bool.false_ne_true hu
  · intro u v hnonedge
    apply Bool.eq_false_iff.mpr
    intro hv
    obtain ⟨a, b, hab, ha, hb⟩ := hsound j g hg hand (pairInput u v) hv
    simp only [pairInput, decide_eq_true_eq] at ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · rw [ha, hb] at hab
      exact G.irrefl hab
    · rw [ha, hb] at hab
      exact hnonedge hab
    · rw [ha, hb] at hab
      exact hnonedge hab.symm
    · rw [ha, hb] at hab
      exact G.irrefl hab

-- No correctness, minimality, triangle, or four-cycle hypothesis is needed here.
theorem all_and_sound_iff_finite_tests {n : ℕ} (G : SimpleGraph (Fin n))
    (C : Circuit) (hmono : Monotone2 C) :
    AllAndSound G C ↔ RejectsNonedgePairs G C :=
  ⟨all_and_sound_implies_finite_tests G C,
    finite_tests_imply_all_and_sound G C hmono⟩

end Pnp1031OwnershipFinite
