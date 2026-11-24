import Mathlib
import PEqualNP.Defs

namespace Pnp1894Scratch
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def support : Fin 42 → Bool := fun i =>
  decide (i.val ∈ ([0, 1, 2, 6, 8, 18, 24, 31, 33, 37] : List Nat))

def Incident (u v : Fin 42) : Prop :=
  u.val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - u.val) % 21 ∈ ([0, 5, 7, 17, 20] : List Nat)

def HasIncidence (x : Fin 42 → Bool) : Prop :=
  ∃ u v : Fin 42, Incident u v ∧ x u = true ∧ x v = true

lemma support_independent : ¬ HasIncidence support := by
  unfold HasIncidence Incident support
  decide

def closedSupport (i : Fin 42) : Bool := support i || decide (i.val = 15)

lemma closedSupport_independent : ¬ HasIncidence closedSupport := by
  unfold HasIncidence Incident closedSupport support
  decide

lemma complement_dominated_by_support : ∀ i : Fin 42, closedSupport i = false →
    ∃ u : Fin 42, support u = true ∧ (Incident i u ∨ Incident u i) := by
  unfold Incident closedSupport support
  decide

lemma complement_count :
    (Finset.univ.filter (fun i : Fin 42 => closedSupport i = false)).card = 31 := by
  unfold closedSupport support
  decide

lemma cofactor_is_or31 (x : Fin 42 → Bool)
    (hfixed : ∀ i : Fin 42, support i = true → x i = true) :
    HasIncidence x ↔ ∃ i : Fin 42, closedSupport i = false ∧ x i = true := by
  constructor
  · rintro ⟨u, v, huv, hxu, hxv⟩
    cases hsu : closedSupport u with
    | false => exact ⟨u, hsu, hxu⟩
    | true =>
      have hsv : closedSupport v = false := by
        apply Bool.eq_false_iff.mpr
        intro hsv
        exact closedSupport_independent ⟨u, v, huv, hsu, hsv⟩
      exact ⟨v, hsv, hxv⟩
  · rintro ⟨i, hi, hxi⟩
    obtain ⟨u, hu, hEdge⟩ := complement_dominated_by_support i hi
    rcases hEdge with hEdge | hEdge
    · exact ⟨i, u, hEdge, hxi, hfixed u hu⟩
    · exact ⟨u, i, hEdge, hfixed u hu, hxi⟩

lemma cofactor_extension (x : Fin 42 → Bool) :
    HasIncidence (fun i => support i || x i) ↔
      ∃ i : Fin 42, closedSupport i = false ∧ x i = true := by
  rw [cofactor_is_or31 _ (by intro i hi; simp [hi])]
  constructor
  · rintro ⟨i, hi, hx⟩
    have hs : support i = false := (Bool.or_eq_false_iff.mp hi).1
    exact ⟨i, hi, by simpa [hs] using hx⟩
  · rintro ⟨i, hi, hx⟩
    exact ⟨i, hi, by simp [hx]⟩

def gatedOff : Circuit :=
  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.and, [42, 3]⟩], 43⟩

lemma gatedOff_mono : Monotone2 gatedOff := by
  intro g hg
  simp only [gatedOff, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl <;> simp

lemma gatedOff_first_fires :
    (gatedOff.wires (List.ofFn support)).getD 42 false = true := by decide

lemma gatedOff_output_false : gatedOff.eval (List.ofFn support) = false := by decide

lemma internal_fire_need_not_reach_output :
    ∃ C : Circuit, Monotone2 C ∧ C.size = 2 ∧
      C.gates[0]? = some ⟨GateOp.and, [0, 1]⟩ ∧
      (C.wires (List.ofFn support)).getD 42 false = true ∧
      C.eval (List.ofFn support) = false :=
  ⟨gatedOff, gatedOff_mono, rfl, rfl, gatedOff_first_fires, gatedOff_output_false⟩

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_start (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    change wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) = _
    rw [ht]; simp

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_start gs w
  rw [ht]; simp [hl]

lemma getD_wiresFrom (gs : List Gate) (w : List Bool) (i : Nat) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_start gs w
  rw [ht, List.getD_append _ _ _ _ h]

lemma getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : Nat) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma gate_mono_true (g : Gate) (hop : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (w w' : List Bool)
    (h : ∀ i, w.getD i false = true → w'.getD i false = true) :
    g.op.eval (g.inputs.map fun i => w.getD i false) = true →
      g.op.eval (g.inputs.map fun i => w'.getD i false) = true := by
  intro ht
  rcases hop with hop | hop
  · change g.op = GateOp.and at hop
    rw [hop] at ht ⊢
    simp only [GateOp.eval, List.all_map, Function.comp_def, id_eq, List.all_eq_true] at ht ⊢
    intro i hi
    exact h i (ht i hi)
  · change g.op = GateOp.or at hop
    rw [hop] at ht ⊢
    simp only [GateOp.eval, List.any_map, Function.comp_def, id_eq, List.any_eq_true] at ht ⊢
    obtain ⟨i, hi, ht⟩ := ht
    exact ⟨i, hi, h i ht⟩

lemma wires_mono_true (gs : List Gate)
    (hok : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) :
    ∀ w w' : List Bool, w.length = w'.length →
    (∀ i, w.getD i false = true → w'.getD i false = true) →
    ∀ i, (wiresFrom gs w).getD i false = true → (wiresFrom gs w').getD i false = true := by
  induction gs with
  | nil => intro w w' _ hw; exact hw
  | cons g gs ih =>
    intro w w' hlen hw
    apply ih (fun k hk => hok k (List.mem_cons_of_mem _ hk))
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)]) (by simp [hlen])
    intro i hi
    by_cases heq : i = w.length
    · subst i
      have hs : g.op.eval (g.inputs.map fun i => w.getD i false) = true := by simpa using hi
      have ht := gate_mono_true g (hok g List.mem_cons_self) w w' hw hs
      rw [hlen]
      simpa using ht
    · rw [getD_snoc_ne _ _ _ _ heq] at hi
      rw [getD_snoc_ne _ _ _ _ (by omega)]
      exact hw i hi

def val (n : Nat) (C : Circuit) (x : Fin n → Bool) (i : Nat) : Bool :=
  (C.wires (List.ofFn x)).getD i false

lemma val_mono_true {n : Nat} (C : Circuit) (hmono : Monotone2 C)
    (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true)
    (a : Nat) (ha : val n C x a = true) : val n C y a = true := by
  apply wires_mono_true C.gates (fun g hg => (hmono g hg).1)
    (List.ofFn x) (List.ofFn y) (by simp) ?_ a ha
  intro i hi
  by_cases hin : i < n
  · have hx : x ⟨i, hin⟩ = true := by simpa [hin] using hi
    simpa [hin] using hxy ⟨i, hin⟩ hx
  · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
    contradiction

lemma firing_wire_constant_on_cofactor (C : Circuit) (hmono : Monotone2 C)
    (a : Nat) (ha : val 42 C support a = true) :
    ∀ x : Fin 42 → Bool, val 42 C (fun i => support i || x i) a = true := by
  intro x
  exact val_mono_true C hmono support (fun i => support i || x i)
    (by intro i hi; simp [hi]) a ha

lemma val_before {n : Nat} {C : Circuit} (pre : List Gate) (g : Gate) (post : List Gate)
    (hC : C.gates = pre ++ g :: post) (x : Fin n → Bool) (i : Nat)
    (hi : i < n + pre.length) :
    val n C x i = (wiresFrom pre (List.ofFn x)).getD i false := by
  change (wiresFrom C.gates (List.ofFn x)).getD i false = _
  rw [hC, wiresFrom_append]
  exact getD_wiresFrom _ _ _ (by simpa [length_wiresFrom])

lemma val_gate {n : Nat} {C : Circuit} (pre : List Gate) (g : Gate) (post : List Gate)
    (hC : C.gates = pre ++ g :: post) (x : Fin n → Bool) :
    val n C x (n + pre.length) =
      g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn x)).getD i false) := by
  let w := wiresFrom pre (List.ofFn x)
  have hw : w.length = n + pre.length := by simp [w, length_wiresFrom]
  change (wiresFrom C.gates (List.ofFn x)).getD (n + pre.length) false = _
  rw [hC, wiresFrom_append]
  change (wiresFrom post (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).getD
      (n + pre.length) false = _
  rw [getD_wiresFrom _ _ _ (by simp [hw])]
  rw [← hw]
  simp [w]

def OrStep (n : Nat) (C : Circuit) (a b : Nat) : Prop :=
  ∃ (pre : List Gate) (g : Gate) (post : List Gate),
    C.gates = pre ++ g :: post ∧ g.op = GateOp.or ∧ a ∈ g.inputs ∧
      a < n + pre.length ∧ b = n + pre.length

lemma orStep_true {n : Nat} {C : Circuit} {a b : Nat} (x : Fin n → Bool)
    (h : OrStep n C a b) (ha : val n C x a = true) : val n C x b = true := by
  obtain ⟨pre, g, post, hC, hop, hmem, hbefore, rfl⟩ := h
  have hread : (wiresFrom pre (List.ofFn x)).getD a false = true := by
    rw [← val_before pre g post hC x a hbefore]
    exact ha
  rw [val_gate pre g post hC x, hop]
  simp only [GateOp.eval, List.any_map, Function.comp_def, id_eq]
  exact List.any_eq_true.mpr ⟨a, hmem, hread⟩

lemma orPath_true {n : Nat} {C : Circuit} {a b : Nat} (x : Fin n → Bool)
    (h : Relation.ReflTransGen (OrStep n C) a b) (ha : val n C x a = true) :
    val n C x b = true := by
  induction h with
  | refl => exact ha
  | tail hpath hstep ih => exact orStep_true x hstep ih

lemma true_wire_before_any_firing_and {n : Nat} (C : Circuit) (hmono : Monotone2 C)
    (x : Fin n → Bool) : ∀ a : Nat, val n C x a = true →
    (∀ (pre : List Gate) (g : Gate) (post : List Gate),
      C.gates = pre ++ g :: post → n + pre.length ≤ a → g.op = GateOp.and →
        val n C x (n + pre.length) = false) →
    ∃ v : Fin n, x v = true ∧ Relation.ReflTransGen (OrStep n C) v.val a := by
  intro a
  induction a using Nat.strong_induction_on with
  | ind a ih =>
    intro ha hno
    by_cases han : a < n
    · refine ⟨⟨a, han⟩, ?_, Relation.ReflTransGen.refl⟩
      change (wiresFrom C.gates (List.ofFn x)).getD a false = true at ha
      rw [getD_wiresFrom _ _ _ (by simpa)] at ha
      simpa [han] using ha
    · have halive : a < n + C.gates.length := by
        by_contra hbound
        have hd : val n C x a = false := by
          apply List.getD_eq_default
          change (wiresFrom C.gates (List.ofFn x)).length ≤ a
          simp only [length_wiresFrom, List.length_ofFn]
          omega
        rw [hd] at ha
        contradiction
      let j := a - n
      have hj : j < C.gates.length := by dsimp [j]; omega
      let g := C.gates[j]
      let pre := C.gates.take j
      let post := C.gates.drop (j + 1)
      have hC : C.gates = pre ++ g :: post := by
        have hs : C.gates = (C.gates.take j ++ [g]) ++ C.gates.drop (j + 1) := by
          conv_lhs => rw [← List.take_append_drop (j + 1) C.gates]
          rw [List.take_succ_eq_append_getElem hj]
        simpa [pre, post] using hs
      have hpre : pre.length = j := by simp [pre, Nat.min_eq_left hj.le]
      have hwire : n + pre.length = a := by rw [hpre]; dsimp [j]; omega
      have hmem : g ∈ C.gates := by rw [hC]; simp
      rcases (hmono g hmem).1 with hop | hop
      · change g.op = GateOp.and at hop
        have hf := hno pre g post hC (by omega) hop
        rw [hwire] at hf
        rw [hf] at ha
        contradiction
      · change g.op = GateOp.or at hop
        rw [← hwire, val_gate pre g post hC x, hop] at ha
        simp only [GateOp.eval, List.any_map, Function.comp_def, id_eq, List.any_eq_true] at ha
        obtain ⟨u, hu, huval⟩ := ha
        have hua : u < a := by
          by_contra hbound
          rw [List.getD_eq_default _ _ (by simp [length_wiresFrom]; omega)] at huval
          contradiction
        have hufull : val n C x u = true := by
          rw [val_before pre g post hC x u (by omega)]
          exact huval
        obtain ⟨v, hv, hpath⟩ := ih u hua hufull (by
          intro p k q hC' hle hop'
          exact hno p k q hC' (by omega) hop')
        exact ⟨v, hv, hpath.tail ⟨pre, g, post, hC, hop, hu, by omega, hwire.symm⟩⟩

lemma no_or_path_from_firing_wire (C : Circuit)
    (hcorrect : ∀ x : Fin 42 → Bool, C.eval (List.ofFn x) = true ↔ HasIncidence x)
    (a : Nat) (ha : val 42 C support a = true) :
    ¬ Relation.ReflTransGen (OrStep 42 C) a C.output := by
  intro hpath
  have ht := orPath_true support hpath ha
  exact support_independent ((hcorrect support).mp ht)

def CausalStep (n : Nat) (C : Circuit) (a b : Nat) : Prop :=
  ∃ (pre : List Gate) (g : Gate) (post : List Gate),
    C.gates = pre ++ g :: post ∧ a ∈ g.inputs ∧
      a < n + pre.length ∧ b = n + pre.length

lemma path_true_false_edge {r : Nat → Nat → Prop} {a b : Nat}
    (f : Nat → Bool) (hpath : Relation.ReflTransGen r a b) :
    f a = true → f b = false → ∃ u v, r u v ∧ f u = true ∧ f v = false := by
  induction hpath with
  | refl => intro ha hb; simp_all
  | @tail b c hpath hstep ih =>
    intro ha hc
    cases hb : f b with
    | false => exact ih ha hb
    | true => exact ⟨b, c, hstep, hb, hc⟩

def BlockingAnd (n : Nat) (C : Circuit) (x : Fin n → Bool) : Prop :=
  ∃ (pre : List Gate) (g : Gate) (post : List Gate) (u k : Nat),
    C.gates = pre ++ g :: post ∧ g.op = GateOp.and ∧ g.inputs.length = 2 ∧
    u ∈ g.inputs ∧ k ∈ g.inputs ∧ u ≠ k ∧ u < n + pre.length ∧
    val n C x u = true ∧ val n C x (n + pre.length) = false ∧
    (wiresFrom pre (List.ofFn x)).getD k false = false

lemma path_has_blocking_and {n : Nat} (C : Circuit) (hmono : Monotone2 C)
    (x : Fin n → Bool) (a b : Nat)
    (hpath : Relation.ReflTransGen (CausalStep n C) a b)
    (ha : val n C x a = true) (hb : val n C x b = false) : BlockingAnd n C x := by
  obtain ⟨u, v, hstep, hu, hv⟩ := path_true_false_edge (val n C x) hpath ha hb
  obtain ⟨pre, g, post, hC, hmem, hbefore, rfl⟩ := hstep
  have hg : g ∈ C.gates := by rw [hC]; simp
  obtain ⟨hop, hlen⟩ := hmono g hg
  rcases hop with hop | hop
  · change g.op = GateOp.and at hop
    have hgate := hv
    rw [val_gate pre g post hC x, hop] at hgate
    simp only [GateOp.eval, List.all_map, Function.comp_def, id_eq] at hgate
    obtain ⟨k, hk, hkfalse⟩ := List.all_eq_false.mp hgate
    have hkval : (wiresFrom pre (List.ofFn x)).getD k false = false :=
      Bool.eq_false_iff.mpr hkfalse
    have huval : (wiresFrom pre (List.ofFn x)).getD u false = true := by
      rw [← val_before pre g post hC x u hbefore]
      exact hu
    have hne : u ≠ k := by
      intro heq
      rw [heq, hkval] at huval
      contradiction
    have hcard : 2 ≤ g.inputs.toFinset.card := by
      have hsub : ({u, k} : Finset Nat) ⊆ g.inputs.toFinset := by
        intro i hi
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi
        rcases hi with rfl | rfl
        · exact List.mem_toFinset.mpr hmem
        · exact List.mem_toFinset.mpr hk
      have hc := Finset.card_le_card hsub
      simpa [hne] using hc
    have hlen' := List.toFinset_card_le g.inputs
    have hlen2 : g.inputs.length = 2 := by omega
    exact ⟨pre, g, post, u, k, hC, hop, hlen2, hmem, hk, hne, hbefore, hu, hv, hkval⟩
  · change g.op = GateOp.or at hop
    have htrue := orStep_true x ⟨pre, g, post, hC, hop, hmem, hbefore, rfl⟩ hu
    rw [hv] at htrue
    contradiction

lemma correct_support_has_blocker (C : Circuit) (hmono : Monotone2 C)
    (hcorrect : ∀ x : Fin 42 → Bool, C.eval (List.ofFn x) = true ↔ HasIncidence x)
    (a : Nat) (ha : val 42 C support a = true)
    (hpath : Relation.ReflTransGen (CausalStep 42 C) a C.output) :
    BlockingAnd 42 C support := by
  apply path_has_blocking_and C hmono support a C.output hpath ha
  apply Bool.eq_false_iff.mpr
  intro ht
  exact support_independent ((hcorrect support).mp ht)

end Pnp1894Scratch
