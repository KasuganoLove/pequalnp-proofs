import PEqualNP.Defs

/-! Reusable partial work for L-meta-2391. The constant-propagation core below
is adapted from the merged L_meta_1680 and L_meta_1425 files, with a private task
namespace. No import of another Outside proof is used. -/

namespace Pnp2391Pruning
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_start (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_start gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_start gs w
  rw [ht, List.getD_append _ _ _ _ h]

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

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

abbrev Stat : Type := Bool ⊕ ℕ

def Stat.val (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

theorem elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)

theorem elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega

theorem elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
    (∃ g ∈ gs, k ∈ g.inputs) → (elim n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _ h; obtain ⟨g, hg, _⟩ := h; simp at hg
  | cons g gs ih =>
    intro acc hok hk hc hex
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
        rw [hnone]; simp
      have := elim_len n gs (elimStep n acc g)
      omega
    · have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        obtain ⟨g', hg', hk'⟩ := hex
        rcases List.mem_cons.1 hg' with rfl | h
        · exact absurd hk' hkg
        · exact ⟨g', h, hk'⟩
      have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          refine ⟨c, ?_⟩
          simp only [elimStep]
          rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
        hex'
      have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      omega

theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Sum.inl false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Sum.inl false)).val (wiresFrom acc.2 y) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_start r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Sum.inl false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Sum.inl false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

theorem elim_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List Stat × List Gate) :
    elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl

theorem elim_append (n : ℕ) (pre post : List Gate) (acc : List Stat × List Gate) :
    elim n (pre ++ post) acc = elim n post (elim n pre acc) := by
  simp [elim, List.foldl_append]

def idStats (n : ℕ) : List Stat := List.ofFn (fun i : Fin n => Sum.inr i)

theorem inv_id (n : ℕ) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y) (idStats n, []) := by
  refine ⟨by simp [idStats], ?_⟩
  intro i
  by_cases hlt : i < n
  · simp [idStats, hlt, Stat.Valid, Stat.val, wiresFrom]
  · rw [List.getD_eq_default _ _ (by simp [idStats]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

theorem getD_ofFn {α : Type} (m : ℕ) (F : Fin m → α) (d : α) (j : Fin m) :
    (List.ofFn F).getD j d = F j := by
  simp
theorem split_at {α : Type} : ∀ (l : List α) (p : ℕ) (g : α), l[p]? = some g →
    ∃ pre post, l = pre ++ g :: post ∧ pre.length = p := by
  intro l
  induction l with
  | nil => intro p g h; simp at h
  | cons x l ih =>
    intro p g h
    cases p with
    | zero =>
      simp at h
      subst h
      exact ⟨[], l, rfl, rfl⟩
    | succ p =>
      simp at h
      obtain ⟨pre, post, rfl, rfl⟩ := ih p g h
      exact ⟨x :: pre, post, rfl, rfl⟩

theorem simplify_small (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (m : ℕ)
    (ins : List Stat) (hl : ins.length ≤ 1) : (simplify op m ins).1 = none := by
  rcases hop with rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩
    · simp [simplify, simpAnd]
    · cases a <;> simp [simplify, simpAnd]
    · simp at hl
  · rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩
    · simp [simplify, simpOr]
    · cases a <;> simp [simplify, simpOr]
    · simp at hl

theorem wire_at (n : ℕ) (pre post : List Gate) (g : Gate) (X : List Bool) (hX : X.length = n) :
    (wiresFrom (pre ++ g :: post) X).getD (n + pre.length) false
      = g.op.eval (g.inputs.map fun i => (wiresFrom pre X).getD i false) := by
  have h1 : wiresFrom (pre ++ g :: post) X = wiresFrom post
      (wiresFrom pre X ++ [g.op.eval (g.inputs.map fun i => (wiresFrom pre X).getD i false)]) := by
    rw [wiresFrom_append]; rfl
  have hl : (wiresFrom pre X).length = n + pre.length := by
    rw [length_wiresFrom]; omega
  rw [h1, getD_wiresFrom _ _ _ (by simp [hl]), getD_snoc_len _ _ _ _ hl]

-- Replacing a gate by a gate of at most one input with the same value saves a gate.

def CleanGate (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ g.inputs = [j, k])

def CleanL (m : ℕ) (gs : List Gate) : Prop :=
  ∀ (p : ℕ) (g : Gate), gs[p]? = some g → CleanGate (m + p) g

theorem CleanGate.nok {m : ℕ} {g : Gate} (h : CleanGate m g) : NOk g := by
  rcases h with ⟨h1, j, _, h2⟩ | ⟨h1 | h1, j, k, _, _, h2⟩
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inr (Or.inr rfl)
    · rw [h2]; simp
    · intro _; rw [h2]; simp
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inl rfl
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inr (Or.inl rfl)
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h

theorem CleanGate.lt {m : ℕ} {g : Gate} (h : CleanGate m g) : ∀ a ∈ g.inputs, a < m := by
  intro a ha
  rcases h with ⟨_, j, hj, h2⟩ | ⟨_, j, k, hj, hk, h2⟩
  · rw [h2] at ha
    simp at ha
    subst ha; exact hj
  · rw [h2] at ha
    simp at ha
    rcases ha with rfl | rfl
    · exact hj
    · exact hk

theorem clean_nok (m : ℕ) (gs : List Gate) (h : CleanL m gs) : ∀ g ∈ gs, NOk g := by
  intro g hg
  obtain ⟨p, hp⟩ := List.mem_iff_getElem?.1 hg
  exact (h p g hp).nok

theorem simplify_clean (op : GateOp) (m : ℕ) (ins : List Stat) (hv : ∀ s ∈ ins, s.Valid m) :
    ∀ g ∈ (simplify op m ins).1, CleanGate m g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg
    refine Or.inr ⟨Or.inl rfl, _, _, ?_, ?_, rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg
    refine Or.inr ⟨Or.inr rfl, _, _, ?_, ?_, rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg
    refine Or.inl ⟨rfl, _, ?_, rfl⟩
    exact hv _ List.mem_cons_self
  · simp at hg
  · simp at hg

theorem toList_getElem? {α : Type} (o : Option α) (k : ℕ) (a : α)
    (h : o.toList[k]? = some a) : k = 0 ∧ a ∈ o := by
  cases o with
  | none => simp at h
  | some b =>
    cases k with
    | zero => simp at h; simp [h]
    | succ k => simp at h

theorem clean_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      CleanL n acc.2 → CleanL n (elim n gs acc).2 := by
  induction gs with
  | nil => intro w acc _ _ h; exact h
  | cons g gs ih =>
    intro w acc hok hinv hcl
    have hinv' : Inv n y (wiresFrom [g] w) (elimStep n acc g) :=
      inv_elim n y hy [g] w acc (fun g' hg' => hok g' (by simp at hg'; simp [hg'])) hinv
    refine ih _ (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) hinv' ?_
    intro p g' hp
    have hp' : (acc.2 ++ (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)[p]? = some g' := hp
    by_cases hlt : p < acc.2.length
    · rw [List.getElem?_append_left hlt] at hp'
      exact hcl p g' hp'
    · rw [List.getElem?_append_right (by omega)] at hp'
      obtain ⟨h0, hmem⟩ := toList_getElem? _ _ _ hp'
      have hpl : p = acc.2.length := by omega
      rw [hpl]
      exact simplify_clean _ _ _ (fun s hs => by
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        exact (hinv.2 a).1) g' hmem


theorem simplify_op (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, g.op = op := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; rfl)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; rfl)
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; rfl)
  · simp at hg
  · simp at hg

def AO (gs : List Gate) : Prop :=
  ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or

theorem elim_ao (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    AO gs → AO acc.2 → AO (elim n gs acc).2 := by
  induction gs with
  | nil => intro acc _ h; exact h
  | cons g gs ih =>
    intro acc hgs h
    apply ih (elimStep n acc g) (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · rw [simplify_op _ _ _ g' (by simpa using h1)]
      exact hgs g List.mem_cons_self

theorem ao_clean_isAO2 (n : ℕ) (gs : List Gate) (o : ℕ)
    (hao : AO gs) (hc : CleanL n gs) : PEqualNP.TopForm.IsAO2 n ⟨gs, o⟩ := by
  refine ⟨hao, ?_, ?_⟩
  · intro j hj w hw
    have hg : PEqualNP.MetaComplexity.NestedCover.gateAt ⟨gs, o⟩ j = gs[j] := by
      simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hj]
    rw [hg] at hw
    exact (hc j gs[j] (List.getElem?_eq_getElem hj)).lt w hw
  · intro g hg
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hg
    rcases hc j g hj with h | h
    · obtain ⟨hop, _⟩ := h
      rcases hao g hg with ha | ho <;> simp_all
    · obtain ⟨_, a, b, _, _, hi⟩ := h
      simp [hi]

/-- Constant propagation removes an explicitly zero gate, without emitting
constants or unary gates, whenever the computed function is nonconstant. -/
theorem prune_explicit_zero (n : ℕ) (pre post : List Gate) (o : ℕ)
    (hao : AO (pre ++ (⟨GateOp.or, []⟩ : Gate) :: post))
    (hok : ∀ g ∈ pre ++ (⟨GateOp.or, []⟩ : Gate) :: post, Ok g)
    (f : (Fin n → Bool) → Bool)
    (hev : ∀ x, (wiresFrom (pre ++ (⟨GateOp.or, []⟩ : Gate) :: post)
      (List.ofFn x)).getD o false = f x)
    (hnc : ∃ x y, f x ≠ f y) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧
      circuitFun n D = f ∧ D.size ≤ pre.length + post.length := by
  let gs := pre ++ (⟨GateOp.or, []⟩ : Gate) :: post
  let acc := elim n gs (idStats n, [])
  have hinv : ∀ x : Fin n → Bool,
      Inv n (List.ofFn x) (wiresFrom gs (List.ofFn x)) acc :=
    fun x => inv_elim n _ (by simp) gs _ _ hok (inv_id n x)
  have hval : ∀ x : Fin n → Bool,
      (acc.1.getD o (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn x)) = f x := by
    intro x
    exact ((hinv x).2 o).2.trans (hev x)
  have hlen : acc.2.length ≤ pre.length + post.length := by
    have e : acc = elim n post
        (elimStep n (elim n pre (idStats n, [])) ⟨GateOp.or, []⟩) := by
      simp only [acc, gs, elim_append, elim_cons]
    have h1 := elim_len n pre (idStats n, [])
    have h2 : (elimStep n (elim n pre (idStats n, [])) ⟨GateOp.or, []⟩).2.length
        = (elim n pre (idStats n, [])).2.length := by
      simp [elimStep, simplify, simpOr]
    have h3 := elim_len n post
      (elimStep n (elim n pre (idStats n, [])) ⟨GateOp.or, []⟩)
    rw [← e] at h3
    simp only [List.length_nil, zero_add] at h1
    omega
  cases hs : acc.1.getD o (Sum.inl false) with
  | inl b =>
    exfalso
    obtain ⟨x, y, hxy⟩ := hnc
    apply hxy
    rw [← hval x, ← hval y, hs]
    rfl
  | inr w =>
    refine ⟨⟨acc.2, w⟩, ?_, ?_, hlen⟩
    · apply ao_clean_isAO2
      · exact elim_ao n gs _ hao (by intro g hg; simp at hg)
      · exact clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) gs _ _ hok
          (inv_id n _) (by intro p g hp; simp at hp)
    · funext x
      have hx := hval x
      rw [hs] at hx
      exact hx

def WLE (w v : List Bool) : Prop :=
  w.length = v.length ∧ ∀ i, w.getD i false = true → v.getD i false = true

theorem wle_snoc {w v : List Bool} (h : WLE w v) {a b : Bool}
    (hab : a = true → b = true) : WLE (w ++ [a]) (v ++ [b]) := by
  refine ⟨by simp [h.1], ?_⟩
  intro i
  by_cases hi : i = w.length
  · subst i
    rw [getD_snoc_eq, h.1, getD_snoc_eq]
    exact hab
  · rw [getD_snoc_ne _ _ _ _ hi,
      getD_snoc_ne _ _ _ _ (by intro hv; exact hi (hv.trans h.1.symm))]
    exact h.2 i

theorem gate_mono (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    {w v : List Bool} (h : WLE w v) :
    g.op.eval (g.inputs.map fun i => w.getD i false) = true →
    g.op.eval (g.inputs.map fun i => v.getD i false) = true := by
  rcases hg with ha | ho
  · rw [ha]
    simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro hw i hi
    exact h.2 i (hw i hi)
  · rw [ho]
    simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, hw⟩
    exact ⟨i, hi, h.2 i hw⟩

theorem wires_mono (gs : List Gate) (hao : AO gs) {w v : List Bool}
    (h : WLE w v) : WLE (wiresFrom gs w) (wiresFrom gs v) := by
  induction gs generalizing w v with
  | nil => exact h
  | cons g gs ih =>
    exact ih (fun g' hg' => hao g' (List.mem_cons_of_mem _ hg'))
      (wle_snoc h (gate_mono g (hao g List.mem_cons_self) h))

open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

def Increasing {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true

theorem graph_true_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
  simp [graphFun]

theorem pair_below {n : ℕ} (u v : Fin n) (x : Fin n → Bool)
    (hu : x u = true) (hv : x v = true) :
    ∀ i, pairInput u v i = true → x i = true := by
  intro i hi
  simp only [pairInput, decide_eq_true_eq] at hi
  rcases hi with rfl | rfl
  · exact hu
  · exact hv

/-- A monotone function below a graph function is equal to it as soon as it
accepts every edge-pair. This is the semantic justification for pruning a
gate that is false at every edge-pair input. -/
theorem graph_sandwich {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (f : (Fin n → Bool) → Bool) (hmono : Increasing f)
    (hbelow : ∀ x, f x = true → graphFun G ∅ x = true)
    (hedges : ∀ u v, G.Adj u v → f (pairInput u v) = true) :
    f = graphFun G ∅ := by
  funext x
  apply Bool.eq_iff_iff.mpr
  constructor
  · exact hbelow x
  · intro hx
    obtain ⟨u, v, huv, hu, hv⟩ := (graph_true_iff G x).mp hx
    exact hmono _ x (pair_below u v x hu hv) (hedges u v huv)


theorem zero_lower_wires (pre post : List Gate) (g : Gate) (x : List Bool)
    (hao : AO post) :
    WLE (wiresFrom (pre ++ (⟨GateOp.or, []⟩ : Gate) :: post) x)
      (wiresFrom (pre ++ g :: post) x) := by
  rw [wiresFrom_append, wiresFrom_append]
  change WLE (wiresFrom post (wiresFrom pre x ++ [false]))
    (wiresFrom post (wiresFrom pre x ++ [_]))
  exact wires_mono post hao (wle_snoc ⟨rfl, fun _ h => h⟩ (by simp))

theorem zero_same_wires (pre post : List Gate) (g : Gate) (x : List Bool)
    (hzero : g.op.eval (g.inputs.map fun i => (wiresFrom pre x).getD i false) = false) :
    wiresFrom (pre ++ (⟨GateOp.or, []⟩ : Gate) :: post) x =
      wiresFrom (pre ++ g :: post) x := by
  rw [wiresFrom_append, wiresFrom_append]
  change wiresFrom post (wiresFrom pre x ++ [false]) =
    wiresFrom post (wiresFrom pre x ++ [_])
  rw [hzero]

theorem wle_inputs {n : ℕ} (x y : Fin n → Bool)
    (h : ∀ i, x i = true → y i = true) : WLE (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp, ?_⟩
  intro i hi
  by_cases hlt : i < n
  · have hx : (List.ofFn x).getD i false = x ⟨i, hlt⟩ :=
      getD_ofFn n x false ⟨i, hlt⟩
    have hy : (List.ofFn y).getD i false = y ⟨i, hlt⟩ :=
      getD_ofFn n y false ⟨i, hlt⟩
    rw [hx] at hi
    rw [hy]
    exact h ⟨i, hlt⟩ hi
  · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
    cases hi

theorem zero_preserves_graph {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (pre post : List Gate) (g : Gate) (o : ℕ)
    (hao : AO (pre ++ g :: post))
    (hfun : ∀ x, (wiresFrom (pre ++ g :: post) (List.ofFn x)).getD o false = graphFun G ∅ x)
    (hzero : ∀ u v, G.Adj u v →
      g.op.eval (g.inputs.map fun i =>
        (wiresFrom pre (List.ofFn (pairInput u v))).getD i false) = false) :
    (fun x => (wiresFrom (pre ++ (⟨GateOp.or, []⟩ : Gate) :: post)
      (List.ofFn x)).getD o false) = graphFun G ∅ := by
  have hap : AO post := fun a ha => hao a (List.mem_append_right _ (List.mem_cons_of_mem _ ha))
  have haz : AO (pre ++ (⟨GateOp.or, []⟩ : Gate) :: post) := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hao a (List.mem_append_left _ ha)
    · rcases List.mem_cons.mp ha with rfl | ha
      · exact Or.inr rfl
      · exact hap a ha
  apply graph_sandwich G
  · intro x y hxy hx
    exact (wires_mono _ haz (wle_inputs x y hxy)).2 o hx
  · intro x hx
    have hh := (zero_lower_wires pre post g (List.ofFn x) hap).2 o hx
    rwa [hfun x] at hh
  · intro u v huv
    rw [zero_same_wires pre post g _ (hzero u v huv), hfun]
    apply (graph_true_iff G _).mpr
    exact ⟨u, v, huv, by simp [pairInput], by simp [pairInput]⟩

/-- Every real gate of every least AO2 graph circuit accepts an edge-pair.
This does not imply that an AND gate is clean: it may also accept nonedges. -/
theorem least_gate_productive {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hne : G.edgeFinset.Nonempty) (C : Circuit)
    (hmin : PEqualNP.TopForm.IsLeastAO G C) (j : ℕ) (hj : j < C.gates.length) :
    ∃ u v, G.Adj u v ∧ gateVal n C j (pairInput u v) = true := by
  by_contra hnone
  have hdead : ∀ u v, G.Adj u v → gateVal n C j (pairInput u v) = false := by
    intro u v huv
    cases hv : gateVal n C j (pairInput u v) with
    | false => rfl
    | true => exact False.elim (hnone ⟨u, v, huv, hv⟩)
  obtain ⟨pre, post, hs, hp⟩ := split_at C.gates j C.gates[j] (List.getElem?_eq_getElem hj)
  have hao : AO (pre ++ C.gates[j] :: post) := by
    rw [← hs]
    exact hmin.1.1
  have hok : ∀ g ∈ pre ++ (⟨GateOp.or, []⟩ : Gate) :: post, Ok g := by
    intro g hg
    have old : g ∈ C.gates → Ok g := by
      intro hg
      refine ⟨?_, le_of_eq (hmin.1.2.2 g hg)⟩
      rcases hmin.1.1 g hg with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    rcases List.mem_append.mp hg with hg | hg
    · exact old (hs ▸ List.mem_append_left _ hg)
    · rcases List.mem_cons.mp hg with rfl | hg
      · exact ⟨Or.inr (Or.inl rfl), by simp⟩
      · exact old (hs ▸ List.mem_append_right _ (List.mem_cons_of_mem _ hg))
  have haz : AO (pre ++ (⟨GateOp.or, []⟩ : Gate) :: post) := by
    intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact hao g (List.mem_append_left _ hg)
    · rcases List.mem_cons.mp hg with rfl | hg
      · exact Or.inr rfl
      · exact hao g (List.mem_append_right _ (List.mem_cons_of_mem _ hg))
  have hfun : ∀ x, (wiresFrom (pre ++ C.gates[j] :: post) (List.ofFn x)).getD C.output false
      = graphFun G ∅ x := by
    intro x
    rw [← hs]
    exact congrFun hmin.2.1 x
  have hzero : ∀ u v, G.Adj u v →
      C.gates[j].op.eval (C.gates[j].inputs.map fun i =>
        (wiresFrom pre (List.ofFn (pairInput u v))).getD i false) = false := by
    intro u v huv
    have hw := wire_at n pre post C.gates[j] (List.ofFn (pairInput u v)) (by simp)
    rw [hp, ← hs] at hw
    exact hw.symm.trans (hdead u v huv)
  have heq := zero_preserves_graph G pre post C.gates[j] C.output hao hfun hzero
  have hnc : ∃ x y, graphFun G ∅ x ≠ graphFun G ∅ y := by
    obtain ⟨e, he⟩ := hne
    induction e using Sym2.ind with
    | _ u v =>
      have huv : G.Adj u v := by simpa using he
      refine ⟨pairInput u v, fun _ => false, ?_⟩
      have htrue : graphFun G ∅ (pairInput u v) = true :=
        (graph_true_iff G _).mpr ⟨u, v, huv, by simp [pairInput], by simp [pairInput]⟩
      have hfalse : graphFun G ∅ (fun _ => false) = false := by simp [graphFun]
      rw [htrue, hfalse]
      decide
  obtain ⟨D, hD, hfD, hsize⟩ := prune_explicit_zero n pre post C.output haz hok
    (graphFun G ∅) (fun x => congrFun heq x) hnc
  have hleast := hmin.2.2 D hD hfD
  have hlen : C.size = pre.length + post.length + 1 := by
    change C.gates.length = _
    rw [hs]
    simp only [List.length_append, List.length_cons]
    omega
  omega

theorem prune_small_gate (n : ℕ) (pre post : List Gate) (o : ℕ)
    (g0 : Gate)
    (hsmall : (g0.op = GateOp.and ∨ g0.op = GateOp.or) ∧ g0.inputs.length ≤ 1)
    (hao : AO (pre ++ g0 :: post))
    (hok : ∀ g ∈ pre ++ g0 :: post, Ok g)
    (f : (Fin n → Bool) → Bool)
    (hev : ∀ x, (wiresFrom (pre ++ g0 :: post)
      (List.ofFn x)).getD o false = f x)
    (hnc : ∃ x y, f x ≠ f y) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧
      circuitFun n D = f ∧ D.size ≤ pre.length + post.length := by
  let gs := pre ++ g0 :: post
  let acc := elim n gs (idStats n, [])
  have hinv : ∀ x : Fin n → Bool,
      Inv n (List.ofFn x) (wiresFrom gs (List.ofFn x)) acc :=
    fun x => inv_elim n _ (by simp) gs _ _ hok (inv_id n x)
  have hval : ∀ x : Fin n → Bool,
      (acc.1.getD o (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn x)) = f x := by
    intro x
    exact ((hinv x).2 o).2.trans (hev x)
  have hlen : acc.2.length ≤ pre.length + post.length := by
    have e : acc = elim n post
        (elimStep n (elim n pre (idStats n, [])) g0) := by
      simp only [acc, gs, elim_append, elim_cons]
    have h1 := elim_len n pre (idStats n, [])
    have h2 : (elimStep n (elim n pre (idStats n, [])) g0).2.length
        = (elim n pre (idStats n, [])).2.length := by
      simp only [elimStep]
      rw [simplify_small _ hsmall.1 _ _ (by simpa using hsmall.2)]
      simp
    have h3 := elim_len n post
      (elimStep n (elim n pre (idStats n, [])) g0)
    rw [← e] at h3
    simp only [List.length_nil, zero_add] at h1
    omega
  cases hs : acc.1.getD o (Sum.inl false) with
  | inl b =>
    exfalso
    obtain ⟨x, y, hxy⟩ := hnc
    apply hxy
    rw [← hval x, ← hval y, hs]
    rfl
  | inr w =>
    refine ⟨⟨acc.2, w⟩, ?_, ?_, hlen⟩
    · apply ao_clean_isAO2
      · exact elim_ao n gs _ hao (by intro g hg; simp at hg)
      · exact clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) gs _ _ hok
          (inv_id n _) (by intro p g hp; simp at hp)
    · funext x
      have hx := hval x
      rw [hs] at hx
      exact hx

theorem plane3_gate_productive (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (C : Circuit)
    (hplane : ∀ a b : Fin 26, G.Adj a b ↔ ∃ u t : Fin 13,
      (u = t ∨ u = t + 1 ∨ u = t + 3 ∨ u = t + 9) ∧
      ((a = Fin.castAdd 13 u ∧ b = Fin.natAdd 13 t) ∨
        (b = Fin.castAdd 13 u ∧ a = Fin.natAdd 13 t)))
    (hmin : PEqualNP.TopForm.IsLeastAO G C) (j : ℕ) (hj : j < C.gates.length) :
    ∃ u v : Fin 26, G.Adj u v ∧ gateVal 26 C j (pairInput u v) = true := by
  apply least_gate_productive G ?_ C hmin j hj
  have hadj : G.Adj (Fin.castAdd 13 (0 : Fin 13)) (Fin.natAdd 13 (0 : Fin 13)) :=
    (hplane _ _).mpr ⟨0, 0, Or.inl rfl, Or.inl ⟨rfl, rfl⟩⟩
  refine ⟨s(Fin.castAdd 13 (0 : Fin 13), Fin.natAdd 13 (0 : Fin 13)), ?_⟩
  simpa using hadj

/-- A gate of a least AO2 circuit cannot be replaced by a constant or an
earlier-wire alias which is pointwise smaller and agrees on all edge-pairs.
`g0` has at most one input; the constant-propagation pass physically deletes it.
This permits the singleton-intersection case of a pure-point product to be
handled by an input alias, provided the displayed semantic hypotheses hold. -/
theorem least_no_small_replacement {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hne : G.edgeFinset.Nonempty) (pre post : List Gate) (g g0 : Gate) (o : ℕ)
    (hmin : PEqualNP.TopForm.IsLeastAO G ⟨pre ++ g :: post, o⟩)
    (hsmall : (g0.op = GateOp.and ∨ g0.op = GateOp.or) ∧ g0.inputs.length ≤ 1)
    (hlow : ∀ x : Fin n → Bool,
      g0.op.eval (g0.inputs.map fun i => (wiresFrom pre (List.ofFn x)).getD i false) = true →
      g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn x)).getD i false) = true)
    (hedge : ∀ u v, G.Adj u v →
      g0.op.eval (g0.inputs.map fun i =>
        (wiresFrom pre (List.ofFn (pairInput u v))).getD i false) =
      g.op.eval (g.inputs.map fun i =>
        (wiresFrom pre (List.ofFn (pairInput u v))).getD i false)) : False := by
  have hao : AO (pre ++ g :: post) := hmin.1.1
  have hap : AO post := fun a ha => hao a (List.mem_append_right _ (List.mem_cons_of_mem _ ha))
  have ha0 : AO (pre ++ g0 :: post) := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hao a (List.mem_append_left _ ha)
    · rcases List.mem_cons.mp ha with rfl | ha
      · exact hsmall.1
      · exact hap a ha
  have hok : ∀ a ∈ pre ++ g0 :: post, Ok a := by
    intro a ha
    have old : a ∈ pre ++ g :: post → Ok a := by
      intro ha
      refine ⟨?_, le_of_eq (hmin.1.2.2 a ha)⟩
      rcases hao a ha with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    rcases List.mem_append.mp ha with ha | ha
    · exact old (List.mem_append_left _ ha)
    · rcases List.mem_cons.mp ha with rfl | ha
      · refine ⟨?_, hsmall.2.trans (by decide)⟩
        rcases hsmall.1 with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · exact old (List.mem_append_right _ (List.mem_cons_of_mem _ ha))
  have hf : ∀ x, (wiresFrom (pre ++ g :: post) (List.ofFn x)).getD o false = graphFun G ∅ x :=
    fun x => congrFun hmin.2.1 x
  have heq : (fun x => (wiresFrom (pre ++ g0 :: post) (List.ofFn x)).getD o false)
      = graphFun G ∅ := by
    apply graph_sandwich G
    · intro x y hxy hx
      exact (wires_mono _ ha0 (wle_inputs x y hxy)).2 o hx
    · intro x hx
      have hr : WLE (wiresFrom (pre ++ g0 :: post) (List.ofFn x))
          (wiresFrom (pre ++ g :: post) (List.ofFn x)) := by
        rw [wiresFrom_append, wiresFrom_append]
        exact wires_mono post hap (wle_snoc ⟨rfl, fun _ h => h⟩ (hlow x))
      have hh := hr.2 o hx
      rwa [hf x] at hh
    · intro u v huv
      have hw : wiresFrom (pre ++ g0 :: post) (List.ofFn (pairInput u v)) =
          wiresFrom (pre ++ g :: post) (List.ofFn (pairInput u v)) := by
        rw [wiresFrom_append, wiresFrom_append]
        change wiresFrom post (_ ++ [_]) = wiresFrom post (_ ++ [_])
        rw [hedge u v huv]
      rw [hw, hf]
      exact (graph_true_iff G _).mpr ⟨u, v, huv, by simp [pairInput], by simp [pairInput]⟩
  have hnc : ∃ x y, graphFun G ∅ x ≠ graphFun G ∅ y := by
    obtain ⟨e, he⟩ := hne
    induction e using Sym2.ind with
    | _ u v =>
      have huv : G.Adj u v := by simpa using he
      refine ⟨pairInput u v, fun _ => false, ?_⟩
      have ht : graphFun G ∅ (pairInput u v) = true :=
        (graph_true_iff G _).mpr ⟨u, v, huv, by simp [pairInput], by simp [pairInput]⟩
      have hz : graphFun G ∅ (fun _ => false) = false := by simp [graphFun]
      rw [ht, hz]
      decide
  obtain ⟨D, hD, hDf, hsize⟩ := prune_small_gate n pre post o g0 hsmall ha0 hok
    (graphFun G ∅) (fun x => congrFun heq x) hnc
  have hleast := hmin.2.2 D hD hDf
  change (pre ++ g :: post).length ≤ D.gates.length at hleast
  change D.gates.length ≤ pre.length + post.length at hsize
  simp only [List.length_append, List.length_cons] at hleast
  omega

end Pnp2391Pruning
