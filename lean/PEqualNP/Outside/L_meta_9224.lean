import PEqualNP.Defs

-- Constant propagation is adapted from the public L_meta_5148 proof and its
-- upstream predecessors L_meta_2513 and L_meta_1543. The four-by-four
-- lower-bound certificate is from the public L_meta_6023 proof.
namespace PEqualNP.Outside.L_meta_9224

namespace BasePin

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
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
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

theorem normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this; exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate] <;> omega

theorem wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have s1 : wiresFrom ((g :: gs).map normGate) w = wiresFrom (gs.map normGate)
        (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) := rfl
    have s2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s1, s2, normGate_eval, ih]

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
    obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
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

theorem elim_fst_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; rfl
  | cons g gs ih =>
    intro acc
    rw [elim_cons, ih]
    simp only [elimStep, List.length_append, List.length_cons, List.length_nil]
    omega

theorem elimStep_none (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (c : Bool) (hc : acc.1.getD k (Sum.inl false) = Sum.inl c) :
    (elimStep n acc g).2.length = acc.2.length := by
  have hnone : (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
    apply simplify_count
    · exact hg.1.1
    · simpa using hg.1.2
    · intro h; simpa using hg.2 h
    · exact ⟨c, List.mem_map.2 ⟨k, hk, hc⟩⟩
  show (acc.2 ++ (simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
  rw [hnone]; simp

theorem elim_split_getD (n : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (acc : List Stat × List Gate) (a : ℕ) (d : Stat) (h : a ≤ acc.1.length + pre.length) :
    (elim n (pre ++ g :: post) acc).1.getD a d = (elimStep n (elim n pre acc) g).1.getD a d := by
  rw [elim_append, elim_cons, elim_getD n a d post _ (by
    show a < ((elim n pre acc).1 ++ [_]).length
    rw [List.length_append, elim_fst_len, List.length_singleton]; omega)]

theorem elim_split_getD_lt (n : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (acc : List Stat × List Gate) (a : ℕ) (d : Stat) (h : a < acc.1.length + pre.length) :
    (elim n (pre ++ g :: post) acc).1.getD a d = (elim n pre acc).1.getD a d := by
  rw [elim_split_getD n pre g post acc a d (le_of_lt h)]
  show ((elim n pre acc).1 ++ [_]).getD a d = _
  exact getD_snoc_ne _ _ _ _ (by rw [elim_fst_len]; omega)

theorem elim_count (n : ℕ) (acc : List Stat × List Gate) : ∀ gs : List Gate,
    (∀ g ∈ gs, NOk g) → ∀ S : Finset ℕ,
    (∀ p ∈ S, ∃ g, gs[p]? = some g ∧ ∃ a ∈ g.inputs, a < acc.1.length + p ∧
        ∃ c, (elim n gs acc).1.getD a (Sum.inl false) = Sum.inl c) →
      (elim n gs acc).2.length + S.card ≤ acc.2.length + gs.length := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _ S hS
    have hE : S = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro p hp
      obtain ⟨g, hg, _⟩ := hS p hp
      simp at hg
    subst hE
    simp [elim]
  | append_singleton gs g ih =>
    intro hok S hS
    have hstep : elim n (gs ++ [g]) acc = elimStep n (elim n gs acc) g := by
      rw [elim_append]; rfl
    have hpre : ∀ (a : ℕ) (d : Stat), a < acc.1.length + gs.length →
        (elim n (gs ++ [g]) acc).1.getD a d = (elim n gs acc).1.getD a d :=
      fun a d h => elim_split_getD_lt n gs g [] acc a d h
    have hok' : ∀ g' ∈ gs, NOk g' := fun g' h => hok g' (List.mem_append_left _ h)
    have ih' := ih hok' (S.erase gs.length) (by
      intro p hp
      obtain ⟨hne, hpS⟩ := Finset.mem_erase.1 hp
      obtain ⟨g', hg', a, ha, hlt, c, hc⟩ := hS p hpS
      have hpl : p < gs.length := by
        obtain ⟨h1, _⟩ := List.getElem?_eq_some_iff.1 hg'
        rw [List.length_append, List.length_singleton] at h1
        omega
      rw [List.getElem?_append_left hpl] at hg'
      rw [hpre a _ (by omega)] at hc
      exact ⟨g', hg', a, ha, hlt, c, hc⟩)
    rw [hstep, List.length_append, List.length_singleton]
    by_cases hin : gs.length ∈ S
    · obtain ⟨g', hg', a, ha, hlt, c, hc⟩ := hS _ hin
      have hgg : g' = g := by
        rw [List.getElem?_concat_length] at hg'
        exact (Option.some.inj hg').symm
      subst hgg
      rw [hpre a _ hlt] at hc
      have h2 := elimStep_none n (elim n gs acc) g' (hok g' (by simp)) a ha c hc
      have hcard := Finset.card_erase_of_mem hin
      have hpos : 1 ≤ S.card := Finset.card_pos.2 ⟨_, hin⟩
      omega
    · have h2 : (elimStep n (elim n gs acc) g).2.length ≤ (elim n gs acc).2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + (elim n gs acc).2.length)
          (g.inputs.map fun i => (elim n gs acc).1.getD i (Sum.inl false))).1
        omega
      rw [Finset.erase_eq_of_notMem hin] at ih'
      omega

def inputImg (n v : ℕ) : List Stat :=
  (List.range n).map fun i => if i = v then Sum.inl false else Sum.inr i

theorem inputImg_length (n v : ℕ) : (inputImg n v).length = n := by
  simp [inputImg]

theorem inputImg_getD (n v k : ℕ) :
    (inputImg n v).getD k (Sum.inl false)
      = if k < n ∧ k ≠ v then Sum.inr k else Sum.inl false := by
  by_cases hk : k < n
  · by_cases hv : k = v
    · subst hv
      simp [inputImg, hk]
    · simp [inputImg, hk, hv]
  · rw [List.getD_eq_default _ _ (by rw [inputImg_length]; omega)]
    simp [hk]

theorem inputImg_inv (n : ℕ) (v : Fin n) (x : Fin n → Bool) (hx : x v = false) :
    Inv n (List.ofFn x) (List.ofFn x) (inputImg n v, []) := by
  refine ⟨by simp [inputImg_length], ?_⟩
  intro k
  show ((inputImg n v).getD k (Sum.inl false)).Valid (n + 0) ∧
    ((inputImg n v).getD k (Sum.inl false)).val (List.ofFn x) = (List.ofFn x).getD k false
  rw [inputImg_getD]
  by_cases hk : k < n
  · by_cases hv : k = (v : ℕ)
    · subst hv
      simp [Stat.Valid, Stat.val, hx]
    · simp [hk, hv, Stat.Valid, Stat.val]
  · simp [hk, Stat.Valid, Stat.val]

theorem normGate_mem (g : Gate) (v : ℕ) (hv : v ∈ g.inputs)
    (hnot : g.op = GateOp.not → g.inputs.head? = some v) : v ∈ (normGate g).inputs := by
  obtain ⟨op, inputs⟩ := g
  cases op
  case not =>
    have h := hnot rfl
    cases inputs with
    | nil => simp at h
    | cons a l =>
      simp only [List.head?_cons, Option.some.injEq] at h
      subst h
      simp [normGate]
  all_goals exact hv

end BasePin

namespace BaseFour

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

abbrev W := BitVec 128

def ops (x y : W) : List W := [x &&& y, x ||| y]

def sep (x : W) : BitVec 64 := ((x >>> 64) &&& ~~~x).setWidth 64

def cuts (ws : List W) : BitVec 64 := ws.foldr (fun w v => sep w ||| v) 0

def goal : W := (-1 : BitVec 64) ++ (0 : BitVec 64)

def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

def rawInputs : List W :=
  [0xffffff0101010101010101, 0xffff0000000606060606060606, 0xffff00000000001818181818181818, 0xff00000000000000e0e0e0e0e0e0e0e0, 0xff00ff00000000ff0202020202020202, 0xff0000ff0000002121212121212121, 0xff0000ff004848484848484848, 0xff00009494949494949494]

def inputs : List W :=
  [0xffffff0101010101010101, 0xffff0000000606060606060606, 0xffff00000000001818181818181818, 0xff00000000000000e0e0e0e0e0e0e0e0, 0xff00ff00000000ff0202020202020202, 0xff0000ff0000002121212121212121, 0xff0000ff004848484848484848, 0xff00009494949494949494]

theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 64) (w : W) : Prop :=
  w.getLsbD (64 + i.val) = true ∧ w.getLsbD i.val = false

theorem ops_differs (i : Fin 64) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  unfold differs at hd ⊢
  rcases hz with rfl | rfl <;> revert hd <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or] <;>
    cases a.getLsbD (64 + i.val) <;> cases a.getLsbD i.val <;>
    cases b.getLsbD (64 + i.val) <;> cases b.getLsbD i.val <;> simp

theorem goal_differs : ∀ i : Fin 64, differs i goal := by
  unfold differs
  decide

theorem cuts_spec (ws : List W) (i : Fin 64) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have hi : i.val < 128 := by omega
    simp [sep, i.isLt, differs, hi, Nat.add_comm]

theorem cuts_full {k : ℕ} {ws : List W} (h : live basicOps goal k ws.toFinset) :
    cuts ws = -1 := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (goal_differs ⟨j, hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 64)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp [basicOps, ops, BitVec.and_comm, BitVec.or_comm]

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def possible (w : List W) (z : W) : Bool :=
  z == 0 || z == BitVec.allOnes 128 || w.any (fun u => z == u ||
    w.any (fun v => z == (u &&& v) || z == (u ||| v)))

private def bit (k : Fin 128) (z : W) : Bool := z[k.val]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 128) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

private theorem read_wire (w : List W) (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ w := by
  by_cases h : i < w.length
  · exact Or.inr (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt h)]

private theorem atom {ws : List W} {x : W} (hx : x = 0 ∨ x ∈ ws) : possible ws x := by
  rcases hx with rfl | hx
  · simp [possible]
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    exact .inr ⟨x, hx, .inl rfl⟩

private theorem pair {ws : List W} {x y : W} (hx : x = 0 ∨ x ∈ ws) (hy : y = 0 ∨ y ∈ ws) :
    possible ws (x &&& y) ∧ possible ws (x ||| y) := by
  rcases hx with rfl | hx
  · simpa [possible] using atom hy
  rcases hy with rfl | hy
  · simpa [possible] using atom (.inr hx)
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    constructor
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inl rfl⟩⟩
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inr rfl⟩⟩

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def legal (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

set_option maxRecDepth 2000 in
private theorem gate_table (w ws : List W) (hw : w ⊆ ws) (g : Gate) (hg : legal g) :
    ∃ z, possible ws z ∧ ∀ k, step (w.map (bit k)) g = (w ++ [z]).map (bit k) := by
  have mem (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ ws :=
    (read_wire w i).imp_right (fun h => hw h)
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  change op = .and ∨ op = .or at hop
  change args.length ≤ 2 at hlen
  cases args with
  | nil =>
    rcases hop with rfl | rfl
    · exact ⟨BitVec.allOnes 128, by simp [possible], by simp [step, GateOp.eval, bit]; decide⟩
    · exact ⟨0, by simp [possible], by simp [step, GateOp.eval, bit]⟩
  | cons i tail =>
    cases tail with
    | nil =>
      rcases hop with rfl | rfl
      · exact ⟨_, atom (mem i),
          by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
      · exact ⟨_, atom (mem i),
          by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
    | cons j tail =>
      cases tail with
      | cons => simp at hlen
      | nil =>
        rcases hop with rfl | rfl
        · exact ⟨_, (pair (mem i) (mem j)).1,
            by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩
        · exact ⟨_, (pair (mem i) (mem j)).2,
            by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩

def represents (available : Finset W) (w : List W) : Prop :=
  ∀ u ∈ w, u = 0 ∨ u = BitVec.allOnes 128 ∨ u ∈ available

theorem classify {available : Finset W} {ws : List W} (hw : represents available ws)
    {z : W} (hz : possible ws z) :
    z = 0 ∨ z = BitVec.allOnes 128 ∨ z ∈ available ∨
      ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧ z ∈ basicOps a b := by
  have lift {t : W} (h : t = 0 ∨ t = BitVec.allOnes 128 ∨ t ∈ available) :
      t = 0 ∨ t = BitVec.allOnes 128 ∨ t ∈ available ∨
        ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧ t ∈ basicOps a b :=
    h.imp_right (Or.imp_right Or.inl)
  simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hz
  rcases hz with ((h | h) | ⟨x, hx, h | ⟨y, hy, h | h⟩⟩)
  · exact .inl h
  · exact .inr (.inl h)
  · subst z; exact lift (hw _ hx)
  · subst z
    rcases hw _ hx with rfl | rfl | hu
    · left; simp
    · rw [BitVec.allOnes_and]; exact lift (hw _ hy)
    rcases hw _ hy with rfl | rfl | hv
    · left; simp
    · rw [BitVec.and_allOnes]; exact .inr (.inr (.inl hu))
    by_cases h : x = y
    · subst h; rw [BitVec.and_self]; exact .inr (.inr (.inl hu))
    · exact .inr (.inr (.inr ⟨x, hu, y, hv, h, by simp [basicOps, ops]⟩))
  · subst z
    rcases hw _ hx with rfl | rfl | hu
    · rw [show (0 : W) ||| y = y by ext i hi; simp]; exact lift (hw _ hy)
    · right; left; exact BitVec.allOnes_or
    rcases hw _ hy with rfl | rfl | hv
    · rw [show x ||| (0 : W) = x by ext i hi; simp]; exact .inr (.inr (.inl hu))
    · right; left; exact BitVec.or_allOnes
    by_cases h : x = y
    · subst h; rw [BitVec.or_self]; exact .inr (.inr (.inl hu))
    · exact .inr (.inr (.inr ⟨x, hu, y, hv, h, by simp [basicOps, ops]⟩))

private theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : represents av w)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k goal) :
    build basicOps goal gs.length av := by
  induction gs generalizing w av with
  | nil =>
    have hval : w.getD out 0 = goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i, hi⟩
    have hr := read_wire w out
    rw [hval] at hr
    rcases hr with hz | hm
    · exact False.elim ((by decide : goal ≠ (0 : W)) hz)
    · rcases hw _ hm with h | h | h
      · exact False.elim ((by decide : goal ≠ (0 : W)) h)
      · exact False.elim ((by decide : goal ≠ BitVec.allOnes 128) h)
      · exact h
  | cons g gs ih =>
    obtain ⟨z, hz, hstep⟩ := gate_table w w (fun _ h => h) g (hg g (by simp))
    have fn := ih (fun g' h => hg g' (by simp [h])) (w ++ [z])
    have he' : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k goal := by
      intro k; simpa only [List.foldl_cons, hstep] using he k
    have appendOK (h : z = 0 ∨ z = BitVec.allOnes 128 ∨ z ∈ av) : represents av (w ++ [z]) := by
      intro u hu
      rcases List.mem_append.mp hu with old | fresh
      · exact hw _ old
      · have eq : u = z := List.mem_singleton.mp fresh
        exact eq ▸ h
    rcases classify hw hz with h | h | h | ⟨a, ha, b, hb, hab, hop⟩
    · exact Or.inl (fn av (appendOK (.inl h)) he')
    · exact Or.inl (fn av (appendOK (.inr (.inl h))) he')
    · exact Or.inl (fn av (appendOK (.inr (.inr h))) he')
    · refine Or.inr ⟨a, ha, b, hb, hab, z, hop, fn (insert z av) ?_ he'⟩
      intro u hu
      rcases List.mem_append.mp hu with hu | hu
      · exact (hw _ hu).imp_right (Or.imp_right (Finset.mem_insert_of_mem ·))
      · simp_all

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => ws == [goal]
  | k + 1, extra, ws => ws == [goal] ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (optimized k) a b r)

theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

theorem optimized_complete (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps goal n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (optimized k) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps goal k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatch_complete (k := k) (extra := extra) (optimized k) hop hk (by omega) (by omega) (cuts_full hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def A : Fin 4 → Fin 4 → Bool := fun u v : Fin 4 => (4973 : ℕ).testBit (4 * u.val + v.val)

def posL : List (Fin 4 × Fin 4) :=
  [(0, 0), (0, 2), (0, 3), (1, 1), (1, 2), (2, 0), (2, 1), (3, 0)]

def negL : List (Fin 4 × Fin 4) :=
  [(0, 1), (1, 0), (1, 3), (2, 2), (2, 3), (3, 1), (3, 2), (3, 3)]

def samp (k : Fin 128) : Fin 4 × Fin 4 :=
  if k.val < 64 then negL.getD (k.val % 8) (0, 0) else posL.getD ((k.val - 64) / 8) (0, 0)

theorem input_rows : ∀ k : Fin 128,
    rawInputs.map (bit k) = PEqualNP.Represents.oneEach (samp k).1 (samp k).2 := by
  decide +kernel

theorem goal_rows : ∀ k : Fin 128, bit k goal = A (samp k).1 (samp k).2 := by
  decide +kernel

theorem rows_eval (C : Circuit) (hr : PEqualNP.Represents.Represents A C) (k : Fin 128) :
    (C.gates.foldl step (rawInputs.map (bit k))).getD C.output false = bit k goal := by
  rw [input_rows k, goal_rows k]
  exact hr (samp k).1 (samp k).2

theorem raw_ok : (rawInputs.all fun u => u == 0 || u == BitVec.allOnes 128 || inputs.contains u) = true := by
  decide +kernel

theorem initial_rep : represents inputs.toFinset rawInputs := by
  intro u hu
  have h := List.all_eq_true.mp raw_ok u hu
  simp only [Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem] at h
  rcases h with (h | h) | h
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (List.mem_toFinset.mpr h))

theorem get_build (C : Circuit) (hg : Monotone2 C) (hr : PEqualNP.Represents.Represents A C) :
    build basicOps goal C.gates.length inputs.toFinset :=
  compile C.gates C.output hg rawInputs inputs.toFinset initial_rep (rows_eval C hr)

theorem extend_live {m0 n0 : ℕ} {s : Finset W} (le : m0 ≤ n0) (h : live basicOps goal m0 s) :
    live basicOps goal n0 s := by
  induction le with
  | refl => exact h
  | step _ ih => exact Or.inl ih

theorem inputs_nodup : inputs.Nodup := by decide +kernel

def frontPred (ws : List W) : Bool := decide (9 < ws.length) || !(optimized 8 (9 - ws.length) ws)

def frontChunk (k : ℕ) := (inputs.sublists.drop (k * 16)).take 16

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem frontChunk_0 : (frontChunk 0).all frontPred = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem frontChunk_1 : (frontChunk 1).all frontPred = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem frontChunk_2 : (frontChunk 2).all frontPred = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem frontChunk_3 : (frontChunk 3).all frontPred = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem frontChunk_4 : (frontChunk 4).all frontPred = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem frontChunk_5 : (frontChunk 5).all frontPred = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem frontChunk_6 : (frontChunk 6).all frontPred = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem frontChunk_7 : (frontChunk 7).all frontPred = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem frontChunk_8 : (frontChunk 8).all frontPred = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem frontChunk_9 : (frontChunk 9).all frontPred = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem frontChunk_10 : (frontChunk 10).all frontPred = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem frontChunk_11 : (frontChunk 11).all frontPred = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem frontChunk_12 : (frontChunk 12).all frontPred = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem frontChunk_13 : (frontChunk 13).all frontPred = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem frontChunk_14 : (frontChunk 14).all frontPred = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem frontChunk_15 : (frontChunk 15).all frontPred = true := by decide +kernel

theorem all_front : inputs.sublists.all (fun l => decide (9 < l.length) || !(optimized 8 (9 - l.length) l)) = true := by
  change inputs.sublists.all frontPred = true
  have eq : inputs.sublists = frontChunk 0 ++ frontChunk 1 ++ frontChunk 2 ++ frontChunk 3 ++ frontChunk 4 ++ frontChunk 5 ++ frontChunk 6 ++ frontChunk 7 ++ frontChunk 8 ++ frontChunk 9 ++ frontChunk 10 ++ frontChunk 11 ++ frontChunk 12 ++ frontChunk 13 ++ frontChunk 14 ++ frontChunk 15 := by decide +kernel
  rw [eq]
  simp only [List.all_append,frontChunk_0,frontChunk_1,frontChunk_2,frontChunk_3,frontChunk_4,frontChunk_5,frontChunk_6,frontChunk_7,frontChunk_8,frontChunk_9,frontChunk_10,frontChunk_11,frontChunk_12,frontChunk_13,frontChunk_14,frontChunk_15,Bool.and_true]

theorem no_small (C : Circuit) (hm : Monotone2 C) (hs : C.size ≤ 8)
    (hr : PEqualNP.Represents.Represents A C) : False := by
  obtain ⟨S, hsub, hl⟩ := compress (get_build C hm hr)
  have hl3 : live basicOps goal 8 S := extend_live hs hl
  let l := inputs.filter (fun w => decide (w ∈ S))
  have hlS : l.toFinset = S := by
    ext v
    simp only [l, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨List.mem_toFinset.mp (hsub h), h⟩
  have hnd : l.Nodup := inputs_nodup.filter _
  have hcard := live_card hl3
  rw [← hlS, List.toFinset_card_of_nodup hnd] at hcard
  have hsearch := optimized_complete 8 l (9 - l.length) hnd (by omega) (hlS ▸ hl3)
  have hmem : l ∈ inputs.sublists := List.mem_sublists.mpr List.filter_sublist
  have hrow := List.all_eq_true.mp all_front l hmem
  have h4 : decide (9 < l.length) = false := by simp; omega
  rw [h4, hsearch] at hrow
  exact Bool.noConfusion hrow

def upperC : Circuit :=
  { gates := [{ op := GateOp.or, inputs := [1, 4] }, { op := GateOp.or, inputs := [2, 6] }, { op := GateOp.or, inputs := [3, 9] }, { op := GateOp.or, inputs := [7, 9] }, { op := GateOp.or, inputs := [0, 5] }, { op := GateOp.and, inputs := [8, 10] }, { op := GateOp.or, inputs := [12, 13] }, { op := GateOp.or, inputs := [8, 11] }, { op := GateOp.and, inputs := [14, 15] }],
    output := 16 }

theorem upper_mono : Monotone2 upperC := by
  intro g hg
  simp only [upperC, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem upper_rep : PEqualNP.Represents.Represents A upperC := by
  decide +kernel

end BaseFour

theorem BaseFour : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (4973 : ℕ).testBit (4 * u.val + v.val)) 9 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (4973 : ℕ).testBit (4 * u.val + v.val)) 8 := by
  refine ⟨⟨BaseFour.upperC, BaseFour.upper_mono,
    by decide, BaseFour.upper_rep⟩, ?_⟩
  rintro ⟨C, hm, hs, hr⟩
  exact BaseFour.no_small C hm hs hr

namespace Pin9219

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity BasePin

def restrictInput {n m : ℕ} (ρ : Fin n → Option (Fin m)) (z : Fin m → Bool) (i : Fin n) : Bool :=
  match ρ i with
  | none => false
  | some j => z j

private def image {n m : ℕ} (ρ : Fin n → Option (Fin m)) : List Stat :=
  List.ofFn fun i => match ρ i with
    | none => Sum.inl false
    | some j => Sum.inr j.val

private theorem image_inv {n m : ℕ} (ρ : Fin n → Option (Fin m)) (z : Fin m → Bool) :
    Inv m (List.ofFn z) (List.ofFn (restrictInput ρ z)) (image ρ, []) := by
  refine ⟨by simp [image],?_⟩
  intro k
  change ((image ρ).getD k (.inl false)).Valid (m+0) ∧
    ((image ρ).getD k (.inl false)).val (List.ofFn z) = (List.ofFn (restrictInput ρ z)).getD k false
  by_cases hk : k < n
  · cases h : ρ ⟨k,hk⟩ with
    | none => simp [image,restrictInput,hk,h,Stat.Valid,Stat.val]
    | some j => simp [image,restrictInput,hk,h,Stat.Valid,Stat.val]
  · simp [image,restrictInput,hk,Stat.Valid,Stat.val]

private def MonoGate (g : Gate) := (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

private theorem simplify_mono (op : GateOp) (ok : op = .and ∨ op = .or) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, MonoGate g := by
  intro g hg
  rcases ok with rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simplify,simpAnd] at hg <;> (subst hg; simp [MonoGate])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simplify,simpOr] at hg <;> (subst hg; simp [MonoGate])

private theorem elim_mono (m : ℕ) (gs : List Gate) (legal : ∀ g ∈ gs, MonoGate g) :
    ∀ acc : List Stat × List Gate, (∀ g ∈ acc.2, MonoGate g) → ∀ g ∈ (elim m gs acc).2, MonoGate g := by
  induction gs with
  | nil => intro acc ha; exact ha
  | cons g gs ih =>
    intro acc ha
    apply ih (fun k hk => legal k (List.mem_cons_of_mem _ hk)) (elimStep m acc g)
    intro k hk
    obtain h | h := List.mem_append.mp hk
    · exact ha k h
    · exact simplify_mono _ (legal g List.mem_cons_self).1 _ _ k (by simpa using h)

theorem project {n m : ℕ} (C : Circuit) (ρ : Fin n → Option (Fin m)) (S : Finset ℕ)
    (mono : Monotone2 C)
    (readers : ∀ j ∈ S, ∃ g, C.gates[j]? = some g ∧ ∃ a : Fin n, a.val ∈ g.inputs ∧ ρ a = none) :
    (∃ b : Bool, ∀ z, C.eval (List.ofFn (restrictInput ρ z)) = b) ∨
    ∃ D : Circuit, Monotone2 D ∧ D.size + S.card ≤ C.size ∧
      ∀ z, D.eval (List.ofFn z) = C.eval (List.ofFn (restrictInput ρ z)) := by
  let acc := elim m C.gates (image ρ, [])
  have legal (g : Gate) (hg : g ∈ C.gates) : NOk g := by
    have hop : g.op = GateOp.and ∨ g.op = GateOp.or := (mono g hg).1
    refine ⟨⟨hop.elim Or.inl (fun h => Or.inr (Or.inl h)),(mono g hg).2⟩,?_⟩
    rintro h; rcases hop with h' | h' <;> rw [h'] at h <;> contradiction
  have budget : acc.2.length + S.card ≤ 0 + C.gates.length := by
    apply elim_count m (image ρ, []) C.gates legal S
    intro j hj
    obtain ⟨g,hg,a,ha,pin⟩ := readers j hj
    refine ⟨g,hg,a.val,ha,?_,false,?_⟩
    · simp only [image,List.length_ofFn]; omega
    · rw [elim_getD m a.val _ C.gates _ (by simp [image])]
      simp [image,pin]
  have value (z : Fin m → Bool) :
      (acc.1.getD C.output (.inl false)).val (wiresFrom acc.2 (List.ofFn z)) =
      C.eval (List.ofFn (restrictInput ρ z)) := by
    exact ((inv_elim m (List.ofFn z) (by simp) C.gates _ _
      (fun g hg => (legal g hg).1) (image_inv ρ z)).2 C.output).2
  cases h : acc.1.getD C.output (.inl false) with
  | inl b =>
    exact Or.inl ⟨b,fun z => by simpa only [h,Stat.val] using (value z).symm⟩
  | inr j =>
    refine Or.inr ⟨⟨acc.2,j⟩,?_,by simpa [Circuit.size] using budget,?_⟩
    · exact elim_mono m C.gates (fun g hg => mono g hg) (image ρ, []) (by simp)
    · intro z
      change (wiresFrom acc.2 (List.ofFn z)).getD j false = _
      simpa only [h,Stat.val] using value z

theorem project_nonconstant {n m : ℕ} (C : Circuit) (ρ : Fin n → Option (Fin m)) (S : Finset ℕ)
    (mono : Monotone2 C)
    (readers : ∀ j ∈ S, ∃ g, C.gates[j]? = some g ∧ ∃ a : Fin n, a.val ∈ g.inputs ∧ ρ a = none)
    (different : ∃ x y, C.eval (List.ofFn (restrictInput ρ x)) ≠ C.eval (List.ofFn (restrictInput ρ y))) :
    ∃ D : Circuit, Monotone2 D ∧ D.size + S.card ≤ C.size ∧
      ∀ z, D.eval (List.ofFn z) = C.eval (List.ofFn (restrictInput ρ z)) := by
  rcases project C ρ S mono readers with ⟨b,constant⟩ | found
  · obtain ⟨x,y,hne⟩ := different
    exact False.elim (hne ((constant x).trans (constant y).symm))
  · exact found

end Pin9219

namespace Table9219.Quotient

open PEqualNP.CircuitLowerBounds PEqualNP.Represents PEqualNP.MetaComplexity

def table (u v : Fin 4) : Bool := (14494 : ℕ).testBit (4 * u.val + v.val)

private def row (v : Fin 4) : Fin 4 := ![0, 3, 1, 2] v
private def col (u : Fin 4) : Fin 4 := ![3, 0, 1, 2] u

private theorem entries : ∀ u v : Fin 4,
    table (row v) (col u) = (4973 : ℕ).testBit (4 * u.val + v.val) := by decide

private def wire : Fin 8 → Fin 8 := ![4, 6, 7, 5, 1, 2, 3, 0]

private def permute (i : Fin 8) : Option (Fin 8) := some (wire i)

private def pair (u v : Fin 4) (i : Fin 8) : Bool := (oneEach u v).getD i.val false

private theorem pair_values : ∀ u v : Fin 4, List.ofFn (pair u v) = oneEach u v := by decide

private theorem input_values : ∀ u v : Fin 4,
    List.ofFn (Pin9219.restrictInput permute (pair u v)) = oneEach (row v) (col u) := by decide

theorem no_eight : ¬ RepSizeAtMost table 8 := by
  rintro ⟨C, hc, hs, rep⟩
  have eval_pair (u v : Fin 4) : C.eval (List.ofFn (Pin9219.restrictInput permute (pair u v))) =
      (4973 : ℕ).testBit (4 * u.val + v.val) := by
    rw [input_values, rep, entries]
  have different : ∃ x y, C.eval (List.ofFn (Pin9219.restrictInput permute x)) ≠
      C.eval (List.ofFn (Pin9219.restrictInput permute y)) := by
    refine ⟨pair 0 0, pair 0 1, ?_⟩
    rw [eval_pair, eval_pair]
    decide
  obtain ⟨D, hd, budget, sim⟩ :=
    Pin9219.project_nonconstant C permute ∅ hc (by simp) different
  apply BaseFour.2
  refine ⟨D, hd, (by simpa using budget.trans hs), ?_⟩
  intro u v
  rw [← pair_values u v, sim, eval_pair]

end Table9219.Quotient

namespace Table9219.RequiredPins

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open BasePin

private def Off (v : ℕ) (x y : List Bool) : Prop :=
  ∀ i, i ≠ v → x.getD i false = true → y.getD i false = true

private theorem runOff (v : ℕ) (gs : List Gate)
    (ops : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    (unread : ∀ g ∈ gs, v ∉ g.inputs) (x y : List Bool)
    (len : x.length = y.length) (le : Off v x y) :
    Off v (wiresFrom gs x) (wiresFrom gs y) := by
  induction gs generalizing x y with
  | nil => exact le
  | cons g gs ih =>
    have headle : g.op.eval (g.inputs.map fun i => x.getD i false) = true →
        g.op.eval (g.inputs.map fun i => y.getD i false) = true := by
      have pins (i : ℕ) (hi : i ∈ g.inputs) :=
        le i (fun eq => unread g List.mem_cons_self (eq ▸ hi))
      rcases ops g List.mem_cons_self with hop | hop
      · rw [hop]
        simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
        exact fun h i hi => pins i hi (h i hi)
      · rw [hop]
        simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
        exact fun ⟨i, hi, h⟩ => ⟨i, hi, pins i hi h⟩
    apply ih (fun a ha => ops a (List.mem_cons_of_mem _ ha))
      (fun a ha => unread a (List.mem_cons_of_mem _ ha))
      (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)])
      (y ++ [g.op.eval (g.inputs.map fun i => y.getD i false)]) (by simp [len])
    intro i hiv
    by_cases hi : i = x.length
    · subst i
      rw [getD_snoc_eq, len, getD_snoc_eq]
      exact headle
    · rw [getD_snoc_ne _ _ _ _ hi, getD_snoc_ne _ _ _ _ (by omega)]
      exact le i hiv

private theorem needed (C : Circuit) (mono : Monotone2 C) (v n : ℕ)
    (x y z : List Bool) (len : x.length = y.length) (nx : x.length = n)
    (le : ∀ i : Fin n, i.val ≠ v → x.getD i.val false = true → y.getD i.val false = true)
    (pos : C.eval x = true) (neg : C.eval y = false)
    (vz : v < z.length) (bit : z.getD v false = true) (offz : C.eval z = false) :
    ∃ (j : ℕ) (g : Gate), C.gates[j]? = some g ∧ v ∈ g.inputs := by
  classical
  by_contra h
  have unread (g : Gate) (hg : g ∈ C.gates) : v ∉ g.inputs := by
    obtain ⟨j,hj⟩ := List.mem_iff_getElem?.mp hg
    exact fun hv => h ⟨j,g,hj,hv⟩
  have hout : C.output ≠ v := by
    intro eq
    obtain ⟨tail, extend, _⟩ := wiresFrom_prefix C.gates z
    change (wiresFrom C.gates z).getD C.output false = false at offz
    rw [eq, extend, List.getD_append _ _ _ _ vz, bit] at offz
    contradiction
  have hle : Off v x y := by
    intro i hv hi
    by_cases hn : i < n
    · exact le ⟨i,hn⟩ hv hi
    · rw [List.getD_eq_default _ _ (by omega)] at hi
      contradiction
  have hy := runOff v C.gates (fun g hg => (mono g hg).1) unread x y len hle C.output hout pos
  change C.eval y = true at hy
  rw [neg] at hy
  contradiction

theorem rowRead (C : Circuit) (mono : Monotone2 C)
    (rep : Represents (fun u v : Fin 5 => (7586366 : ℕ).testBit (5*u.val+v.val)) C) :
    ∃ (j : ℕ) (g : Gate), C.gates[j]? = some g ∧ 4 ∈ g.inputs := by
  apply needed C mono 4 10 (oneEach (4 : Fin 5) (0 : Fin 5))
    (oneEach (0 : Fin 5) (0 : Fin 5)) (oneEach (4 : Fin 5) (3 : Fin 5))
  all_goals first | (rw [rep] <;> decide) | decide

theorem colRead (C : Circuit) (mono : Monotone2 C)
    (rep : Represents (fun (u : Fin 4) (v : Fin 5) => (7586366 : ℕ).testBit (5*u.val+v.val)) C) :
    ∃ (j : ℕ) (g : Gate), C.gates[j]? = some g ∧ 6 ∈ g.inputs := by
  apply needed C mono 6 9 (oneEach (0 : Fin 4) (2 : Fin 5))
    (oneEach (0 : Fin 4) (0 : Fin 5)) (oneEach (1 : Fin 4) (2 : Fin 5))
  all_goals first | (rw [rep] <;> decide) | decide

end Table9219.RequiredPins

namespace Table9219

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

private def full (u v : Fin 5) : Bool := (7586366 : ℕ).testBit (5*u.val + v.val)
private def intermediate (u : Fin 4) (v : Fin 5) : Bool := (7586366 : ℕ).testBit (5*u.val + v.val)

private def pinRow : Fin 10 → Option (Fin 9) :=
  ![some 0,some 1,some 2,some 3,none,some 4,some 5,some 6,some 7,some 8]

private def pinColumn : Fin 9 → Option (Fin 8) :=
  ![some 0,some 1,some 2,some 3,some 4,some 5,none,some 6,some 7]

private def hot {a b : ℕ} (u : Fin a) (v : Fin b) : Fin (a+b) → Bool :=
  Fin.append (fun i => decide (i = u)) (fun j => decide (j = v))

private theorem hot_list {a b : ℕ} (u : Fin a) (v : Fin b) : List.ofFn (hot u v) = oneEach u v := by
  simp [hot,oneEach]

private theorem shrink {n m a b : ℕ} (A : Fin n → Fin m → Bool) (B : Fin a → Fin b → Bool)
    (ρ : Fin (n+m) → Option (Fin (a+b))) (v : Fin (n+m)) (q : ρ v = none)
    (row : Fin a → Fin n) (col : Fin b → Fin m)
    (words : ∀ p l, List.ofFn (Pin9219.restrictInput ρ (hot p l)) = oneEach (row p) (col l))
    (entries : ∀ p l, A (row p) (col l) = B p l)
    (different : ∃ p l p' l', B p l ≠ B p' l')
    (C : Circuit) (mono : Monotone2 C) (rep : Represents A C)
    (reader : ∃ (j : ℕ) (g : Gate), C.gates[j]? = some g ∧ v.val ∈ g.inputs) :
    ∃ D : Circuit, Monotone2 D ∧ D.size + 1 ≤ C.size ∧ Represents B D := by
  obtain ⟨j,g,hg,reads⟩ := reader
  have agree (p : Fin a) (l : Fin b) : C.eval (List.ofFn (Pin9219.restrictInput ρ (hot p l))) = B p l := by
    rw [words p l, rep (row p) (col l), entries p l]
  have notConstant : ∃ x y, C.eval (List.ofFn (Pin9219.restrictInput ρ x)) ≠ C.eval (List.ofFn (Pin9219.restrictInput ρ y)) := by
    obtain ⟨p,l,p',l',hne⟩ := different
    exact ⟨hot p l,hot p' l',by rwa [agree p l,agree p' l']⟩
  obtain ⟨D,valid,count,eq⟩ := Pin9219.project_nonconstant C ρ {j} mono (by
    intro i hi
    obtain rfl := Finset.mem_singleton.mp hi
    exact ⟨g,hg,v,reads,q⟩) notConstant
  refine ⟨D,valid,by simpa using count,?_⟩
  intro p l
  simpa only [hot_list] using (eq (hot p l)).trans (agree p l)

private def keepRow (p : Fin 4) : Fin 5 := ![0,1,2,3] p
private def keepColumn (l : Fin 4) : Fin 5 := ![0,1,3,4] l

private theorem first {C : Circuit} (mono : Monotone2 C) (rep : Represents full C)
    (read : ∃ (j : ℕ) (g : Gate), C.gates[j]? = some g ∧ 4 ∈ g.inputs) :
    ∃ D : Circuit, Monotone2 D ∧ D.size + 1 ≤ C.size ∧ Represents intermediate D := by
  refine shrink full intermediate pinRow 4 (by decide) keepRow id (by decide) (by decide) ?_ C mono rep read
  exact ⟨0,0,0,1,by decide⟩

private theorem second {C : Circuit} (mono : Monotone2 C) (rep : Represents intermediate C)
    (read : ∃ (j : ℕ) (g : Gate), C.gates[j]? = some g ∧ 6 ∈ g.inputs) :
    ∃ D : Circuit, Monotone2 D ∧ D.size + 1 ≤ C.size ∧ Represents Quotient.table D := by
  refine shrink intermediate Quotient.table pinColumn 6 (by decide) id keepColumn (by decide) (by decide) ?_ C mono rep read
  exact ⟨0,0,0,1,by decide⟩

private theorem exclude
    (rowRead : ∀ (C : Circuit), Monotone2 C → Represents full C → ∃ (j : ℕ) (g : Gate), C.gates[j]? = some g ∧ 4 ∈ g.inputs)
    (colRead : ∀ (C : Circuit), Monotone2 C → Represents intermediate C → ∃ (j : ℕ) (g : Gate), C.gates[j]? = some g ∧ 6 ∈ g.inputs) :
    ¬ RepSizeAtMost (fun u v : Fin 5 => (7586366 : ℕ).testBit (5*u.val+v.val)) 10 := by
  rintro ⟨C,mono,budget,rep⟩
  obtain ⟨D,md,cd,rd⟩ := first mono rep (rowRead C mono rep)
  obtain ⟨E,me,ce,re⟩ := second md rd (colRead D md rd)
  exact Quotient.no_eight ⟨E,me,by omega,re⟩

theorem no_ten : ¬ RepSizeAtMost (fun u v : Fin 5 => (7586366 : ℕ).testBit (5*u.val+v.val)) 10 :=
  exclude RequiredPins.rowRead RequiredPins.colRead

end Table9219

end PEqualNP.Outside.L_meta_9224

theorem PEqualNP.Outside.L_meta_9224 : ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (7586366 : ℕ).testBit (5 * u.val + v.val)) 10 := PEqualNP.Outside.L_meta_9224.Table9219.no_ten
