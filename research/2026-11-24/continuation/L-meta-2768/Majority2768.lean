import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.Majority2768
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev T := BitVec 8
def maj : T := 0xe8
def meet : T := 0xc0
def joinT : T := 0xfc
def leaf (m j : Bool) : List T :=
  [0, 255, 240, 204, 170] ++ (if m then [meet] else []) ++ (if j then [joinT] else [])
def binary (d : Bool) (a b : T) : T := if d then a ||| b else a &&& b

lemma and255 : ∀ x : T, x &&& 255 = x := by decide

def val (s : List T) (g : Gate) : T :=
  let vs := g.inputs.map fun w => s.getD w 0
  match g.op with
  | .and => vs.foldr (binary false) (BitVec.allOnes 8)
  | .or => vs.foldr (binary true) 0
  | _ => 0

def run (gs : List Gate) (s : List T) : List T :=
  gs.foldl (fun w g => w ++ [val w g]) s

def fresh (s : List T) : List T :=
  ((s.flatMap fun a => s.flatMap fun b => [a &&& b, a ||| b]).eraseDups).filter (fun x => !s.contains x)

def excludes : ℕ → List T → Bool
  | 0, s => !s.contains maj
  | n+1, s => !s.contains maj && excludes n s &&
      (fresh s).all (fun x => excludes n (x::s))

lemma read_mem {s pool : List T} (sub : ∀ x ∈ s, x ∈ pool) (hz : 0 ∈ pool) (i : ℕ) :
    s.getD i 0 ∈ pool := by
  rw [List.getD_eq_getElem?_getD]
  cases eq : s[i]? with
  | none => exact hz
  | some a => exact sub a (List.mem_of_getElem? eq)

lemma new_or_old (d : Bool) {s : List T} {a b : T} (ha : a ∈ s) (hb : b ∈ s) :
    binary d a b ∈ s ∨ binary d a b ∈ fresh s := by
  by_cases old : binary d a b ∈ s
  · exact Or.inl old
  · right
    apply List.mem_filter.mpr
    refine ⟨List.mem_eraseDups.mpr (List.mem_flatMap.mpr ⟨a,ha,List.mem_flatMap.mpr ⟨b,hb,?_⟩⟩),?_⟩
    · cases d <;> simp [binary]
    · simpa using old

lemma classified (g : Gate) {s pool : List T} (sub : ∀ x ∈ s, x ∈ pool)
    (hz : 0 ∈ pool) (ho : 255 ∈ pool)
    (legal : g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    val s g ∈ pool ∨ val s g ∈ fresh pool := by
  obtain ⟨op,ins⟩ := g
  obtain ⟨ok,hl⟩ := legal
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ok
  cases ins with
  | nil => rcases ok with rfl | rfl <;> exact Or.inl (by assumption)
  | cons a ins =>
    have aa := read_mem sub hz a
    cases ins with
    | nil =>
      rcases ok with rfl | rfl
      · left
        change (s.getD a 0 &&& BitVec.allOnes 8) ∈ pool
        rw [BitVec.and_allOnes]
        exact aa
      · left
        simpa [val,binary] using aa
    | cons b ins =>
      have bb := read_mem sub hz b
      cases ins with
      | cons c xs => simp at hl
      | nil =>
        rcases ok with rfl | rfl
        · have same : val s ⟨.and,[a,b]⟩ = binary false (s.getD a 0) (s.getD b 0) :=
            congrArg (fun z => s.getD a 0 &&& z) (BitVec.and_allOnes (x := s.getD b 0))
          rw [same]
          exact new_or_old false aa bb
        · simpa [val,binary] using new_or_old true aa bb

theorem exclude_sound (n : ℕ) (pool : List T) (ok : excludes n pool = true) :
    ∀ (gs : List Gate) (s : List T), gs.length ≤ n →
    (∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    (∀ x ∈ s, x ∈ pool) → 0 ∈ pool → 255 ∈ pool → ∀ i, (run gs s).getD i 0 ≠ maj := by
  induction n generalizing pool with
  | zero =>
    intro gs s hl _ sub hz _ i out
    have nil : gs = [] := List.length_eq_zero_iff.mp (by omega)
    subst gs
    have mem := read_mem sub hz i
    change s.getD i 0 = maj at out
    rw [out] at mem
    simpa [excludes,mem] using ok
  | succ n ih =>
    intro gs s hl legal sub hz ho i
    simp only [excludes, Bool.and_eq_true] at ok
    cases gs with
    | nil =>
      intro out
      change s.getD i 0 = maj at out
      have mem := read_mem sub hz i
      rw [out] at mem
      simpa [mem] using ok.1.1
    | cons g gs =>
      have hlen : gs.length ≤ n := by simpa using hl
      have tailLegal (u) (h : u ∈ gs) := legal u (List.mem_cons_of_mem _ h)
      change (run gs (s ++ [val s g])).getD i 0 ≠ maj
      rcases classified g sub hz ho (legal _ List.mem_cons_self) with old | added
      · apply ih pool ok.1.2 gs _ hlen tailLegal _ hz ho i
        intro a ha
        rcases List.mem_append.mp ha with mem | eq
        · exact sub a mem
        · exact (List.mem_singleton.mp eq) ▸ old
      · apply ih (val s g :: pool) (List.all_eq_true.mp ok.2 _ added) gs _ hlen tailLegal
          _ (List.mem_cons_of_mem _ hz) (List.mem_cons_of_mem _ ho) i
        intro a ha
        rcases List.mem_append.mp ha with mem | eq
        · exact List.mem_cons_of_mem _ (sub _ mem)
        · exact List.mem_cons.mpr (Or.inl (List.mem_singleton.mp eq))

theorem finite_cases : ∀ m j : Bool, excludes (3 - m.toNat - j.toNat) (leaf m j) = true := by
  decide +kernel

theorem majority_budget (C : Circuit) (s : List T) (m j : Bool) (mono : Monotone2 C)
    (covered : ∀ x ∈ s, x ∈ leaf m j) (computed : (run C.gates s).getD C.output 0 = maj) :
    4 ≤ C.size + m.toNat + j.toNat := by
  by_contra! low
  change C.gates.length + m.toNat + j.toNat < 4 at low
  exact exclude_sound _ _ (finite_cases m j) C.gates s (by omega) mono covered
    (by simp [leaf]) (by simp [leaf]) C.output computed

def bit (r : Fin 8) (a : T) := a.getLsbD r.val

lemma b_read (r : Fin 8) (s : List T) (k : ℕ) :
    (s.map (bit r)).getD k false = bit r (s.getD k 0) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases s[k]? <;> simp [bit]

lemma gate_bits (g : Gate) (s : List T) (r : Fin 8)
    (hg : g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp)) :
    bit r (val s g) = g.op.eval (g.inputs.map fun i => (s.map (bit r)).getD i false) := by
  obtain ⟨op,ins⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [b_read]
  have bitop (d : Bool) (u v : T) : bit r (binary d u v) =
      (if d then bit r u || bit r v else bit r u && bit r v) := by
    cases d <;> simp [binary,bit]
  rcases hg with rfl | rfl
  · induction ins with
    | nil => exact (show ∀ q : Fin 8, bit q 255 = true by decide) r
    | cons i l ih =>
      change bit r (binary false _ _) = (_ && _)
      rw [bitop]
      exact congrArg (fun x => bit r (s.getD i 0) && x) ih
  · induction ins with
    | nil => exact (show ∀ q : Fin 8, bit q 0 = false by decide) r
    | cons i l ih =>
      change bit r (binary true _ _) = (_ || _)
      rw [bitop]
      exact congrArg (fun x => bit r (s.getD i 0) || x) ih

lemma run_bits (gs : List Gate) (r : Fin 8) (s : List T)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp)) :
    (run gs s).map (bit r) =
      gs.foldl (fun (l : List Bool) g => l ++ [g.op.eval (g.inputs.map fun j => l.getD j false)])
        (s.map (bit r)) := by
  induction gs generalizing s with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (s ++ [val s g])).map _ = _
    rw [ih _ (fun a ha => legal a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,gate_bits g s r (legal g (by simp))]

def bare : List T := [0,255,240,204,meet,joinT]

theorem closed (gs : List Gate) (s : List T)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (covers : ∀ a ∈ s, a ∈ bare) : ∀ a ∈ run gs s, a ∈ bare := by
  induction gs generalizing s with
  | nil => exact covers
  | cons g gs ih =>
    apply ih _ (fun u hu => legal _ (List.mem_cons_of_mem _ hu))
    intro a ha
    rcases List.mem_append.mp ha with old | eq
    · exact covers _ old
    · rw [List.mem_singleton.mp eq]
      rcases classified g covers (by decide) (by decide) (legal g List.mem_cons_self) with known | new
      · exact known
      · rw [show fresh bare = [] by decide +kernel] at new
        exact False.elim (List.not_mem_nil new)

def col (e i : Bool) : T :=
  if e then (if i then 255 else 240) else (if i then 204 else 0)
def square {n : ℕ} (e i : Fin n → Bool) (a b : Bool) : Fin n → Bool :=
  if a then (if b then (fun j => e j || i j) else e)
  else (if b then i else (fun j => e j && i j))
def rawTables (e i : Fin 9 → Bool) : List T :=
  List.ofFn (fun j => col (e j) (i j)) ++ [col (e 0) (i 0) ||| col (e 3) (i 3)]

theorem squareBudget (A B : Circuit) (am : Monotone2 A) (bm : Monotone2 B)
    (e i : Fin 9 → Bool)
    (majority : ∀ a b t : Bool, let x := square e i a b
      B.eval (A.wires (List.ofFn x ++ [x 0 || x 3]) ++ [t]) =
        ((a && b) || ((a || b) && t))) :
    let state := run A.gates (rawTables e i)
    4 ≤ B.size + (state.contains meet).toNat + (state.contains joinT).toNat := by
  let raw := rawTables e i
  let state := run A.gates raw
  have col_mem : ∀ a b : Bool, col a b ∈ bare := by decide
  have seed_mem : ∀ a b c d : Bool, col a b ||| col c d ∈ bare := by decide
  have stateBare : ∀ z ∈ state, z ∈ bare := by
    apply closed _ _ am
    intro z hz
    rcases List.mem_append.mp hz with h | h
    · obtain ⟨v,rfl⟩ := List.mem_ofFn.mp h
      exact col_mem _ _
    · rw [List.mem_singleton.mp h]
      exact seed_mem _ _ _ _
  let m := state.contains meet
  let j := state.contains joinT
  have cover : ∀ z ∈ state ++ [170], z ∈ leaf m j := by
    intro z hz
    rcases List.mem_append.mp hz with mem | t
    · have c := stateBare _ mem
      simp only [bare,List.mem_cons,List.not_mem_nil,or_false] at c
      rcases c with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp [leaf,m,j,mem]
    · rw [List.mem_singleton.mp t]
      simp [leaf]
  apply majority_budget B _ m j bm cover
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  let r : Fin 8 := ⟨k,hk⟩
  let a := bit r 240
  let b := bit r 204
  let t := bit r 170
  let x := square e i a b
  have col_eq : ∀ (q : Fin 8) (u v : Bool),
      bit q (col u v) =
      (if bit q 240 then (if bit q 204 then u || v else u)
       else (if bit q 204 then v else u && v)) := by decide
  have cx (k : Fin 9) : bit r (col (e k) (i k)) = x k := by
    rw [col_eq]
    cases ha : bit r 240 <;> cases hb : bit r 204 <;> simp [x,square,a,b,ha,hb]
  have rawEq : raw.map (bit r) = List.ofFn x ++ [x 0 || x 3] := by
    simp only [raw,rawTables,List.map_append,List.map_singleton,List.map_ofFn]
    have funEq : (bit r) ∘ (fun k : Fin 9 => col (e k) (i k)) = x := funext cx
    rw [funEq]
    have eqb : bit r (col (e 0) (i 0) ||| col (e 3) (i 3)) =
        (bit r (col (e 0) (i 0)) || bit r (col (e 3) (i 3))) := by simp [bit]
    rw [eqb,cx,cx]
  have midEq : state.map (bit r) = A.wires (List.ofFn x ++ [x 0 || x 3]) := by
    rw [show state = run A.gates raw from rfl, run_bits A.gates r raw (fun g h => (am g h).1),rawEq]
    rfl
  change bit r _ = bit r maj
  rw [←b_read,run_bits B.gates r _ (fun g h => (bm g h).1)]
  simp only [List.map_append,List.map_singleton,midEq]
  have M : ∀ q : Fin 8, bit q maj = ((bit q 240 && bit q 204) ||
      ((bit q 240 || bit q 204) && bit q 170)) := by decide
  exact (majority a b t).trans (M r).symm

theorem four_rows {α : Type*} [Preorder α] (guard : α → Bool) (tail : α → Bool → Bool)
    (gm : Monotone guard)
    (tm : ∀ x y, x ≤ y → ∀ b c, b ≤ c → tail x b ≤ tail y c)
    {p n q m : α} (pn : p ≤ n) (nq : n ≤ q) (qm : q ≤ m)
    (pTrue : tail p (!(guard p)) = true) (nFalse : tail n (!(guard n)) = false)
    (qTrue : tail q (!(guard q)) = true) (mFalse : tail m (!(guard m)) = false) :
    False := by
  have descent {x y : α} (xy : x ≤ y)
      (tx : tail x (!(guard x)) = true) (ty : tail y (!(guard y)) = false) :
      guard x = false ∧ guard y = true := by
    have impossible : ¬ (!(guard x)) ≤ (!(guard y)) := by
      intro order
      have v := tm x y xy _ _ order
      rw [tx,ty] at v
      exact (by decide : ¬ (true ≤ false)) v
    cases hx : guard x <;> cases hy : guard y <;> simp_all
  have nTrue := (descent pn pTrue nFalse).2
  have qFalse := (descent qm qTrue mFalse).1
  have ord := gm nq
  rw [nTrue,qFalse] at ord
  exact (by decide : ¬ (true ≤ false)) ord

end PEqualNP.Outside.Majority2768
