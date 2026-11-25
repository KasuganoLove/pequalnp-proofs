import Pnp2343QuadClean
import Pnp2343CleanCost
import Pnp2343Pruning

/-!
Research bridge to the exact free-OR samples of L-meta-2343.
The conditional result requires every AND gate to reject every negative.
This additional hypothesis is not part of the original open task.
-/

namespace Pnp2343FreeOr

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.EdgeOwnership
open PEqualNP.HeptadCover
open PEqualNP.Outside.L_meta_4101_aux.Plane
open PEqualNP.Outside.Pnp2343Pruning
open Pnp2343QuadClean

lemma near_iff_mem (p l : Fin 13) :
    near p l ↔ p - l ∈ diff := by
  simp [near, diff]

lemma singer_iff_mem (p l : Fin 13) :
    p ∈ singerLines3 l ↔ p - l ∈ diff := by
  revert p l
  decide +kernel

lemma quad_iff (Q : Finset (Fin 13)) :
    IsQuadrangle singerLines3 Q ↔ quad Q := by
  have he (l : Fin 13) : Q ∩ singerLines3 l = Q.filter (fun p => p - l ∈ diff) := by
    ext p
    simp only [Finset.mem_inter, Finset.mem_filter, singer_iff_mem]
  simp only [IsQuadrangle, quad, he]

lemma miss_iff (Q : Finset (Fin 13)) (l : Fin 13) :
    l ∈ missLines singerLines3 Q ↔ ∀ p ∈ Q, p - l ∉ diff := by
  simp only [missLines, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h p hp hn
    exact Finset.disjoint_left.mp h ((singer_iff_mem p l).2 hn) hp
  · intro h
    exact Finset.disjoint_left.mpr (fun p hp hq => h p hq ((singer_iff_mem p l).1 hp))

lemma quadInput_list (Q : Finset (Fin 13)) :
    List.ofFn (quadInput Q) =
      (List.ofFn fun p : Fin 13 => decide (p ∈ Q)) ++
      List.ofFn (fun l : Fin 13 => decide (∀ p ∈ Q, p - l ∉ diff)) := by
  simp only [quadInput, List.ofFn_fin_append, miss_iff]

lemma pairInput_list (p l : Fin 13) :
    List.ofFn (pairInput (pV p) (lV l)) =
      (List.ofFn fun a : Fin 13 => decide (a = p)) ++
      List.ofFn (fun b : Fin 13 => decide (b = l)) := by
  rw [List.ofFn_add (n := 13) (m := 13)]
  congr 1 <;> apply congrArg List.ofFn <;> funext i
  · apply decide_eq_decide.mpr
    constructor
    · rintro (h | h)
      · apply Fin.ext
        have hv := congrArg (fun z : Fin 26 => z.val) h
        exact hv
      · have hv := congrArg Fin.val h
        change i.val = 13 + l.val at hv
        omega
    · intro h
      subst i
      exact Or.inl rfl
  · apply decide_eq_decide.mpr
    constructor
    · rintro (h | h)
      · have hv := congrArg Fin.val h
        change 13 + i.val = p.val at hv
        omega
      · apply Fin.ext
        have hv := congrArg Fin.val h
        change 13 + i.val = 13 + l.val at hv
        omega
    · intro h
      subst i
      exact Or.inr rfl

/-- Charge the formerly free OR as one ordinary gate. Its wire is exactly 26. -/
def charged (C : Circuit) (s : List ℕ) : Circuit :=
  ⟨⟨GateOp.or, s⟩ :: C.gates, C.output⟩

lemma charged_wires (C : Circuit) (s : List ℕ) (x : List Bool) :
    (charged C s).wires x = C.wires (augment s x) := by
  simp [charged, Circuit.wires, augment, GateOp.eval, List.any_map]

lemma charged_eval (C : Circuit) (s : List ℕ) (x : List Bool) :
    (charged C s).eval x = C.eval (augment s x) := by
  change ((charged C s).wires x).getD C.output false =
    (C.wires (augment s x)).getD C.output false
  rw [charged_wires]

lemma charged_size (C : Circuit) (s : List ℕ) :
    (charged C s).size = C.size + 1 := by
  simp [charged, Circuit.size]

lemma charged_mono (C : Circuit) (s : List ℕ)
    (hm : Monotone2 C) (hs : s.length ≤ 2) : Monotone2 (charged C s) := by
  intro g hg
  rcases List.mem_cons.mp hg with rfl | hg
  · exact ⟨Or.inr rfl, hs⟩
  · exact hm g hg

theorem free_or_clean_bound (C : Circuit) (s : List ℕ)
    (hs : s.length ≤ 2) (hm : Monotone2 C)
    (hfit : Fits (positive s) (negative s) C)
    (hclean : ∀ r < C.gates.length,
      (PEqualNP.MetaComplexity.NestedCover.gateAt C r).op = GateOp.and →
      ∀ Q : Quad, val C (negative s Q) (27+r) = false) :
    63 ≤ C.size := by
  have hflag (p l : Fin 13) (hp : near p l) :
      (charged C s).eval (List.ofFn (pairInput (pV p) (lV l))) = true := by
    rw [charged_eval, pairInput_list]
    exact hfit.1 ⟨(p,l), (near_iff_mem p l).1 hp⟩
  have hacc (u v : Fin 26) (h : G.Adj u v) :
      (charged C s).eval (List.ofFn (pairInput u v)) = true := by
    have hh := (G_adj u v).1 h
    simp only [adjB, Bool.or_eq_true] at hh
    rcases hh with hh | hh
    · obtain ⟨p,l,hp,rfl,rfl⟩ := (directedB_iff u v).1 hh
      exact hflag p l hp
    · obtain ⟨p,l,hp,rfl,rfl⟩ := (directedB_iff v u).1 hh
      have he : pairInput (lV l) (pV p) = pairInput (pV p) (lV l) := by
        funext i
        simp only [pairInput, or_comm]
      rw [he]
      exact hflag p l hp
  have hrej (z : Fin 26 → Bool) (hz : Negative z) :
      (charged C s).eval (List.ofFn z) = false := by
    obtain ⟨Q,hQ,rfl⟩ := hz
    rw [charged_eval, quadInput_list]
    exact hfit.2 ⟨Q,(quad_iff Q).1 hQ⟩
  have hand (j : ℕ) (g : Gate) (hj : (charged C s).gates[j]? = some g)
      (hop : g.op = GateOp.and) (z : Fin 26 → Bool) (hz : Negative z) :
      gateVal 26 (charged C s) j z = false := by
    obtain ⟨Q,hQ,rfl⟩ := hz
    cases j with
    | zero =>
      have hg : g = ⟨GateOp.or, s⟩ := by simpa [charged] using hj.symm
      rw [hg] at hop
      cases hop
    | succ r =>
      have hrget : C.gates[r]? = some g := by simpa [charged] using hj
      have hr : r < C.gates.length := List.getElem?_eq_some_iff.mp hrget |>.1
      have hg : PEqualNP.MetaComplexity.NestedCover.gateAt C r = g := by
        change C.gates.getD r _ = g
        rw [List.getD_eq_getElem _ _ hr]
        exact List.getElem?_eq_some_iff.mp hrget |>.2
      have ht := hclean r hr (by rw [hg]; exact hop) ⟨Q,(quad_iff Q).1 hQ⟩
      change ((charged C s).wires (List.ofFn (quadInput Q))).getD (26+(r+1)) false = false
      rw [charged_wires, quadInput_list]
      have hn : 26 + (r+1) = 27+r := by omega
      rw [hn]
      exact ht
  have hb := Pnp2343CleanCost.plane_bound_of_negative_family (charged C s)
    (charged_mono C s hm hs) Negative nonedge_pair_covered hacc hrej hand
  rw [charged_size] at hb
  omega

/-- Any counterexample must contain an AND gate that fires on a forbidden quadrangle. -/
theorem small_has_firing_and (C : Circuit) (s : List ℕ)
    (hs : s.length ≤ 2) (hm : Monotone2 C)
    (hfit : Fits (positive s) (negative s) C) (hsmall : C.size < 63) :
    ∃ r, r < C.gates.length ∧
      (PEqualNP.MetaComplexity.NestedCover.gateAt C r).op = GateOp.and ∧
      ∃ Q : Quad, val C (negative s Q) (27+r) = true := by
  classical
  by_contra hex
  have hclean : ∀ r < C.gates.length,
      (PEqualNP.MetaComplexity.NestedCover.gateAt C r).op = GateOp.and →
      ∀ Q : Quad, val C (negative s Q) (27+r) = false := by
    intro r hr hop Q
    cases he : val C (negative s Q) (27+r)
    · rfl
    · exact False.elim (hex ⟨r,hr,hop,Q,he⟩)
  have hb := free_or_clean_bound C s hs hm hfit hclean
  omega

end Pnp2343FreeOr
