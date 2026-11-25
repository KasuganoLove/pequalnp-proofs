import PEqualNP.Outside.L_meta_4101
import Pnp1031OwnershipFinite

/-!
Research composition for L-meta-2343. The three finite quadrangle witness tables
below are copied, with attribution, from upstream L_meta_5272. Their use here
connects quadrangle negatives to the all-AND finite-test equivalence in
Pnp1031OwnershipFinite. This file does not prove the unconditional task.
-/

namespace Pnp2343QuadClean

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.EdgeOwnership
open PEqualNP.HeptadCover Pnp1031OwnershipFinite
open PEqualNP.Outside.L_meta_4101_aux.Plane

def qPt2Base (k : Fin 13) : Finset (Fin 13) :=
  match k.val with
  | 0 => {0, 1, 2, 5}
  | 1 => {0, 1, 2, 5}
  | 2 => {0, 1, 2, 5}
  | 3 => {0, 2, 3, 4}
  | 4 => {0, 1, 4, 6}
  | 5 => {0, 1, 2, 5}
  | 6 => {0, 1, 2, 6}
  | 7 => {0, 1, 2, 7}
  | 8 => {0, 1, 4, 8}
  | 9 => {0, 2, 4, 9}
  | 10 => {0, 1, 5, 10}
  | 11 => {0, 1, 2, 11}
  | 12 => {0, 1, 4, 12}
  | _ => {0, 1, 2, 5}

def qPlBase (k : Fin 13) : Finset (Fin 13) :=
  match k.val with
  | 0 => {0, 1, 2, 5}
  | 1 => {0, 1, 2, 5}
  | 2 => {2, 4, 5, 6}
  | 3 => {0, 1, 2, 5}
  | 4 => {2, 4, 5, 6}
  | 5 => {2, 4, 5, 6}
  | 6 => {2, 4, 5, 6}
  | 7 => {2, 4, 7, 8}
  | 8 => {2, 4, 5, 8}
  | 9 => {0, 1, 2, 5}
  | 10 => {2, 5, 6, 10}
  | 11 => {2, 4, 6, 11}
  | 12 => {2, 4, 5, 12}
  | _ => {0, 1, 2, 5}

def qLn2Base (k : Fin 13) : Finset (Fin 13) :=
  match k.val with
  | 0 => {2, 4, 5, 6}
  | 1 => {5, 6, 7, 11}
  | 2 => {4, 6, 7, 8}
  | 3 => {2, 5, 7, 8}
  | 4 => {2, 6, 8, 10}
  | 5 => {2, 4, 7, 11}
  | 6 => {4, 5, 8, 10}
  | 7 => {2, 4, 5, 6}
  | 8 => {2, 5, 6, 10}
  | 9 => {2, 4, 6, 8}
  | 10 => {2, 4, 5, 8}
  | 11 => {2, 4, 5, 6}
  | 12 => {4, 5, 6, 10}
  | _ => {0, 1, 2, 5}


/-- The exact 26 raw bits of a quadrangle negative. -/
def quadInput (Q : Finset (Fin 13)) : Fin 26 → Bool :=
  Fin.append (fun p : Fin 13 => decide (p ∈ Q))
    (fun l : Fin 13 => decide (l ∈ missLines singerLines3 Q))

def pairQuad (u v : Fin 26) : Finset (Fin 13) :=
  let a := Fin.ofNat 13 u.val
  let b := Fin.ofNat 13 v.val
  let c := Fin.ofNat 13 (u.val - 13)
  let d := Fin.ofNat 13 (v.val - 13)
  if u.val < 13 then
    if v.val < 13 then (qPt2Base (b-a)).image (· + a)
    else (qPlBase (a-d)).image (· + d)
  else
    if v.val < 13 then (qPlBase (b-c)).image (· + c)
    else (qLn2Base (d-c)).image (· + c)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pairQuad_spec : ∀ u v : Fin 26, adjB u v = false →
    IsQuadrangle singerLines3 (pairQuad u v) ∧
    quadInput (pairQuad u v) u = true ∧ quadInput (pairQuad u v) v = true := by
  decide +kernel

def Negative (z : Fin 26 → Bool) : Prop :=
  ∃ Q : Finset (Fin 13), IsQuadrangle singerLines3 Q ∧ z = quadInput Q

theorem nonedge_pair_covered (u v : Fin 26) (h : ¬ G.Adj u v) :
    ∃ z, Negative z ∧ ∀ i, pairInput u v i = true → z i = true := by
  have ha : adjB u v = false := by
    cases hb : adjB u v
    · rfl
    · exact False.elim (h ((G_adj u v).2 hb))
  obtain ⟨hQ, hu, hv⟩ := pairQuad_spec u v ha
  refine ⟨quadInput (pairQuad u v), ⟨pairQuad u v, hQ, rfl⟩, ?_⟩
  intro i hi
  have he : i = u ∨ i = v := by simpa only [pairInput, decide_eq_true_eq] using hi
  rcases he with rfl | rfl
  · exact hu
  · exact hv

theorem quad_clean_finite_tests (C : Circuit) (hm : Monotone2 C)
    (hclean : ∀ j g, C.gates[j]? = some g → g.op = GateOp.and →
      ∀ z, Negative z → gateVal 26 C j z = false) :
    RejectsNonedgePairs G C := by
  intro j g hj hop
  have hmono (x z : Fin 26 → Bool)
      (hxz : ∀ i, x i = true → z i = true) :
      gateVal 26 C j x = true → gateVal 26 C j z = true := by
    exact Wire.val_mono C.gates hm x z hxz (26+j)
  have hpair (u v : Fin 26) (h : ¬ G.Adj u v) :
      gateVal 26 C j (pairInput u v) = false := by
    obtain ⟨z, hz, hxz⟩ := nonedge_pair_covered u v h
    cases he : gateVal 26 C j (pairInput u v)
    · rfl
    · have ht := hmono _ z hxz he
      rw [hclean j g hj hop z hz] at ht
      exact Bool.noConfusion ht
  refine ⟨?_, hpair⟩
  cases he : gateVal 26 C j (fun _ => false)
  · rfl
  · have ht := hmono _ (pairInput 0 0) (by simp) he
    rw [hpair 0 0 (G.loopless.irrefl 0)] at ht
    exact Bool.noConfusion ht

theorem quad_clean_all_and_sound (C : Circuit) (hm : Monotone2 C)
    (hclean : ∀ j g, C.gates[j]? = some g → g.op = GateOp.and →
      ∀ z, Negative z → gateVal 26 C j z = false) :
    AllAndSound G C :=
  (all_and_sound_iff_finite_tests G C hm).2 (quad_clean_finite_tests C hm hclean)

end Pnp2343QuadClean
