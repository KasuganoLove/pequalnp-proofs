import PEqualNP.Outside.L_meta_2289

namespace PetersenSecondAnd

open PEqualNP.Outside.L_meta_2289

def seed04 : Sig := inputs.getD 0 zero ||| inputs.getD 4 zero

def afterAnd (i : Fin 9) (keepInput keepSeed : Bool) : List Sig :=
  let a := inputs.getD i.val zero
  let roots := if keepInput then inputs else inputs.erase a
  let rest := if keepSeed then seed04 :: roots else roots
  (a &&& seed04) :: rest

theorem deletion_bound : Slice inputs graph (subcube 17 0) 11 := by
  have proj := col_sound (m := 511) (17, 0, 494, 0, 11) (boundsBefore known383)
    (before_sound known383 valid383) (by decide +kernel)
  have roots : vars 511 = inputs := by decide +kernel
  have tgt : chartGoal 511 = graph := by decide +kernel
  rw [roots, tgt] at proj
  exact proj

set_option maxHeartbeats 2000000 in
private theorem finite_checks :
    ∀ i : Fin 9, i ≠ 0 → i ≠ 4 → ∀ keepInput keepSeed : Bool,
      (afterAnd i keepInput keepSeed).Nodup ∧
      poolCut (subcube 17 0) 11 13 0 inputs (afterAnd i keepInput keepSeed) = true := by
  decide +kernel

theorem excluded (i : Fin 9) (ne0 : i ≠ 0) (ne4 : i ≠ 4) (keepInput keepSeed : Bool) :
    Impossible graph 13 (afterAnd i keepInput keepSeed).toFinset := by
  obtain ⟨distinct, cut⟩ := finite_checks i ne0 ne4 keepInput keepSeed
  exact poolCut_sound deletion_bound [] rfl distinct cut

end PetersenSecondAnd
