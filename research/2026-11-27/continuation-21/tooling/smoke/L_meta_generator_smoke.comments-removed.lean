import PEqualNP.Defs
import PEqualNP.Library.Helpers.PromiseColTree




namespace PEqualNP.Outside.L_meta_generator_smoke
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Library.Helpers.Replay PEqualNP.Library.Helpers.ReplayCol
open PEqualNP.Library.Helpers.PromiseCol PEqualNP.Library.Helpers.PromiseColTree

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
def witness : Circuit := ⟨[
  ⟨.not, [1, 0]⟩
], 4⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
def rowMasks : List ℕ := [
  6
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem witness_shape_check : fanInTwoB witness = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem witness_shape : FanInTwo witness :=
  fanInTwoB_sound witness_shape_check

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem witness_size : witness.size ≤ 1 := by decide +kernel


set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
def replayRowMasks : List ℕ := [
  6,
  1
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem replay_rows_bound_check :
    replayRowMasks.all (fun r => decide (r < 2 ^ 3)) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem replay_rows_bound : ∀ r ∈ replayRowMasks, r < 2 ^ 3 := by
  intro r hr
  exact of_decide_eq_true (List.all_eq_true.mp replay_rows_bound_check r hr)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem replay_row_prefix : ∀ u : Fin 1,
    replayRowMasks.getD u.val 0 = rowMasks.getD u.val 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem replay_operations : aonB witness = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem promise_capacity : 1 * 3 ≤ 2 ^ 2 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem tree_capacity : 1 + 3 + witness.gates.length ≤ 2 ^ 3 := by decide +kernel


set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem output_replay :
    ((tcols 2 3 witness 1 3).1.rd 3 witness.output ==
      tcol 3 replayRowMasks) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem represented : PEqualNP.Represents.Represents
    (fun (u : Fin 1) (v : Fin 3) => (rowMasks.getD u.val 0).testBit v.val) witness := by
  have h := represents_of_tcols (n := 1) (m := 3) (N := 2) (D := 3)
    promise_capacity witness replayRowMasks replay_rows_bound replay_operations
    tree_capacity output_replay
  intro u v
  simpa only [replay_row_prefix u] using h u v

end PEqualNP.Outside.L_meta_generator_smoke

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem PEqualNP.Outside.L_meta_generator_smoke :
(∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 1 ∧ PEqualNP.Represents.Represents (fun (u : Fin 1) (v : Fin 3) => (([6] : List Nat).getD u.val 0).testBit v.val) C)

:= by
  exact ⟨PEqualNP.Outside.L_meta_generator_smoke.witness, PEqualNP.Outside.L_meta_generator_smoke.witness_shape,
    PEqualNP.Outside.L_meta_generator_smoke.witness_size, PEqualNP.Outside.L_meta_generator_smoke.represented⟩
