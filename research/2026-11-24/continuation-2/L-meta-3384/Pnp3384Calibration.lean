import Mathlib.Data.Fintype.Pi
import PEqualNP.Defs

namespace Pnp3384Calibration

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def target (x : Fin 7 → Bool) : Bool :=
  ([1,12,4,15,26,35,46,36] : List ℕ).any fun e =>
    x (Fin.ofNat 7 (e / 10)) && x (Fin.ofNat 7 (e % 10))

def source : Circuit :=
  ⟨[⟨.or,[1,4]⟩, ⟨.and,[0,7]⟩,
    ⟨.or,[2,5]⟩, ⟨.and,[1,9]⟩,
    ⟨.or,[5,6]⟩, ⟨.and,[3,11]⟩,
    ⟨.or,[2,4]⟩, ⟨.and,[6,13]⟩,
    ⟨.or,[8,10]⟩, ⟨.or,[12,14]⟩, ⟨.or,[15,16]⟩],17⟩

def modified : Circuit :=
  ⟨[⟨.or,[2,5]⟩, ⟨.and,[1,0]⟩,
    ⟨.or,[3,6]⟩, ⟨.and,[2,10]⟩,
    ⟨.or,[6,7]⟩, ⟨.and,[4,0]⟩,
    ⟨.or,[3,5]⟩, ⟨.and,[7,14]⟩,
    ⟨.or,[9,11]⟩, ⟨.or,[13,15]⟩, ⟨.or,[16,17]⟩],18⟩

def zeroReaders : Circuit :=
  ⟨[⟨.or,[1,4]⟩, ⟨.and,[0,7]⟩,
    ⟨.or,[1,6]⟩, ⟨.and,[2,9]⟩,
    ⟨.or,[1,3]⟩, ⟨.and,[5,11]⟩,
    ⟨.or,[3,4]⟩, ⟨.and,[6,13]⟩,
    ⟨.or,[8,10]⟩, ⟨.or,[12,14]⟩, ⟨.or,[15,16]⟩],17⟩

theorem count_is_or (g : Gate)
    (h : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    g.op.eval [true,false] = true ↔ g.op = GateOp.or := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with h | h | h <;> simp [h, GateOp.eval]

theorem source_fan : FanInTwo source := by simp [FanInTwo, source]

theorem source_size : source.size = 11 := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem source_correct : ∀ x : Fin 7 → Bool, circuitFun 7 source x = target x := by
  decide +kernel

theorem source_count :
    (source.gates.filter (fun g => g.op.eval [true,false] && g.inputs.contains 2)).length = 2 := by
  decide

theorem correspondence :
    List.Forall₂ (fun g h : Gate => g.op = h.op ∧
      List.Forall₂ (fun i j : ℕ => j = i+1 ∨ j = 0 ∧ (i = 7 ∨ i = 11))
        g.inputs h.inputs) source.gates modified.gates := by
  simp [source, modified, List.forall₂_cons]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem modified_correct : ∀ x : Fin 7 → Bool,
    (modified.wires (true :: List.ofFn x)).getD (source.output+1) false =
      (target x || x 0 || x 3) := by
  decide +kernel

theorem zeroReaders_fan : FanInTwo zeroReaders := by simp [FanInTwo, zeroReaders]

theorem zeroReaders_size : zeroReaders.size = 11 := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem zeroReaders_correct : ∀ x : Fin 7 → Bool, circuitFun 7 zeroReaders x = target x := by
  decide +kernel

theorem zeroReaders_count :
    (zeroReaders.gates.filter (fun g => g.op.eval [true,false] && g.inputs.contains 2)).length = 0 := by
  decide

end Pnp3384Calibration
