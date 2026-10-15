import Proof.Amplification.RecoveryRowStructureSmallTests

/-! The paid final conjunction in the zero and singleton structural cases.
Both prior checks are read from physical cells before the common result is
overwritten; no supplied Boolean controls this machine's transition. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRowStructure
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStream
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def smallGateBit (single valid zero one : Bool) := if single then valid && one else !valid && zero
def smallGate (single : Bool) : Machine 52 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q scanned=>if q.val=0 then some ⟨1,
    fun i=>if i=50 then some (smallGateBit single (scanned 50) (scanned 43) (scanned 44)) else none,
    fun _=>.stay⟩ else none

theorem small_gate_run (single : Bool) (d : Data) (capacity : Nat) :
    ∃ r,runFrom (smallGate single) 1 (cfg d capacity 0)=some r ∧
      r.final=cfg (setValid d (smallGateBit single d.valid (d.flags 0) (d.flags 1))) capacity 1 ∧ r.steps=1 := by
  have h := valid_step (cfg d capacity (0 : Fin 2)).heads (cfg d capacity (0 : Fin 2)).tapes d.valid
    (smallGateBit single d.valid (d.flags 0) (d.flags 1)) (by rfl) (by rfl)
  have hs : step (smallGate single) (cfg d capacity 0)=
      step (validMachine (smallGateBit single d.valid (d.flags 0) (d.flags 1))) (cfg d capacity 0) := rfl
  have ht := hs.trans h
  obtain ⟨r,hr,hf,hsteps⟩ := (Timed.single (by rfl) ht).run (by rfl)
  refine ⟨r,hr,?_,hsteps⟩
  rw [hf]
  apply configuration_ext
  · rfl
  · rfl
  · exact (cfg_valid d capacity _).symm

end NearCubicWires.RepairOrdinary.RecoveryRowStructure
