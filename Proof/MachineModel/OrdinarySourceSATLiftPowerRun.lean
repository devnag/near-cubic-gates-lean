import Proof.MachineModel.OrdinarySourceSATLiftCall

namespace NearCubicWires.RepairSource.OrdinarySourceSATLift.Full
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem powered_run (C : ℕ) (p : OrdinaryOracleProgram) (input : List Bool) (b : ℕ) :
    ∃ out r,runFrom (RecoveryFocus.machine (power p) (PCPSerializerCapacity.Power.machine 2 C))
      (PCPSerializerCapacity.Power.budget 2 C b)
      ⟨(PCPSerializerCapacity.Power.machine 2 C).start,parsedHeads p input b,parsed p input b⟩=some r ∧
      r.final.heads=parsedHeads p input b ∧
      r.final.tapes=install (power p) (parsed p input b) out ∧
      r.steps ≤ PCPSerializerCapacity.Power.budget 2 C b ∧
      out (PCPSerializerCapacity.Power.outputSlot 2)=List.replicate (C*(b+1)^2) true := by
  obtain ⟨out,hready,_hraw,hcap⟩ := PCPSerializerCapacity.Power.capacity_run 2 C b
  obtain ⟨r,hr,hh,ht,hs⟩ := hready.focus_at (power p) (power_injective p)
    (parsedHeads p input b) (parsed p input b) (parsed_power p input b) (parsed_heads_power p input b)
  exact ⟨out,r,hr,hh,ht,hs,hcap⟩

end NearCubicWires.RepairSource.OrdinarySourceSATLift.Full
