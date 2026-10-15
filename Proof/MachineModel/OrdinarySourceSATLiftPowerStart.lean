import Proof.MachineModel.OrdinarySourceSATLiftPowerRun

namespace NearCubicWires.RepairSource.OrdinarySourceSATLift.Full
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/- Keep the focused start syntactically identical to the enclosing piece.
The definitional projection is discharged with abstract C, before the large
fixed printer is instantiated. -/
theorem power_focused_run (C : ℕ) (p : OrdinaryOracleProgram) (input : List Bool) (b : ℕ) :
    ∃ out r,runFrom (RecoveryFocus.machine (power p) (PCPSerializerCapacity.Power.machine 2 C))
      (PCPSerializerCapacity.Power.budget 2 C b)
      ⟨(RecoveryFocus.machine (power p) (PCPSerializerCapacity.Power.machine 2 C)).start,
        parsedHeads p input b,parsed p input b⟩=some r ∧
      r.final.heads=parsedHeads p input b ∧
      r.final.tapes=install (power p) (parsed p input b) out ∧
      r.steps ≤ PCPSerializerCapacity.Power.budget 2 C b ∧
      out (PCPSerializerCapacity.Power.outputSlot 2)=List.replicate (C*(b+1)^2) true := by
  exact powered_run C p input b

end NearCubicWires.RepairSource.OrdinarySourceSATLift.Full
