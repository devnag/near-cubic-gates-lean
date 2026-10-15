import Proof.MachineModel.ClockFloorLogFromInput
import Proof.Hierarchy.HierarchyReductionReady
import Proof.MachineModel.ClockTotalCanonical

/-! Enclosing paid suppliers for the fixed-U clock, code-length limit, and
hierarchy padding constructor. U acceptance semantics remain a separate
consumer of these concrete tapes and executions. -/
namespace NearCubicWires.RepairOrdinary.ClockFloorLogFromInput
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def ordinaryBudget (bits : List Bool) := 54*(bits.length+1)*PCPResourceLedger.q bits.length
theorem budget_bound (bits : List Bool) : budget bits≤ordinaryBudget bits := by
  dsimp [budget,ordinaryBudget,HierarchyInputLength.budget,HierarchyInputLength.rawBudget,
    ClockInputLength.cost,PCPResourceLedger.q]
  ring_nf
  omega

theorem guard_limit_run (bits : List Bool) :
    ∃ r,run machine (ordinaryBudget bits) (input bits)=some r ∧
      r.final.tapes 0=frame (ClockBinary.word bits.length) ∧ r.final.tapes 2=frame bits ∧
      r.final.tapes 4=RepairSource.VerifierDecoding.CompareMachine.word (Nat.log 2 bits.length) ∧
      r.final.heads=![0,0,0,0,1,0] ∧ r.steps ≤ ordinaryBudget bits := by
  obtain ⟨r,hr,h0,h2,h4,hh,hs⟩ := from_input_run bits
  have hb := budget_bound bits
  have hm := run_moreFuel machine (budget bits) (ordinaryBudget bits-budget bits) _ r hr
  rw [Nat.add_sub_of_le hb] at hm
  exact ⟨r,hm,h0,h2,h4,hh,hs.trans hb⟩

end NearCubicWires.RepairOrdinary.ClockFloorLogFromInput
