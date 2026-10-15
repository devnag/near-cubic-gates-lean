import Proof.MachineModel.UEmissionAnswer

/-! Whole U through the physical memory result: ordinary external input,
complete event production, delimiter, one whole output rewind and checker. -/
namespace NearCubicWires.RepairOrdinary.UWhole
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def checkedMachine := UMemoryClose.machine UEmission.machine (92 : Fin 157) 156
def input (raw witness : List Bool) := UMemoryClose.inputTapes (UEmission.input raw witness)
def checkedBudget (raw : List Bool) :=
  2*UEmission.budget raw+UAggregateClock.checkerFuel raw.length+10

theorem checked_run (raw witness : List Bool) :
    ∃ r,run checkedMachine (checkedBudget raw) (input raw witness)=some r ∧
      r.steps≤checkedBudget raw ∧ r.final.heads 176=0 ∧
      (r.final.scanned 176=true ↔ UEmission.Accepted raw witness) := by
  obtain ⟨source,hsource,_,hout⟩ := UEmission.whole_run raw witness
  obtain ⟨answer,ha⟩ := UEmission.answer_ready raw witness source.final hout
  obtain ⟨r,hr,hs,_,hh,hflag,_⟩ := UMemoryClose.close_initial_run UEmission.machine 92 156
    (by decide) (UEmission.budget raw) (UEmission.input raw witness) source hsource answer ha.flag ha.stream
  have hb := UAggregateClock.answer_budget_bound raw.length answer ha.bounds
  have hbudget : 2*UEmission.budget raw+UMemoryClose.answerBudget answer+10≤checkedBudget raw := by
    dsimp [checkedBudget]
    omega
  have hmore := run_moreFuel checkedMachine (2*UEmission.budget raw+UMemoryClose.answerBudget answer+10)
    (checkedBudget raw-(2*UEmission.budget raw+UMemoryClose.answerBudget answer+10)) _ r hr
  rw [Nat.add_sub_of_le hbudget] at hmore
  refine ⟨r,hmore,hs.trans hbudget,hh,?_⟩
  change r.final.scanned 176=UMemoryClose.answerValue answer at hflag
  rw [hflag]
  exact ha.meaning

end NearCubicWires.RepairOrdinary.UWhole
