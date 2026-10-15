import Proof.Amplification.RecoveryPCPFormulaResumeSearchPair

/-! Measure the emitted two-field request, pay its rewind, and write the
outer framing required by the already checked canonical prefix search. -/
namespace NearCubicWires.RepairSource.RecoveryPCPFormulaResumeSearchPair
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def framedMachine := AppendOutputFrame.machine machine (2 : Fin 5)
def fields (left right : List Bool) (i : Fin 9) : List Bool :=
  if i=0 then frame left else if i=1 then frame right else []
def framedBudget (left right : List Bool) := 2*budget left right+4*(frame left++frame right).length+7

theorem framed_input (left right : List Bool) : AppendOutputFrame.input (input left right)=fields left right := by
  funext i; fin_cases i <;> rfl

theorem framed_ready (left right : List Bool) : ∃ out,
    ClockJoin.ReadyRun framedMachine (framedBudget left right) (fields left right) out ∧
      out 7=frame (frame left++frame right) := by
  obtain ⟨base,hbase,bt,bh,bSteps⟩ := pair_run left right
  obtain ⟨r,hr,rt,rh,rSteps⟩ := AppendOutputFrame.frame_run machine 2 forward _ _ base hbase _ bt bh
  have hbudget : 2*base.steps+4*(frame left++frame right).length+7≤framedBudget left right := by
    unfold framedBudget
    omega
  have hm:=run_moreFuel framedMachine _
    (framedBudget left right-(2*base.steps+4*(frame left++frame right).length+7)) _ r hr
  rw [Nat.add_sub_of_le hbudget,framed_input] at hm
  exact ⟨r.final.tapes,⟨r,hm,rfl,rh,rSteps.trans hbudget⟩,rt⟩

end NearCubicWires.RepairSource.RecoveryPCPFormulaResumeSearchPair
