import Proof.Amplification.RecoveryCaseOneBitRun

/-! Reassemble the actual hierarchy input from its two extracted fields,
including the paid return scan required by the enclosing oracle graph. -/
namespace NearCubicWires.RepairSource.RecoveryCaseOneEntryPair
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def machine := Rewind.machine RecoveryPCPFormulaResumeSearchPair.machine
def input (x bound : List Bool) : Fin 6→List Bool :=
  Fin.addCases (m:=5) (n:=1) (motive:=fun _=>List Bool) (RecoveryPCPFormulaResumeSearchPair.input x bound) (fun _=>[])
def budget (x bound : List Bool) := 2*RecoveryPCPFormulaResumeSearchPair.budget x bound+2

theorem ready (x bound : List Bool) : ∃ out,
    ClockJoin.ReadyRun machine (budget x bound) (input x bound) out ∧ out 2=frame x++frame bound := by
  obtain ⟨base,hbase,hout,_hhead,hsteps⟩ := RecoveryPCPFormulaResumeSearchPair.pair_run x bound
  obtain ⟨r,hr,rt,rh,rs,_⟩ := Rewind.reset_run _ _ _ base hbase
  have hb : 2*base.steps+2≤budget x bound := by unfold budget; omega
  have hm:=run_moreFuel machine _ (budget x bound-(2*base.steps+2)) _ r hr
  rw [Nat.add_sub_of_le hb] at hm
  exact ⟨r.final.tapes,⟨r,hm,rfl,rh,rs.le.trans hb⟩,(rt 2).trans hout⟩

end
end NearCubicWires.RepairSource.RecoveryCaseOneEntryPair
