import Proof.Amplification.RecoveryCaseOneBooleanOutput

/-! The existing generated-table evaluator is actually run and its whole
head return is paid before canonical Boolean encoding. -/
namespace NearCubicWires.RepairSource.RecoveryCaseOneEvaluator
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
open SourceInterfaces ExecutableInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def resetMachine := Rewind.machine GeneratedAmplifier.Runtime.machine
def resetInput (word : List Bool) : Fin 19→List Bool :=
  Fin.addCases (m:=18) (n:=1) (motive:=fun _=>List Bool) (GeneratedAmplifier.Entry.input word) (fun _=>[])
def resetBudget {n : Nat} (f : BoolFunction n) (address : BitInput n) :=
  2*GeneratedAmplifier.Runtime.budget f address+2

theorem reset_input (word : List Bool) (i : Fin 19) :
    resetInput word i=if i.val=0 then frame word else [] := by
  refine Fin.addCases (m:=18) (n:=1) (fun j=>?_) (fun j=>?_) i
  · simp only [resetInput,Fin.addCases_left,GeneratedAmplifier.Entry.input,Fin.val_castAdd]
    simp only [Fin.ext_iff,Fin.val_zero]
    rfl
  · simp only [resetInput,Fin.addCases_right,Fin.val_natAdd]
    rw [if_neg (by omega)]

theorem reset_ready {n : Nat} (f : BoolFunction n) (address : BitInput n) :
    ∃ out,ClockJoin.ReadyRun resetMachine (resetBudget f address)
      (resetInput (GeneratedAmplifier.payload f address)) out ∧ out 17=[f address] := by
  obtain ⟨base,hbase,hsteps,hout,_hhead⟩ := GeneratedAmplifier.Runtime.runtime_run f address
  obtain ⟨r,hr,rt,rh,rs,_⟩ := Rewind.reset_run _ _ _ base hbase
  have hb : 2*base.steps+2≤resetBudget f address := by unfold resetBudget; omega
  have hm:=run_moreFuel resetMachine _ (resetBudget f address-(2*base.steps+2)) _ r hr
  rw [Nat.add_sub_of_le hb] at hm
  exact ⟨r.final.tapes,⟨r,hm,rfl,rh,rs.le.trans hb⟩,(rt 17).trans hout⟩

end
end NearCubicWires.RepairSource.RecoveryCaseOneEvaluator
