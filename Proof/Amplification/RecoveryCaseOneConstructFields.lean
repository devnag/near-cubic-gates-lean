import Proof.Amplification.RecoveryCaseOneConstructRun

/-! The complete recovery/amplifier graph still starts with exactly the
five original source fields; all program scratch tapes are empty. -/
namespace NearCubicWires.RepairSource.RecoveryCaseOneConstruct
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
open SourceInterfaces VerifierDecoding ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def fields (program : OrdinaryProgram) (p : RawProjectionPCP) (R Q : Nat) (i : Fin (tapes program)) : List Bool :=
  if i.val=0 then frame R.bits else if i.val=28 then frame Q.bits else
  if i.val=66 then QueryBytes.framedCodes (normalizedRows p R Q).flatten else
  if i.val=67 then DedupBytes.fields p else if i.val=68 then CompareMachine.word (Codec.clauses p).length else []

theorem input_fields (program : OrdinaryProgram) (p : RawProjectionPCP) (R Q : Nat) (i : Fin (tapes program)) :
    input program p R Q i=fields program p R Q i := by
  refine Fin.addCases (m:=1193) (n:=RecoveryCaseOneAmplifier.tapes program) (fun i=>?_) (fun i=>?_) i
  · refine Fin.addCases (m:=1184) (n:=9) (fun i=>?_) (fun i=>?_) i
    · simp only [input,RecoveryCaseOneInput.input,Fin.addCases_left]
      rw [RecoveryPCPFormulaResumeProof.input_fields]
      rfl
    · simp only [input,RecoveryCaseOneInput.input,Fin.addCases_left,Fin.addCases_right,
        fields,Fin.val_castAdd,Fin.val_natAdd]
      split_ifs <;> first | rfl | omega
  · simp only [input,Fin.addCases_right,fields,Fin.val_natAdd]
    split_ifs <;> first | rfl | omega

end
end NearCubicWires.RepairSource.RecoveryCaseOneConstruct
