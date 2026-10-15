import Proof.Amplification.RecoveryPCPFormulaResumeProofLayout

/-! The canonical-proof graph's complete physical input still consists
of exactly the five original source fields. -/
namespace NearCubicWires.RepairSource.RecoveryPCPFormulaResumeProof
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
open SourceInterfaces VerifierDecoding ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def fields (p : RawProjectionPCP) (R Q : Nat) (i : Fin 1184) : List Bool :=
  if i.val=0 then frame R.bits else if i.val=28 then frame Q.bits else
  if i.val=66 then QueryBytes.framedCodes (normalizedRows p R Q).flatten else
  if i.val=67 then DedupBytes.fields p else if i.val=68 then CompareMachine.word (Codec.clauses p).length else []

theorem input_fields (p : RawProjectionPCP) (R Q : Nat) (i : Fin 1184) : input p R Q i=fields p R Q i := by
  refine Fin.addCases (m:=796) (n:=388) (fun i=>?_) (fun i=>?_) i
  · refine Fin.addCases (m:=789) (n:=7) (fun i=>?_) (fun i=>?_) i
    · refine Fin.addCases (m:=788) (n:=1) (fun i=>?_) (fun i=>?_) i
      · refine Fin.addCases (m:=785) (n:=3) (fun i=>?_) (fun i=>?_) i
        · simp only [input,RecoveryPCPFormulaResumeSearchRequest.input,
            RecoveryPCPFormulaResumeSearch.readyInput,RecoveryPCPFormulaResumeSearch.input,
            Fin.addCases_left,fields,Fin.val_castAdd,RecoveryPCPFormulaResumeCold.input]
          rfl
        · simp only [input,RecoveryPCPFormulaResumeSearchRequest.input,
            RecoveryPCPFormulaResumeSearch.readyInput,RecoveryPCPFormulaResumeSearch.input,
            Fin.addCases_left,Fin.addCases_right,fields,Fin.val_castAdd,Fin.val_natAdd]
          split_ifs <;> first | rfl | omega
      · simp only [input,RecoveryPCPFormulaResumeSearchRequest.input,
          RecoveryPCPFormulaResumeSearch.readyInput,Fin.addCases_left,Fin.addCases_right,
          fields,Fin.val_castAdd,Fin.val_natAdd]
        split_ifs <;> first | rfl | omega
    · simp only [input,RecoveryPCPFormulaResumeSearchRequest.input,Fin.addCases_left,Fin.addCases_right,
        fields,Fin.val_castAdd,Fin.val_natAdd]
      split_ifs <;> first | rfl | omega
  · simp only [input,Fin.addCases_right,fields,Fin.val_natAdd]
    split_ifs <;> first | rfl | omega

end NearCubicWires.RepairSource.RecoveryPCPFormulaResumeProof
