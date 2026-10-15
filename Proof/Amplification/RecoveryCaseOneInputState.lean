import Proof.Amplification.RecoveryCaseOneInputLayout

/-! Exact tape handoffs in the Case-1 graph. The dimension is physically
archived; the recovered proof and fresh assembler bank are passed unchanged. -/
namespace NearCubicWires.RepairSource.RecoveryCaseOneInput
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound OrdinaryOracleCompose
open SourceInterfaces VerifierDecoding ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem original_input (p : RawProjectionPCP) (R Q : Nat) (i : Fin 1184) :
    input p R Q (proofSlots i)=RecoveryPCPFormulaResumeProof.input p R Q i := by
  simp only [input,proofSlots,Fin.addCases_left]

theorem fresh_input (p : RawProjectionPCP) (R Q : Nat) (i : Fin 1193) (hi : (1184 : Nat)≤(i : Fin 1193).val) :
    input p R Q i=[] := by
  let j : Fin 9:=⟨i.val-1184,by have hj:=i.isLt; omega⟩
  have he : i=j.natAdd 1184 := by apply Fin.ext; dsimp [j]; omega
  rw [he]
  simp only [input,Fin.addCases_right]

theorem archive_input (p : RawProjectionPCP) (R Q : Nat) (i : Fin 4) :
    input p R Q (archiveSlots i)=RecoveryCaseOneArchive.input R.bits i := by
  fin_cases i
  · exact RecoveryPCPFormulaResumeProof.input_fields p R Q 0
  · exact fresh_input p R Q 1184 (by decide)
  · exact fresh_input p R Q 1185 (by decide)
  · exact fresh_input p R Q 1186 (by decide)

theorem archived_original (p : RawProjectionPCP) (R Q : Nat) (archive : Fin 4→List Bool)
    (h0 : archive 0=frame R.bits) (i : Fin 1184) :
    install archiveSlots (input p R Q) archive (proofSlots i)=RecoveryPCPFormulaResumeProof.input p R Q i := by
  by_cases hi : i=0
  · subst i
    exact (install_slot archiveSlots archive_injective _ archive 0).trans
      (h0.trans (RecoveryPCPFormulaResumeProof.input_fields p R Q 0).symm)
  · rw [install_other _ _ _ _ (by
      intro j hj
      have hv:=congrArg (fun i : Fin 1193=>i.val) hj
      have hn : i.val≠0 := fun h=>hi (Fin.ext h)
      have hb:=i.isLt
      simp only [proofSlots,Fin.val_castAdd] at hv
      fin_cases j <;> simp only [archiveSlots] at hv <;> norm_num at hv <;> omega)]
    exact original_input p R Q i

theorem proof_away (i : Fin 1193) (hi : (1184 : Nat)≤(i : Fin 1193).val) : ∀ j,proofSlots j≠i := by
  intro j h
  have hv:=congrArg (fun i : Fin 1193=>i.val) h
  have hj:=j.isLt
  change j.val=i.val at hv
  omega

theorem archive_away (i : Fin 1193) (hi : (1187 : Nat)≤(i : Fin 1193).val) : ∀ j,archiveSlots j≠i := by
  intro j h
  have hv:=congrArg (fun i : Fin 1193=>i.val) h
  fin_cases j <;> simp only [archiveSlots] at hv <;> norm_num at hv <;> omega

theorem payload_input (p : RawProjectionPCP) (R Q : Nat) (archive : Fin 4→List Bool)
    (h1 : archive 1=frame R.bits) (proof : Fin 1184→List Bool) (table : List Bool)
    (ht : proof 1181=frame table) (i : Fin 8) :
    install proofSlots (install archiveSlots (input p R Q) archive) proof (payloadSlots i)=
      RecoveryCaseOnePayload.fields R.bits table i := by
  by_cases h0 : i=0
  · subst i
    rw [show payloadSlots 0=(1184 : Fin 1193) from rfl,install_other _ _ _ _ (proof_away _ (by decide))]
    exact (install_slot archiveSlots archive_injective _ archive 1).trans h1
  by_cases h2 : i=1
  · subst i
    exact (install_slot proofSlots proof_injective _ proof 1181).trans ht
  · have hv : (2 : Nat)≤(i : Fin 8).val := by
      have hn0 : i.val≠0 := fun h=>h0 (Fin.ext h)
      have hn1 : i.val≠1 := fun h=>h2 (Fin.ext h)
      omega
    have hf : 1187≤(payloadSlots i).val := by simp only [payloadSlots,h0,h2,ite_false]; omega
    rw [install_other _ _ _ _ (proof_away _ (by omega)),install_other _ _ _ _ (archive_away _ hf),
      fresh_input p R Q _ (by omega)]
    simp only [RecoveryCaseOnePayload.fields,h0,h2,ite_false]

end
end NearCubicWires.RepairSource.RecoveryCaseOneInput
