import Proof.Amplification.RecoveryPCPFormulaResumeProofRun

/-! The physically recovered table is the same canonical accepted proof
used by the paper's Case-1 amplifier and hardness argument. -/
namespace NearCubicWires.RepairSource.RecoveryPCPFormulaResumeProof
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound OrdinaryOracleCompose
open SourceInterfaces VerifierDecoding ProjectionNormalization CanonicalRecoveryLanguage BalancedCNFSATEncoding
open CanonicalSATSelfReduction OuterPCPRecovery RecoveryChoice
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem search_proof {M : TimedDecisionMachine} {T : Nat→Nat} (pcp : ProjectionPCP M T)
    {n : Nat} (x : BitInput n) (complete : ∃ proof,∀ randomness,pcp.accepts x proof randomness) :
    RecoveryPrefixBody.search true (balancedCNFPayload (outerProofRecoveryFormula pcp x))
      (RecoveryFormulaPrefix.proofCount pcp n) []=
      List.ofFn (proofSelector pcp x complete).proof := by
  rw [RecoveryPrefixBody.search_canonical true (balancedCNFPayload (outerProofRecoveryFormula pcp x)) (outerProofRecoveryFormula pcp x) _
    (RecoveryFormulaPrefix.payload_decodes _) (outerProofRecoveryFormula_wellSized pcp x)
    (RecoveryFormulaPrefix.proof_range pcp x)]
  rw [proof_prefix pcp x complete (RecoveryFormulaPrefix.proofCount pcp n) (Nat.le_refl _)]
  rw [List.take_of_length_le (by simp [RecoveryFormulaPrefix.proofCount])]

theorem proof_ready (p : RawProjectionPCP) (R Q : Nat) (hr : p.width≤R) (hq : p.queries≤Q)
    {n : Nat} (x : BitInput n)
    (complete : ∃ proof,∀ randomness,(compactProjectionPCP (p.normalized R Q hr hq)).accepts x proof randomness) :
    ∃ cost,cost≤budget R Q (Codec.clauses p).length
      (RecoveryPCPFormulaResume.words (compactProjectionPCP (p.normalized R Q hr hq)) x)
      (balancedCNFPayload (outerProofRecoveryFormula (compactProjectionPCP (p.normalized R Q hr hq)) x)) ∧
    ∃ out,Ready RecoveryOracle.correctedSat program cost (input p R Q) out ∧
      out (1181 : Fin 1184)=frame (List.ofFn
        (proofSelector (compactProjectionPCP (p.normalized R Q hr hq)) x complete).proof) := by
  obtain ⟨cost,hcost,out,hout,ht⟩ := search_ready p R Q hr hq x
  have hword:=search_proof (compactProjectionPCP (p.normalized R Q hr hq)) x complete
  change RecoveryPrefixBody.search true
    (balancedCNFPayload (outerProofRecoveryFormula (compactProjectionPCP (p.normalized R Q hr hq)) x)) (2^R) []=_ at hword
  rw [hword] at ht
  exact ⟨cost,hcost,out,hout,ht⟩

end NearCubicWires.RepairSource.RecoveryPCPFormulaResumeProof
