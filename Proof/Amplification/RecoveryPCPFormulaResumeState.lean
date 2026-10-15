import Proof.Amplification.RecoveryPCPFormulaResumeTapeState

/-! Instantiation of the tape-only handoff with the actual scalar outputs.
The large capacity words remain data rather than expanded proof terms. -/
namespace NearCubicWires.RepairSource.RecoveryPCPFormulaResumeCold
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
open SourceInterfaces VerifierDecoding ProjectionNormalization CanonicalRecoveryLanguage
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem scalar_dock (p : RawProjectionPCP) (R Q : Nat) (out : Fin 66→List Bool)
    (o3 : out 3=CompareMachine.word R)
    (o17 : out 17=List.replicate (RecoveryProjectionRows.capacity R) true)
    (o31 : out 31=CompareMachine.word Q)
    (o37 : out 37=List.replicate (RecoverySourceClauseLoad.uniformBudget Q R) true)
    (o58 : out 58=CompareMachine.word (2^R-1))
    (o61 : out 61=List.replicate (2^R) true)
    (o64 : out 64=frame (List.replicate R false)) (i : Fin 716) :
    install scalarSlots (input p R Q) out (formulaSlots i)=
      RecoveryPCPFormulaResumeSerialize.entryData p R Q (RecoverySourceClauseLoad.uniformBudget Q R) i := by
  rw [scalar_data,entry_lookup]
  simp only [dockedLookup,entryLookup,o3,o17,o31,o37,o58,o61,o64,zero_randomness]

end NearCubicWires.RepairSource.RecoveryPCPFormulaResumeCold
