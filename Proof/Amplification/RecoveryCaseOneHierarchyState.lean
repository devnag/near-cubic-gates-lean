import Proof.Amplification.RecoveryCaseOneHierarchyLayout

/-! The actual source's five outputs feed the whole recovery and amplifier
constructor; every remaining constructor bank is physically blank. -/
namespace NearCubicWires.RepairSource.RecoveryCaseOneHierarchy
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound OrdinaryOracleCompose
open SourceInterfaces VerifierDecoding ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time) (amp : OrdinaryProgram)

theorem construct_tapes (k : Nat) (word : List Bool) (p : RawProjectionPCP) (R Q : Nat)
    (out : Fin (base source k)→List Bool)
    (h0 : out (RecoveryPCPFormulaResumeProofSource.port source k 0)=frame R.bits)
    (h1 : out (RecoveryPCPFormulaResumeProofSource.port source k 1)=frame Q.bits)
    (h2 : out (RecoveryPCPFormulaResumeProofSource.port source k 2)=QueryBytes.framedCodes (normalizedRows p R Q).flatten)
    (h3 : out (RecoveryPCPFormulaResumeProofSource.port source k 3)=DedupBytes.fields p)
    (h4 : out (RecoveryPCPFormulaResumeProofSource.port source k 4)=CompareMachine.word (Codec.clauses p).length)
    (i : Fin (RecoveryCaseOneConstruct.tapes amp)) :
    install (sourceSlots source amp k) (SourceHandoff.sourceTapes word) out (constructSlots source amp k i)=
      RecoveryCaseOneConstruct.input amp p R Q i := by
  rw [RecoveryCaseOneConstruct.input_fields]
  dsimp only [RecoveryCaseOneConstruct.fields]
  by_cases h0v : i.val=0
  · simp only [constructSlots,h0v,ite_true]
    exact (install_slot (sourceSlots source amp k) (source_injective source amp k) _ out
      (RecoveryPCPFormulaResumeProofSource.port source k 0)).trans h0
  by_cases h28v : i.val=28
  · simp only [constructSlots,h28v,ite_true]
    exact (install_slot (sourceSlots source amp k) (source_injective source amp k) _ out
      (RecoveryPCPFormulaResumeProofSource.port source k 1)).trans h1
  by_cases h66v : i.val=66
  · simp only [constructSlots,h66v,ite_true]
    exact (install_slot (sourceSlots source amp k) (source_injective source amp k) _ out
      (RecoveryPCPFormulaResumeProofSource.port source k 2)).trans h2
  by_cases h67v : i.val=67
  · simp only [constructSlots,h67v,ite_true]
    exact (install_slot (sourceSlots source amp k) (source_injective source amp k) _ out
      (RecoveryPCPFormulaResumeProofSource.port source k 3)).trans h3
  by_cases h68v : i.val=68
  · simp only [constructSlots,h68v,ite_true]
    exact (install_slot (sourceSlots source amp k) (source_injective source amp k) _ out
      (RecoveryPCPFormulaResumeProofSource.port source k 4)).trans h4
  simp only [constructSlots,h0v,h28v,h66v,h67v,h68v,ite_false]
  rw [install_other _ _ _ _ (by
    intro j hj
    have hv:=congrArg Fin.val hj
    have hjb:=j.isLt
    change j.val=base source k+i.val at hv
    omega)]
  have hp : 0<base source k := by
    change 0<HierarchyStreams.tapes source k+1
    omega
  simp only [SourceHandoff.sourceTapes,Fin.val_natAdd]
  rw [if_neg (by omega)]

end
end NearCubicWires.RepairSource.RecoveryCaseOneHierarchy
