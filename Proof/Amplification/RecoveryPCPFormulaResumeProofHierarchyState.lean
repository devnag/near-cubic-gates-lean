import Proof.Amplification.RecoveryPCPFormulaResumeProofHierarchyLayout

/-! Exact five-field handoff from the restored source prefix to canonical
proof recovery; every remaining proof/query tape is fresh and blank. -/
namespace NearCubicWires.RepairSource.RecoveryPCPFormulaResumeProofHierarchy
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound OrdinaryOracleCompose
open SourceInterfaces VerifierDecoding ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)

theorem proof_tapes (k : Nat) (word : List Bool) (p : RawProjectionPCP) (R Q : Nat)
    (out : Fin (base source k)→List Bool)
    (h0 : out (RecoveryPCPFormulaResumeProofSource.port source k 0)=frame R.bits)
    (h1 : out (RecoveryPCPFormulaResumeProofSource.port source k 1)=frame Q.bits)
    (h2 : out (RecoveryPCPFormulaResumeProofSource.port source k 2)=QueryBytes.framedCodes (normalizedRows p R Q).flatten)
    (h3 : out (RecoveryPCPFormulaResumeProofSource.port source k 3)=DedupBytes.fields p)
    (h4 : out (RecoveryPCPFormulaResumeProofSource.port source k 4)=CompareMachine.word (Codec.clauses p).length)
    (i : Fin 1184) :
    install (sourceSlots source k) (SourceHandoff.sourceTapes word) out (proofSlots source k i)=
      RecoveryPCPFormulaResumeProof.input p R Q i := by
  rw [RecoveryPCPFormulaResumeProof.input_fields]
  by_cases h0v : i.val=0
  · have he : i=(0 : Fin 1184) := Fin.ext h0v
    subst i
    change install (sourceSlots source k) (SourceHandoff.sourceTapes word) out
      (sourceSlots source k (RecoveryPCPFormulaResumeProofSource.port source k 0))=_
    rw [install_slot (sourceSlots source k) (source_injective source k)]
    exact h0
  by_cases h28v : i.val=28
  · have he : i=(28 : Fin 1184) := Fin.ext h28v
    subst i
    change install (sourceSlots source k) (SourceHandoff.sourceTapes word) out
      (sourceSlots source k (RecoveryPCPFormulaResumeProofSource.port source k 1))=_
    rw [install_slot (sourceSlots source k) (source_injective source k)]
    exact h1
  by_cases h66v : i.val=66
  · have he : i=(66 : Fin 1184) := Fin.ext h66v
    subst i
    change install (sourceSlots source k) (SourceHandoff.sourceTapes word) out
      (sourceSlots source k (RecoveryPCPFormulaResumeProofSource.port source k 2))=_
    rw [install_slot (sourceSlots source k) (source_injective source k)]
    exact h2
  by_cases h67v : i.val=67
  · have he : i=(67 : Fin 1184) := Fin.ext h67v
    subst i
    change install (sourceSlots source k) (SourceHandoff.sourceTapes word) out
      (sourceSlots source k (RecoveryPCPFormulaResumeProofSource.port source k 3))=_
    rw [install_slot (sourceSlots source k) (source_injective source k)]
    exact h3
  by_cases h68v : i.val=68
  · have he : i=(68 : Fin 1184) := Fin.ext h68v
    subst i
    change install (sourceSlots source k) (SourceHandoff.sourceTapes word) out
      (sourceSlots source k (RecoveryPCPFormulaResumeProofSource.port source k 4))=_
    rw [install_slot (sourceSlots source k) (source_injective source k)]
    exact h4
  simp only [proofSlots,RecoveryPCPFormulaResumeProof.fields,h0v,h28v,h66v,h67v,h68v,ite_false]
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
end NearCubicWires.RepairSource.RecoveryPCPFormulaResumeProofHierarchy
