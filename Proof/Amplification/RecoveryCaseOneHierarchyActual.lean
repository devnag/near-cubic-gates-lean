import Proof.Amplification.RecoveryCaseOneHierarchyRun

/-! The actual fixed hierarchy input reaches the selected amplifier's
complete output, preserving the same source and total canonical request. -/
namespace NearCubicWires.RepairSource.RecoveryCaseOneHierarchy
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound OrdinaryOracleCompose
open SourceInterfaces VerifierDecoding ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)

theorem hierarchy_ready {c d k : Nat} (amplifier : OrdinaryScheduleAmplifier c d)
    (H : OrdinaryHierarchy (fun n=>n^(k+2))) (Cpad : Nat) (hpad : k+3≤Cpad) (r : InputRequest) :
    ∃ cost,cost≤budget source amplifier k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 hpad ∧ ∃ out,
      Ready RecoveryOracle.correctedSat
        (program source amplifier.constructor.program k H.coefficient Cpad (VerifierEncoding.code H.verifier)) cost
        (SourceHandoff.sourceTapes (HierarchySourceInput.hierarchyInput H r)) out ∧
      out (((RecoveryCaseOneAmplifier.output amplifier.constructor.program).natAdd 1193).natAdd (base source k))=
        frame (amplifierOutput amplifier.toScheduleAmplifier (RecoveryCaseOneRequest.request
          (compactProjectionPCP (RecoveryPCPFormulaResumeHierarchy.hierarchyNormalized source H Cpad hpad r)) r.2)) := by
  obtain ⟨cost,hcost,out,hr,hout⟩ := constructor_ready source amplifier k H.coefficient Cpad
    (VerifierEncoding.code H.verifier) (H.time r.1).bits r.2 hpad
  rw [RecoveryPCPFormulaResumeHierarchy.normalized_hierarchy source H Cpad hpad r] at hout
  exact ⟨cost,hcost,out,hr,hout⟩

end
end NearCubicWires.RepairSource.RecoveryCaseOneHierarchy
