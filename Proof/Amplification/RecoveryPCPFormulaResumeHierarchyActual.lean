import Proof.Amplification.RecoveryPCPFormulaResumeHierarchyRun

/-! Literal hierarchy-request specialization, preserving the selected source,
length-only normalization and exact original recovery formula. -/
namespace NearCubicWires.RepairSource.RecoveryPCPFormulaResumeHierarchy
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
open SourceInterfaces VerifierDecoding ProjectionNormalization CanonicalRecoveryLanguage BalancedCNFSATEncoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)

def hierarchyNormalized {k : Nat} (H : OrdinaryHierarchy (fun n=>n^(k+2)))
    (Cpad : Nat) (hpad : k+3≤Cpad) (r : InputRequest) :=
  (source.output (HierarchyEncode.encode H Cpad r)).normalized
    (HierarchyProjection.width source H Cpad r.1) (HierarchyProjection.queries source H Cpad r.1)
    (HierarchyProjection.width_fits source H Cpad hpad r) (HierarchyProjection.queries_fit source H Cpad hpad r)

theorem normalized_hierarchy {k : Nat} (H : OrdinaryHierarchy (fun n=>n^(k+2)))
    (Cpad : Nat) (hpad : k+3≤Cpad) (r : InputRequest) :
    normalized source k H.coefficient Cpad (VerifierEncoding.code H.verifier) (List.ofFn r.2) hpad=
      hierarchyNormalized source H Cpad hpad r := by
  obtain ⟨he,hR,hQ⟩ := HierarchyStreams.hierarchy_dimensions source H Cpad hpad r
  unfold normalized hierarchyNormalized
  simp only [he,hR,hQ]

theorem hierarchy_run {k : Nat} (H : OrdinaryHierarchy (fun n=>n^(k+2)))
    (Cpad : Nat) (hpad : k+3≤Cpad) (r : InputRequest) : ∃ receipt,
    run (machine source k H.coefficient Cpad (VerifierEncoding.code H.verifier))
      (budget source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 hpad)
      (SourceHandoff.sourceTapes (HierarchySourceInput.hierarchyInput H r))=some receipt ∧
      receipt.final.tapes ((783 : Fin 785).natAdd (HierarchyStreams.tapes source k))=
        frame (balancedCNFPayload (outerProofRecoveryFormula
          (compactProjectionPCP (hierarchyNormalized source H Cpad hpad r)) r.2)).bits ∧
      receipt.steps≤budget source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 hpad := by
  obtain ⟨receipt,hr,ht,hs⟩ := constructor_run source k H.coefficient Cpad
    (VerifierEncoding.code H.verifier) (H.time r.1).bits r.2 hpad
  rw [normalized_hierarchy source H Cpad hpad r] at ht
  exact ⟨receipt,hr,ht,hs⟩

end
end NearCubicWires.RepairSource.RecoveryPCPFormulaResumeHierarchy
