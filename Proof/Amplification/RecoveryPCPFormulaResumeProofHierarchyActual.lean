import Proof.Amplification.RecoveryPCPFormulaResumeProofHierarchyRun

/-! The actual fixed hierarchy and selected source reach their same canonical
accepting proof through one ordinary oracle graph. -/
namespace NearCubicWires.RepairSource.RecoveryPCPFormulaResumeProofHierarchy
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound OrdinaryOracleCompose
open SourceInterfaces VerifierDecoding ProjectionNormalization CanonicalRecoveryLanguage RecoveryChoice
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)

private theorem proof_word_congr {m : TimedDecisionMachine} {time : Nat→Nat}
    {p q : ProjectionPCP m time} (h : p=q) {n : Nat} (x : BitInput n)
    (hp : ∃ proof,∀ randomness,p.accepts x proof randomness)
    (hq : ∃ proof,∀ randomness,q.accepts x proof randomness) :
    frame (List.ofFn (proofSelector p x hp).proof)=frame (List.ofFn (proofSelector q x hq).proof) := by
  subst q
  rfl

theorem hierarchy_ready {k : Nat} (H : OrdinaryHierarchy (fun n=>n^(k+2)))
    (Cpad : Nat) (hpad : k+3≤Cpad) (r : InputRequest)
    (complete : ∃ proof,∀ randomness,
      (compactProjectionPCP (RecoveryPCPFormulaResumeHierarchy.hierarchyNormalized source H Cpad hpad r)).accepts r.2 proof randomness) :
    ∃ cost,cost≤budget source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 hpad ∧ ∃ out,
      Ready RecoveryOracle.correctedSat (program source k H.coefficient Cpad (VerifierEncoding.code H.verifier)) cost
        (SourceHandoff.sourceTapes (HierarchySourceInput.hierarchyInput H r)) out ∧
      out ((1181 : Fin 1184).natAdd (base source k))=frame (List.ofFn
        (proofSelector (compactProjectionPCP
          (RecoveryPCPFormulaResumeHierarchy.hierarchyNormalized source H Cpad hpad r)) r.2 complete).proof) := by
  have hc : ∃ proof,∀ randomness,
      (compactProjectionPCP (RecoveryPCPFormulaResumeHierarchy.normalized source k H.coefficient Cpad
        (VerifierEncoding.code H.verifier) (List.ofFn r.2) hpad)).accepts r.2 proof randomness := by
    rw [RecoveryPCPFormulaResumeHierarchy.normalized_hierarchy source H Cpad hpad r]
    exact complete
  obtain ⟨cost,hcost,out,hr,hout⟩ := proof_ready source k H.coefficient Cpad
    (VerifierEncoding.code H.verifier) (H.time r.1).bits r.2 hpad hc
  refine ⟨cost,hcost,out,hr,?_⟩
  exact hout.trans (proof_word_congr
    (congrArg compactProjectionPCP (RecoveryPCPFormulaResumeHierarchy.normalized_hierarchy source H Cpad hpad r))
    r.2 hc complete)

end
end NearCubicWires.RepairSource.RecoveryPCPFormulaResumeProofHierarchy
