import Proof.Amplification.RecoveryPCPFormulaResumeProofHierarchyState

/-! The selected hierarchy source is now consumed through the complete
ordinary canonical-proof recovery graph, with the same canonical table
and all physical source, formula, query and return work charged. -/
namespace NearCubicWires.RepairSource.RecoveryPCPFormulaResumeProofHierarchy
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound OrdinaryOracleCompose
open SourceInterfaces VerifierDecoding ProjectionNormalization CanonicalRecoveryLanguage BalancedCNFSATEncoding RecoveryChoice
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)

def budget (k CH Cpad : Nat) (code : List Bool) {n : Nat} (x : BitInput n) (hpad : k+3≤Cpad) :=
  RecoveryPCPFormulaResumeProofSource.budget source k CH Cpad code (List.ofFn x)+2+
    RecoveryPCPFormulaResumeProof.budget
      (HierarchyStreams.R source k CH Cpad code (List.ofFn x))
      (HierarchyStreams.Q source k CH Cpad code (List.ofFn x))
      (Codec.clauses (source.output (HierarchyStreams.request k CH Cpad code (List.ofFn x)))).length
      (RecoveryPCPFormulaResume.words
        (compactProjectionPCP (RecoveryPCPFormulaResumeHierarchy.normalized source k CH Cpad code (List.ofFn x) hpad)) x)
      (balancedCNFPayload (outerProofRecoveryFormula
        (compactProjectionPCP (RecoveryPCPFormulaResumeHierarchy.normalized source k CH Cpad code (List.ofFn x) hpad)) x))

theorem proof_ready (k CH Cpad : Nat) (code bound : List Bool) {n : Nat} (x : BitInput n)
    (hpad : k+3≤Cpad)
    (complete : ∃ proof,∀ randomness,
      (compactProjectionPCP (RecoveryPCPFormulaResumeHierarchy.normalized source k CH Cpad code (List.ofFn x) hpad)).accepts x proof randomness) :
    ∃ cost,cost≤budget source k CH Cpad code x hpad ∧ ∃ out,
      Ready RecoveryOracle.correctedSat (program source k CH Cpad code) cost
        (SourceHandoff.sourceTapes (frame (List.ofFn x)++frame bound)) out ∧
      out ((1181 : Fin 1184).natAdd (base source k))=frame (List.ofFn
        (proofSelector (compactProjectionPCP
          (RecoveryPCPFormulaResumeHierarchy.normalized source k CH Cpad code (List.ofFn x) hpad)) x complete).proof) := by
  obtain ⟨src,hsrc,s0,s1,s2,s3,s4⟩ := RecoveryPCPFormulaResumeProofSource.source_ready source k CH Cpad code (List.ofFn x) bound hpad
  let ambient : Fin (tapes source k)→List Bool := SourceHandoff.sourceTapes (frame (List.ofFn x)++frame bound)
  let a:=install (sourceSlots source k) ambient src
  have ha:=hsrc.focus (sourceSlots source k) (source_injective source k) ambient (by intro i; rfl)
  obtain ⟨ca,hca,haOracle⟩ := RecoveryPrefixCold.ordinary_ready (o:=RecoveryOracle.correctedSat)
    (ports source k) (sourceMachine source k CH Cpad code) _ _ ha
  obtain ⟨cb,hcb,proofOut,hproof,proofValue⟩ := RecoveryPCPFormulaResumeProof.proof_ready
    (source.output (HierarchyStreams.request k CH Cpad code (List.ofFn x)))
    (HierarchyStreams.R source k CH Cpad code (List.ofFn x))
    (HierarchyStreams.Q source k CH Cpad code (List.ofFn x))
    (Dimensions.width_fits source _ (RecoveryPCPFormulaResumeHierarchy.request_positive k CH Cpad code (List.ofFn x) hpad))
    (Dimensions.queries_fit source _ (RecoveryPCPFormulaResumeHierarchy.request_positive k CH Cpad code (List.ofFn x) hpad)) x complete
  have hbOracle:=hproof.focus (ports source k) (proofSlots source k) (proof_injective source k) (by rfl) a
    (proof_tapes source k (frame (List.ofFn x)++frame bound) _ _ _ src s0 s1 s2 s3 s4)
  have trA:=Ready.call (ports source k) (pieces source k CH Cpad code) 0 (next source k CH Cpad code)
    0 1 haOracle (by intro q; rfl)
  have trB:=Ready.stop (ports source k) (pieces source k CH Cpad code) 0 (next source k CH Cpad code)
    1 hbOracle (by intro q; rfl)
  have trace:=trans trA trB
  have hstart : controlConfig (RecoveryCalls.code (fun j=>(pieces source k CH Cpad code j).states) 0)
      (initialConfiguration (pieces source k CH Cpad code 0).machine ambient)=
      initialConfiguration (program source k CH Cpad code).base.machine ambient := rfl
  rw [hstart] at trace
  refine ⟨(ca+1)+(cb+1),?_,install (proofSlots source k) a proofOut,?_,?_⟩
  · unfold budget RecoveryPCPFormulaResumeHierarchy.normalized
    omega
  · refine ⟨_,trace,?_,fun _=>rfl,rfl⟩
    simp [program,Ports.program,graph,RecoveryCalls.machine,RecoveryCalls.stopped]
  · exact (install_slot (proofSlots source k) (proof_injective source k) a proofOut (1181 : Fin 1184)).trans proofValue

end
end NearCubicWires.RepairSource.RecoveryPCPFormulaResumeProofHierarchy
