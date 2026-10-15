import Proof.Amplification.RecoveryCaseOneEvaluatorReady
import Proof.PCP.ProjectionRealization

/-! The constructed request belongs to the selected global outer PCP.
Its constant-input serialization view has exactly the same formula, case
predicate and searched proof at this request. -/
namespace NearCubicWires.RepairSource.RecoveryCaseOneRequest
open SourceInterfaces CanonicalRecoveryLanguage
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem source_request {v : OrdinaryVerifier} {T U : Nat→Nat}
    (source : ProjectionSourceAlgorithm v U) (H : OrdinaryHierarchy T)
    (encode : InputRequest→InputRequest) (R Q : Nat→Nat)
    (hr : ∀ r : InputRequest,(source.output (encode r)).width≤R r.1)
    (hq : ∀ r : InputRequest,(source.output (encode r)).queries≤Q r.1) (r : InputRequest) :
    request (normalizedSourcePCP source H encode R Q hr hq) r.2=
      request (compactProjectionPCP ((source.output (encode r)).normalized (R r.1) (Q r.1) (hr r) (hq r))) r.2 := by
  rcases r with ⟨n,x⟩
  have hlit (randomness : BitInput (R n)) (literal : Literal (Q n)) :
      outerProofLiteral (normalizedSourcePCP source H encode R Q hr hq) x randomness literal=
        outerProofLiteral
          (compactProjectionPCP ((source.output (encode ⟨n,x⟩)).normalized (R n) (Q n) (hr ⟨n,x⟩) (hq ⟨n,x⟩)))
          x randomness literal := by
    cases literal <;> rfl
  have hrow (randomness : BitInput (R n)) :
      outerProofRowFormula (normalizedSourcePCP source H encode R Q hr hq) x randomness=
        outerProofRowFormula
          (compactProjectionPCP ((source.output (encode ⟨n,x⟩)).normalized (R n) (Q n) (hr ⟨n,x⟩) (hq ⟨n,x⟩)))
          x randomness := by
    unfold outerProofRowFormula
    apply List.map_congr_left
    intro clause _
    simp only [outerProofClause,hlit]
  have hf : outerProofRecoveryFormula (normalizedSourcePCP source H encode R Q hr hq) x=
      outerProofRecoveryFormula
        (compactProjectionPCP ((source.output (encode ⟨n,x⟩)).normalized (R n) (Q n) (hr ⟨n,x⟩) (hq ⟨n,x⟩))) x := by
    exact congrArg (fun rows=>CircuitInputCNF.circuitInputTautologies (2^R n)++rows)
      (congrArg (fun f=>List.flatMap f (allBitInputs (R n))) (funext hrow))
  apply congrArg (fun f : BoolFunction (R n)=>(⟨R n,f⟩ : ExecutableInterfaces.AmplifierRequest))
  funext address
  simp only [OuterPCPRecovery.proofFunction,proof,table,hf]
  rfl

theorem source_case {v : OrdinaryVerifier} {T U : Nat→Nat}
    (source : ProjectionSourceAlgorithm v U) (H : OrdinaryHierarchy T)
    (encode : InputRequest→InputRequest) (R Q : Nat→Nat)
    (hr : ∀ r : InputRequest,(source.output (encode r)).width≤R r.1)
    (hq : ∀ r : InputRequest,(source.output (encode r)).queries≤Q r.1) (r : InputRequest) (d : Nat) :
    RecoveryChoice.caseTwo (normalizedSourcePCP source H encode R Q hr hq) d r.2=
      RecoveryChoice.caseTwo
        (compactProjectionPCP ((source.output (encode r)).normalized (R r.1) (Q r.1) (hr r) (hq r))) d r.2 := rfl

end
end NearCubicWires.RepairSource.RecoveryCaseOneRequest
