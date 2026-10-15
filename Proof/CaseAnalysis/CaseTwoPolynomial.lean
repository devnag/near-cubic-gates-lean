import Proof.CaseAnalysis.CaseTwoExecutionBudget

/-! Consumer boundary: one actual ordinary Case 2 machine, the same original
canonical circuit and PCPP, and the complete C.12 polynomial run. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Execution
open LocalBitMultitape SourceInterfaces RepairSource RepairRepresentation
open RepairSource.ProjectionNormalization OuterPCPRecovery RecoveryScheduleEnvelope RecoveryPipeline
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem polynomial_run
    (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time) (a : PointwisePCPPAlgorithm)
    {k : ℕ} (H : OrdinaryHierarchy (fun n=>n^(k+2))) (Cpad : ℕ)
    (hcoeff : H.coefficient≤Cpad) (hpad : k+3≤Cpad) (degree D copies : ℕ) (hD : 1≤D) :
    ∃ C E : ℕ,1≤C ∧
      ∀ (r : InputRequest)
        (oracle : BooleanCircuit (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2)),
        oracle.size≤oracleSizeBound degree
          (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2) →
        ∀ (target : ℕ) (point : BitInput target)
          (hcb : (a.output (WholeBlock.request source a H Cpad hpad r oracle)).clauseBits≤
            CloseoutLanguage.clauseWidth D (WholeBlock.request source a H Cpad hpad r oracle).arity)
          (hfit : copies*((WholeBlock.request source a H Cpad hpad r oracle).arity+
            CloseoutLanguage.clauseWidth D (WholeBlock.request source a H Cpad hpad r oracle).arity+1)≤target),
        let req:=WholeBlock.request source a H Cpad hpad r oracle
        let R:=PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2
        let B:=oracleSizeBound degree R
        let hierarchy:=HierarchySourceInput.hierarchyInput H r
        let description:=frame (canonicalBoundedCircuitDescription B oracle)
        let address:=frame (List.ofFn point)
        ∃ out,ClockJoin.ReadyRun
          (machine source a k D copies H.coefficient Cpad (VerifierEncoding.code H.verifier))
          (C*(r.1+2^target+1)^E)
          (input source a k D copies hierarchy description address R B) out ∧
          out (outputSlot source a k D copies)=
            [padCore (xorPower (CloseoutLanguage.paddedUnsigned (a.output req) hcb) copies) hfit point] ∧
          out (old source a k D copies 0)=hierarchy ∧
          out (old source a k D copies 1)=description ∧ out (old source a k D copies 2)=address:=by
  obtain ⟨C,E,hC,hbudget⟩:=budget_polynomial source a H Cpad hcoeff hpad degree D copies
  refine ⟨C,E,hC,fun r oracle hc target point hcb hfit=>?_⟩
  obtain ⟨out,hr,hbit,hH,hdesc,haddr⟩:=run source a H Cpad hcoeff hpad r oracle
    (oracleSizeBound degree _) D copies hc hD point hcb hfit
  exact ⟨out,ClockJoin.enlarge _ _ _ _ _ hr (hbudget r oracle hc target point hcb),hbit,hH,hdesc,haddr⟩

end
end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Execution
