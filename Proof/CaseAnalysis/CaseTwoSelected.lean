import Proof.CaseAnalysis.CaseTwoSelectedNormalized
import Proof.CaseAnalysis.CaseTwoSelectedDescription

/-! The actual Case2 execution consumes the recovered canonical description
and returns the same selected common core. One source cutoff is chosen before
the hierarchy clock, and the original source length is charged to final length. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Selected
open LocalBitMultitape SourceInterfaces RepairSource RepairRepresentation
open SelectedRecoveryIntegration CloseoutLanguage RecoveryScheduleEnvelope
open ProjectionNormalization
open RecoveryPipeline OuterPCPRecovery CanonicalSATSelfReduction BoundedOracleStructuralCircuit
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem selected_polynomial_run (sources : EightSources) (degree D : ℕ) (hD : 1 ≤ D)
    (clauses : ClauseReady sources degree D) :
    ∃ cutoff : ℕ,1 ≤ cutoff ∧
      ∀ (k : ℕ) (clock : OrdinaryClock (fun m=>m^(k+2))) (copies : ℕ),1 ≤ copies →
      ∃ C E : ℕ,1 ≤ C ∧ ∀ (n : ℕ) (point : BitInput n),
      let source:=fixedProjection sources
      let H:=(sources.hierarchy (fun m=>m^(k+2)) clock).hierarchy
      let p:=(outer sources k clock).result.pcp
      let s:=selectedIndex (widthAt sources k clock copies D) n
      let R:=p.nativeWidth (2^s)
      ∀ (input : BitInput (2^s)),cutoff ≤ 2^s →
      ∀ (_small : RecoveryChoice.SmallOracle p degree input),
      let B:=oracleSizeBound degree R
      let hierarchy:=HierarchySourceInput.hierarchyInput H ⟨2^s,input⟩
      let description:=frame (recoveredPrefix (descriptionWidth R B)
        (boundedOracleRecoveryFormula p input B))
      let address:=frame (List.ofFn point)
      ∃ out,ClockJoin.ReadyRun
        (Execution.machine source (selectedPCPP sources) k D copies H.coefficient
          (padding sources k clock) (VerifierEncoding.code H.verifier))
        (C*(2^n+1)^E)
        (Execution.input source (selectedPCPP sources) k D copies hierarchy description address R B) out ∧
        out (Execution.outputSlot source (selectedPCPP sources) k D copies)=
          [core p (selectedPCPP sources) (selectedAmplifier sources.amplification degree)
            input copies (clauseWidth D R) n point] ∧
        out (Execution.old source (selectedPCPP sources) k D copies 0)=hierarchy ∧
        out (Execution.old source (selectedPCPP sources) k D copies 1)=description ∧
        out (Execution.old source (selectedPCPP sources) k D copies 2)=address := by
  obtain ⟨cutoff,hcutoff,live⟩:=case_two_live_cutoff sources degree D clauses
  refine ⟨cutoff,hcutoff,?_⟩
  intro k clock copies hcopies
  let source:=fixedProjection sources
  let H:=(sources.hierarchy (fun m=>m^(k+2)) clock).hierarchy
  let Cpad:=padding sources k clock
  have hcoeff:H.coefficient ≤ Cpad:=Nat.le_max_left _ _
  have hpad:k+3 ≤ Cpad:=Nat.le_max_right _ _
  obtain ⟨C,E,hC,run⟩:=normalized_polynomial_run source (selectedPCPP sources)
    H Cpad hcoeff hpad degree D copies hD
  have hCE : 1 ≤ C*2^E := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul hC (Nat.one_le_pow _ _ (by decide : 1 ≤ 2))
  refine ⟨C*2^E,E,hCE,?_⟩
  intro n point source' H' p s R input hcut small B hierarchy description address
  let oracle:=(RecoveryChoice.oracleSelector p degree input small).circuit
  have bounded:oracle.size ≤ oracleSizeBound degree R:=
    (RecoveryChoice.oracleSelector p degree input small).sizeBounded
  obtain ⟨_,hN,_,arity,hclause,hfit⟩:=
    live k clock copies n input oracle hcopies hcut bounded
  change (CloseoutWitnessPolicy.request sources k clock input oracle).arity=R at arity
  change copies*((CloseoutWitnessPolicy.request sources k clock input oracle).arity+
    clauseWidth D R+1) ≤ n at hfit
  have hcb : ((selectedPCPP sources).output
      (CloseoutWitnessPolicy.request sources k clock input oracle)).clauseBits ≤
      clauseWidth D (CloseoutWitnessPolicy.request sources k clock input oracle).arity :=
    hclause.trans_eq (congrArg (clauseWidth D) arity.symm)
  have fit : copies*((CloseoutWitnessPolicy.request sources k clock input oracle).arity+
      clauseWidth D (CloseoutWitnessPolicy.request sources k clock input oracle).arity+1) ≤ n := by
    simpa only [←arity] using hfit
  obtain ⟨out,hrun,hout,h0,h1,h2⟩:=run ⟨2^s,input⟩ oracle bounded n point hcb fit
  change ClockJoin.ReadyRun
    (Execution.machine source (selectedPCPP sources) k D copies H.coefficient Cpad
      (VerifierEncoding.code H.verifier)) (C*(2^s+2^n+1)^E)
    (Execution.input source (selectedPCPP sources) k D copies hierarchy
      (frame (canonicalBoundedCircuitDescription B oracle)) address R B) out at hrun
  change out (Execution.old source (selectedPCPP sources) k D copies 1)=
    frame (canonicalBoundedCircuitDescription B oracle) at h1
  have hdescription : description=frame (canonicalBoundedCircuitDescription B oracle):=
    congrArg frame (recovered_description p degree input small)
  rw [←hdescription] at hrun h1
  have hcore:=core_case_two p (selectedPCPP sources)
    (selectedAmplifier sources.amplification degree) input copies
    (clauseWidth D (CloseoutWitnessPolicy.request sources k clock input oracle).arity) n small hcb fit
  refine ⟨out,ClockJoin.enlarge _ _ _ _ _ hrun (selected_budget C E (2^s) n hN),?_,h0,h1,h2⟩
  rw [←arity,hcore]
  exact hout

end
end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Selected
