import Proof.CaseAnalysis.CaseTwoSelectedOutputRun

/-! The selected Case2 branch returns the exact framed Boolean expected by
ordinary common dispatch, charging the complete framing worker and connection. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.SelectedOutput
open LocalBitMultitape SourceInterfaces RepairSource RepairRepresentation
open SelectedRecoveryIntegration CloseoutLanguage RecoveryScheduleEnvelope ProjectionNormalization
open RecoveryPipeline OuterPCPRecovery CanonicalSATSelfReduction BoundedOracleStructuralCircuit
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem joined_budget (C E n : ℕ) : C*(2^n+1)^E+9 ≤ (C+9)*(2^n+1)^E:=by
  have h:1 ≤ (2^n+1)^E:=Nat.one_le_pow _ _ (Nat.succ_le_succ (Nat.zero_le (2^n)))
  rw [Nat.add_mul]
  have h9:=Nat.mul_le_mul_left 9 h
  omega

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
      ∀ (x : BitInput (2^s)),cutoff ≤ 2^s →
      ∀ (_small : RecoveryChoice.SmallOracle p degree x),
      let B:=oracleSizeBound degree R
      let hierarchy:=HierarchySourceInput.hierarchyInput H ⟨2^s,x⟩
      let description:=frame (recoveredPrefix (descriptionWidth R B)
        (boundedOracleRecoveryFormula p x B))
      let address:=frame (List.ofFn point)
      ∃ out,ClockJoin.ReadyRun
        (machine source (selectedPCPP sources) k D copies H.coefficient
          (padding sources k clock) (VerifierEncoding.code H.verifier))
        (C*(2^n+1)^E)
        (input source (selectedPCPP sources) k D copies
          (Execution.input source (selectedPCPP sources) k D copies hierarchy description address R B)) out ∧
        out (fresh source (selectedPCPP sources) k D copies 0)=
          frame (core p (selectedPCPP sources) (selectedAmplifier sources.amplification degree)
            x copies (clauseWidth D R) n point).toNat.bits ∧
        out (old source (selectedPCPP sources) k D copies
          (Execution.old source (selectedPCPP sources) k D copies 0))=hierarchy ∧
        out (old source (selectedPCPP sources) k D copies
          (Execution.old source (selectedPCPP sources) k D copies 1))=description ∧
        out (old source (selectedPCPP sources) k D copies
          (Execution.old source (selectedPCPP sources) k D copies 2))=address :=by
  obtain ⟨cutoff,hcutoff,selected⟩:=Selected.selected_polynomial_run sources degree D hD clauses
  refine ⟨cutoff,hcutoff,?_⟩
  intro k clock copies hcopies
  obtain ⟨C,E,hC,actual⟩:=selected k clock copies hcopies
  refine ⟨C+9,E,by omega,?_⟩
  intro n point source H p s R x hcut small B hierarchy description address
  obtain ⟨raw,rawRun,rawValue,h0,h1,h2⟩:=actual n point x hcut small
  obtain ⟨out,framed,framedValue,retained⟩:=run source (selectedPCPP sources) k D copies
    H.coefficient (padding sources k clock) (C*(2^n+1)^E) (VerifierEncoding.code H.verifier)
    _ raw (core p (selectedPCPP sources) (selectedAmplifier sources.amplification degree)
      x copies (clauseWidth D R) n point) rawRun rawValue
  refine ⟨out,ClockJoin.enlarge _ _ _ _ _ framed (joined_budget C E n),framedValue,?_,?_,?_⟩
  · exact (retained _ (original_port_outside source (selectedPCPP sources) k D copies 0)).trans h0
  · exact (retained _ (original_port_outside source (selectedPCPP sources) k D copies 1)).trans h1
  · exact (retained _ (original_port_outside source (selectedPCPP sources) k D copies 2)).trans h2

end
end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.SelectedOutput
