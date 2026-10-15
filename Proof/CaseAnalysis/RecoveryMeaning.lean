import Proof.CaseAnalysis.CloseoutRecoveryColdBudget
import Proof.CaseAnalysis.RecoverySourceIdentity
import Proof.Amplification.RecoveryPCPFormulaResumeHierarchyActual
import Proof.Assembly.SelectedRecoveryIntegration

/-! The physical cold worker asks the global selected PCP's exact full
formula, hence returns its case flag and original canonical description. -/
namespace NearCubicWires.RepairSource.RecoveryBoundedCold
open LocalBitMultitape RepairOrdinary SourceInterfaces ProjectionNormalization
open RecoveryScheduleEnvelope BoundedOracleStructuralCircuit
open CanonicalSATSelfReduction OuterPCPRecovery RecoveryChoice
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
  {k : Nat} (H : OrdinaryHierarchy (fun n=>n^(k+2))) (Cpad : Nat) (hpad : k+3 ≤ Cpad)

abbrev hierarchyPCP:=normalizedSourcePCP source H (HierarchyEncode.encode H Cpad)
  (HierarchyProjection.width source H Cpad) (HierarchyProjection.queries source H Cpad)
  (HierarchyProjection.width_fits source H Cpad hpad) (HierarchyProjection.queries_fit source H Cpad hpad)

theorem payload_hierarchy (d : Nat) (r : InputRequest) :
    payload source k d H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 hpad=
      RecoveryFormulaPrefix.payload (boundedOracleRecoveryFormula (hierarchyPCP source H Cpad hpad) r.2
        (oracleSizeBound d ((hierarchyPCP source H Cpad hpad).nativeWidth r.1))) := by
  have hf:=CloseoutRecoverySourceIdentity.source_formula source H (HierarchyEncode.encode H Cpad)
    (HierarchyProjection.width source H Cpad) (HierarchyProjection.queries source H Cpad)
    (HierarchyProjection.width_fits source H Cpad hpad) (HierarchyProjection.queries_fit source H Cpad hpad)
    r (oracleSizeBound d (HierarchyProjection.width source H Cpad r.1))
  apply Eq.trans _ (congrArg RecoveryFormulaPrefix.payload hf.symm)
  obtain ⟨_,hR,_⟩:=HierarchyStreams.hierarchy_dimensions source H Cpad hpad r
  change RecoveryFormulaPrefix.payload (boundedOracleRecoveryFormula
    (compactProjectionPCP (RecoveryPCPFormulaResumeHierarchy.normalized source k H.coefficient Cpad
      (VerifierEncoding.code H.verifier) (List.ofFn r.2) hpad)) r.2
    (oracleSizeBound d (HierarchyStreams.R source k H.coefficient Cpad
      (VerifierEncoding.code H.verifier) (List.ofFn r.2))))=_
  rw [RecoveryPCPFormulaResumeHierarchy.normalized_hierarchy source H Cpad hpad r,hR]
  rfl

theorem total_hierarchy (d : Nat) (r : InputRequest) :
    total source k d H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2=
      RecoveryFormulaPrefix.oracleCount (hierarchyPCP source H Cpad hpad) d r.1 := by
  obtain ⟨_,hR,_⟩:=HierarchyStreams.hierarchy_dimensions source H Cpad hpad r
  unfold total PCPPNativeHierarchyNodes.width
  rw [hR]
  rfl

theorem flag_hierarchy (d : Nat) (r : InputRequest) :
    RecoveryOracle.correctedSat (RecoveryQuery.code true
      (payload source k d H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 hpad) 0 0)=
      caseTwo (hierarchyPCP source H Cpad hpad) d r.2 := by
  rw [payload_hierarchy source H Cpad hpad]
  exact CloseoutRecoveryCaseQuery.case_query _ d r.2

theorem description_hierarchy (d : Nat) (r : InputRequest)
    (small : SmallOracle (hierarchyPCP source H Cpad hpad) d r.2) :
    RecoveryPrefixBody.search true
      (payload source k d H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 hpad)
      (total source k d H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2) []=
      canonicalBoundedCircuitDescription
        (oracleSizeBound d ((hierarchyPCP source H Cpad hpad).nativeWidth r.1))
        (oracleSelector (hierarchyPCP source H Cpad hpad) d r.2 small).circuit := by
  rw [payload_hierarchy source H Cpad hpad,total_hierarchy source H Cpad hpad]
  exact RecoveryBoundedSearchExecution.canonical_search _ d r.2 small

theorem selected_pcp (sources : EightSources) (clock : OrdinaryClock (fun n=>n^(k+2))) :
    hierarchyPCP (SelectedRecoveryIntegration.fixedProjection sources)
      (sources.hierarchy (fun n=>n^(k+2)) clock).hierarchy
      (SelectedRecoveryIntegration.padding sources k clock) (Nat.le_max_right _ _)=
      (SelectedRecoveryIntegration.outer sources k clock).result.pcp := rfl

end
end NearCubicWires.RepairSource.RecoveryBoundedCold
