import Proof.CaseAnalysis.CommonProgramSourceRun

/-! One source-selected capacity pays every native recovery request and
the resulting full recovery budget. All coefficients are fixed in advance. -/
namespace NearCubicWires.RepairSource.CloseoutCommonProgram
open LocalBitMultitape RepairOrdinary SourceInterfaces ProjectionNormalization
open SelectedRecoveryIntegration RecoveryScheduleEnvelope BoundedOracleStructuralCircuit
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem exists_fits (p : Parameters) :
    ∃ A B0 : ℕ,∀ n (r : InputRequest),r.1 ≤ 2^n → R p r ≤ n →
      Fits p r (CloseoutCapacity.capacity A B0 n):=by
  obtain ⟨A,B0,h⟩:=CloseoutRecoveryCapacity.actual_capacity_with_source
    (source p) (hierarchy p) (pad p) p.degree (pad_coefficient p) (pad_large p)
  refine ⟨A,B0,?_⟩
  intro n r hn hr
  obtain ⟨hN,hW,_hR,_hQ,_hB,hbytes,htwo⟩:=h n r hn hr
  exact ⟨hN,hW,hbytes,htwo⟩

theorem recovery_polynomial (p : Parameters) :
    ∃ C E : ℕ,1 ≤ C ∧ ∀ (r : InputRequest) (W : ℕ),Fits p r W →
      recoveryBudget p r W ≤ C*(W+1)^E:=by
  obtain ⟨C,E,hC,h⟩:=RecoveryBoundedCold.polynomial_budget
    (source p) (hierarchy p) (pad p) p.degree (pad_coefficient p) (pad_large p)
  refine ⟨C,E,hC,?_⟩
  intro r W fits
  have hR:=native_width p r
  have hQ:=native_queries p r
  have hP:=native_source p r
  dsimp only [code] at hR hQ hP
  apply h r W fits.length
  · rw [hR,hQ,hP]
    exact fits.workspace
  · rw [hR]
    exact fits.two

theorem recovery_description (p : Parameters) (r : InputRequest)
    (small : RecoveryChoice.SmallOracle (globalPCP p) p.degree r.2) :
    recoveryDescription p r=frame (CanonicalSATSelfReduction.recoveredPrefix
      (BoundedOracleStructuralCircuit.descriptionWidth (R p r) (B p r))
      (boundedOracleRecoveryFormula (globalPCP p) r.2 (B p r))):=by
  apply congrArg frame
  exact (RecoveryBoundedCold.description_hierarchy (source p) (hierarchy p) (pad p)
    (pad_large p) p.degree r small).trans
      (CloseoutCaseTwo.Selected.recovered_description (globalPCP p) p.degree r.2 small).symm

end
end NearCubicWires.RepairSource.CloseoutCommonProgram
