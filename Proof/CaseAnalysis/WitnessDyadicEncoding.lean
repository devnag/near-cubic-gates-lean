import Proof.CaseAnalysis.WitnessBoundedEncoding
import Proof.CaseAnalysis.WitnessSourceSize

/-! At one eventual dyadic onset, every actual source-dependent honest
family fits the unchanged ordinary witness cap and preserves its exact fields. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.BoundedFields
open SourceInterfaces RepairSource RepairRepresentation CanonicalWitnessCodec
open CloseoutWitnessPolicy SelectedRecoveryIntegration PolynomialSchedule RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem encoded_eventually (sources : EightSources) (k : ℕ)
    (clock : OrdinaryClock (fun n=>n^(k+2))) (oracleDegree degree copies : ℕ)
    (W : ℕ→ℕ) (delta : ℚ) (hW:PolynomiallyBounded W) :
    ∃ onset,∀ s,onset ≤ s→∀ input : BitInput (2^s),
      ∀ oracle : BooleanCircuit ((SelectedRecoveryIntegration.outer sources k clock).result.pcp.nativeWidth (2^s)),
      oracle.size≤RecoveryScheduleEnvelope.oracleSizeBound oracleDegree
        ((SelectedRecoveryIntegration.outer sources k clock).result.pcp.nativeWidth (2^s))→
      ∀ w : FamilyWitness (CloseoutWitnessPolicy.actual sources k clock oracleDegree degree copies W delta input oracle)
        (CloseoutWitnessPolicy.variableCount sources k clock input),
      ∃ guess : BitInput (2^s/16),
        value (List.ofFn guess)=w.code ∧
        16*(List.ofFn guess).length≤2^s ∧ CompetitorWitnessTriple.headerValid (List.ofFn guess) ∧
        decodeBooleanCircuit ((SelectedRecoveryIntegration.outer sources k clock).result.pcp.nativeWidth (2^s))
          (value (BoundedFields.oracle (List.ofFn guess)))=some w.oracle ∧
        value (family (List.ofFn guess))=w.payload ∧ symmetric (List.ofFn guess)=decide (w.mode=0) := by
  obtain ⟨onset,small⟩:=actual_family_sixteenth sources k clock oracleDegree degree copies W delta hW
  exact ⟨onset,fun s hs input oracle ho w=>encoded_guess w (2^s) (small s hs input oracle ho w)⟩

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.BoundedFields
