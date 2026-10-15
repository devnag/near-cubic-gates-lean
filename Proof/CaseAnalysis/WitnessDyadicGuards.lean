import Proof.CaseAnalysis.WitnessSelectedSourceRequest
import Proof.CaseAnalysis.WitnessOracleWidth

/-! At one dyadic onset, the existing source-length and native-width
guards accept every correctly decoded oracle with the original size cap. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.SelectedSource
open SourceInterfaces RepairSource RepairRepresentation SelectedRecoveryIntegration CanonicalWitnessCodec RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

private theorem decode_cast {n m : ℕ} (h:n=m) {raw : ℕ} {oracle : BooleanCircuit m}
    (hd:decodeBooleanCircuit m raw=some oracle) :
    decodeBooleanCircuit n raw=some (cast (congrArg BooleanCircuit h.symm) oracle) := by
  cases h;exact hd

private theorem size_cast {n m : ℕ} (h:n=m) (oracle : BooleanCircuit m) :
    (cast (congrArg BooleanCircuit h.symm) oracle).size=oracle.size := by
  cases h;rfl

theorem guards_eventually (sources : EightSources) (k : ℕ)
    (clock : OrdinaryClock (fun n=>n^(k+2))) (cutoff G : ℕ) :
    ∃ onset,∀ s,onset ≤ s→∀ x : BitInput (2^s),
      ∀ oracle : BooleanCircuit ((outer sources k clock).result.pcp.nativeWidth (2^s)),
      oracle.size≤RecoveryScheduleEnvelope.oracleSizeBound G
        ((outer sources k clock).result.pcp.nativeWidth (2^s))→∀ raw : List Bool,
      decodeBooleanCircuit ((outer sources k clock).result.pcp.nativeWidth (2^s)) (value raw)=some oracle→
      ColdNative.passed (fixedProjection sources) k (hierarchy sources k clock).coefficient
        (padding sources k clock) cutoff G (code sources k clock) (List.ofFn x) raw=true := by
  obtain ⟨onset,hw⟩:=CloseoutLanguage.oracle_width_onset sources k clock
  refine ⟨max onset (max 2 cutoff),?_⟩
  intro s hs x oracle ho raw hd
  have hq: (outer sources k clock).result.pcp.nativeWidth (2^s)≤2^s:=
    (hw s ((Nat.le_max_left _ _).trans hs)).1
  have hcut:max 2 cutoff≤2^s:=
    ((Nat.le_max_right _ _).trans hs).trans (Nat.lt_two_pow_self.le)
  have decoded:=decode_cast (width sources k clock x) hd
  have cap:(cast (congrArg BooleanCircuit (width sources k clock x).symm) oracle).size≤
      RecoveryScheduleEnvelope.oracleSizeBound G (SelectedOracle.width (fixedProjection sources) k
        (hierarchy sources k clock).coefficient (padding sources k clock) (code sources k clock) (List.ofFn x)):=by
    rw [size_cast (width sources k clock x) oracle,width sources k clock x]
    exact ho
  simp only [ColdNative.passed,ColdOracle.passed,GuardedOracle.passed,decoded,Option.isSome_some,
    Option.any_some,Bool.and_true,Bool.and_eq_true,decide_eq_true_eq,List.length_ofFn]
  exact ⟨⟨hcut,(width sources k clock x).trans_le hq⟩,cap⟩

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.SelectedSource
