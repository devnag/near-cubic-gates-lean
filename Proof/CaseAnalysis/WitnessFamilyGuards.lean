import Proof.CaseAnalysis.CloseoutWitnessColdFamilyResources

/-! The actual paid cutoff and width guards discharge the native family
resource transport without any additional physical arity test. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.ColdFamilyGuards
open LocalBitMultitape SourceInterfaces RepairSource RepairRepresentation ProjectionNormalization CanonicalWitnessCodec
open RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
theorem live (k CH Cpad cutoff G : ℕ) (code x raw : List Bool)
    (yes:ColdNative.passed source k CH Cpad cutoff G code x raw=true) :
    max 2 cutoff≤x.length ∧ SelectedOracle.width source k CH Cpad code x≤x.length ∧
      ∃ oracle,decodeBooleanCircuit (SelectedOracle.width source k CH Cpad code x) (value raw)=some oracle ∧
        oracle.size≤RecoveryScheduleEnvelope.oracleSizeBound G (SelectedOracle.width source k CH Cpad code x):=by
  have both:ColdOracle.passed source k CH Cpad cutoff code x raw=true ∧
      (decodeBooleanCircuit (SelectedOracle.width source k CH Cpad code x) (value raw)).any
        (fun oracle=>decide (oracle.size≤RecoveryScheduleEnvelope.oracleSizeBound G
          (SelectedOracle.width source k CH Cpad code x)))=true:=
    by simpa only [ColdNative.passed,Bool.and_eq_true] using yes
  have guards:max 2 cutoff≤x.length ∧ SelectedOracle.width source k CH Cpad code x≤x.length ∧
      (decodeBooleanCircuit (SelectedOracle.width source k CH Cpad code x) (value raw)).isSome=true:=
    by simpa only [ColdOracle.passed,GuardedOracle.passed,Bool.and_eq_true,decide_eq_true_eq] using both.1
  refine ⟨guards.1,guards.2.1,?_⟩
  cases hd:decodeBooleanCircuit (SelectedOracle.width source k CH Cpad code x) (value raw) with
  | none => simp [hd] at both
  | some oracle => exact ⟨oracle,rfl,by simpa [hd] using both.2⟩

theorem arity (a : PointwisePCPPAlgorithm) (k CH Cpad : ℕ) (code : List Bool)
    {n : ℕ} (x : BitInput n) (hpad : k+3≤Cpad)
    (oracle : BooleanCircuit (SelectedOracle.width source k CH Cpad code (List.ofFn x)))
    (hcut : 2^a.minimumArity≤n) :
    (ColdNative.request source a k CH Cpad code x hpad oracle).arity=
      SelectedOracle.width source k CH Cpad code (List.ofFn x):=by
  let L:=(HierarchyPadding.rawInput k CH Cpad code (List.ofFn x)).length
  have hl:n+1≤L:=by simpa only [List.length_ofFn] using
    (HierarchyPadding.linear_length k CH Cpad code (List.ofFn x) hpad).1
  have ht:=UAggregateClock.input_le_time L
  have hp:1≤logScale (UAggregateClock.time L):=Nat.clog_pos (by decide) (by omega)
  have he:n+1≤Dimensions.envelope source L:=by
    apply (hl.trans ht).trans
    change UAggregateClock.time L ≤ source.coefficient*UAggregateClock.time L*
      logScale (UAggregateClock.time L)^source.degrees.proofLog
    calc
      _=1*UAggregateClock.time L*1:=by ring
      _≤_:=Nat.mul_le_mul (Nat.mul_le_mul_right _ source.coefficientPositive)
        (Nat.one_le_pow _ _ hp)
  have hm:a.minimumArity≤SelectedOracle.width source k CH Cpad code (List.ofFn x):=by
    have hlog:=Nat.le_log_of_pow_le (by decide : 1<2) (hcut.trans ((Nat.le_succ n).trans he))
    change a.minimumArity≤Nat.log 2 (Dimensions.envelope source L)+1
    omega
  change max (SelectedOracle.width source k CH Cpad code (List.ofFn x)) a.minimumArity=_
  exact Nat.max_eq_left hm

theorem query_bound (k CH Cpad : ℕ) (code x : List Bool) :
    SelectedStreams.queries source k CH Cpad code x≤
      source.coefficient*(SelectedOracle.width source k CH Cpad code x+1)^source.degrees.queries:=Nat.le_refl _

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.ColdFamilyGuards
