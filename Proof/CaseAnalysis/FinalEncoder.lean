import Proof.CaseAnalysis.FinalCompletenessDyadic
import Proof.CaseAnalysis.WitnessSampledSource

namespace NearCubicWires.RepairSource.CloseoutFinal

open RepairOrdinary RepairRepresentation SourceInterfaces SupplierPipeline
open SelectedRecoveryIntegration CloseoutLanguage CircuitRestriction
open RepairOrdinary.CloseoutWitness CanonicalWitnessCodec PolynomialSchedule
open RecoveryScheduleEnvelope

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

/-- The paper's wire cap policy `floor (wireScale cap e q)` is polynomially
bounded, which is what the eventual `N/16` encoding theorem asks of `W`. -/
theorem wireScaleFloor_polynomial (cap : ℝ) (e : ℕ) :
    PolynomiallyBounded (fun q => ⌊wireScale cap e q⌋₊) := by
  refine polynomiallyBounded_mono (fun q => ?_)
    (polynomiallyBounded_mul (polynomiallyBounded_constant ⌈|cap|⌉₊)
      (polynomiallyBounded_pow polynomiallyBounded_id 3))
  have hone : (1 : ℝ) ≤ (logScale q : ℝ) := by exact_mod_cast logScale_pos q
  have hlog : (1 : ℝ) ≤ (logScale q : ℝ) ^ e := one_le_pow₀ hone
  have hq : (0 : ℝ) ≤ (q : ℝ) ^ 3 := by positivity
  have hcap : cap ≤ (⌈|cap|⌉₊ : ℝ) := (le_abs_self cap).trans (Nat.le_ceil _)
  have hmain : wireScale cap e q ≤ ((⌈|cap|⌉₊ * q ^ 3 : ℕ) : ℝ) := by
    have hpos : (0 : ℝ) < (logScale q : ℝ) ^ e := lt_of_lt_of_le zero_lt_one hlog
    have hstep : cap * (q : ℝ) ^ 3 / (logScale q : ℝ) ^ e ≤ (⌈|cap|⌉₊ : ℝ) * (q : ℝ) ^ 3 := by
      rw [div_le_iff₀ hpos]
      calc cap * (q : ℝ) ^ 3 ≤ (⌈|cap|⌉₊ : ℝ) * (q : ℝ) ^ 3 :=
            mul_le_mul_of_nonneg_right hcap hq
        _ = (⌈|cap|⌉₊ : ℝ) * (q : ℝ) ^ 3 * 1 := by ring
        _ ≤ (⌈|cap|⌉₊ : ℝ) * (q : ℝ) ^ 3 * (logScale q : ℝ) ^ e :=
            mul_le_mul_of_nonneg_left hlog (by positivity)
    have hcast : ((⌈|cap|⌉₊ * q ^ 3 : ℕ) : ℝ) = (⌈|cap|⌉₊ : ℝ) * (q : ℝ) ^ 3 := by push_cast; ring
    rw [hcast]
    simpa [wireScale] using hstep
  simpa using Nat.floor_le_of_le hmain

/-- **E1a, symmetric.** Beyond one eventual dyadic onset, every honest
symmetric `SumFamily` at the selected request is carried by an ordinary
`2^s/16`-bit witness string whose decoded oracle field is the selected oracle
and whose decoded payload field is *that same family*. -/
theorem symmetric_family_guess (sources : EightSources) (k : Nat)
    (clock : OrdinaryClock (fun n => n^(k+2)))
    (degree clauseDegree copies : Nat) (delta : ℚ) (cap : ℝ) :
    ∃ onset, ∀ s, onset ≤ s → ∀ input : BitInput (2^s),
      ∀ oracle : BooleanCircuit ((outer sources k clock).result.pcp.nativeWidth (2^s)),
      oracle.size ≤ oracleSizeBound degree ((outer sources k clock).result.pcp.nativeWidth (2^s)) →
      ∀ family : CloseoutWitness.SumFamily NormalizedSymmetricThresholdCircuit
          NormalizedSymmetricThresholdCircuit.wireCount
          NormalizedSymmetricThresholdCircuit.descriptionBits
          (CloseoutSampledWitness.symmetricLimits (selectedPCPP sources)
            (CloseoutWitnessPolicy.request sources k clock input oracle)
            (clauseWidth clauseDegree ((outer sources k clock).result.pcp.nativeWidth (2^s)))
            copies ⌊wireScale cap 5 ((outer sources k clock).result.pcp.nativeWidth (2^s))⌋₊ delta)
          (CloseoutWitnessPolicy.variableCount sources k clock input oracle),
      ∃ guess : BitInput (2^s/16),
        16*(List.ofFn guess).length ≤ 2^s ∧
        CompetitorWitnessTriple.headerValid (List.ofFn guess) ∧
        decodeBooleanCircuit ((outer sources k clock).result.pcp.nativeWidth (2^s))
            (RadixSemantics.value (BoundedFields.oracle (List.ofFn guess))) = some oracle ∧
        CloseoutWitness.SumFamily.decode symmetricCircuitCodec
            NormalizedSymmetricThresholdCircuit.wireCount
            NormalizedSymmetricThresholdCircuit.descriptionBits
            (CloseoutSampledWitness.symmetricLimits (selectedPCPP sources)
              (CloseoutWitnessPolicy.request sources k clock input oracle)
              (clauseWidth clauseDegree ((outer sources k clock).result.pcp.nativeWidth (2^s)))
              copies ⌊wireScale cap 5 ((outer sources k clock).result.pcp.nativeWidth (2^s))⌋₊ delta)
            (CloseoutWitnessPolicy.variableCount sources k clock input oracle)
            (RadixSemantics.value (BoundedFields.family (List.ofFn guess))) = some family ∧
        BoundedFields.symmetric (List.ofFn guess) = true := by
  obtain ⟨onset, henc⟩ := BoundedFields.encoded_eventually sources k clock degree clauseDegree
    copies (fun q => ⌊wireScale cap 5 q⌋₊) delta (wireScaleFloor_polynomial cap 5)
  refine ⟨onset, ?_⟩
  intro s hs input oracle ho family
  obtain ⟨guess, _hcode, hlen, hheader, horacle, hpayload, hmode⟩ :=
    henc s hs input oracle ho (FamilyWitness.symmetric oracle ho family)
  refine ⟨guess, hlen, hheader, horacle, ?_, ?_⟩
  · rw [hpayload]
    exact CloseoutWitness.SumFamily.decode_encode symmetricCircuitCodec family
  · rw [hmode]
    rfl

/-- **E1a, threshold.** The same statement for the threshold class: exponent
`9` in the wire cap, `thresholdCircuitCodec` for the payload, and a `false`
mode bit. -/
theorem threshold_family_guess (sources : EightSources) (k : Nat)
    (clock : OrdinaryClock (fun n => n^(k+2)))
    (degree clauseDegree copies : Nat) (delta : ℚ) (cap : ℝ) :
    ∃ onset, ∀ s, onset ≤ s → ∀ input : BitInput (2^s),
      ∀ oracle : BooleanCircuit ((outer sources k clock).result.pcp.nativeWidth (2^s)),
      oracle.size ≤ oracleSizeBound degree ((outer sources k clock).result.pcp.nativeWidth (2^s)) →
      ∀ family : CloseoutWitness.SumFamily NormalizedThresholdThresholdCircuit
          NormalizedThresholdThresholdCircuit.wireCount
          NormalizedThresholdThresholdCircuit.descriptionBits
          (CloseoutSampledWitness.thresholdLimits (selectedPCPP sources)
            (CloseoutWitnessPolicy.request sources k clock input oracle)
            (clauseWidth clauseDegree ((outer sources k clock).result.pcp.nativeWidth (2^s)))
            copies ⌊wireScale cap 9 ((outer sources k clock).result.pcp.nativeWidth (2^s))⌋₊ delta)
          (CloseoutWitnessPolicy.variableCount sources k clock input oracle),
      ∃ guess : BitInput (2^s/16),
        16*(List.ofFn guess).length ≤ 2^s ∧
        CompetitorWitnessTriple.headerValid (List.ofFn guess) ∧
        decodeBooleanCircuit ((outer sources k clock).result.pcp.nativeWidth (2^s))
            (RadixSemantics.value (BoundedFields.oracle (List.ofFn guess))) = some oracle ∧
        CloseoutWitness.SumFamily.decode thresholdCircuitCodec
            NormalizedThresholdThresholdCircuit.wireCount
            NormalizedThresholdThresholdCircuit.descriptionBits
            (CloseoutSampledWitness.thresholdLimits (selectedPCPP sources)
              (CloseoutWitnessPolicy.request sources k clock input oracle)
              (clauseWidth clauseDegree ((outer sources k clock).result.pcp.nativeWidth (2^s)))
              copies ⌊wireScale cap 9 ((outer sources k clock).result.pcp.nativeWidth (2^s))⌋₊ delta)
            (CloseoutWitnessPolicy.variableCount sources k clock input oracle)
            (RadixSemantics.value (BoundedFields.family (List.ofFn guess))) = some family ∧
        BoundedFields.symmetric (List.ofFn guess) = false := by
  obtain ⟨onset, henc⟩ := BoundedFields.encoded_eventually sources k clock degree clauseDegree
    copies (fun q => ⌊wireScale cap 9 q⌋₊) delta (wireScaleFloor_polynomial cap 9)
  refine ⟨onset, ?_⟩
  intro s hs input oracle ho family
  obtain ⟨guess, _hcode, hlen, hheader, horacle, hpayload, hmode⟩ :=
    henc s hs input oracle ho (FamilyWitness.threshold oracle ho family)
  refine ⟨guess, hlen, hheader, horacle, ?_, ?_⟩
  · rw [hpayload]
    exact CloseoutWitness.SumFamily.decode_encode thresholdCircuitCodec family
  · rw [hmode]
    rfl

/-- **`hyes` for the selected request, restated at the `EncodesSym` binders.**
`honest_estimates_pass` demands the substituted request circuit be a
tautology; the canonical accepting oracle plus the outer PCP's
randomness-independent decision formula supply exactly that. -/
theorem selected_yes (sources : EightSources) (k : Nat)
    (clock : OrdinaryClock (fun n => n^(k+2))) (degree : Nat) {N : Nat} (input : BitInput N)
    (hsmall : RecoveryChoice.SmallOracle (outer sources k clock).result.pcp degree input) :
    ∀ u, (CloseoutWitnessPolicy.request sources k clock input
        (RecoveryChoice.oracleSelector (outer sources k clock).result.pcp degree input
          hsmall).circuit).circuit.eval u = true :=
  CloseoutWitness.selected_request_true sources k clock degree input hsmall

/-- The selected oracle meets the size guard the actual witness policy uses. -/
theorem selected_oracle_small (sources : EightSources) (k : Nat)
    (clock : OrdinaryClock (fun n => n^(k+2))) (degree : Nat) {N : Nat} (input : BitInput N)
    (hsmall : RecoveryChoice.SmallOracle (outer sources k clock).result.pcp degree input) :
    (RecoveryChoice.oracleSelector (outer sources k clock).result.pcp degree input
        hsmall).circuit.size ≤
      oracleSizeBound degree ((outer sources k clock).result.pcp.nativeWidth N) :=
  (RecoveryChoice.oracleSelector (outer sources k clock).result.pcp degree input hsmall).sizeBounded

end
end NearCubicWires.RepairSource.CloseoutFinal
