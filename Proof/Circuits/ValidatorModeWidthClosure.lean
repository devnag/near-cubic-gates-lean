import Proof.Circuits.ValidatorLeafPremiseSweep

namespace NearCubicWires.ValidatorModeWidthClosure

open NearCubicWires
open NearCubicWires.CanonicalRecoveryValidatorProgram
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.ValidatorLeafWidthCore
open NearCubicWires.ValidatorPolynomialDomination
open NearCubicWires.ValidatorStageEnvelopes

/-! ## §1 The legal-sum guard never widens its handoff -/

/-- **The legal-sum prefix's output width, unconditionally.**  Sixteen times the
prefix width — the very ledger `hprefix` is charged from. -/
theorem natBitLength_recoveryValidatorLegalSumPrefixOutput_le
    (inputLength : ℕ) (limits : RecoveryWitnessLimits) (raw : ℕ) :
    natBitLength
        (recoveryValidatorLegalSumPrefixOutput inputLength limits raw) ≤
      16 * recoveryValidatorPrefixWidth limits raw := by
  by_cases haccepts :
      recoveryValidatorLegalSumPrefixOutput inputLength limits raw = 0
  · have hzero : natBitLength 0 = 1 := natBitLength_zero
    have hpositive := one_le_recoveryValidatorPrefixWidth limits raw
    rw [haccepts]
    omega
  · rw [recoveryValidatorLegalSumPrefixOutput_eq_oraclePrefixOutput haccepts,
      recoveryValidatorOraclePrefixOutput_eq_handoff
        (recoveryValidatorOraclePrefixOutput_ne_zero_of_legalSum haccepts)]
    exact
      (natBitLength_mono (recoveryValidatorHandoffOutput_le limits raw)).trans
        (recoveryValidatorHandoffBits_le limits raw)

/-- **`hmode`, discharged.**  It is the prefix width certificate again. -/
theorem polyBounded_legalSumPrefixOutput
    {inputLength : ℕ} {limits : RecoveryWitnessLimits}
    {raw measure coefficient degree : ℕ}
    (hwidth :
      PolyBounded (recoveryValidatorPrefixWidth limits raw) measure coefficient
        degree) :
    PolyBounded
      (natBitLength
        (recoveryValidatorLegalSumPrefixOutput inputLength limits raw))
      measure (16 * coefficient) degree :=
  (hwidth.const_mul 16).mono
    (natBitLength_recoveryValidatorLegalSumPrefixOutput_le inputLength limits
      raw)

end NearCubicWires.ValidatorModeWidthClosure
