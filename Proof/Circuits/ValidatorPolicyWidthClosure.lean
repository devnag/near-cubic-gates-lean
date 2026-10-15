import Proof.Circuits.ValidatorComputableLimitsAssembly
import Proof.Circuits.ValidatorDescriptionLeafClosure

/-!
# The serialized policy's width, at degree two

`ValidatorComputableLimitsAssembly` §2 discharged the validator's `hprefix`
premise at the computable limits family in exchange for one hypothesis about the
family's own parameters:

```
hpolicy : PolyBounded (recoveryWitnessLimitsCodeBitBound P) measure c d
```

and `recoveryWitnessLimitsCodeBitBound` routes, through
`canonicalRationalCodeBitBound`, into `encodeNatBitsBound p = 1 + 2 · p⁴ · (p + 1)`.
That is **quintic** in the width parameter, so a degree-`1` certificate for the
parameter would only certify the serialized policy at degree `5` — one above the
machine's published `recoveryVerifierDegree = 4`.

The quintic is not the truth about the codec; it is the truth about the *coarse*
`balancedListCodeBits_le` reading of it.  `ValidatorLeafWidthCore` §5 publishes
the sharp reading — `natBitLength_encodeBalancedList_le_quadratic`, quadratic in
the atom **count** rather than quartic in the code — and `encodeNat` is exactly a
balanced list of one-bit atoms, so its width is *quadratic* in the source's.
This is the same cancellation `ValidatorCompositeLeafBounds` §5 spends for
`natBitLength_encodeNat_canonicalNatCandidate_le`; there the atom count is
additionally capped by the node-count shallowness lemma and the result is
linear, here the count is the parameter itself and the result is quadratic.

* §1 re-derives the three canonical numeric codecs — `encodeNat`, `encodeInt`
  and `encodeCanonicalRational` — at **degree two** in the field width.

* §2 re-derives the serialized policy record's width from the *same* width
  certificate `ValidatorPolynomialDomination` §4 already produces, at degree
  two, and instantiates it at the computable family.

* §3 spends it: the unit-budget transport of `ValidatorDescriptionLeafClosure`
  §1 turns a degree-`d` certificate for the family's width parameter into a
  degree-`2d` certificate for the serialized record, so `hprefix` closes at
  degree `2` over the measure-linear anchor — **inside** the saturated slot of
  four — and `hpolicy` disappears from the assembly's signature.
-/

namespace NearCubicWires.ValidatorPolicyWidthClosure

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalRecoveryRequest
open NearCubicWires.CanonicalRecoveryValidatorProgram
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.ExecutableRecoveryMachine
open NearCubicWires.RecoveryLimitsComputableFamily
open NearCubicWires.RecoveryWitnessPolicy
open NearCubicWires.ValidatorComputableLimitsAssembly
open NearCubicWires.ValidatorDescriptionLeafClosure
open NearCubicWires.ValidatorLeafWidthCore
open NearCubicWires.ValidatorPolynomialDomination
open NearCubicWires.ValidatorStageEnvelopes

/-! ## §1 The three numeric codecs, quadratically

`encodeNat value` *is* `encodeBalancedList (value.bits.map boolCode)`: a
balanced list whose atoms are all one bit wide and whose length is the source's
own bit count.  §5 of `ValidatorLeafWidthCore` charges such a list at
`16 · (count + 1)² · atomWidth`, so the whole re-encoding costs a quadratic —
never the quartic-in-the-width `balancedListCodeBits_le` reads off the
unconstrained atom list. -/

private theorem bitsLength_le_natBitLength (value : ℕ) :
    value.bits.length ≤ natBitLength value := by
  rw [Nat.size_eq_bits_len]
  apply (Nat.size_le).2
  simpa [natBitLength, Nat.succ_eq_add_one] using
    (Nat.lt_pow_succ_log_self (b := 2) (by omega) value)

/-- **The canonical natural codec, at degree two.** -/
theorem natBitLength_encodeNat_le_quadratic (value : ℕ) :
    natBitLength (encodeNat value) ≤ 16 * (natBitLength value + 1) ^ 2 := by
  have hmembers :
      ∀ atom ∈ value.bits.map boolCode, natBitLength atom ≤ 1 := by
    intro atom hatom
    rw [List.mem_map] at hatom
    obtain ⟨bit, _, rfl⟩ := hatom
    cases bit
    · rw [show boolCode false = 0 from rfl, natBitLength_zero]
    · rw [show boolCode true = 1 from rfl, natBitLength_one]
  have hquadratic :=
    natBitLength_encodeBalancedList_le_quadratic (value.bits.map boolCode) 1
      (le_refl 1) hmembers
  have hcode :
      encodeNat value = encodeBalancedList (value.bits.map boolCode) := rfl
  rw [hcode]
  simp only [List.length_map, Nat.mul_one] at hquadratic
  refine hquadratic.trans ?_
  exact Nat.mul_le_mul_left 16
    (Nat.pow_le_pow_left (by
      have := bitsLength_le_natBitLength value
      omega) 2)

/-- A field width bounds the canonical natural codec quadratically. -/
theorem natBitLength_encodeNat_le_quadratic_parameter
    {value parameter : ℕ} (hvalue : natBitLength value ≤ parameter) :
    natBitLength (encodeNat value) ≤ 16 * (parameter + 1) ^ 2 :=
  (natBitLength_encodeNat_le_quadratic value).trans
    (Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left (by omega) 2))

/-- **The canonical signed codec, at degree two.**  One sign bit paired with the
magnitude's canonical natural code; a pairing at most doubles the width. -/
theorem natBitLength_encodeInt_le_quadratic
    {value : ℤ} {parameter : ℕ}
    (hvalue : natBitLength value.natAbs ≤ parameter) :
    natBitLength (encodeInt value) ≤ 32 * (parameter + 1) ^ 2 := by
  have hsign : natBitLength (if value < 0 then 1 else 0) ≤ 1 := by
    split <;> rfl
  have hmagnitude :
      natBitLength (encodeNat value.natAbs) ≤ 16 * (parameter + 1) ^ 2 :=
    natBitLength_encodeNat_le_quadratic_parameter hvalue
  have hpair :=
    pairCodeBits_le (if value < 0 then 1 else 0) (encodeNat value.natAbs)
  have hcode :
      natBitLength (encodeInt value) ≤
        2 * max (natBitLength (if value < 0 then 1 else 0))
          (natBitLength (encodeNat value.natAbs)) := by
    simpa only [encodeInt] using hpair
  obtain ⟨square, hsquare⟩ : ∃ square : ℕ, (parameter + 1) ^ 2 = square :=
    ⟨_, rfl⟩
  have hone : 1 ≤ square := by
    rw [← hsquare]
    exact Nat.one_le_pow _ _ (by omega)
  rw [hsquare] at hmagnitude ⊢
  omega

/-- **The canonical rational codec, at degree two.**  A two-field tagged record
over the signed numerator and the natural denominator. -/
theorem natBitLength_encodeCanonicalRational_le_quadratic
    (coefficient : ℚ) (parameter : ℕ)
    (hnumerator : natBitLength coefficient.num.natAbs ≤ parameter)
    (hdenominator : natBitLength coefficient.den ≤ parameter) :
    natBitLength (encodeCanonicalRational coefficient) ≤
      400 * (parameter + 1) ^ 2 := by
  have hnumeratorCode :
      natBitLength (encodeInt coefficient.num) ≤ 32 * (parameter + 1) ^ 2 :=
    natBitLength_encodeInt_le_quadratic hnumerator
  have hdenominatorCode :
      natBitLength (encodeNat coefficient.den) ≤ 16 * (parameter + 1) ^ 2 :=
    natBitLength_encodeNat_le_quadratic_parameter hdenominator
  have hrecord := encodeTaggedList_two_bits_le hnumeratorCode hdenominatorCode
  have hexpand :
      taggedListBitBound
          [32 * (parameter + 1) ^ 2, 16 * (parameter + 1) ^ 2] =
        4 * (32 * (parameter + 1) ^ 2 +
          4 * (16 * (parameter + 1) ^ 2 + 1)) := by
    simp only [taggedListBitBound]
  have hcode :
      natBitLength (encodeCanonicalRational coefficient) ≤
        taggedListBitBound
          [32 * (parameter + 1) ^ 2, 16 * (parameter + 1) ^ 2] := by
    simpa only [encodeCanonicalRational] using hrecord
  obtain ⟨square, hsquare⟩ : ∃ square : ℕ, (parameter + 1) ^ 2 = square :=
    ⟨_, rfl⟩
  have hone : 1 ≤ square := by
    rw [← hsquare]
    exact Nat.one_le_pow _ _ (by omega)
  rw [hsquare] at hexpand hcode ⊢
  omega

/-! ## §2 The serialized policy record, quadratically

`ValidatorPolynomialDomination` §4 already produces the *width certificate*
`RecoveryWitnessLimitsWidth limits parameter` for the computable family, and its
record-shape ledgers `natBitLength_encodeLegalSumLimits_le` and
`natBitLength_encodeRecoveryWitnessLimits_le` are stated against an arbitrary
uniform field bound.  Only the rational mass cap's field bound was quintic; §1
replaces it, and the same two ledgers deliver the record at degree two. -/

/-- **The serialized policy's quadratic width bound.**  The replacement for
`recoveryWitnessLimitsCodeBitBound`: `512` record doublings over a field bound
of `400 · (parameter + 1)²`. -/
def recoveryWitnessLimitsCodeQuadraticBound (parameter : ℕ) : ℕ :=
  204800 * (parameter + 1) ^ 2

/-- **The serialized policy width, at degree two.**  Same hypothesis as
`natBitLength_encodeRecoveryWitnessLimits_le_parameter`, quadratic conclusion. -/
theorem natBitLength_encodeRecoveryWitnessLimits_le_quadratic
    {limits : RecoveryWitnessLimits} {parameter : ℕ}
    (hwidth : RecoveryWitnessLimitsWidth limits parameter) :
    natBitLength (encodeRecoveryWitnessLimits limits) ≤
      recoveryWitnessLimitsCodeQuadraticBound parameter := by
  obtain ⟨square, hsquare⟩ : ∃ square : ℕ, (parameter + 1) ^ 2 = square :=
    ⟨_, rfl⟩
  have hexpand : (parameter + 1) ^ 2 = (parameter + 1) * (parameter + 1) := by
    ring
  have hgrow : parameter + 1 ≤ (parameter + 1) * (parameter + 1) :=
    Nat.le_mul_of_pos_left _ (by omega)
  have hparameter : parameter + 1 ≤ square := by
    rw [← hsquare, hexpand]
    exact hgrow
  have hbranch :
      ∀ policy : LegalSumLimits, LegalSumLimitsWidth policy parameter →
        natBitLength (encodeLegalSumLimits policy) ≤ 32 * (400 * square) := by
    intro policy hpolicy
    refine natBitLength_encodeLegalSumLimits_le policy (400 * square)
      (hpolicy.expectedArity.trans (by omega))
      (hpolicy.termCap.trans (by omega))
      (hpolicy.coefficientBitCap.trans (by omega)) ?_
      (hpolicy.wireCap.trans (by omega))
      (hpolicy.descriptionCap.trans (by omega))
    have hmass :=
      natBitLength_encodeCanonicalRational_le_quadratic
        policy.coefficientMassCap parameter hpolicy.massNumerator
        hpolicy.massDenominator
    rw [hsquare] at hmass
    omega
  have hrecord :=
    natBitLength_encodeRecoveryWitnessLimits_le limits (32 * (400 * square))
      (hwidth.oracleArity.trans (by omega))
      (hwidth.oracleSizeCap.trans (by omega))
      (hwidth.sumArity.trans (by omega))
      (hbranch limits.symmetric hwidth.symmetric)
      (hbranch limits.threshold hwidth.threshold)
  simp only [recoveryWitnessLimitsCodeQuadraticBound, hsquare]
  omega

/-- **The computable policy's serialized width, at degree two.**  Unconditional,
exactly as `natBitLength_encodeComputableXorRecoveryWitnessLimits_le` is: only
the arithmetic shape of the family is used. -/
theorem natBitLength_encodeComputableXorLimits_le_quadratic
    (profile : XorNumeralProfile)
    (copyBound oracleArity oracleSizeCap sumArity symmetricWireCap
      thresholdWireCap : ℕ) :
    natBitLength (encodeRecoveryWitnessLimits
        (computableXorRecoveryWitnessLimits profile copyBound oracleArity
          oracleSizeCap sumArity symmetricWireCap thresholdWireCap)) ≤
      recoveryWitnessLimitsCodeQuadraticBound
        (computableRecoveryWitnessLimitsWidthParameter profile copyBound
          oracleArity oracleSizeCap sumArity symmetricWireCap
          thresholdWireCap) :=
  natBitLength_encodeRecoveryWitnessLimits_le_quadratic
    (computableXorRecoveryWitnessLimits_width profile copyBound oracleArity
      oracleSizeCap sumArity symmetricWireCap thresholdWireCap)

/-- The same, presented at the machine's `limitsOf` function. -/
theorem natBitLength_encodeComputableLimits_le_quadratic
    (profile : XorNumeralProfile)
    (copyBound oracleArity oracleSizeCap sumArity symmetricWireCap
      thresholdWireCap : ℕ → ℕ) (arity : ℕ) :
    natBitLength
        (encodeRecoveryWitnessLimits
          (computableLimitsOf profile copyBound oracleArity oracleSizeCap
            sumArity symmetricWireCap thresholdWireCap arity)) ≤
      recoveryWitnessLimitsCodeQuadraticBound
        (computableLimitsWidthParameter profile copyBound oracleArity
          oracleSizeCap sumArity symmetricWireCap thresholdWireCap arity) :=
  natBitLength_encodeComputableXorLimits_le_quadratic profile (copyBound arity)
    (oracleArity arity) (oracleSizeCap arity) (sumArity arity)
    (symmetricWireCap arity) (thresholdWireCap arity)

/-! ## §3 `hprefix`, from the family's parameter alone

The unit-budget transport of `ValidatorDescriptionLeafClosure` §1 is exactly the
rule this shape needs: a bound of the form `budget · (width + 1) ^ k` against a
degree-`d` certificate for `width` is a degree-`k · d` certificate.  With
`k = 2` and the measure-linear anchor `d = 1` the serialized policy record lands
at degree **two**, and the published slot is four. -/

/-- **The serialized policy record, dominated.** -/
theorem polyBounded_encodeComputableLimits
    (profile : XorNumeralProfile)
    (copyBound oracleArity oracleSizeCap sumArity symmetricWireCap
      thresholdWireCap : ℕ → ℕ)
    {arity measure parameterCoefficient parameterDegree : ℕ}
    (hparameter :
      PolyBounded
        (computableLimitsWidthParameter profile copyBound oracleArity
          oracleSizeCap sumArity symmetricWireCap thresholdWireCap arity)
        measure parameterCoefficient parameterDegree) :
    PolyBounded
      (natBitLength
        (encodeRecoveryWitnessLimits
          (computableLimitsOf profile copyBound oracleArity oracleSizeCap
            sumArity symmetricWireCap thresholdWireCap arity)))
      measure (204800 * (parameterCoefficient + 1) ^ 2)
      (2 * parameterDegree) :=
  (polyBounded_unitBudget 204800 2 hparameter).mono
    (natBitLength_encodeComputableLimits_le_quadratic profile copyBound
      oracleArity oracleSizeCap sumArity symmetricWireCap thresholdWireCap
      arity)

/-- **`hprefix`, discharged from the family's parameter.**  This is
`ValidatorComputableLimitsAssembly.polyBounded_computableLimits_prefixWidth`
with its quintic premise replaced by a certificate for the width parameter
itself — the six schedule functions' own growth, and nothing else. -/
theorem polyBounded_computableLimits_prefixWidth_of_parameter
    (profile : XorNumeralProfile)
    (copyBound oracleArity oracleSizeCap sumArity symmetricWireCap
      thresholdWireCap : ℕ → ℕ)
    {parameterCoefficient parameterDegree degree : ℕ}
    (hdegreeLow : 1 ≤ degree)
    (hdegreeHigh : 2 * parameterDegree ≤ degree)
    (hparameter : ∀ request : WeakVerifierRequest,
      PolyBounded
        (computableLimitsWidthParameter profile copyBound oracleArity
          oracleSizeCap sumArity symmetricWireCap thresholdWireCap
          request.inputArity)
        request.measure parameterCoefficient parameterDegree)
    (request : WeakVerifierRequest) :
    PolyBounded
      (recoveryValidatorPrefixWidth
        (computableLimitsOf profile copyBound oracleArity oracleSizeCap sumArity
          symmetricWireCap thresholdWireCap request.inputArity)
        (encodeBitInput request.witness))
      request.measure
      (max 4 (204800 * (parameterCoefficient + 1) ^ 2)) degree := by
  have hwitness :
      PolyBounded (natBitLength (encodeBitInput request.witness))
        request.measure 4 degree :=
    (polyBounded_witnessWidth request).degree_mono hdegreeLow
  have hserialized :=
    (polyBounded_encodeComputableLimits profile copyBound oracleArity
      oracleSizeCap sumArity symmetricWireCap thresholdWireCap
      (hparameter request)).degree_mono hdegreeHigh
  exact hwitness.max hserialized

theorem polyBounded_recoveryWitnessLimitsCodeQuadraticBound
    (profile : XorNumeralProfile)
    (copyBound oracleArity oracleSizeCap sumArity symmetricWireCap
      thresholdWireCap : ℕ → ℕ)
    {arity measure parameterCoefficient : ℕ}
    (hparameter :
      PolyBounded
        (computableLimitsWidthParameter profile copyBound oracleArity
          oracleSizeCap sumArity symmetricWireCap thresholdWireCap arity)
        measure parameterCoefficient 1) :
    PolyBounded
      (recoveryWitnessLimitsCodeQuadraticBound
        (computableLimitsWidthParameter profile copyBound oracleArity
          oracleSizeCap sumArity symmetricWireCap thresholdWireCap arity))
      measure (204800 * (parameterCoefficient + 1) ^ 2) 2 := by
  have hbudget := polyBounded_unitBudget 204800 2 hparameter
  simpa only [recoveryWitnessLimitsCodeQuadraticBound, Nat.mul_one] using
    hbudget

end NearCubicWires.ValidatorPolicyWidthClosure
