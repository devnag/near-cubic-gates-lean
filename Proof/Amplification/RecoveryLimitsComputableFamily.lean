import Proof.CaseAnalysis.CaseTwoWitnessCompleteness

/-!
# A program-computable recovery-limits family

`RecoveryLimitsFrontEndProgram` reduces the machine's limits obligation to one
run theorem for a family `inputLength ↦ encodeRecoveryWitnessLimits (limitsOf
inputLength)`, and records that such a program exists only when the family is
computable from the finitely many naturals frozen into its instruction stream.
The exact schedule policies of `RecoveryWitnessScheduleCapacity` are *not* of
that shape: their two term caps are

```
xorAuthorizedTermCap witness delta copies arity =
  ⌈witness.termCoefficient delta * arity / xorEpsilon delta copies ^ 2⌉₊
```

with `witness.termCoefficient : ℝ → ℝ` an arbitrary real function, so the
dependence on `arity` is a ceiling of a real multiple and no finite instruction
list over natural immediates realizes it.  The same applies to the real mass
envelope `witness.massCoefficient delta / xorEpsilon delta copies`.

Opacity of a *natural* is not the obstruction — a frozen natural is a `.set`
immediate whatever its provenance.  Only the two genuinely real-valued
envelopes are.  This module therefore replaces exactly those two fields by
explicit arithmetic over the frozen naturals

```
⌈witness.termCoefficient delta⌉₊    ⌈witness.massCoefficient delta⌉₊
```

and leaves every other field of the published policies untouched: the two
arities are constrained to be *equal* by `RecoveryWitnessLimits.Weakens`, and
they, the oracle size cap, the wire caps and both description caps are already
explicit arithmetic in the schedule's frozen naturals.

The resulting family is a genuine weakening of the exact policy at every
schedule coordinate, so completeness transports through
`CheckedRecoveryWitness.widen` without changing a single serialized bit, and it
remains `PolynomiallyBounded`, so the executable `n / 16` witness shape still
absorbs it after an internally derived onset.

Two `noncomputable` markers appear below.  They are Lean code-generation
markers only: the frozen naturals are selected by `Classical.choice` inside the
published contracts.  Every field of the family is an arithmetic expression in
those naturals and the public input length, which is exactly what an
`NPOracleProgram` can evaluate.
-/

namespace NearCubicWires.RecoveryLimitsComputableFamily

open NearCubicWires
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoRecoveryAssembly
open NearCubicWires.CaseTwoWitnessCompleteness
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialSchedule
open NearCubicWires.ProjectionWidthEnvelope
open NearCubicWires.RecoveryPipeline
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RecoveryWitnessNormalization
open NearCubicWires.RecoveryWitnessPolicy
open NearCubicWires.RecoveryWitnessScheduleCapacity
open NearCubicWires.RecoveryWitnessShape
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces

/-! ## §1 The frozen numeral profile of the published amplifier

Four naturals is everything the decoder policy needs from the imported XOR
amplifier at the published radius.  Two of them are already natural fields of
the amplifier witness; the other two are ceilings of its real coefficients. -/

/-- Natural profile of one XOR amplification witness at a fixed radius. -/
structure XorNumeralProfile where
  /-- A natural dominating the amplifier's real term coefficient. -/
  termCoefficientCap : ℕ
  /-- A natural dominating the amplifier's real mass coefficient. -/
  massCoefficientCap : ℕ
  /-- The amplifier's own coefficient-bit coefficient, already a natural. -/
  coefficientBitCoefficient : ℕ
  /-- The amplifier's own coefficient-bit degree, already a natural. -/
  coefficientBitDegree : ℕ

/-- The profile of the published amplifier at a published radius. -/
noncomputable def xorNumeralProfileOf
    (witness : XorAmplificationWitness) (delta : ℝ) : XorNumeralProfile where
  termCoefficientCap := ⌈witness.termCoefficient delta⌉₊
  massCoefficientCap := ⌈witness.massCoefficient delta⌉₊
  coefficientBitCoefficient := witness.coefficientBitCoefficient delta
  coefficientBitDegree := witness.coefficientBitDegree delta

/-! ## §2 The computable policy shape

Every field below is a closed arithmetic expression in the profile numerals,
the copy-count envelope and the schedule's own natural fields. -/

/-- Computable term envelope.  The quarter-ball estimate on `xorEpsilon`
converts the exact real denominator into the natural factor `16 ^ copyBound`. -/
def computableTermCap (profile : XorNumeralProfile)
    (copyBound arity : ℕ) : ℕ :=
  profile.termCoefficientCap * arity * 16 ^ copyBound

/-- Computable coefficient-bit envelope.  This is definitionally the exact
envelope: the amplifier's coefficient-bit data is already natural. -/
def computableCoefficientBitCap (profile : XorNumeralProfile)
    (arity : ℕ) : ℕ :=
  profile.coefficientBitCoefficient * (arity + 1) ^ profile.coefficientBitDegree

/-- Computable coefficient-mass envelope, presented as the canonical rational
image of a natural. -/
def computableMassCap (profile : XorNumeralProfile) (copyBound : ℕ) : ℚ :=
  ((profile.massCoefficientCap * 4 ^ copyBound : ℕ) : ℚ)

/-- Computable decoder limits for the normalized `SYM ∘ THR` branch. -/
def computableSymmetricLegalSumLimits (profile : XorNumeralProfile)
    (copyBound arity wireCap : ℕ) : LegalSumLimits where
  expectedArity := arity
  termCap := computableTermCap profile copyBound arity
  coefficientBitCap := computableCoefficientBitCap profile arity
  coefficientMassCap := computableMassCap profile copyBound
  wireCap := wireCap
  descriptionCap := symmetricDescriptionCap arity wireCap

/-- Computable decoder limits for the normalized `THR ∘ THR` branch. -/
def computableThresholdLegalSumLimits (profile : XorNumeralProfile)
    (copyBound arity wireCap : ℕ) : LegalSumLimits where
  expectedArity := arity
  termCap := computableTermCap profile copyBound arity
  coefficientBitCap := computableCoefficientBitCap profile arity
  coefficientMassCap := computableMassCap profile copyBound
  wireCap := wireCap
  descriptionCap := thresholdDescriptionCap arity wireCap

/-- **The computable witness policy.**  Structurally identical to
`xorRecoveryWitnessLimits`, with the two real-valued envelopes replaced by
arithmetic in the profile numerals. -/
def computableXorRecoveryWitnessLimits (profile : XorNumeralProfile)
    (copyBound oracleArity oracleSizeCap sumArity
      symmetricWireCap thresholdWireCap : ℕ) :
    RecoveryWitnessLimits where
  oracleArity := oracleArity
  oracleSizeCap := oracleSizeCap
  sumArity := sumArity
  symmetric :=
    computableSymmetricLegalSumLimits profile copyBound sumArity
      symmetricWireCap
  threshold :=
    computableThresholdLegalSumLimits profile copyBound sumArity
      thresholdWireCap
  symmetricArity := rfl
  thresholdArity := rfl

/-! ## §3 Weakening the exact policy into the computable one -/

private theorem legalSumLimits_weakens_trans
    {first second third : LegalSumLimits}
    (hfirst : first.Weakens second) (hsecond : second.Weakens third) :
    first.Weakens third where
  expectedArity_eq :=
    hfirst.expectedArity_eq.trans hsecond.expectedArity_eq
  termCap_le := hfirst.termCap_le.trans hsecond.termCap_le
  coefficientBitCap_le :=
    hfirst.coefficientBitCap_le.trans hsecond.coefficientBitCap_le
  coefficientMassCap_le :=
    hfirst.coefficientMassCap_le.trans hsecond.coefficientMassCap_le
  wireCap_le := hfirst.wireCap_le.trans hsecond.wireCap_le
  descriptionCap_le :=
    hfirst.descriptionCap_le.trans hsecond.descriptionCap_le

/-- Transitivity of the policy weakening order.  The exact schedule policy
reaches the computable family through the existing wire-cap widening, so the
two steps must compose. -/
theorem recoveryWitnessLimits_weakens_trans
    {first second third : RecoveryWitnessLimits}
    (hfirst : first.Weakens second) (hsecond : second.Weakens third) :
    first.Weakens third where
  oracleArity_eq := hfirst.oracleArity_eq.trans hsecond.oracleArity_eq
  oracleSizeCap_le := hfirst.oracleSizeCap_le.trans hsecond.oracleSizeCap_le
  sumArity_eq := hfirst.sumArity_eq.trans hsecond.sumArity_eq
  symmetric := legalSumLimits_weakens_trans hfirst.symmetric hsecond.symmetric
  threshold := legalSumLimits_weakens_trans hfirst.threshold hsecond.threshold

/-- Quarter-power lower bound on the XOR advantage.  Stated at a general
radius inside the published quarter ball so no schedule constant enters. -/
private theorem xorEpsilon_quarter_lower {delta : ℝ}
    (hquarter : delta ≤ 1 / 4) (copies : ℕ) (hcopies : 1 ≤ copies) :
    1 / (4 : ℝ) ^ copies ≤ xorEpsilon delta copies := by
  have hpower :
      ((1 : ℝ) / 4) ^ (copies - 1) ≤ (1 - delta) ^ (copies - 1) :=
    pow_le_pow_left₀ (by norm_num) (by linarith) (copies - 1)
  calc
    1 / (4 : ℝ) ^ copies = ((1 : ℝ) / 4) ^ copies := by
      rw [one_div_pow]
    _ = ((1 : ℝ) / 4) ^ (copies - 1) * (1 / 4) := by
      calc
        ((1 : ℝ) / 4) ^ copies =
            ((1 : ℝ) / 4) ^ (copies - 1 + 1) := by
          congr 1
          omega
        _ = ((1 : ℝ) / 4) ^ (copies - 1) * (1 / 4) := by
          rw [pow_succ]
    _ ≤ (1 - delta) ^ (copies - 1) * (1 / 2 - delta) :=
      mul_le_mul hpower (by linarith) (by norm_num)
        (pow_nonneg (by linarith) (copies - 1))
    _ = xorEpsilon delta copies := rfl

private theorem xorEpsilon_quarter_positive {delta : ℝ}
    (hquarter : delta ≤ 1 / 4) (copies : ℕ) :
    0 < xorEpsilon delta copies :=
  mul_pos (pow_pos (by linarith) (copies - 1)) (by linarith)

/-- The exact term envelope is dominated by the computable one.  The estimate
is the quarter-ball bound on `xorEpsilon`, which converts the real denominator
into `16 ^ copies`; the numerator's real coefficient is absorbed by its own
ceiling. -/
private theorem xorAuthorizedTermCap_le_computable
    (witness : XorAmplificationWitness) (delta : ℝ)
    (hquarter : delta ≤ 1 / 4) (copies arity : ℕ) (hcopies : 1 ≤ copies) :
    xorAuthorizedTermCap witness delta copies arity ≤
      ⌈witness.termCoefficient delta⌉₊ * arity * 16 ^ copies := by
  apply Nat.ceil_le.mpr
  have hepsilon := xorEpsilon_quarter_lower hquarter copies hcopies
  have hpositive : 0 < xorEpsilon delta copies :=
    xorEpsilon_quarter_positive hquarter copies
  have hdenominator :
      (1 / (4 : ℝ) ^ copies) ^ 2 ≤ xorEpsilon delta copies ^ 2 := by
    gcongr
  change
    witness.termCoefficient delta * arity /
        xorEpsilon delta copies ^ 2 ≤
      ((⌈witness.termCoefficient delta⌉₊ * arity * 16 ^ copies : ℕ) : ℝ)
  apply (div_le_iff₀ (sq_pos_of_pos hpositive)).mpr
  calc
    witness.termCoefficient delta * arity ≤
        (⌈witness.termCoefficient delta⌉₊ : ℝ) * arity := by
      gcongr
      exact Nat.le_ceil _
    _ =
        ((⌈witness.termCoefficient delta⌉₊ *
          arity * 16 ^ copies : ℕ) : ℝ) *
            (1 / (4 : ℝ) ^ copies) ^ 2 := by
      push_cast
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num, ← pow_mul]
      field_simp
      ring
    _ ≤
        ((⌈witness.termCoefficient delta⌉₊ *
          arity * 16 ^ copies : ℕ) : ℝ) *
            xorEpsilon delta copies ^ 2 := by
      gcongr

/-- The exact real mass envelope is dominated by the computable natural one. -/
private theorem xorAuthorizedCoefficientMass_ceil_le_computable
    (witness : XorAmplificationWitness) (delta : ℝ)
    (hquarter : delta ≤ 1 / 4) (copies : ℕ) (hcopies : 1 ≤ copies) :
    ⌈xorAuthorizedCoefficientMass witness delta copies⌉₊ ≤
      ⌈witness.massCoefficient delta⌉₊ * 4 ^ copies := by
  apply Nat.ceil_le.mpr
  have hepsilon := xorEpsilon_quarter_lower hquarter copies hcopies
  have hpositive : 0 < xorEpsilon delta copies :=
    xorEpsilon_quarter_positive hquarter copies
  change
    witness.massCoefficient delta / xorEpsilon delta copies ≤
      ((⌈witness.massCoefficient delta⌉₊ * 4 ^ copies : ℕ) : ℝ)
  apply (div_le_iff₀ hpositive).mpr
  calc
    witness.massCoefficient delta ≤
        (⌈witness.massCoefficient delta⌉₊ : ℝ) :=
      Nat.le_ceil _
    _ =
        ((⌈witness.massCoefficient delta⌉₊ * 4 ^ copies : ℕ) : ℝ) *
          (1 / (4 : ℝ) ^ copies) := by
      push_cast
      field_simp
    _ ≤
        ((⌈witness.massCoefficient delta⌉₊ * 4 ^ copies : ℕ) : ℝ) *
          xorEpsilon delta copies := by
      gcongr

private theorem symmetricDescriptionCap_mono_wire
    {arity smaller larger : ℕ} (hle : smaller ≤ larger) :
    symmetricDescriptionCap arity smaller ≤
      symmetricDescriptionCap arity larger := by
  unfold symmetricDescriptionCap
  gcongr

private theorem thresholdDescriptionCap_mono_wire
    {arity smaller larger : ℕ} (hle : smaller ≤ larger) :
    thresholdDescriptionCap arity smaller ≤
      thresholdDescriptionCap arity larger := by
  unfold thresholdDescriptionCap
  exact Nat.add_le_add
    (normalizedGateDescriptionCap_mono hle)
    (Nat.mul_le_mul_right _ hle)

/-- **The single design theorem.**  Every exact XOR-authorized policy inside
the published quarter ball is weakened by the computable policy built from its
own numeral profile, at any copy-count envelope dominating the exact copy count
and any wire caps dominating the exact ones.  Both arities and the oracle size
cap are carried over unchanged, so the resource inequalities are the only
content. -/
theorem xorRecoveryWitnessLimits_weakens_computable
    (witness : XorAmplificationWitness) (delta : ℝ)
    (hquarter : delta ≤ 1 / 4)
    (copies copyBound oracleArity oracleSizeCap sumArity
      symmetricWireCap thresholdWireCap
      computableSymmetricWireCap computableThresholdWireCap : ℕ)
    (hcopies : 1 ≤ copies) (hcopyBound : copies ≤ copyBound)
    (hsymmetricWire : symmetricWireCap ≤ computableSymmetricWireCap)
    (hthresholdWire : thresholdWireCap ≤ computableThresholdWireCap) :
    (xorRecoveryWitnessLimits witness delta copies oracleArity oracleSizeCap
        sumArity symmetricWireCap thresholdWireCap)
      |>.Weakens
        (computableXorRecoveryWitnessLimits
          (xorNumeralProfileOf witness delta) copyBound oracleArity
          oracleSizeCap sumArity computableSymmetricWireCap
          computableThresholdWireCap) := by
  have hterm :
      xorAuthorizedTermCap witness delta copies sumArity ≤
        computableTermCap (xorNumeralProfileOf witness delta) copyBound
          sumArity := by
    refine (xorAuthorizedTermCap_le_computable witness delta hquarter copies
      sumArity hcopies).trans ?_
    exact Nat.mul_le_mul_left _
      (Nat.pow_le_pow_right (by omega) hcopyBound)
  have hmass :
      xorAuthorizedRationalMassCap witness delta copies ≤
        computableMassCap (xorNumeralProfileOf witness delta) copyBound := by
    have hnatural :
        ⌈xorAuthorizedCoefficientMass witness delta copies⌉₊ ≤
          ⌈witness.massCoefficient delta⌉₊ * 4 ^ copyBound := by
      refine (xorAuthorizedCoefficientMass_ceil_le_computable witness delta
        hquarter copies hcopies).trans ?_
      exact Nat.mul_le_mul_left _
        (Nat.pow_le_pow_right (by omega) hcopyBound)
    change (⌈xorAuthorizedCoefficientMass witness delta copies⌉₊ : ℚ) ≤
      ((⌈witness.massCoefficient delta⌉₊ * 4 ^ copyBound : ℕ) : ℚ)
    exact_mod_cast hnatural
  exact
    { oracleArity_eq := rfl
      oracleSizeCap_le := le_rfl
      sumArity_eq := rfl
      symmetric :=
        { expectedArity_eq := rfl
          termCap_le := hterm
          coefficientBitCap_le := le_rfl
          coefficientMassCap_le := hmass
          wireCap_le := hsymmetricWire
          descriptionCap_le :=
            symmetricDescriptionCap_mono_wire hsymmetricWire }
      threshold :=
        { expectedArity_eq := rfl
          termCap_le := hterm
          coefficientBitCap_le := le_rfl
          coefficientMassCap_le := hmass
          wireCap_le := hthresholdWire
          descriptionCap_le :=
            thresholdDescriptionCap_mono_wire hthresholdWire } }

/-! ## §4 The inverse-polynomial schedule

The exact copy count is real-derived, so it is replaced by the linear
`logScale` envelope already used by the schedule's own polynomial closure.
Every other field of `inverseRecoveryWitnessSourceLimits` is retained
verbatim: its wire caps are already the cubic core envelope, which is explicit
arithmetic. -/

/-- Frozen copy-count envelope of the inverse schedule. -/
noncomputable def inverseComputableCopyBound
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    (rate sourceIndex : ℕ) : ℕ :=
  inverseCopiesLinearCoefficient outer pcppSource rate *
    logScale (sourceIndex + 1)

/-- **The computable inverse validator policy**, keyed by the source index
recovered from the public input length. -/
noncomputable def computableInverseRecoveryWitnessSourceLimits
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower sourceIndex : ℕ) : RecoveryWitnessLimits :=
  let requiredDegree := inverseRequiredDegree contracts advantagePower
  let rate := inverseRate contracts advantagePower
  let wireCap :=
    inverseRecoverySourceWireCap contracts outer advantagePower sourceIndex
  computableXorRecoveryWitnessLimits
    (xorNumeralProfileOf (publishedXorWitness contracts)
      (publishedRecoveryDelta contracts))
    (inverseComputableCopyBound outer (publishedPointwisePCPP contracts)
      rate sourceIndex)
    (scheduledWidth outer sourceIndex)
    (oracleSizeBound requiredDegree (scheduledWidth outer sourceIndex))
    (seedArity outer (publishedPointwisePCPP contracts)
      requiredDegree sourceIndex)
    wireCap wireCap

/-- Public-arity view of the computable inverse policy.  This is the family
`RecoveryLimitsFrontEndProgram` consumes: its argument is exactly
`WeakVerifierRequest.inputArity`. -/
noncomputable def computableInverseRecoveryWitnessLimitsAtLength
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower inputLength : ℕ) : RecoveryWitnessLimits :=
  computableInverseRecoveryWitnessSourceLimits contracts outer advantagePower
    (sourceIndexOfLength inputLength)

@[simp] theorem computableInverseRecoveryWitnessLimitsAtLength_sourceLength
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower sourceIndex : ℕ) :
    computableInverseRecoveryWitnessLimitsAtLength contracts outer
        advantagePower (sourceLength sourceIndex) =
      computableInverseRecoveryWitnessSourceLimits contracts outer
        advantagePower sourceIndex := by
  simp [computableInverseRecoveryWitnessLimitsAtLength]

/-- The sole inverse validator policy is weakened by its computable image.
Only the two real-valued envelopes move. -/
theorem inverseRecoveryWitnessSourceLimits_weakens_computable
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower sourceIndex : ℕ) :
    (inverseRecoveryWitnessSourceLimits contracts outer advantagePower
        sourceIndex)
      |>.Weakens
        (computableInverseRecoveryWitnessSourceLimits contracts outer
          advantagePower sourceIndex) :=
  xorRecoveryWitnessLimits_weakens_computable (publishedXorWitness contracts)
    (publishedRecoveryDelta contracts)
    (publishedRecoveryDelta_le_quarter contracts)
    (inverseCopies outer (publishedPointwisePCPP contracts)
      (inverseRate contracts advantagePower) sourceIndex)
    (inverseComputableCopyBound outer (publishedPointwisePCPP contracts)
      (inverseRate contracts advantagePower) sourceIndex)
    (scheduledWidth outer sourceIndex)
    (oracleSizeBound (inverseRequiredDegree contracts advantagePower)
      (scheduledWidth outer sourceIndex))
    (seedArity outer (publishedPointwisePCPP contracts)
      (inverseRequiredDegree contracts advantagePower) sourceIndex)
    (inverseRecoverySourceWireCap contracts outer advantagePower sourceIndex)
    (inverseRecoverySourceWireCap contracts outer advantagePower sourceIndex)
    (inverseRecoverySourceWireCap contracts outer advantagePower sourceIndex)
    (inverseRecoverySourceWireCap contracts outer advantagePower sourceIndex)
    (inverseCopies_positive outer (publishedPointwisePCPP contracts)
      (inverseRate contracts advantagePower) sourceIndex)
    (inverseCopies_le_sourceLog outer (publishedPointwisePCPP contracts)
      (inverseRate contracts advantagePower) sourceIndex)
    le_rfl le_rfl

/-- The exact inverse schedule policy at a schedule coordinate is weakened by
the computable policy at the source index that coordinate selects. -/
theorem inverseRecoveryWitnessLimits_weakens_computable
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower scheduleIndex : ℕ) :
    (inverseRecoveryWitnessLimits contracts outer advantagePower scheduleIndex)
      |>.Weakens
        (computableInverseRecoveryWitnessSourceLimits contracts outer
          advantagePower (inverseSourceIndex scheduleIndex)) :=
  recoveryWitnessLimits_weakens_trans
    (inverseRecoveryWitnessLimits_weakens_sourceLimits contracts outer
      advantagePower scheduleIndex)
    (inverseRecoveryWitnessSourceLimits_weakens_computable contracts outer
      advantagePower (inverseSourceIndex scheduleIndex))

/-! ## §5 The fixed-rate schedule

Here the copy count is already a frozen natural; the two wire caps are the
real-floor physical sizes, so they are widened to the same cubic core envelope
the schedule's polynomial closure already uses. -/

/-- Computable wire envelope of the fixed-rate schedule. -/
noncomputable def fixedComputableWireCap
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate sourceIndex : ℕ) : ℕ :=
  (fixedEnvelope contracts outer requestedRate).coreArity sourceIndex ^ 3

/-- **The computable fixed-rate validator policy.** -/
noncomputable def computableFixedRecoveryWitnessLimits
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate sourceIndex : ℕ) : RecoveryWitnessLimits :=
  let requiredDegree := fixedRequiredDegree contracts requestedRate
  let rate := fixedRate contracts requestedRate
  let wireCap :=
    fixedComputableWireCap contracts outer requestedRate sourceIndex
  computableXorRecoveryWitnessLimits
    (xorNumeralProfileOf (publishedXorWitness contracts)
      (publishedRecoveryDelta contracts))
    (fixedCopies (publishedPointwisePCPP contracts) rate)
    (scheduledWidth outer sourceIndex)
    (oracleSizeBound requiredDegree (scheduledWidth outer sourceIndex))
    (seedArity outer (publishedPointwisePCPP contracts)
      requiredDegree sourceIndex)
    wireCap wireCap

/-- Public-arity view of the computable fixed-rate policy. -/
noncomputable def computableFixedRecoveryWitnessLimitsAtLength
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate inputLength : ℕ) : RecoveryWitnessLimits :=
  computableFixedRecoveryWitnessLimits contracts outer requestedRate
    (sourceIndexOfLength inputLength)

@[simp] theorem computableFixedRecoveryWitnessLimitsAtLength_sourceLength
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate sourceIndex : ℕ) :
    computableFixedRecoveryWitnessLimitsAtLength contracts outer requestedRate
        (sourceLength sourceIndex) =
      computableFixedRecoveryWitnessLimits contracts outer requestedRate
        sourceIndex := by
  simp [computableFixedRecoveryWitnessLimitsAtLength]

private theorem fixedPhysicalCoefficient_unit
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate : ℕ) :
    0 ≤ fixedPhysicalCoefficient contracts outer requestedRate ∧
      fixedPhysicalCoefficient contracts outer requestedRate ≤ 1 := by
  refine ⟨(fixedPhysicalCoefficient_positive contracts outer requestedRate).le,
    ?_⟩
  exact fixedPhysicalCoefficient_le_one contracts outer requestedRate

/-- The exact fixed-rate policy is weakened by its computable image. -/
theorem fixedRecoveryWitnessLimits_weakens_computable
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate sourceIndex : ℕ) :
    (fixedRecoveryWitnessLimits contracts outer requestedRate sourceIndex)
      |>.Weakens
        (computableFixedRecoveryWitnessLimits contracts outer requestedRate
          sourceIndex) := by
  obtain ⟨hnonnegative, hone⟩ :=
    fixedPhysicalCoefficient_unit contracts outer requestedRate
  have hsymmetric :
      fixedCaseTwoSymmetricSize contracts outer requestedRate sourceIndex ≤
        fixedComputableWireCap contracts outer requestedRate sourceIndex :=
    wireScale_floor_le_cube hnonnegative hone 5
      ((fixedEnvelope contracts outer requestedRate).coreArity sourceIndex)
  have hthreshold :
      fixedCaseTwoThresholdSize contracts outer requestedRate sourceIndex ≤
        fixedComputableWireCap contracts outer requestedRate sourceIndex :=
    wireScale_floor_le_cube hnonnegative hone 9
      ((fixedEnvelope contracts outer requestedRate).coreArity sourceIndex)
  exact xorRecoveryWitnessLimits_weakens_computable
    (publishedXorWitness contracts) (publishedRecoveryDelta contracts)
    (publishedRecoveryDelta_le_quarter contracts)
    (fixedCopies (publishedPointwisePCPP contracts)
      (fixedRate contracts requestedRate))
    (fixedCopies (publishedPointwisePCPP contracts)
      (fixedRate contracts requestedRate))
    (scheduledWidth outer sourceIndex)
    (oracleSizeBound (fixedRequiredDegree contracts requestedRate)
      (scheduledWidth outer sourceIndex))
    (seedArity outer (publishedPointwisePCPP contracts)
      (fixedRequiredDegree contracts requestedRate) sourceIndex)
    (fixedCaseTwoSymmetricSize contracts outer requestedRate sourceIndex)
    (fixedCaseTwoThresholdSize contracts outer requestedRate sourceIndex)
    (fixedComputableWireCap contracts outer requestedRate sourceIndex)
    (fixedComputableWireCap contracts outer requestedRate sourceIndex)
    (fixedCopies_positive (publishedPointwisePCPP contracts)
      (fixedRate contracts requestedRate))
    le_rfl hsymmetric hthreshold

private theorem normalizedGateDescriptionCap_polynomiallyBounded
    (arity : ℕ → ℕ) (harity : PolynomiallyBounded arity) :
    PolynomiallyBounded
      (fun n => normalizedGateDescriptionCap (arity n)) := by
  have hone := polynomiallyBounded_constant 1
  have hsucc := polynomiallyBounded_add harity hone
  have hsquare := polynomiallyBounded_mul harity harity
  have hproduct := polynomiallyBounded_mul hsucc
    (polynomiallyBounded_add hsquare hone)
  simpa only [normalizedGateDescriptionCap] using
    polynomiallyBounded_add hproduct harity

private theorem symmetricDescriptionCap_polynomiallyBounded
    (arity wireCap : ℕ → ℕ)
    (harity : PolynomiallyBounded arity)
    (hwireCap : PolynomiallyBounded wireCap) :
    PolynomiallyBounded
      (fun n => symmetricDescriptionCap (arity n) (wireCap n)) := by
  have hone := polynomiallyBounded_constant 1
  simpa only [symmetricDescriptionCap] using
    polynomiallyBounded_mul
      (polynomiallyBounded_add hwireCap hone)
      (polynomiallyBounded_add
        (normalizedGateDescriptionCap_polynomiallyBounded arity harity)
        hone)

private theorem thresholdDescriptionCap_polynomiallyBounded
    (arity wireCap : ℕ → ℕ)
    (harity : PolynomiallyBounded arity)
    (hwireCap : PolynomiallyBounded wireCap) :
    PolynomiallyBounded
      (fun n => thresholdDescriptionCap (arity n) (wireCap n)) := by
  simpa only [thresholdDescriptionCap] using
    polynomiallyBounded_add
      (normalizedGateDescriptionCap_polynomiallyBounded wireCap hwireCap)
      (polynomiallyBounded_mul hwireCap
        (normalizedGateDescriptionCap_polynomiallyBounded arity harity))

private theorem computableCoefficientBitCap_polynomiallyBounded
    (profile : XorNumeralProfile) (arity : ℕ → ℕ)
    (harity : PolynomiallyBounded arity) :
    PolynomiallyBounded
      (fun n => computableCoefficientBitCap profile (arity n)) := by
  have hone := polynomiallyBounded_constant 1
  simpa only [computableCoefficientBitCap] using
    polynomiallyBounded_mul
      (polynomiallyBounded_constant profile.coefficientBitCoefficient)
      (polynomiallyBounded_pow (polynomiallyBounded_add harity hone)
        profile.coefficientBitDegree)

private theorem two_pow_clog_le (length : ℕ) :
    2 ^ Nat.clog 2 length ≤ 2 * (length + 1) := by
  by_cases hsmall : length ≤ 1
  · have hclog : Nat.clog 2 length = 0 :=
      Nat.clog_of_right_le_one hsmall 2
    simp [hclog]
    omega
  · have hpositive : 0 < Nat.clog 2 length :=
      Nat.clog_pos (by omega) (by omega)
    have hpred :
        2 ^ (Nat.clog 2 length).pred < length :=
      (Nat.pow_pred_clog_lt_self (by omega) (by omega))
    have heq :
        (Nat.clog 2 length).pred + 1 = Nat.clog 2 length :=
      Nat.succ_pred_eq_of_pos hpositive
    rw [← heq, pow_succ]
    nlinarith

/-- The dyadic weight of a `logScale`-linear copy envelope is still
polynomial.  This is the exact estimate that keeps the computable term cap
inside the executable witness shape. -/
private theorem sixteen_pow_logScale_polynomiallyBounded (coefficient : ℕ) :
    PolynomiallyBounded
      (fun sourceIndex => 16 ^ (coefficient * logScale (sourceIndex + 1))) := by
  apply polynomiallyBounded_mono
    (larger := fun sourceIndex => (2 * (sourceIndex + 4)) ^ (4 * coefficient))
  · intro sourceIndex
    have htwo :
        2 ^ logScale (sourceIndex + 1) ≤ 2 * (sourceIndex + 4) := by
      simpa [logScale, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using two_pow_clog_le (sourceIndex + 3)
    calc
      16 ^ (coefficient * logScale (sourceIndex + 1)) =
          (2 ^ logScale (sourceIndex + 1)) ^ (4 * coefficient) := by
        rw [show 16 = 2 ^ 4 by norm_num]
        simp only [← pow_mul]
        congr 1
        ring
      _ ≤ (2 * (sourceIndex + 4)) ^ (4 * coefficient) :=
        Nat.pow_le_pow_left htwo (4 * coefficient)
  · exact polynomiallyBounded_pow
      (polynomiallyBounded_mul
        (polynomiallyBounded_constant 2)
        (polynomiallyBounded_add polynomiallyBounded_id
          (polynomiallyBounded_constant 4)))
      (4 * coefficient)

private theorem coreArity_polynomiallyBounded
    {rawArity : ℕ → ℕ} (envelope : SmoothCoreEnvelope rawArity) :
    PolynomiallyBounded envelope.coreArity :=
  ⟨envelope.coefficient, envelope.degree,
    envelope.coefficientPositive, fun _ => le_rfl⟩

private theorem inverseRecoveryScheduleCeiling_polynomiallyBounded :
    PolynomiallyBounded inverseRecoveryScheduleCeiling := by
  apply polynomiallyBounded_mono
    (larger := fun sourceIndex => (sourceIndex + 2) * (sourceIndex + 4))
  · intro sourceIndex
    calc
      inverseRecoveryScheduleCeiling sourceIndex ≤
          inverseSourceMeasure (sourceIndex + 1) :=
        Nat.sub_le _ _
      _ ≤ (sourceIndex + 2) * (sourceIndex + 4) := by
        unfold inverseSourceMeasure
        gcongr
        simpa only [Nat.add_assoc] using
          logScale_le_add_two (sourceIndex + 2)
  · exact polynomiallyBounded_mul
      (polynomiallyBounded_add polynomiallyBounded_id
        (polynomiallyBounded_constant 2))
      (polynomiallyBounded_add polynomiallyBounded_id
        (polynomiallyBounded_constant 4))

/-- Every syntactic field of the computable inverse policy is polynomial in
the source index. -/
theorem computableInverseRecoveryWitnessCodeBitBound_polynomiallyBounded
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower : ℕ) :
    PolynomiallyBounded
      (fun sourceIndex =>
        recoveryWitnessCodeBitBound
          (computableInverseRecoveryWitnessSourceLimits contracts outer
            advantagePower sourceIndex)) := by
  let profile :=
    xorNumeralProfileOf (publishedXorWitness contracts)
      (publishedRecoveryDelta contracts)
  let requiredDegree := inverseRequiredDegree contracts advantagePower
  let rate := inverseRate contracts advantagePower
  let arity := seedArity outer (publishedPointwisePCPP contracts)
    requiredDegree
  let wire := inverseRecoverySourceWireCap contracts outer advantagePower
  have horacleArity := scheduledWidth_polynomiallyBounded outer
  have horacleSize :=
    scheduledOracleSize_polynomiallyBounded outer requiredDegree
  have harity : PolynomiallyBounded arity :=
    seedArity_polynomiallyBounded outer
      (publishedPointwisePCPP contracts) requiredDegree
  have hcore :
      PolynomiallyBounded
        (fun sourceIndex =>
          (inverseEnvelope contracts outer advantagePower).coreArity
            (inverseRecoveryScheduleCeiling sourceIndex)) :=
    polynomiallyBounded_comp
      (coreArity_polynomiallyBounded
        (inverseEnvelope contracts outer advantagePower))
      inverseRecoveryScheduleCeiling_polynomiallyBounded
  have hwire : PolynomiallyBounded wire := by
    change PolynomiallyBounded
      (fun sourceIndex =>
        (inverseEnvelope contracts outer advantagePower).coreArity
          (inverseRecoveryScheduleCeiling sourceIndex) ^ 3)
    exact polynomiallyBounded_pow hcore 3
  have hcopyPower :
      PolynomiallyBounded
        (fun sourceIndex =>
          16 ^ inverseComputableCopyBound outer
            (publishedPointwisePCPP contracts) rate sourceIndex) := by
    change PolynomiallyBounded
      (fun sourceIndex =>
        16 ^ (inverseCopiesLinearCoefficient outer
          (publishedPointwisePCPP contracts) rate *
            logScale (sourceIndex + 1)))
    exact sixteen_pow_logScale_polynomiallyBounded _
  have hterm :
      PolynomiallyBounded
        (fun sourceIndex =>
          computableTermCap profile
            (inverseComputableCopyBound outer
              (publishedPointwisePCPP contracts) rate sourceIndex)
            (arity sourceIndex)) := by
    simpa only [computableTermCap] using
      polynomiallyBounded_mul
        (polynomiallyBounded_mul
          (polynomiallyBounded_constant profile.termCoefficientCap) harity)
        hcopyPower
  have hcoefficient :
      PolynomiallyBounded
        (fun sourceIndex =>
          computableCoefficientBitCap profile (arity sourceIndex)) :=
    computableCoefficientBitCap_polynomiallyBounded profile arity harity
  have hsymmetricDescription :
      PolynomiallyBounded
        (fun sourceIndex =>
          symmetricDescriptionCap (arity sourceIndex) (wire sourceIndex)) :=
    symmetricDescriptionCap_polynomiallyBounded arity wire harity hwire
  have hthresholdDescription :
      PolynomiallyBounded
        (fun sourceIndex =>
          thresholdDescriptionCap (arity sourceIndex) (wire sourceIndex)) :=
    thresholdDescriptionCap_polynomiallyBounded arity wire harity hwire
  apply recoveryWitnessCodeBitBound_polynomiallyBounded
  apply recoveryWitnessCodeParameter_polynomiallyBounded
  · simpa only [computableInverseRecoveryWitnessSourceLimits,
      computableXorRecoveryWitnessLimits] using horacleArity
  · simpa only [computableInverseRecoveryWitnessSourceLimits,
      computableXorRecoveryWitnessLimits] using horacleSize
  · simpa only [computableInverseRecoveryWitnessSourceLimits,
      computableXorRecoveryWitnessLimits] using harity
  · simpa only [computableInverseRecoveryWitnessSourceLimits,
      computableXorRecoveryWitnessLimits,
      computableSymmetricLegalSumLimits] using hterm
  · simpa only [computableInverseRecoveryWitnessSourceLimits,
      computableXorRecoveryWitnessLimits,
      computableSymmetricLegalSumLimits] using hcoefficient
  · simpa only [computableInverseRecoveryWitnessSourceLimits,
      computableXorRecoveryWitnessLimits,
      computableSymmetricLegalSumLimits] using hwire
  · simpa only [computableInverseRecoveryWitnessSourceLimits,
      computableXorRecoveryWitnessLimits,
      computableSymmetricLegalSumLimits] using hsymmetricDescription
  · simpa only [computableInverseRecoveryWitnessSourceLimits,
      computableXorRecoveryWitnessLimits,
      computableThresholdLegalSumLimits] using hterm
  · simpa only [computableInverseRecoveryWitnessSourceLimits,
      computableXorRecoveryWitnessLimits,
      computableThresholdLegalSumLimits] using hcoefficient
  · simpa only [computableInverseRecoveryWitnessSourceLimits,
      computableXorRecoveryWitnessLimits,
      computableThresholdLegalSumLimits] using hwire
  · simpa only [computableInverseRecoveryWitnessSourceLimits,
      computableXorRecoveryWitnessLimits,
      computableThresholdLegalSumLimits] using hthresholdDescription

/-- Every syntactic field of the computable fixed-rate policy is polynomial in
the source index. -/
theorem computableFixedRecoveryWitnessCodeBitBound_polynomiallyBounded
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate : ℕ) :
    PolynomiallyBounded
      (fun sourceIndex =>
        recoveryWitnessCodeBitBound
          (computableFixedRecoveryWitnessLimits contracts outer requestedRate
            sourceIndex)) := by
  let profile :=
    xorNumeralProfileOf (publishedXorWitness contracts)
      (publishedRecoveryDelta contracts)
  let requiredDegree := fixedRequiredDegree contracts requestedRate
  let rate := fixedRate contracts requestedRate
  let arity := seedArity outer (publishedPointwisePCPP contracts)
    requiredDegree
  let wire := fixedComputableWireCap contracts outer requestedRate
  have horacleArity := scheduledWidth_polynomiallyBounded outer
  have horacleSize :=
    scheduledOracleSize_polynomiallyBounded outer requiredDegree
  have harity : PolynomiallyBounded arity :=
    seedArity_polynomiallyBounded outer
      (publishedPointwisePCPP contracts) requiredDegree
  have hwire : PolynomiallyBounded wire := by
    change PolynomiallyBounded
      (fun sourceIndex =>
        (fixedEnvelope contracts outer requestedRate).coreArity sourceIndex ^ 3)
    exact polynomiallyBounded_pow
      (coreArity_polynomiallyBounded
        (fixedEnvelope contracts outer requestedRate)) 3
  have hterm :
      PolynomiallyBounded
        (fun sourceIndex =>
          computableTermCap profile
            (fixedCopies (publishedPointwisePCPP contracts) rate)
            (arity sourceIndex)) := by
    simpa only [computableTermCap] using
      polynomiallyBounded_mul
        (polynomiallyBounded_mul
          (polynomiallyBounded_constant profile.termCoefficientCap) harity)
        (polynomiallyBounded_constant
          (16 ^ fixedCopies (publishedPointwisePCPP contracts) rate))
  have hcoefficient :
      PolynomiallyBounded
        (fun sourceIndex =>
          computableCoefficientBitCap profile (arity sourceIndex)) :=
    computableCoefficientBitCap_polynomiallyBounded profile arity harity
  have hsymmetricDescription :
      PolynomiallyBounded
        (fun sourceIndex =>
          symmetricDescriptionCap (arity sourceIndex) (wire sourceIndex)) :=
    symmetricDescriptionCap_polynomiallyBounded arity wire harity hwire
  have hthresholdDescription :
      PolynomiallyBounded
        (fun sourceIndex =>
          thresholdDescriptionCap (arity sourceIndex) (wire sourceIndex)) :=
    thresholdDescriptionCap_polynomiallyBounded arity wire harity hwire
  apply recoveryWitnessCodeBitBound_polynomiallyBounded
  apply recoveryWitnessCodeParameter_polynomiallyBounded
  · simpa only [computableFixedRecoveryWitnessLimits,
      computableXorRecoveryWitnessLimits] using horacleArity
  · simpa only [computableFixedRecoveryWitnessLimits,
      computableXorRecoveryWitnessLimits] using horacleSize
  · simpa only [computableFixedRecoveryWitnessLimits,
      computableXorRecoveryWitnessLimits] using harity
  · simpa only [computableFixedRecoveryWitnessLimits,
      computableXorRecoveryWitnessLimits,
      computableSymmetricLegalSumLimits] using hterm
  · simpa only [computableFixedRecoveryWitnessLimits,
      computableXorRecoveryWitnessLimits,
      computableSymmetricLegalSumLimits] using hcoefficient
  · simpa only [computableFixedRecoveryWitnessLimits,
      computableXorRecoveryWitnessLimits,
      computableSymmetricLegalSumLimits] using hwire
  · simpa only [computableFixedRecoveryWitnessLimits,
      computableXorRecoveryWitnessLimits,
      computableSymmetricLegalSumLimits] using hsymmetricDescription
  · simpa only [computableFixedRecoveryWitnessLimits,
      computableXorRecoveryWitnessLimits,
      computableThresholdLegalSumLimits] using hterm
  · simpa only [computableFixedRecoveryWitnessLimits,
      computableXorRecoveryWitnessLimits,
      computableThresholdLegalSumLimits] using hcoefficient
  · simpa only [computableFixedRecoveryWitnessLimits,
      computableXorRecoveryWitnessLimits,
      computableThresholdLegalSumLimits] using hwire
  · simpa only [computableFixedRecoveryWitnessLimits,
      computableXorRecoveryWitnessLimits,
      computableThresholdLegalSumLimits] using hthresholdDescription

/-! ## §7 Eventual capacity in the executable witness shape

These are the exact analogues of the schedule-capacity theorems, re-derived at
the computable family.  The onsets are internally derived from §6; no capacity
premise is left to a caller. -/

/-- The computable inverse policy eventually fits the executable `n / 16`
witness shape at the source length it is keyed by. -/
theorem computableInverseRecoveryWitnessSource_eventually_fits
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower : ℕ) :
    ∃ onset, ∀ sourceIndex, onset ≤ sourceIndex →
      recoveryWitnessCodeBitBound
          (computableInverseRecoveryWitnessSourceLimits contracts outer
            advantagePower sourceIndex) ≤
        recoveryWitnessWidth (sourceLength sourceIndex) := by
  obtain ⟨onset, hcapacity⟩ :=
    polynomiallyBounded_eventually_le_sixteenth_exponential
      (computableInverseRecoveryWitnessCodeBitBound_polynomiallyBounded
        contracts outer advantagePower)
  exact ⟨onset, fun sourceIndex honset => by
    simpa only [sourceLength, recoveryWitnessWidth_eq] using
      hcapacity sourceIndex honset⟩

/-- Transport of the computable capacity onset back to inverse schedule
coordinates. -/
theorem computableInverseRecoveryWitnessSource_eventually_fits_at_schedule
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower : ℕ) :
    ∃ onset, ∀ scheduleIndex, onset ≤ scheduleIndex →
      recoveryWitnessCodeBitBound
          (computableInverseRecoveryWitnessSourceLimits contracts outer
            advantagePower (inverseSourceIndex scheduleIndex)) ≤
        recoveryWitnessWidth
          (sourceLength (inverseSourceIndex scheduleIndex)) := by
  obtain ⟨sourceOnset, hcapacity⟩ :=
    computableInverseRecoveryWitnessSource_eventually_fits contracts outer
      advantagePower
  refine
    ⟨inverseSourceMeasure sourceOnset, fun scheduleIndex honset => ?_⟩
  have hsourceOnset :
      sourceOnset ≤ inverseSourceIndex scheduleIndex := by
    apply le_inverseSourceIndex_of_measure_le
    exact honset.trans (by omega)
  exact hcapacity (inverseSourceIndex scheduleIndex) hsourceOnset

/-- Zero-extension preserves every checked witness of the computable inverse
policy after the internally derived onset. -/
theorem computableInverseRecoveryWitness_eventual_readback
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower : ℕ) :
    ∃ onset, ∀ scheduleIndex, onset ≤ scheduleIndex →
      ∀ witness : CheckedRecoveryWitness
          (computableInverseRecoveryWitnessSourceLimits contracts outer
            advantagePower (inverseSourceIndex scheduleIndex)),
        encodeBitInput
            (paddedRecoveryWitnessCode
              (sourceLength (inverseSourceIndex scheduleIndex)) witness) =
          witness.code := by
  obtain ⟨onset, hcapacity⟩ :=
    computableInverseRecoveryWitnessSource_eventually_fits_at_schedule
      contracts outer advantagePower
  exact ⟨onset, fun scheduleIndex honset witness =>
    encodeBitInput_paddedRecoveryWitnessCode witness
      (hcapacity scheduleIndex honset)⟩

def ComputableInverseRecoveryWitnessAuditAt
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower target : ℕ) : Prop :=
  let scheduleIndex :=
    inverseSelectedSource contracts outer advantagePower target
  recoveryWitnessCodeBitBound
      (computableInverseRecoveryWitnessSourceLimits contracts outer
        advantagePower (inverseSourceIndex scheduleIndex)) ≤
    recoveryWitnessWidth
      (sourceLength (inverseSourceIndex scheduleIndex))

theorem computableInverseRecoveryWitnessAudit_eventually
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower : ℕ) :
    ∃ onset, ∀ target, onset ≤ target →
      ComputableInverseRecoveryWitnessAuditAt contracts outer advantagePower
        target := by
  obtain ⟨scheduleOnset, hcapacity⟩ :=
    computableInverseRecoveryWitnessSource_eventually_fits_at_schedule
      contracts outer advantagePower
  let envelope := inverseEnvelope contracts outer advantagePower
  refine
    ⟨max envelope.targetOnset
      (2 * envelope.coreArity scheduleOnset), fun target htarget => ?_⟩
  have henvelope : envelope.targetOnset ≤ target :=
    (le_max_left _ _).trans htarget
  have hsourceTarget :
      2 * envelope.coreArity scheduleOnset ≤ target :=
    (le_max_right _ _).trans htarget
  have hschedule :
      scheduleOnset ≤
        inverseSelectedSource contracts outer advantagePower target :=
    (inverseSchedule contracts outer advantagePower).output_source_ge
      target henvelope scheduleOnset hsourceTarget
  exact hcapacity
    (inverseSelectedSource contracts outer advantagePower target) hschedule

/-- The computable fixed-rate policy eventually fits the executable witness
shape. -/
theorem computableFixedRecoveryWitness_eventually_fits
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate : ℕ) :
    ∃ onset, ∀ sourceIndex, onset ≤ sourceIndex →
      recoveryWitnessCodeBitBound
          (computableFixedRecoveryWitnessLimits contracts outer requestedRate
            sourceIndex) ≤
        recoveryWitnessWidth (sourceLength sourceIndex) := by
  obtain ⟨onset, hcapacity⟩ :=
    polynomiallyBounded_eventually_le_sixteenth_exponential
      (computableFixedRecoveryWitnessCodeBitBound_polynomiallyBounded
        contracts outer requestedRate)
  exact ⟨onset, fun sourceIndex honset => by
    simpa only [sourceLength, recoveryWitnessWidth_eq] using
      hcapacity sourceIndex honset⟩

theorem computableFixedRecoveryWitness_eventual_readback
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate : ℕ) :
    ∃ onset, ∀ sourceIndex, onset ≤ sourceIndex →
      ∀ witness : CheckedRecoveryWitness
          (computableFixedRecoveryWitnessLimits contracts outer requestedRate
            sourceIndex),
        encodeBitInput
            (paddedRecoveryWitnessCode (sourceLength sourceIndex) witness) =
          witness.code := by
  obtain ⟨onset, hcapacity⟩ :=
    computableFixedRecoveryWitness_eventually_fits contracts outer requestedRate
  exact ⟨onset, fun sourceIndex honset witness =>
    encodeBitInput_paddedRecoveryWitnessCode witness
      (hcapacity sourceIndex honset)⟩

def ComputableFixedRecoveryWitnessAuditAt
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate target : ℕ) : Prop :=
  let sourceIndex :=
    fixedSelectedSource contracts outer requestedRate target
  recoveryWitnessCodeBitBound
      (computableFixedRecoveryWitnessLimits contracts outer requestedRate
        sourceIndex) ≤
    recoveryWitnessWidth (sourceLength sourceIndex)

theorem computableFixedRecoveryWitnessAudit_eventually
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate : ℕ) :
    ∃ onset, ∀ target, onset ≤ target →
      ComputableFixedRecoveryWitnessAuditAt contracts outer requestedRate
        target := by
  obtain ⟨sourceOnset, hcapacity⟩ :=
    computableFixedRecoveryWitness_eventually_fits contracts outer requestedRate
  let envelope := fixedEnvelope contracts outer requestedRate
  refine
    ⟨max envelope.targetOnset
      (2 * envelope.coreArity sourceOnset), fun target htarget => ?_⟩
  have henvelope : envelope.targetOnset ≤ target :=
    (le_max_left _ _).trans htarget
  have hsourceTarget :
      2 * envelope.coreArity sourceOnset ≤ target :=
    (le_max_right _ _).trans htarget
  have hsource :
      sourceOnset ≤
        fixedSelectedSource contracts outer requestedRate target :=
    (fixedSchedule contracts outer requestedRate).output_source_ge
      target henvelope sourceOnset hsourceTarget
  exact hcapacity
    (fixedSelectedSource contracts outer requestedRate target) hsource

/-! ## §8 Case-2 completeness at the computable family

The completeness chain of `CaseTwoWitnessCompleteness` is limits-parametric:
the semantic witness is produced at the exact XOR policy, rechecked under a
weaker policy by `CheckedRecoveryWitness.widen`, and accepted once the policy
fits the executable witness shape.  Instantiating that chain at the computable
family therefore costs exactly the two facts proved above — the weakening and
the capacity onset — and no new serialization path. -/

/-- Sole verifier-run hypothesis of Case-2 completeness, at the computable
inverse policy the limits front end can actually install. -/
def ComputableInverseCaseTwoVerifierCompleteness
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) : Prop :=
  ∀ (scheduleIndex : ℕ)
    (input : BitInput (sourceLength (inverseSourceIndex scheduleIndex)))
    (caseTwo : CanonicalAcceptingOracle
      (sizeBound := oracleSizeBound
        (inverseRequiredDegree contracts advantagePower))
      (paddedOuterPCP outer) input),
    RecoveryVerifierAcceptsApproximation machine
      (computableInverseRecoveryWitnessSourceLimits contracts outer
        advantagePower (inverseSourceIndex scheduleIndex))
      (publishedRecoveryDelta contracts) input
      (caseTwoSeed (publishedPointwisePCPP contracts) caseTwo)

/-- Canonical inverse-schedule witness rechecked in the computable policy,
carrying the executed approximation check.  Widening changes no canonical
bits, so the public witness ABI is unchanged. -/
private theorem computableInverseApproximatingWitness
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower scheduleIndex : ℕ)
    {input : BitInput (sourceLength (inverseSourceIndex scheduleIndex))}
    (caseTwo : CanonicalAcceptingOracle
      (sizeBound := oracleSizeBound
        (inverseRequiredDegree contracts advantagePower))
      (paddedOuterPCP outer) input)
    (approximation :
      PublishedLegalApproximation contracts
        (caseTwoSeed (publishedPointwisePCPP contracts) caseTwo)
        (inverseCopies outer (publishedPointwisePCPP contracts)
          (inverseRate contracts advantagePower)
          (inverseSourceIndex scheduleIndex))
        (inverseCaseTwoSymmetricSize contracts outer advantagePower
          scheduleIndex)
        (inverseCaseTwoThresholdSize contracts outer advantagePower
          scheduleIndex)) :
    ∃ witness : CheckedRecoveryWitness
      (computableInverseRecoveryWitnessSourceLimits contracts outer
        advantagePower (inverseSourceIndex scheduleIndex)),
      RecoveryWitnessApproximates
        (caseTwoSeed (publishedPointwisePCPP contracts) caseTwo)
        (publishedRecoveryDelta contracts) witness := by
  obtain ⟨witness, happroximates⟩ :=
    exists_approximatingCheckedRecoveryWitness contracts
      (inverseCopies outer (publishedPointwisePCPP contracts)
        (inverseRate contracts advantagePower)
        (inverseSourceIndex scheduleIndex))
      (inverseCaseTwoSymmetricSize contracts outer advantagePower
        scheduleIndex)
      (inverseCaseTwoThresholdSize contracts outer advantagePower
        scheduleIndex)
      (caseTwoSeed (publishedPointwisePCPP contracts) caseTwo)
      caseTwo.circuit caseTwo.sizeBounded approximation
  exact
    ⟨witness.widen
        (inverseRecoveryWitnessLimits_weakens_computable contracts outer
          advantagePower scheduleIndex),
      recoveryWitnessApproximates_widen
        (inverseRecoveryWitnessLimits contracts outer advantagePower
          scheduleIndex)
        (computableInverseRecoveryWitnessSourceLimits contracts outer
          advantagePower (inverseSourceIndex scheduleIndex))
        (inverseRecoveryWitnessLimits_weakens_computable contracts outer
          advantagePower scheduleIndex)
        (caseTwoSeed (publishedPointwisePCPP contracts) caseTwo)
        (publishedRecoveryDelta contracts) witness happroximates⟩

/-- **Case-2 completeness at the computable inverse family**, in schedule
coordinates.  The conclusion is literally the schedule's own acceptance
predicate: it mentions no policy, so this is a drop-in replacement for
`inverseCaseTwoAcceptance_eventually`. -/
theorem computableInverseCaseTwoAcceptance_eventually
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (hshape : machine.witnessShape = recoveryWitnessShape)
    (hverifier :
      ComputableInverseCaseTwoVerifierCompleteness contracts outer
        advantagePower machine) :
    ∃ onset, ∀ scheduleIndex, onset ≤ scheduleIndex →
      ∀ (input : BitInput (sourceLength (inverseSourceIndex scheduleIndex)))
        (caseTwo : CanonicalAcceptingOracle
          (sizeBound := oracleSizeBound
            (inverseRequiredDegree contracts advantagePower))
          (paddedOuterPCP outer) input),
        InverseCaseTwoAcceptance contracts outer advantagePower scheduleIndex
          caseTwo machine := by
  obtain ⟨onset, hcapacity⟩ :=
    computableInverseRecoveryWitnessSource_eventually_fits_at_schedule
      contracts outer advantagePower
  refine ⟨onset, fun scheduleIndex honset input caseTwo => ?_⟩
  intro approximation
  obtain ⟨witness, happroximates⟩ :=
    computableInverseApproximatingWitness contracts outer advantagePower
      scheduleIndex caseTwo approximation
  exact accepts_of_verifierAcceptsApproximation machine hshape
    (computableInverseRecoveryWitnessSourceLimits contracts outer
      advantagePower (inverseSourceIndex scheduleIndex))
    (publishedRecoveryDelta contracts)
    (sourceLength (inverseSourceIndex scheduleIndex)) input
    (caseTwoSeed (publishedPointwisePCPP contracts) caseTwo)
    (hverifier scheduleIndex input caseTwo) witness
    (hcapacity scheduleIndex honset) happroximates

/-- Target-indexed form, the shape consumed by the inverse recovery
constructor. -/
theorem computableInverseCaseTwoAcceptance_eventually_at_target
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (hshape : machine.witnessShape = recoveryWitnessShape)
    (hverifier :
      ComputableInverseCaseTwoVerifierCompleteness contracts outer
        advantagePower machine) :
    ∃ onset, ∀ target, onset ≤ target →
      ∀ (input : BitInput
          (sourceLength (inverseSourceIndex
            (inverseSelectedSource contracts outer advantagePower target))))
        (caseTwo : CanonicalAcceptingOracle
          (sizeBound := oracleSizeBound
            (inverseRequiredDegree contracts advantagePower))
          (paddedOuterPCP outer) input),
        InverseCaseTwoAcceptance contracts outer advantagePower
          (inverseSelectedSource contracts outer advantagePower target)
          caseTwo machine := by
  obtain ⟨scheduleOnset, hacceptance⟩ :=
    computableInverseCaseTwoAcceptance_eventually contracts outer
      advantagePower machine hshape hverifier
  let envelope := inverseEnvelope contracts outer advantagePower
  refine
    ⟨max envelope.targetOnset (2 * envelope.coreArity scheduleOnset),
      fun target htarget input caseTwo => ?_⟩
  have henvelope : envelope.targetOnset ≤ target :=
    (le_max_left _ _).trans htarget
  have hsourceTarget :
      2 * envelope.coreArity scheduleOnset ≤ target :=
    (le_max_right _ _).trans htarget
  have hschedule :
      scheduleOnset ≤
        inverseSelectedSource contracts outer advantagePower target :=
    (inverseSchedule contracts outer advantagePower).output_source_ge
      target henvelope scheduleOnset hsourceTarget
  exact hacceptance
    (inverseSelectedSource contracts outer advantagePower target) hschedule
    input caseTwo

/-- Sole verifier-run hypothesis at the computable fixed-rate policy. -/
def ComputableFixedCaseTwoVerifierCompleteness
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) : Prop :=
  ∀ (sourceIndex : ℕ) (input : BitInput (sourceLength sourceIndex))
    (caseTwo : CanonicalAcceptingOracle
      (sizeBound := oracleSizeBound
        (fixedRequiredDegree contracts requestedRate))
      (paddedOuterPCP outer) input),
    RecoveryVerifierAcceptsApproximation machine
      (computableFixedRecoveryWitnessLimits contracts outer requestedRate
        sourceIndex)
      (publishedRecoveryDelta contracts) input
      (caseTwoSeed (publishedPointwisePCPP contracts) caseTwo)

private theorem computableFixedApproximatingWitness
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate sourceIndex : ℕ)
    {input : BitInput (sourceLength sourceIndex)}
    (caseTwo : CanonicalAcceptingOracle
      (sizeBound := oracleSizeBound
        (fixedRequiredDegree contracts requestedRate))
      (paddedOuterPCP outer) input)
    (approximation :
      PublishedLegalApproximation contracts
        (caseTwoSeed (publishedPointwisePCPP contracts) caseTwo)
        (fixedCopies (publishedPointwisePCPP contracts)
          (fixedRate contracts requestedRate))
        (fixedCaseTwoSymmetricSize contracts outer requestedRate sourceIndex)
        (fixedCaseTwoThresholdSize contracts outer requestedRate sourceIndex)) :
    ∃ witness : CheckedRecoveryWitness
      (computableFixedRecoveryWitnessLimits contracts outer requestedRate
        sourceIndex),
      RecoveryWitnessApproximates
        (caseTwoSeed (publishedPointwisePCPP contracts) caseTwo)
        (publishedRecoveryDelta contracts) witness := by
  obtain ⟨witness, happroximates⟩ :=
    exists_approximatingCheckedRecoveryWitness contracts
      (fixedCopies (publishedPointwisePCPP contracts)
        (fixedRate contracts requestedRate))
      (fixedCaseTwoSymmetricSize contracts outer requestedRate sourceIndex)
      (fixedCaseTwoThresholdSize contracts outer requestedRate sourceIndex)
      (caseTwoSeed (publishedPointwisePCPP contracts) caseTwo)
      caseTwo.circuit caseTwo.sizeBounded approximation
  exact
    ⟨witness.widen
        (fixedRecoveryWitnessLimits_weakens_computable contracts outer
          requestedRate sourceIndex),
      recoveryWitnessApproximates_widen
        (fixedRecoveryWitnessLimits contracts outer requestedRate sourceIndex)
        (computableFixedRecoveryWitnessLimits contracts outer requestedRate
          sourceIndex)
        (fixedRecoveryWitnessLimits_weakens_computable contracts outer
          requestedRate sourceIndex)
        (caseTwoSeed (publishedPointwisePCPP contracts) caseTwo)
        (publishedRecoveryDelta contracts) witness happroximates⟩

/-- **Case-2 completeness at the computable fixed-rate family**, in source
coordinates. -/
theorem computableFixedCaseTwoAcceptance_eventually
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (hshape : machine.witnessShape = recoveryWitnessShape)
    (hverifier :
      ComputableFixedCaseTwoVerifierCompleteness contracts outer requestedRate
        machine) :
    ∃ onset, ∀ sourceIndex, onset ≤ sourceIndex →
      ∀ (input : BitInput (sourceLength sourceIndex))
        (caseTwo : CanonicalAcceptingOracle
          (sizeBound := oracleSizeBound
            (fixedRequiredDegree contracts requestedRate))
          (paddedOuterPCP outer) input),
        FixedCaseTwoAcceptance contracts outer requestedRate sourceIndex
          caseTwo machine := by
  obtain ⟨onset, hcapacity⟩ :=
    computableFixedRecoveryWitness_eventually_fits contracts outer requestedRate
  refine ⟨onset, fun sourceIndex honset input caseTwo => ?_⟩
  intro approximation
  obtain ⟨witness, happroximates⟩ :=
    computableFixedApproximatingWitness contracts outer requestedRate
      sourceIndex caseTwo approximation
  exact accepts_of_verifierAcceptsApproximation machine hshape
    (computableFixedRecoveryWitnessLimits contracts outer requestedRate
      sourceIndex)
    (publishedRecoveryDelta contracts) (sourceLength sourceIndex) input
    (caseTwoSeed (publishedPointwisePCPP contracts) caseTwo)
    (hverifier sourceIndex input caseTwo) witness
    (hcapacity sourceIndex honset) happroximates

/-- Target-indexed form of fixed-rate Case-2 completeness. -/
theorem computableFixedCaseTwoAcceptance_eventually_at_target
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (hshape : machine.witnessShape = recoveryWitnessShape)
    (hverifier :
      ComputableFixedCaseTwoVerifierCompleteness contracts outer requestedRate
        machine) :
    ∃ onset, ∀ target, onset ≤ target →
      ∀ (input : BitInput
          (sourceLength
            (fixedSelectedSource contracts outer requestedRate target)))
        (caseTwo : CanonicalAcceptingOracle
          (sizeBound := oracleSizeBound
            (fixedRequiredDegree contracts requestedRate))
          (paddedOuterPCP outer) input),
        FixedCaseTwoAcceptance contracts outer requestedRate
          (fixedSelectedSource contracts outer requestedRate target)
          caseTwo machine := by
  obtain ⟨sourceOnset, hacceptance⟩ :=
    computableFixedCaseTwoAcceptance_eventually contracts outer requestedRate
      machine hshape hverifier
  let envelope := fixedEnvelope contracts outer requestedRate
  refine
    ⟨max envelope.targetOnset (2 * envelope.coreArity sourceOnset),
      fun target htarget input caseTwo => ?_⟩
  have henvelope : envelope.targetOnset ≤ target :=
    (le_max_left _ _).trans htarget
  have hsourceTarget :
      2 * envelope.coreArity sourceOnset ≤ target :=
    (le_max_right _ _).trans htarget
  have hsource :
      sourceOnset ≤
        fixedSelectedSource contracts outer requestedRate target :=
    (fixedSchedule contracts outer requestedRate).output_source_ge
      target henvelope sourceOnset hsourceTarget
  exact hacceptance
    (fixedSelectedSource contracts outer requestedRate target) hsource
    input caseTwo

end NearCubicWires.RecoveryLimitsComputableFamily
