import Proof.Amplification.CaseTwoRecoveryAssembly
import Proof.Circuits.PhysicalHeadlineAdapters
import Proof.Amplification.RecoveryWitnessNormalization
import Proof.Amplification.RecoveryWitnessShape

/-!
# Scheduled capacity of canonical recovery witnesses

This module freezes the exact Case-2 decoder limits for both published
schedules and proves that their complete canonical encodings eventually fit
the executable `n / 16` witness shape.  The capacity proof is derived from the
fixed-delta XOR syntax envelopes and source schedule; callers supply no bound
on an encoded witness.
-/

namespace NearCubicWires.RecoveryWitnessScheduleCapacity

open NearCubicWires
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoRecoveryAssembly
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PhysicalHardness
open NearCubicWires.PhysicalHeadlineAdapters
open NearCubicWires.PolynomialSchedule
open NearCubicWires.ProjectionWidthEnvelope
open NearCubicWires.RecoveryPipeline
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RecoveryWitnessNormalization
open NearCubicWires.RecoveryWitnessPolicy
open NearCubicWires.RecoveryWitnessShape
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.HeadlineClosure

/-- Quarter-power lower bound on the XOR advantage at any radius inside the
published quarter ball.  Stated at a general radius so the schedule's
approximation radius is free to shrink. -/
private theorem xorEpsilon_quarter_lower {delta : ℝ}
    (_hnonneg : 0 ≤ delta) (hquarter : delta ≤ 1 / 4)
    (copies : ℕ) (hcopies : 1 ≤ copies) :
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

/-- Radius-generic form of the term-cap estimate.  Stating it at an arbitrary
radius inside the quarter ball is what keeps the estimate independent of the
magnitude of the published schedule constants. -/
private theorem xorAuthorizedTermCap_le
    (witness : NearCubicWires.RecoveryPipeline.XorAmplificationWitness)
    (delta : ℝ) (hnonneg : 0 ≤ delta) (hquarter : delta ≤ 1 / 4)
    (copies arity : ℕ) (hcopies : 1 ≤ copies) :
    xorAuthorizedTermCap witness delta copies arity ≤
      ⌈witness.termCoefficient delta⌉₊ *
        arity * 16 ^ copies := by
  apply Nat.ceil_le.mpr
  have hepsilon := xorEpsilon_quarter_lower hnonneg hquarter copies hcopies
  have hepsilonPositive :
      0 < xorEpsilon delta copies := by
    exact mul_pos (pow_pos (by linarith) (copies - 1)) (by linarith)
  have hcoefficient :
      witness.termCoefficient delta ≤
        (⌈witness.termCoefficient delta⌉₊ : ℝ) :=
    Nat.le_ceil _
  have hdenominator :
      (1 / (4 : ℝ) ^ copies) ^ 2 ≤
        xorEpsilon delta copies ^ 2 := by
    gcongr
  change
    witness.termCoefficient delta * arity /
        xorEpsilon delta copies ^ 2 ≤
      ((⌈witness.termCoefficient delta⌉₊ *
        arity * 16 ^ copies : ℕ) : ℝ)
  apply (div_le_iff₀ (sq_pos_of_pos hepsilonPositive)).mpr
  calc
    witness.termCoefficient delta * arity ≤
        (⌈witness.termCoefficient delta⌉₊ : ℝ) * arity := by
      gcongr
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

private theorem xorAuthorizedTermCap_polynomiallyBounded
    (witness : NearCubicWires.RecoveryPipeline.XorAmplificationWitness)
    (delta : ℝ) (hnonneg : 0 ≤ delta) (hquarter : delta ≤ 1 / 4)
    (copies arity : ℕ → ℕ)
    (hcopies : ∀ n, 1 ≤ copies n)
    (hcopyPower :
      PolynomiallyBounded (fun n => 16 ^ copies n))
    (harity : PolynomiallyBounded arity) :
    PolynomiallyBounded
      (fun n =>
        xorAuthorizedTermCap witness delta
          (copies n) (arity n)) := by
  apply polynomiallyBounded_mono
    (larger := fun n =>
      ⌈witness.termCoefficient delta⌉₊ *
        arity n * 16 ^ copies n)
  · intro n
    exact xorAuthorizedTermCap_le
      witness delta hnonneg hquarter (copies n) (arity n) (hcopies n)
  · exact polynomiallyBounded_mul
      (polynomiallyBounded_mul
        (polynomiallyBounded_constant
          ⌈witness.termCoefficient delta⌉₊)
        harity)
      hcopyPower

private theorem xorAuthorizedCoefficientBitCap_polynomiallyBounded
    (witness : NearCubicWires.RecoveryPipeline.XorAmplificationWitness)
    (delta : ℝ)
    (arity : ℕ → ℕ) (harity : PolynomiallyBounded arity) :
    PolynomiallyBounded
      (fun n =>
        xorAuthorizedCoefficientBitCap witness delta
          (arity n)) := by
  have hone := polynomiallyBounded_constant 1
  have hsucc := polynomiallyBounded_add harity hone
  have hpower := polynomiallyBounded_pow hsucc
    (witness.coefficientBitDegree delta)
  have hscaled := polynomiallyBounded_mul
    (polynomiallyBounded_constant
      (witness.coefficientBitCoefficient delta))
    hpower
  simpa only [xorAuthorizedCoefficientBitCap,
    xorCoefficientBitBound] using hscaled

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

private theorem sixteen_pow_inverseCopies_polynomiallyBounded
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource) (rate : ℕ) :
    PolynomiallyBounded
      (fun sourceIndex =>
        16 ^ inverseCopies outer pcppSource rate sourceIndex) := by
  let coefficient := inverseCopiesLinearCoefficient outer pcppSource rate
  let larger := fun sourceIndex =>
    16 ^ (coefficient * logScale (sourceIndex + 1))
  have hle :
      ∀ sourceIndex,
        16 ^ inverseCopies outer pcppSource rate sourceIndex ≤
          larger sourceIndex := by
    intro sourceIndex
    exact Nat.pow_le_pow_right (by omega)
      (inverseCopies_le_sourceLog outer pcppSource rate sourceIndex)
  apply polynomiallyBounded_mono hle
  let polynomial := fun sourceIndex =>
    (2 * (sourceIndex + 4)) ^ (4 * coefficient)
  apply polynomiallyBounded_mono
    (larger := polynomial)
  · intro sourceIndex
    have htwo :
        2 ^ logScale (sourceIndex + 1) ≤
          2 * (sourceIndex + 4) := by
      simpa [logScale, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using two_pow_clog_le (sourceIndex + 3)
    calc
      larger sourceIndex =
          (2 ^ logScale (sourceIndex + 1)) ^ (4 * coefficient) := by
        dsimp only [larger]
        rw [show 16 = 2 ^ 4 by norm_num]
        simp only [← pow_mul]
        congr 1
        ring
      _ ≤ polynomial sourceIndex :=
        Nat.pow_le_pow_left htwo (4 * coefficient)
  · dsimp only [polynomial]
    exact polynomiallyBounded_pow
      (polynomiallyBounded_mul
        (polynomiallyBounded_constant 2)
        (polynomiallyBounded_add polynomiallyBounded_id
          (polynomiallyBounded_constant 4)))
      (4 * coefficient)

private theorem sixteen_pow_fixedCopies_polynomiallyBounded
    (pcppSource : UniformPointwisePCPPSource) (rate : ℕ) :
    PolynomiallyBounded
      (fun _ => 16 ^ fixedCopies pcppSource rate) :=
  polynomiallyBounded_constant _

private theorem SmoothCoreEnvelope.coreArity_polynomiallyBounded
    {rawArity : ℕ → ℕ} (envelope : SmoothCoreEnvelope rawArity) :
    PolynomiallyBounded envelope.coreArity := by
  exact ⟨envelope.coefficient, envelope.degree,
    envelope.coefficientPositive, fun _ => le_rfl⟩

/-- Exact decoder limits for the inverse-polynomial Case-2 schedule. -/
noncomputable def inverseRecoveryWitnessLimits
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower scheduleIndex : ℕ) : RecoveryWitnessLimits :=
  let requiredDegree := inverseRequiredDegree contracts advantagePower
  let rate := inverseRate contracts advantagePower
  let sourceIndex := inverseSourceIndex scheduleIndex
  xorRecoveryWitnessLimits (publishedXorWitness contracts)
    (publishedRecoveryDelta contracts)
    (inverseCopies outer (publishedPointwisePCPP contracts) rate sourceIndex)
    (scheduledWidth outer sourceIndex)
    (oracleSizeBound requiredDegree (scheduledWidth outer sourceIndex))
    (seedArity outer (publishedPointwisePCPP contracts)
      requiredDegree sourceIndex)
    (inverseCaseTwoSymmetricSize contracts outer advantagePower scheduleIndex)
    (inverseCaseTwoThresholdSize contracts outer advantagePower scheduleIndex)

/-- Last inverse schedule coordinate that can map to a displayed source
index.  The `- 3` is exact: `inverseSourceIndex` admits `t` while
`t + 2 < inverseSourceMeasure (s + 1)`. -/
def inverseRecoveryScheduleCeiling (sourceIndex : ℕ) : ℕ :=
  inverseSourceMeasure (sourceIndex + 1) - 3

theorem scheduleIndex_le_inverseRecoveryScheduleCeiling
    (scheduleIndex : ℕ) :
    scheduleIndex ≤
      inverseRecoveryScheduleCeiling
        (inverseSourceIndex scheduleIndex) := by
  have hcross := inverseSourceIndex_next_crosses scheduleIndex
  unfold inverseRecoveryScheduleCeiling
  omega

/-- One computable natural wire envelope for every inverse coordinate sharing
the same public input length.  The cubic bound avoids evaluating a real floor
inside the fixed verifier and dominates both physical modes. -/
noncomputable def inverseRecoverySourceWireCap
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower sourceIndex : ℕ) : ℕ :=
  (inverseEnvelope contracts outer advantagePower).coreArity
      (inverseRecoveryScheduleCeiling sourceIndex) ^ 3

/-- The sole inverse validator policy keyed by the source index recoverable
from `sourceLength`.  Exact schedule witnesses widen into this policy without
changing their canonical code. -/
noncomputable def inverseRecoveryWitnessSourceLimits
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower sourceIndex : ℕ) : RecoveryWitnessLimits :=
  let requiredDegree := inverseRequiredDegree contracts advantagePower
  let rate := inverseRate contracts advantagePower
  let wireCap :=
    inverseRecoverySourceWireCap contracts outer advantagePower sourceIndex
  xorRecoveryWitnessLimits (publishedXorWitness contracts)
    (publishedRecoveryDelta contracts)
    (inverseCopies outer (publishedPointwisePCPP contracts) rate sourceIndex)
    (scheduledWidth outer sourceIndex)
    (oracleSizeBound requiredDegree (scheduledWidth outer sourceIndex))
    (seedArity outer (publishedPointwisePCPP contracts)
      requiredDegree sourceIndex)
    wireCap wireCap

/-- Public-arity view of the sole inverse policy.  The verifier derives this
index from `WeakVerifierRequest.inputArity`; no schedule coordinate enters the
witness or request ABI. -/
noncomputable def inverseRecoveryWitnessLimitsAtLength
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower inputLength : ℕ) : RecoveryWitnessLimits :=
  inverseRecoveryWitnessSourceLimits contracts outer advantagePower
    (sourceIndexOfLength inputLength)

@[simp] theorem inverseRecoveryWitnessLimitsAtLength_sourceLength
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower sourceIndex : ℕ) :
    inverseRecoveryWitnessLimitsAtLength contracts outer advantagePower
        (sourceLength sourceIndex) =
      inverseRecoveryWitnessSourceLimits contracts outer advantagePower
        sourceIndex := by
  simp [inverseRecoveryWitnessLimitsAtLength]

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

/-- **Magnitude-independent weakening of one XOR witness policy.**  Two policies
built from the same witness, radius, copy count, oracle and sum data differ only
in their two wire caps, and every remaining field is then a propositional
identity.  Stating it at *variable* radius and copy count is what keeps the
proof independent of the size of the published schedule constants: no
`RecoveryWitnessLimits` field is ever normalized, so the checker never evaluates
a copy count or a block length. -/
private theorem xorRecoveryWitnessLimits_weakens_wireCap
    (witness : NearCubicWires.RecoveryPipeline.XorAmplificationWitness)
    (delta : ℝ) (copies oracleArity oracleSizeCap sumArity : ℕ)
    (symmetricWireCap thresholdWireCap
      symmetricWireCap' thresholdWireCap' : ℕ)
    (hsymmetric : symmetricWireCap ≤ symmetricWireCap')
    (hthreshold : thresholdWireCap ≤ thresholdWireCap') :
    (xorRecoveryWitnessLimits witness delta copies oracleArity oracleSizeCap
        sumArity symmetricWireCap thresholdWireCap)
      |>.Weakens
        (xorRecoveryWitnessLimits witness delta copies oracleArity
          oracleSizeCap sumArity symmetricWireCap' thresholdWireCap') where
  oracleArity_eq := rfl
  oracleSizeCap_le := le_rfl
  sumArity_eq := rfl
  symmetric :=
    { expectedArity_eq := rfl
      termCap_le := le_rfl
      coefficientBitCap_le := le_rfl
      coefficientMassCap_le := le_rfl
      wireCap_le := hsymmetric
      descriptionCap_le := symmetricDescriptionCap_mono_wire hsymmetric }
  threshold :=
    { expectedArity_eq := rfl
      termCap_le := le_rfl
      coefficientBitCap_le := le_rfl
      coefficientMassCap_le := le_rfl
      wireCap_le := hthreshold
      descriptionCap_le := thresholdDescriptionCap_mono_wire hthreshold }

/-- The exact schedule policy and the length-indexed policy are the same XOR
witness policy at two wire caps.  Naming this equation keeps the weakening
theorem below one application of `xorRecoveryWitnessLimits_weakens_wireCap`. -/
private theorem inverseRecoveryWitnessLimits_eq
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower scheduleIndex : ℕ) :
    inverseRecoveryWitnessLimits contracts outer advantagePower scheduleIndex =
      xorRecoveryWitnessLimits (publishedXorWitness contracts)
        (publishedRecoveryDelta contracts)
        (inverseCopies outer (publishedPointwisePCPP contracts)
          (inverseRate contracts advantagePower)
          (inverseSourceIndex scheduleIndex))
        (scheduledWidth outer (inverseSourceIndex scheduleIndex))
        (oracleSizeBound (inverseRequiredDegree contracts advantagePower)
          (scheduledWidth outer (inverseSourceIndex scheduleIndex)))
        (seedArity outer (publishedPointwisePCPP contracts)
          (inverseRequiredDegree contracts advantagePower)
          (inverseSourceIndex scheduleIndex))
        (inverseCaseTwoSymmetricSize contracts outer advantagePower
          scheduleIndex)
        (inverseCaseTwoThresholdSize contracts outer advantagePower
          scheduleIndex) :=
  rfl

private theorem inverseRecoveryWitnessSourceLimits_eq
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower sourceIndex : ℕ) :
    inverseRecoveryWitnessSourceLimits contracts outer advantagePower
        sourceIndex =
      xorRecoveryWitnessLimits (publishedXorWitness contracts)
        (publishedRecoveryDelta contracts)
        (inverseCopies outer (publishedPointwisePCPP contracts)
          (inverseRate contracts advantagePower) sourceIndex)
        (scheduledWidth outer sourceIndex)
        (oracleSizeBound (inverseRequiredDegree contracts advantagePower)
          (scheduledWidth outer sourceIndex))
        (seedArity outer (publishedPointwisePCPP contracts)
          (inverseRequiredDegree contracts advantagePower) sourceIndex)
        (inverseRecoverySourceWireCap contracts outer advantagePower
          sourceIndex)
        (inverseRecoverySourceWireCap contracts outer advantagePower
          sourceIndex) :=
  rfl

/-- Exact schedule limits are a tightening of the one length-indexed policy.
This theorem is the only bridge used by inverse completeness; it preserves
the existing witness ABI and makes the schedule ambiguity explicit.

Both sides are the same XOR witness policy at two wire caps, so the whole
statement reduces to the two cap inequalities.  Nothing here depends on the
value of the approximation radius or of the copy count: at the repaired radius
both are choice-opaque, and even at a small rational literal the checker would
otherwise have to normalize a block length of order `1 / delta`. -/
theorem inverseRecoveryWitnessLimits_weakens_sourceLimits
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower scheduleIndex : ℕ) :
    (inverseRecoveryWitnessLimits contracts outer advantagePower scheduleIndex)
      |>.Weakens
        (inverseRecoveryWitnessSourceLimits contracts outer advantagePower
          (inverseSourceIndex scheduleIndex)) := by
  let envelope := inverseEnvelope contracts outer advantagePower
  let sourceIndex := inverseSourceIndex scheduleIndex
  let wireCap :=
    inverseRecoverySourceWireCap contracts outer advantagePower sourceIndex
  have hschedule :
      scheduleIndex ≤ inverseRecoveryScheduleCeiling sourceIndex :=
    scheduleIndex_le_inverseRecoveryScheduleCeiling scheduleIndex
  have hcore :
      envelope.coreArity scheduleIndex ≤
        envelope.coreArity
          (inverseRecoveryScheduleCeiling sourceIndex) :=
    envelope.coreArity_monotone hschedule
  have hcoreCube :
      envelope.coreArity scheduleIndex ^ 3 ≤ wireCap := by
    exact Nat.pow_le_pow_left hcore 3
  have hcoefficientNonnegative :
      0 ≤ inversePhysicalCoefficient contracts outer advantagePower :=
    (inversePhysicalCoefficient_positive contracts outer advantagePower).le
  have hcoefficientOne :
      inversePhysicalCoefficient contracts outer advantagePower ≤ 1 := by
    unfold inversePhysicalCoefficient
    exact scheduledCoefficient_le_one <|
      inversePhysicalScheduleFactor_positive contracts outer advantagePower
  have hsymmetric :
      inverseCaseTwoSymmetricSize contracts outer advantagePower
          scheduleIndex ≤ wireCap :=
    (wireScale_floor_le_cube hcoefficientNonnegative hcoefficientOne
      10 (envelope.coreArity scheduleIndex)).trans hcoreCube
  have hthreshold :
      inverseCaseTwoThresholdSize contracts outer advantagePower
          scheduleIndex ≤ wireCap :=
    (wireScale_floor_le_cube hcoefficientNonnegative hcoefficientOne
      12 (envelope.coreArity scheduleIndex)).trans hcoreCube
  rw [inverseRecoveryWitnessLimits_eq,
    inverseRecoveryWitnessSourceLimits_eq]
  exact xorRecoveryWitnessLimits_weakens_wireCap
    (publishedXorWitness contracts) (publishedRecoveryDelta contracts)
    (inverseCopies outer (publishedPointwisePCPP contracts)
      (inverseRate contracts advantagePower)
      (inverseSourceIndex scheduleIndex))
    (scheduledWidth outer (inverseSourceIndex scheduleIndex))
    (oracleSizeBound (inverseRequiredDegree contracts advantagePower)
      (scheduledWidth outer (inverseSourceIndex scheduleIndex)))
    (seedArity outer (publishedPointwisePCPP contracts)
      (inverseRequiredDegree contracts advantagePower)
      (inverseSourceIndex scheduleIndex))
    (inverseCaseTwoSymmetricSize contracts outer advantagePower scheduleIndex)
    (inverseCaseTwoThresholdSize contracts outer advantagePower scheduleIndex)
    wireCap wireCap hsymmetric hthreshold

/-- Exact decoder limits for the fixed-rate Case-2 schedule. -/
noncomputable def fixedRecoveryWitnessLimits
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate sourceIndex : ℕ) : RecoveryWitnessLimits :=
  let requiredDegree := fixedRequiredDegree contracts requestedRate
  let rate := fixedRate contracts requestedRate
  xorRecoveryWitnessLimits (publishedXorWitness contracts)
    (publishedRecoveryDelta contracts)
    (fixedCopies (publishedPointwisePCPP contracts) rate)
    (scheduledWidth outer sourceIndex)
    (oracleSizeBound requiredDegree (scheduledWidth outer sourceIndex))
    (seedArity outer (publishedPointwisePCPP contracts)
      requiredDegree sourceIndex)
    (fixedCaseTwoSymmetricSize contracts outer requestedRate sourceIndex)
    (fixedCaseTwoThresholdSize contracts outer requestedRate sourceIndex)

/-- Fixed-rate public-arity adapter.  It shares the same decoder as the
inverse policy, so both weak machines recover their policy from register one. -/
noncomputable def fixedRecoveryWitnessLimitsAtLength
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate inputLength : ℕ) : RecoveryWitnessLimits :=
  fixedRecoveryWitnessLimits contracts outer requestedRate
    (sourceIndexOfLength inputLength)

@[simp] theorem fixedRecoveryWitnessLimitsAtLength_sourceLength
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate sourceIndex : ℕ) :
    fixedRecoveryWitnessLimitsAtLength contracts outer requestedRate
        (sourceLength sourceIndex) =
      fixedRecoveryWitnessLimits contracts outer requestedRate sourceIndex := by
  simp [fixedRecoveryWitnessLimitsAtLength]

/-- The semantic disjoint union used by the XOR contradiction has one
canonical decoder witness at exactly the same limits.  The approximation
distance is an acceptance condition, not serialized witness metadata. -/
private noncomputable def checkedRecoveryWitness_of_publishedLegalApproximation
    (contracts : PublishedContracts)
    {oracleArity oracleSizeCap sumArity : ℕ}
    (copies symmetricWireCap thresholdWireCap : ℕ)
    (seed : BoolFunction sumArity)
    (oracle : BooleanCircuit oracleArity)
    (oracleSize_le : oracle.size ≤ oracleSizeCap)
    (approximation :
      PublishedLegalApproximation contracts seed copies
        symmetricWireCap thresholdWireCap) :
    CheckedRecoveryWitness
      (xorRecoveryWitnessLimits (publishedXorWitness contracts)
        (publishedRecoveryDelta contracts)
        copies oracleArity oracleSizeCap sumArity
        symmetricWireCap thresholdWireCap) :=
  Classical.choice <| by
    simp only [PublishedLegalApproximation] at approximation
    rcases approximation with approximation | approximation
    · rcases approximation with
        ⟨sum, hterms, hbits, hmass, _hdistance⟩
      exact ⟨symmetricCheckedRecoveryWitness_of_contracts
        contracts.thresholdNormalization (publishedXorWitness contracts)
        (publishedRecoveryDelta contracts) copies oracle oracleSize_le sum
        hterms hbits hmass⟩
    · rcases approximation with
        ⟨sum, hterms, hbits, hmass, _hdistance⟩
      exact ⟨thresholdCheckedRecoveryWitness_of_contracts
        contracts.thresholdNormalization (publishedXorWitness contracts)
        (publishedRecoveryDelta contracts) copies oracle oracleSize_le sum
        hterms hbits hmass⟩

/-- Inverse-schedule specialization of the unique semantic-to-canonical
witness bridge. -/
private noncomputable def inverseCheckedRecoveryWitness_of_publishedLegalApproximation
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower scheduleIndex : ℕ)
    {input : BitInput
      (sourceLength (inverseSourceIndex scheduleIndex))}
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
    CheckedRecoveryWitness
      (inverseRecoveryWitnessLimits contracts outer advantagePower
        scheduleIndex) := by
  exact checkedRecoveryWitness_of_publishedLegalApproximation contracts
    (inverseCopies outer (publishedPointwisePCPP contracts)
      (inverseRate contracts advantagePower)
      (inverseSourceIndex scheduleIndex))
    (inverseCaseTwoSymmetricSize contracts outer advantagePower scheduleIndex)
    (inverseCaseTwoThresholdSize contracts outer advantagePower scheduleIndex)
    (caseTwoSeed (publishedPointwisePCPP contracts) caseTwo)
    caseTwo.circuit caseTwo.sizeBounded approximation

/-- The same semantic witness rechecked under the sole length-indexed inverse
policy.  Widening changes no canonical bits, so the public witness ABI remains
identical to the exact schedule construction above. -/
private noncomputable def inverseSourceCheckedRecoveryWitness_of_publishedLegalApproximation
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower scheduleIndex : ℕ)
    {input : BitInput
      (sourceLength (inverseSourceIndex scheduleIndex))}
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
    CheckedRecoveryWitness
      (inverseRecoveryWitnessSourceLimits contracts outer advantagePower
        (inverseSourceIndex scheduleIndex)) :=
  (inverseCheckedRecoveryWitness_of_publishedLegalApproximation
    contracts outer advantagePower scheduleIndex caseTwo approximation).widen
      (inverseRecoveryWitnessLimits_weakens_sourceLimits
        contracts outer advantagePower scheduleIndex)

@[simp] private theorem inverseSourceCheckedRecoveryWitness_code
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower scheduleIndex : ℕ)
    {input : BitInput
      (sourceLength (inverseSourceIndex scheduleIndex))}
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
    (inverseSourceCheckedRecoveryWitness_of_publishedLegalApproximation
      contracts outer advantagePower scheduleIndex caseTwo approximation).code =
      (inverseCheckedRecoveryWitness_of_publishedLegalApproximation
        contracts outer advantagePower scheduleIndex caseTwo
        approximation).code := by
  exact CheckedRecoveryWitness.code_widen _ _

/-- Completeness witness in the verifier's public-arity policy.  This is a
type-level restatement of the source policy, not a second serialization path. -/
noncomputable def inverseLengthCheckedRecoveryWitness_of_publishedLegalApproximation
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower scheduleIndex : ℕ)
    {input : BitInput
      (sourceLength (inverseSourceIndex scheduleIndex))}
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
    CheckedRecoveryWitness
      (inverseRecoveryWitnessLimitsAtLength contracts outer advantagePower
        (sourceLength (inverseSourceIndex scheduleIndex))) := by
  simpa using
    inverseSourceCheckedRecoveryWitness_of_publishedLegalApproximation
      contracts outer advantagePower scheduleIndex caseTwo approximation

/-- Fixed-rate specialization of the same bridge. -/
private noncomputable def fixedCheckedRecoveryWitness_of_publishedLegalApproximation
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
    CheckedRecoveryWitness
      (fixedRecoveryWitnessLimits contracts outer requestedRate
        sourceIndex) := by
  exact checkedRecoveryWitness_of_publishedLegalApproximation contracts
    (fixedCopies (publishedPointwisePCPP contracts)
      (fixedRate contracts requestedRate))
    (fixedCaseTwoSymmetricSize contracts outer requestedRate sourceIndex)
    (fixedCaseTwoThresholdSize contracts outer requestedRate sourceIndex)
    (caseTwoSeed (publishedPointwisePCPP contracts) caseTwo)
    caseTwo.circuit caseTwo.sizeBounded approximation

/-- Fixed-rate completeness witness in the same public-arity ABI. -/
noncomputable def fixedLengthCheckedRecoveryWitness_of_publishedLegalApproximation
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
    CheckedRecoveryWitness
      (fixedRecoveryWitnessLimitsAtLength contracts outer requestedRate
        (sourceLength sourceIndex)) := by
  simpa using
    fixedCheckedRecoveryWitness_of_publishedLegalApproximation contracts outer
      requestedRate sourceIndex caseTwo approximation

/-- Every syntactic field of the inverse-polynomial decoder policy remains
polynomial after the canonical inverse-source selector is applied. -/
theorem inverseRecoveryWitnessCodeBitBound_polynomiallyBounded
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower : ℕ) :
    PolynomiallyBounded
      (fun scheduleIndex =>
        recoveryWitnessCodeBitBound
          (inverseRecoveryWitnessLimits contracts outer advantagePower
            scheduleIndex)) := by
  let requiredDegree := inverseRequiredDegree contracts advantagePower
  let rate := inverseRate contracts advantagePower
  let sourceIndexOf := inverseSourceIndex
  let arity := fun scheduleIndex =>
    seedArity outer (publishedPointwisePCPP contracts) requiredDegree
      (sourceIndexOf scheduleIndex)
  let copies := fun scheduleIndex =>
    inverseCopies outer (publishedPointwisePCPP contracts) rate
      (sourceIndexOf scheduleIndex)
  let core := (inverseEnvelope contracts outer advantagePower).coreArity
  let symmetricWire := fun scheduleIndex =>
    inverseCaseTwoSymmetricSize contracts outer advantagePower scheduleIndex
  let thresholdWire := fun scheduleIndex =>
    inverseCaseTwoThresholdSize contracts outer advantagePower scheduleIndex
  have hsourceIndex :
      PolynomiallyBounded sourceIndexOf := by
    apply polynomiallyBounded_mono
      (larger := fun scheduleIndex => scheduleIndex + 1)
    · exact inverseSourceIndex_le
    · exact polynomiallyBounded_add polynomiallyBounded_id
        (polynomiallyBounded_constant 1)
  have horacleArity :
      PolynomiallyBounded
        (fun scheduleIndex =>
          scheduledWidth outer (sourceIndexOf scheduleIndex)) :=
    polynomiallyBounded_comp
      (scheduledWidth_polynomiallyBounded outer) hsourceIndex
  have horacleSize :
      PolynomiallyBounded
        (fun scheduleIndex =>
          oracleSizeBound requiredDegree
            (scheduledWidth outer (sourceIndexOf scheduleIndex))) :=
    polynomiallyBounded_comp
      (outer := fun sourceIndex =>
        oracleSizeBound requiredDegree (scheduledWidth outer sourceIndex))
      (inner := sourceIndexOf)
      (scheduledOracleSize_polynomiallyBounded outer requiredDegree)
      hsourceIndex
  have harity :
      PolynomiallyBounded arity :=
    polynomiallyBounded_comp
      (seedArity_polynomiallyBounded outer
        (publishedPointwisePCPP contracts) requiredDegree)
      hsourceIndex
  have hcopyPower :
      PolynomiallyBounded
        (fun scheduleIndex => 16 ^ copies scheduleIndex) := by
    exact polynomiallyBounded_comp
      (outer := fun sourceIndex =>
        16 ^ inverseCopies outer (publishedPointwisePCPP contracts) rate
          sourceIndex)
      (inner := sourceIndexOf)
      (sixteen_pow_inverseCopies_polynomiallyBounded outer
        (publishedPointwisePCPP contracts) rate)
      hsourceIndex
  have hterm :
      PolynomiallyBounded
        (fun scheduleIndex =>
          xorAuthorizedTermCap (publishedXorWitness contracts)
            (publishedRecoveryDelta contracts)
            (copies scheduleIndex) (arity scheduleIndex)) :=
    xorAuthorizedTermCap_polynomiallyBounded
      (publishedXorWitness contracts) (publishedRecoveryDelta contracts)
      (publishedRecoveryDelta_nonnegative contracts)
      (publishedRecoveryDelta_le_quarter contracts) copies arity
      (fun scheduleIndex =>
        inverseCopies_positive outer (publishedPointwisePCPP contracts) rate
          (sourceIndexOf scheduleIndex))
      hcopyPower harity
  have hcoefficient :
      PolynomiallyBounded
        (fun scheduleIndex =>
          xorAuthorizedCoefficientBitCap (publishedXorWitness contracts)
            (publishedRecoveryDelta contracts) (arity scheduleIndex)) :=
    xorAuthorizedCoefficientBitCap_polynomiallyBounded
      (publishedXorWitness contracts) (publishedRecoveryDelta contracts)
      arity harity
  have hcore : PolynomiallyBounded core :=
    SmoothCoreEnvelope.coreArity_polynomiallyBounded
      (inverseEnvelope contracts outer advantagePower)
  have hphysicalNonnegative :
      0 ≤ inversePhysicalCoefficient contracts outer advantagePower :=
    (inversePhysicalCoefficient_positive contracts outer advantagePower).le
  have hphysicalOne :
      inversePhysicalCoefficient contracts outer advantagePower ≤ 1 := by
    unfold inversePhysicalCoefficient
    exact scheduledCoefficient_le_one <|
      inversePhysicalScheduleFactor_positive contracts outer advantagePower
  have hsymmetricWire : PolynomiallyBounded symmetricWire := by
    apply polynomiallyBounded_mono
      (larger := fun scheduleIndex => core scheduleIndex ^ 3)
    · intro scheduleIndex
      exact wireScale_floor_le_cube hphysicalNonnegative hphysicalOne
        10 (core scheduleIndex)
    · exact polynomiallyBounded_pow hcore 3
  have hthresholdWire : PolynomiallyBounded thresholdWire := by
    apply polynomiallyBounded_mono
      (larger := fun scheduleIndex => core scheduleIndex ^ 3)
    · intro scheduleIndex
      exact wireScale_floor_le_cube hphysicalNonnegative hphysicalOne
        12 (core scheduleIndex)
    · exact polynomiallyBounded_pow hcore 3
  have hsymmetricDescription :
      PolynomiallyBounded
        (fun scheduleIndex =>
          symmetricDescriptionCap (arity scheduleIndex)
            (symmetricWire scheduleIndex)) :=
    symmetricDescriptionCap_polynomiallyBounded arity symmetricWire
      harity hsymmetricWire
  have hthresholdDescription :
      PolynomiallyBounded
        (fun scheduleIndex =>
          thresholdDescriptionCap (arity scheduleIndex)
            (thresholdWire scheduleIndex)) :=
    thresholdDescriptionCap_polynomiallyBounded arity thresholdWire
      harity hthresholdWire
  apply recoveryWitnessCodeBitBound_polynomiallyBounded
  apply recoveryWitnessCodeParameter_polynomiallyBounded
  · simpa only [inverseRecoveryWitnessLimits, xorRecoveryWitnessLimits] using
      horacleArity
  · simpa only [inverseRecoveryWitnessLimits, xorRecoveryWitnessLimits] using
      horacleSize
  · simpa only [inverseRecoveryWitnessLimits, xorRecoveryWitnessLimits] using
      harity
  · simpa only [inverseRecoveryWitnessLimits, xorRecoveryWitnessLimits,
      symmetricXorLegalSumLimits] using hterm
  · simpa only [inverseRecoveryWitnessLimits, xorRecoveryWitnessLimits,
      symmetricXorLegalSumLimits] using hcoefficient
  · simpa only [inverseRecoveryWitnessLimits, xorRecoveryWitnessLimits,
      symmetricXorLegalSumLimits] using hsymmetricWire
  · simpa only [inverseRecoveryWitnessLimits, xorRecoveryWitnessLimits,
      symmetricXorLegalSumLimits] using hsymmetricDescription
  · simpa only [inverseRecoveryWitnessLimits, xorRecoveryWitnessLimits,
      thresholdXorLegalSumLimits] using hterm
  · simpa only [inverseRecoveryWitnessLimits, xorRecoveryWitnessLimits,
      thresholdXorLegalSumLimits] using hcoefficient
  · simpa only [inverseRecoveryWitnessLimits, xorRecoveryWitnessLimits,
      thresholdXorLegalSumLimits] using hthresholdWire
  · simpa only [inverseRecoveryWitnessLimits, xorRecoveryWitnessLimits,
      thresholdXorLegalSumLimits] using hthresholdDescription

/-- The length-indexed inverse validator policy is polynomial in the source
index itself.  Its coarse cubic wire envelope remains polynomial while
eliminating every noncomputable real-floor calculation from runtime limits. -/
theorem inverseRecoveryWitnessSourceCodeBitBound_polynomiallyBounded
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower : ℕ) :
    PolynomiallyBounded
      (fun sourceIndex =>
        recoveryWitnessCodeBitBound
          (inverseRecoveryWitnessSourceLimits contracts outer advantagePower
            sourceIndex)) := by
  let requiredDegree := inverseRequiredDegree contracts advantagePower
  let rate := inverseRate contracts advantagePower
  let arity := seedArity outer (publishedPointwisePCPP contracts)
    requiredDegree
  let copies := inverseCopies outer (publishedPointwisePCPP contracts) rate
  let wire := inverseRecoverySourceWireCap contracts outer advantagePower
  have hceiling :
      PolynomiallyBounded inverseRecoveryScheduleCeiling := by
    apply polynomiallyBounded_mono
      (larger := fun sourceIndex =>
        (sourceIndex + 2) * (sourceIndex + 4))
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
  have hcore :
      PolynomiallyBounded
        (fun sourceIndex =>
          (inverseEnvelope contracts outer advantagePower).coreArity
            (inverseRecoveryScheduleCeiling sourceIndex)) :=
    polynomiallyBounded_comp
      (SmoothCoreEnvelope.coreArity_polynomiallyBounded
        (inverseEnvelope contracts outer advantagePower))
      hceiling
  have hwire : PolynomiallyBounded wire := by
    change PolynomiallyBounded
      (fun sourceIndex =>
        (inverseEnvelope contracts outer advantagePower).coreArity
          (inverseRecoveryScheduleCeiling sourceIndex) ^ 3)
    exact polynomiallyBounded_pow hcore 3
  have horacleArity := scheduledWidth_polynomiallyBounded outer
  have horacleSize :=
    scheduledOracleSize_polynomiallyBounded outer requiredDegree
  have harity : PolynomiallyBounded arity :=
    seedArity_polynomiallyBounded outer
      (publishedPointwisePCPP contracts) requiredDegree
  have hcopyPower :
      PolynomiallyBounded
        (fun sourceIndex => 16 ^ copies sourceIndex) := by
    exact sixteen_pow_inverseCopies_polynomiallyBounded outer
      (publishedPointwisePCPP contracts) rate
  have hterm :
      PolynomiallyBounded
        (fun sourceIndex =>
          xorAuthorizedTermCap (publishedXorWitness contracts)
            (publishedRecoveryDelta contracts)
            (copies sourceIndex) (arity sourceIndex)) :=
    xorAuthorizedTermCap_polynomiallyBounded
      (publishedXorWitness contracts) (publishedRecoveryDelta contracts)
      (publishedRecoveryDelta_nonnegative contracts)
      (publishedRecoveryDelta_le_quarter contracts) copies arity
      (inverseCopies_positive outer (publishedPointwisePCPP contracts) rate)
      hcopyPower harity
  have hcoefficient :
      PolynomiallyBounded
        (fun sourceIndex =>
          xorAuthorizedCoefficientBitCap (publishedXorWitness contracts)
            (publishedRecoveryDelta contracts) (arity sourceIndex)) :=
    xorAuthorizedCoefficientBitCap_polynomiallyBounded
      (publishedXorWitness contracts) (publishedRecoveryDelta contracts)
      arity harity
  have hsymmetricDescription :
      PolynomiallyBounded
        (fun sourceIndex =>
          symmetricDescriptionCap (arity sourceIndex)
            (wire sourceIndex)) :=
    symmetricDescriptionCap_polynomiallyBounded arity wire harity hwire
  have hthresholdDescription :
      PolynomiallyBounded
        (fun sourceIndex =>
          thresholdDescriptionCap (arity sourceIndex)
            (wire sourceIndex)) :=
    thresholdDescriptionCap_polynomiallyBounded arity wire harity hwire
  apply recoveryWitnessCodeBitBound_polynomiallyBounded
  apply recoveryWitnessCodeParameter_polynomiallyBounded
  · simpa only [inverseRecoveryWitnessSourceLimits,
      xorRecoveryWitnessLimits] using horacleArity
  · simpa only [inverseRecoveryWitnessSourceLimits,
      xorRecoveryWitnessLimits] using horacleSize
  · simpa only [inverseRecoveryWitnessSourceLimits,
      xorRecoveryWitnessLimits] using harity
  · simpa only [inverseRecoveryWitnessSourceLimits,
      xorRecoveryWitnessLimits, symmetricXorLegalSumLimits] using hterm
  · simpa only [inverseRecoveryWitnessSourceLimits,
      xorRecoveryWitnessLimits, symmetricXorLegalSumLimits] using hcoefficient
  · simpa only [inverseRecoveryWitnessSourceLimits,
      xorRecoveryWitnessLimits, symmetricXorLegalSumLimits] using hwire
  · simpa only [inverseRecoveryWitnessSourceLimits,
      xorRecoveryWitnessLimits, symmetricXorLegalSumLimits] using
      hsymmetricDescription
  · simpa only [inverseRecoveryWitnessSourceLimits,
      xorRecoveryWitnessLimits, thresholdXorLegalSumLimits] using hterm
  · simpa only [inverseRecoveryWitnessSourceLimits,
      xorRecoveryWitnessLimits, thresholdXorLegalSumLimits] using hcoefficient
  · simpa only [inverseRecoveryWitnessSourceLimits,
      xorRecoveryWitnessLimits, thresholdXorLegalSumLimits] using hwire
  · simpa only [inverseRecoveryWitnessSourceLimits,
      xorRecoveryWitnessLimits, thresholdXorLegalSumLimits] using
      hthresholdDescription

/-- Every syntactic field of the fixed-rate decoder policy is polynomial in
the source index.  The real-valued mass caps do not appear here: their
canonical rational syntax is already bounded by the coefficient-bit caps. -/
theorem fixedRecoveryWitnessCodeBitBound_polynomiallyBounded
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate : ℕ) :
    PolynomiallyBounded
      (fun sourceIndex =>
        recoveryWitnessCodeBitBound
          (fixedRecoveryWitnessLimits contracts outer requestedRate
            sourceIndex)) := by
  let requiredDegree := fixedRequiredDegree contracts requestedRate
  let rate := fixedRate contracts requestedRate
  let arity := seedArity outer (publishedPointwisePCPP contracts)
    requiredDegree
  let core := (fixedEnvelope contracts outer requestedRate).coreArity
  let symmetricWire := fun sourceIndex =>
    fixedCaseTwoSymmetricSize contracts outer requestedRate sourceIndex
  let thresholdWire := fun sourceIndex =>
    fixedCaseTwoThresholdSize contracts outer requestedRate sourceIndex
  have horacleArity := scheduledWidth_polynomiallyBounded outer
  have horacleSize :=
    scheduledOracleSize_polynomiallyBounded outer requiredDegree
  have harity :
      PolynomiallyBounded arity :=
    seedArity_polynomiallyBounded outer
      (publishedPointwisePCPP contracts) requiredDegree
  have hcopyPower :
      PolynomiallyBounded
        (fun _ => 16 ^ fixedCopies (publishedPointwisePCPP contracts) rate) :=
    sixteen_pow_fixedCopies_polynomiallyBounded
      (publishedPointwisePCPP contracts) rate
  have hterm :
      PolynomiallyBounded
        (fun sourceIndex =>
          xorAuthorizedTermCap (publishedXorWitness contracts)
            (publishedRecoveryDelta contracts)
            (fixedCopies (publishedPointwisePCPP contracts) rate)
            (arity sourceIndex)) :=
    xorAuthorizedTermCap_polynomiallyBounded
      (publishedXorWitness contracts) (publishedRecoveryDelta contracts)
      (publishedRecoveryDelta_nonnegative contracts)
      (publishedRecoveryDelta_le_quarter contracts)
      (fun _ => fixedCopies (publishedPointwisePCPP contracts) rate) arity
      (fun _ =>
        fixedCopies_positive (publishedPointwisePCPP contracts) rate)
      hcopyPower harity
  have hcoefficient :
      PolynomiallyBounded
        (fun sourceIndex =>
          xorAuthorizedCoefficientBitCap (publishedXorWitness contracts)
            (publishedRecoveryDelta contracts) (arity sourceIndex)) :=
    xorAuthorizedCoefficientBitCap_polynomiallyBounded
      (publishedXorWitness contracts) (publishedRecoveryDelta contracts)
      arity harity
  have hcore : PolynomiallyBounded core :=
    SmoothCoreEnvelope.coreArity_polynomiallyBounded
      (fixedEnvelope contracts outer requestedRate)
  have hphysicalNonnegative :
      0 ≤ fixedPhysicalCoefficient contracts outer requestedRate :=
    (fixedPhysicalCoefficient_positive contracts outer requestedRate).le
  have hphysicalOne :
      fixedPhysicalCoefficient contracts outer requestedRate ≤ 1 := by
    exact fixedPhysicalCoefficient_le_one contracts outer requestedRate
  have hsymmetricWire : PolynomiallyBounded symmetricWire := by
    apply polynomiallyBounded_mono
      (larger := fun sourceIndex => core sourceIndex ^ 3)
    · intro sourceIndex
      exact wireScale_floor_le_cube hphysicalNonnegative hphysicalOne
        5 (core sourceIndex)
    · exact polynomiallyBounded_pow hcore 3
  have hthresholdWire : PolynomiallyBounded thresholdWire := by
    apply polynomiallyBounded_mono
      (larger := fun sourceIndex => core sourceIndex ^ 3)
    · intro sourceIndex
      exact wireScale_floor_le_cube hphysicalNonnegative hphysicalOne
        9 (core sourceIndex)
    · exact polynomiallyBounded_pow hcore 3
  have hsymmetricDescription :
      PolynomiallyBounded
        (fun sourceIndex =>
          symmetricDescriptionCap (arity sourceIndex)
            (symmetricWire sourceIndex)) :=
    symmetricDescriptionCap_polynomiallyBounded arity symmetricWire
      harity hsymmetricWire
  have hthresholdDescription :
      PolynomiallyBounded
        (fun sourceIndex =>
          thresholdDescriptionCap (arity sourceIndex)
            (thresholdWire sourceIndex)) :=
    thresholdDescriptionCap_polynomiallyBounded arity thresholdWire
      harity hthresholdWire
  apply recoveryWitnessCodeBitBound_polynomiallyBounded
  apply recoveryWitnessCodeParameter_polynomiallyBounded
  · simpa only [fixedRecoveryWitnessLimits, xorRecoveryWitnessLimits] using
      horacleArity
  · simpa only [fixedRecoveryWitnessLimits, xorRecoveryWitnessLimits] using
      horacleSize
  · simpa only [fixedRecoveryWitnessLimits, xorRecoveryWitnessLimits] using
      harity
  · simpa only [fixedRecoveryWitnessLimits, xorRecoveryWitnessLimits,
      symmetricXorLegalSumLimits] using hterm
  · simpa only [fixedRecoveryWitnessLimits, xorRecoveryWitnessLimits,
      symmetricXorLegalSumLimits] using hcoefficient
  · simpa only [fixedRecoveryWitnessLimits, xorRecoveryWitnessLimits,
      symmetricXorLegalSumLimits] using hsymmetricWire
  · simpa only [fixedRecoveryWitnessLimits, xorRecoveryWitnessLimits,
      symmetricXorLegalSumLimits] using hsymmetricDescription
  · simpa only [fixedRecoveryWitnessLimits, xorRecoveryWitnessLimits,
      thresholdXorLegalSumLimits] using hterm
  · simpa only [fixedRecoveryWitnessLimits, xorRecoveryWitnessLimits,
      thresholdXorLegalSumLimits] using hcoefficient
  · simpa only [fixedRecoveryWitnessLimits, xorRecoveryWitnessLimits,
      thresholdXorLegalSumLimits] using hthresholdWire
  · simpa only [fixedRecoveryWitnessLimits, xorRecoveryWitnessLimits,
      thresholdXorLegalSumLimits] using hthresholdDescription

/-- A polynomial in the inverse schedule index is still eventually dominated
by the exponential source selected at that index.  The first-crossing schedule
supplies the required quadratic transport bound; no density premise is left
to a caller. -/
private theorem polynomiallyBounded_eventually_le_inverse_source_sixteenth
    {function : ℕ → ℕ} (hfunction : PolynomiallyBounded function) :
    ∃ onset, ∀ scheduleIndex, onset ≤ scheduleIndex →
      function scheduleIndex ≤
        2 ^ (inverseSourceIndex scheduleIndex + 1) / 16 := by
  rcases hfunction with
    ⟨coefficient, degree, hcoefficient, hbound⟩
  let sourceMajorant := fun sourceIndex =>
    coefficient * (4 * (sourceIndex + 1) * (sourceIndex + 3)) ^ degree
  have hsourceMajorant :
      PolynomiallyBounded sourceMajorant := by
    dsimp only [sourceMajorant]
    exact polynomiallyBounded_mul
      (polynomiallyBounded_constant coefficient)
      (polynomiallyBounded_pow
        (polynomiallyBounded_mul
          (polynomiallyBounded_mul
            (polynomiallyBounded_constant 4)
            (polynomiallyBounded_add polynomiallyBounded_id
              (polynomiallyBounded_constant 1)))
          (polynomiallyBounded_add polynomiallyBounded_id
            (polynomiallyBounded_constant 3)))
        degree)
  obtain ⟨sourceOnset, hsourceCapacity⟩ :=
    polynomiallyBounded_eventually_le_sixteenth_exponential
      hsourceMajorant
  refine ⟨inverseSourceMeasure sourceOnset, fun scheduleIndex honset => ?_⟩
  let sourceIndex := inverseSourceIndex scheduleIndex
  have hsourceOnset : sourceOnset ≤ sourceIndex := by
    apply le_inverseSourceIndex_of_measure_le
    exact honset.trans (by omega)
  have hlog :
      logScale (sourceIndex + 1) ≤ sourceIndex + 3 := by
    simpa only [Nat.add_assoc] using logScale_le_add_two (sourceIndex + 1)
  have hschedule :
      scheduleIndex + 1 ≤
        4 * (sourceIndex + 1) * (sourceIndex + 3) := by
    have hcross := scheduleIndex_succ_lt_four_measure scheduleIndex
    change scheduleIndex + 1 <
      4 * ((sourceIndex + 1) * logScale (sourceIndex + 1)) at hcross
    calc
      scheduleIndex + 1 ≤
          4 * ((sourceIndex + 1) * logScale (sourceIndex + 1)) :=
        Nat.le_of_lt hcross
      _ ≤ 4 * ((sourceIndex + 1) * (sourceIndex + 3)) := by
        gcongr
      _ = 4 * (sourceIndex + 1) * (sourceIndex + 3) := by ring
  have htransport :
      function scheduleIndex ≤ sourceMajorant sourceIndex := by
    calc
      function scheduleIndex ≤
          coefficient * (scheduleIndex + 1) ^ degree :=
        hbound scheduleIndex
      _ ≤
          coefficient *
            (4 * (sourceIndex + 1) * (sourceIndex + 3)) ^ degree := by
        gcongr
      _ = sourceMajorant sourceIndex := rfl
  exact htransport.trans
    (hsourceCapacity sourceIndex hsourceOnset)

/-- The inverse-polynomial canonical witness eventually fits the executable
shape at its actual selected source length, not merely at the schedule index. -/
theorem inverseRecoveryWitness_eventually_fits
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower : ℕ) :
    ∃ onset, ∀ scheduleIndex, onset ≤ scheduleIndex →
      recoveryWitnessCodeBitBound
          (inverseRecoveryWitnessLimits contracts outer advantagePower
            scheduleIndex) ≤
        recoveryWitnessWidth
          (sourceLength (inverseSourceIndex scheduleIndex)) := by
  obtain ⟨onset, hcapacity⟩ :=
    polynomiallyBounded_eventually_le_inverse_source_sixteenth
      (inverseRecoveryWitnessCodeBitBound_polynomiallyBounded
        contracts outer advantagePower)
  exact ⟨onset, fun scheduleIndex honset => by
    simpa only [sourceLength, recoveryWitnessWidth_eq] using
      hcapacity scheduleIndex honset⟩

/-- The actual fixed-verifier policy eventually fits directly as a function
of the source index encoded by the public input length. -/
theorem inverseRecoveryWitnessSource_eventually_fits
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower : ℕ) :
    ∃ onset, ∀ sourceIndex, onset ≤ sourceIndex →
      recoveryWitnessCodeBitBound
          (inverseRecoveryWitnessSourceLimits contracts outer advantagePower
            sourceIndex) ≤
        recoveryWitnessWidth (sourceLength sourceIndex) := by
  obtain ⟨onset, hcapacity⟩ :=
    polynomiallyBounded_eventually_le_sixteenth_exponential
      (inverseRecoveryWitnessSourceCodeBitBound_polynomiallyBounded
        contracts outer advantagePower)
  exact ⟨onset, fun sourceIndex honset => by
    simpa only [sourceLength, recoveryWitnessWidth_eq] using
      hcapacity sourceIndex honset⟩

/-- Transport the source-index capacity onset back to inverse schedule
coordinates.  This is the exact form consumed after target selection. -/
theorem inverseRecoveryWitnessSource_eventually_fits_at_schedule
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower : ℕ) :
    ∃ onset, ∀ scheduleIndex, onset ≤ scheduleIndex →
      recoveryWitnessCodeBitBound
          (inverseRecoveryWitnessSourceLimits contracts outer advantagePower
            (inverseSourceIndex scheduleIndex)) ≤
        recoveryWitnessWidth
          (sourceLength (inverseSourceIndex scheduleIndex)) := by
  obtain ⟨sourceOnset, hcapacity⟩ :=
    inverseRecoveryWitnessSource_eventually_fits
      contracts outer advantagePower
  refine
    ⟨inverseSourceMeasure sourceOnset, fun scheduleIndex honset => ?_⟩
  have hsourceOnset :
      sourceOnset ≤ inverseSourceIndex scheduleIndex := by
    apply le_inverseSourceIndex_of_measure_le
    exact honset.trans (by omega)
  exact hcapacity (inverseSourceIndex scheduleIndex) hsourceOnset

/-- Zero-extension preserves every checked inverse-schedule witness after the
internally derived onset. -/
theorem inverseRecoveryWitness_eventual_readback
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower : ℕ) :
    ∃ onset, ∀ scheduleIndex, onset ≤ scheduleIndex →
      ∀ witness : CheckedRecoveryWitness
          (inverseRecoveryWitnessLimits contracts outer advantagePower
            scheduleIndex),
        encodeBitInput
            (paddedRecoveryWitnessCode
              (sourceLength (inverseSourceIndex scheduleIndex)) witness) =
          witness.code := by
  obtain ⟨onset, hcapacity⟩ :=
    inverseRecoveryWitness_eventually_fits contracts outer advantagePower
  exact ⟨onset, fun scheduleIndex honset witness =>
    encodeBitInput_paddedRecoveryWitnessCode witness
      (hcapacity scheduleIndex honset)⟩

/-- Zero-extension/readback for the sole source-indexed verifier policy. -/
theorem inverseRecoveryWitnessSource_eventual_readback
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower : ℕ) :
    ∃ onset, ∀ scheduleIndex, onset ≤ scheduleIndex →
      ∀ witness : CheckedRecoveryWitness
          (inverseRecoveryWitnessSourceLimits contracts outer advantagePower
            (inverseSourceIndex scheduleIndex)),
        encodeBitInput
            (paddedRecoveryWitnessCode
              (sourceLength (inverseSourceIndex scheduleIndex)) witness) =
          witness.code := by
  obtain ⟨onset, hcapacity⟩ :=
    inverseRecoveryWitnessSource_eventually_fits_at_schedule
      contracts outer advantagePower
  exact ⟨onset, fun scheduleIndex honset witness =>
    encodeBitInput_paddedRecoveryWitnessCode witness
      (hcapacity scheduleIndex honset)⟩

/-- The fixed-rate canonical witness eventually fits the executable `n / 16`
shape solely from the published contracts and exact schedule definitions. -/
theorem fixedRecoveryWitness_eventually_fits
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate : ℕ) :
    ∃ onset, ∀ sourceIndex, onset ≤ sourceIndex →
      recoveryWitnessCodeBitBound
          (fixedRecoveryWitnessLimits contracts outer requestedRate
            sourceIndex) ≤
        recoveryWitnessWidth (sourceLength sourceIndex) := by
  obtain ⟨onset, hcapacity⟩ :=
    polynomiallyBounded_eventually_le_sixteenth_exponential
      (fixedRecoveryWitnessCodeBitBound_polynomiallyBounded
        contracts outer requestedRate)
  exact ⟨onset, fun sourceIndex honset => by
    simpa only [sourceLength, recoveryWitnessWidth_eq] using
      hcapacity sourceIndex honset⟩

/-- Zero-extension preserves every checked fixed-rate witness after the
internally derived onset; callers provide neither a size nor padding proof. -/
theorem fixedRecoveryWitness_eventual_readback
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate : ℕ) :
    ∃ onset, ∀ sourceIndex, onset ≤ sourceIndex →
      ∀ witness : CheckedRecoveryWitness
          (fixedRecoveryWitnessLimits contracts outer requestedRate
            sourceIndex),
        encodeBitInput
            (paddedRecoveryWitnessCode (sourceLength sourceIndex) witness) =
          witness.code := by
  obtain ⟨onset, hcapacity⟩ :=
    fixedRecoveryWitness_eventually_fits contracts outer requestedRate
  exact ⟨onset, fun sourceIndex honset witness =>
    encodeBitInput_paddedRecoveryWitnessCode witness
      (hcapacity sourceIndex honset)⟩

/-! ## Direct `RecoveredPerClassFacts` schedule fields -/

def InverseRecoveryWitnessAuditAt
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower target : ℕ) : Prop :=
  let scheduleIndex :=
    inverseSelectedSource contracts outer advantagePower target
  recoveryWitnessCodeBitBound
      (inverseRecoveryWitnessSourceLimits contracts outer advantagePower
        (inverseSourceIndex scheduleIndex)) ≤
    recoveryWitnessWidth
      (sourceLength (inverseSourceIndex scheduleIndex))

theorem inverseRecoveryWitnessAudit_eventually
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower : ℕ) :
    ∃ onset, ∀ target, onset ≤ target →
      InverseRecoveryWitnessAuditAt contracts outer advantagePower target := by
  obtain ⟨scheduleOnset, hcapacity⟩ :=
    inverseRecoveryWitnessSource_eventually_fits_at_schedule
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

/-- Target-indexed readback used by the linked verifier completeness proof. -/
private theorem inverseSelectedRecoveryWitness_eventual_readback
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower : ℕ) :
    ∃ onset, ∀ target, onset ≤ target →
      ∀ witness : CheckedRecoveryWitness
          (inverseRecoveryWitnessSourceLimits contracts outer advantagePower
            (inverseSourceIndex
              (inverseSelectedSource contracts outer advantagePower target))),
        encodeBitInput
            (paddedRecoveryWitnessCode
              (sourceLength (inverseSourceIndex
                (inverseSelectedSource contracts outer advantagePower target)))
              witness) =
          witness.code := by
  obtain ⟨onset, hcapacity⟩ :=
    inverseRecoveryWitnessAudit_eventually contracts outer advantagePower
  exact ⟨onset, fun target htarget witness =>
    encodeBitInput_paddedRecoveryWitnessCode witness
      (hcapacity target htarget)⟩

/-- Fixed-rate counterpart of `InverseRecoveryWitnessAuditAt`. -/
def FixedRecoveryWitnessAuditAt
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate target : ℕ) : Prop :=
  let sourceIndex :=
    fixedSelectedSource contracts outer requestedRate target
  recoveryWitnessCodeBitBound
      (fixedRecoveryWitnessLimits contracts outer requestedRate sourceIndex) ≤
    recoveryWitnessWidth (sourceLength sourceIndex)

theorem fixedRecoveryWitnessAudit_eventually
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate : ℕ) :
    ∃ onset, ∀ target, onset ≤ target →
      FixedRecoveryWitnessAuditAt contracts outer requestedRate target := by
  obtain ⟨sourceOnset, hcapacity⟩ :=
    fixedRecoveryWitness_eventually_fits contracts outer requestedRate
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

private theorem fixedSelectedRecoveryWitness_eventual_readback
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate : ℕ) :
    ∃ onset, ∀ target, onset ≤ target →
      ∀ witness : CheckedRecoveryWitness
          (fixedRecoveryWitnessLimits contracts outer requestedRate
            (fixedSelectedSource contracts outer requestedRate target)),
        encodeBitInput
            (paddedRecoveryWitnessCode
              (sourceLength
                (fixedSelectedSource contracts outer requestedRate target))
              witness) =
          witness.code := by
  obtain ⟨onset, hcapacity⟩ :=
    fixedRecoveryWitnessAudit_eventually contracts outer requestedRate
  exact ⟨onset, fun target htarget witness =>
    encodeBitInput_paddedRecoveryWitnessCode witness
      (hcapacity target htarget)⟩

end NearCubicWires.RecoveryWitnessScheduleCapacity
