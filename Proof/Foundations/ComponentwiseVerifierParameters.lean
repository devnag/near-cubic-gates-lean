import Proof.Foundations.BooleanCircuitSizePadding
import Proof.Foundations.ComponentwiseValidity

/-!
# Executable componentwise-verifier parameters

The imported pointwise PCPP exposes real completeness and soundness constants,
whereas the fixed weak verifier can store and compare only finite rational
codes.  This module makes the one canonical rational choice and proves the
entire numerical reserve once.  Downstream machine code therefore receives
data, not an unproved real-comparison side condition.
-/

namespace NearCubicWires.ComponentwiseVerifierParameters

open NearCubicWires
open NearCubicWires.ComponentwiseValidity
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.SourceInterfaces

/-- Finite constants frozen after the PCPP gap and before the weak machine.
The threshold is chosen on the completeness side of the semantic midpoint:
this preserves one-sided soundness while leaving a strict completeness
reserve for the canonical honest branch. -/
structure ExecutableSoundnessParameters
    (completeness soundness : ℝ) where
  zeta : ℚ
  outerError : ℚ
  estimationError : ℚ
  threshold : ℚ
  zetaPositive : 0 < zeta
  zetaBelowThreeHalves : (zeta : ℝ) < 3 / 2
  outerErrorPositive : 0 < outerError
  estimationErrorPositive : 0 < estimationError
  estimationError_le_zeta : estimationError ≤ zeta
  thresholdAboveMidpoint :
    (completeness + soundness) / 2 ≤ (threshold : ℝ)
  soundReserve :
    (outerError : ℝ) +
        6 * Real.sqrt (12 * (zeta : ℝ)) +
        (estimationError : ℝ) <
      (completeness - soundness) / 2
  completenessReserve :
    (threshold : ℝ) +
        6 * Real.sqrt (12 * (zeta : ℝ)) +
        (estimationError : ℝ) <
      completeness

def ExecutableSoundnessParameters.semantic
    {completeness soundness : ℝ}
    (parameters :
      ExecutableSoundnessParameters completeness soundness) :
    SoundnessParameters where
  completeness := completeness
  soundness := soundness
  zeta := parameters.zeta
  outerError := parameters.outerError
  estimationError := parameters.estimationError
  zetaNonnegative := le_of_lt (by exact_mod_cast parameters.zetaPositive)
  outerErrorNonnegative :=
    le_of_lt (by exact_mod_cast parameters.outerErrorPositive)
  estimationErrorNonnegative :=
    le_of_lt (by exact_mod_cast parameters.estimationErrorPositive)
  gap := by
    have hreserve := parameters.soundReserve
    have houter : 0 ≤ (parameters.outerError : ℝ) :=
      le_of_lt (by exact_mod_cast parameters.outerErrorPositive)
    have hestimation : 0 ≤ (parameters.estimationError : ℝ) :=
      le_of_lt (by exact_mod_cast parameters.estimationErrorPositive)
    have hrounding :
        0 ≤ 6 * Real.sqrt (12 * (parameters.zeta : ℝ)) := by positivity
    linarith
  reserve := parameters.soundReserve

@[simp] theorem ExecutableSoundnessParameters.semantic_acceptanceThreshold
    {completeness soundness : ℝ}
    (parameters :
      ExecutableSoundnessParameters completeness soundness) :
    parameters.semantic.acceptanceThreshold =
      (completeness + soundness) / 2 := by
  rfl

theorem ExecutableSoundnessParameters.semanticThreshold_le_executable
    {completeness soundness : ℝ}
    (parameters :
      ExecutableSoundnessParameters completeness soundness) :
    parameters.semantic.acceptanceThreshold ≤ (parameters.threshold : ℝ) := by
  simpa using parameters.thresholdAboveMidpoint

theorem ExecutableSoundnessParameters.thresholdPositive
    {completeness soundness : ℝ}
    (parameters :
      ExecutableSoundnessParameters completeness soundness)
    (soundnessNonnegative : 0 ≤ soundness)
    (gap : soundness < completeness) :
    0 < parameters.threshold := by
  exact_mod_cast (lt_of_lt_of_le
    (by linarith : (0 : ℝ) < (completeness + soundness) / 2)
    parameters.thresholdAboveMidpoint)

theorem ExecutableSoundnessParameters.thresholdBelowOne
    {completeness soundness : ℝ}
    (parameters :
      ExecutableSoundnessParameters completeness soundness)
    (completeness_le_one : completeness ≤ 1) :
    parameters.threshold < 1 := by
  have hrounding :
      0 ≤ 6 * Real.sqrt (12 * (parameters.zeta : ℝ)) := by positivity
  have hestimation : 0 ≤ (parameters.estimationError : ℝ) :=
    le_of_lt (by exact_mod_cast parameters.estimationErrorPositive)
  exact_mod_cast
    (lt_of_lt_of_le
      (by linarith [parameters.completenessReserve] :
        (parameters.threshold : ℝ) < completeness)
      completeness_le_one)

/-- Every strict real PCPP gap admits finite rational verifier constants with
both the one-sided soundness reserve and the honest-branch completeness
reserve.  The concrete fractions are deliberately slack so later layers do
not have to rebalance the same error terms. -/
theorem existsExecutableSoundnessParameters
    {completeness soundness : ℝ}
    (gap : soundness < completeness) :
    Nonempty (ExecutableSoundnessParameters completeness soundness) := by
  let gapSize := completeness - soundness
  have gapPositive : 0 < gapSize := sub_pos.mpr gap
  have zetaBoundPositive :
      0 < min (3 / 2 : ℝ) (gapSize ^ 2 / 43200) := by
    apply lt_min
    · norm_num
    · positivity
  obtain ⟨zeta, zetaPositive, zetaSmall⟩ :=
    exists_pos_rat_lt zetaBoundPositive
  have zetaBelowThreeHalves : (zeta : ℝ) < 3 / 2 :=
    zetaSmall.trans_le (min_le_left _ _)
  have zetaBelowSquare :
      (zeta : ℝ) < gapSize ^ 2 / 43200 :=
    zetaSmall.trans_le (min_le_right _ _)
  have zetaCastPositive : (0 : ℝ) < (zeta : ℝ) := by
    exact_mod_cast zetaPositive
  have roundingReserve :
      6 * Real.sqrt (12 * (zeta : ℝ)) < gapSize / 10 := by
    have innerNonnegative : 0 ≤ 12 * (zeta : ℝ) := by positivity
    have targetPositive : 0 < gapSize / 60 := by positivity
    have squareBound :
        12 * (zeta : ℝ) < (gapSize / 60) ^ 2 := by
      nlinarith [zetaBelowSquare]
    have sqrtBound :
        Real.sqrt (12 * (zeta : ℝ)) < gapSize / 60 :=
      (Real.sqrt_lt' targetPositive).2 squareBound
    nlinarith
  have estimationBoundPositive :
      (0 : ℝ) < min (zeta : ℝ) (gapSize / 20) := by
    exact lt_min zetaCastPositive (by positivity)
  obtain ⟨estimationError, estimationErrorPositive, estimationErrorSmall⟩ :=
    exists_pos_rat_lt estimationBoundPositive
  have estimationError_le_zeta : estimationError ≤ zeta := by
    exact_mod_cast
      (le_of_lt
        (estimationErrorSmall.trans_le (min_le_left _ _)))
  have estimationGapReserve :
      (estimationError : ℝ) < gapSize / 20 :=
    estimationErrorSmall.trans_le (min_le_right _ _)
  obtain ⟨outerError, outerErrorPositive, outerErrorSmall⟩ :=
    exists_pos_rat_lt (show (0 : ℝ) < gapSize / 20 by positivity)
  have midpointBelowUpper :
      (completeness + soundness) / 2 <
        completeness - gapSize / 4 := by
    dsimp [gapSize]
    linarith
  obtain ⟨threshold, thresholdAboveMidpoint, thresholdBelowUpper⟩ :=
    exists_rat_btwn midpointBelowUpper
  refine ⟨{
    zeta := zeta
    outerError := outerError
    estimationError := estimationError
    threshold := threshold
    zetaPositive := zetaPositive
    zetaBelowThreeHalves := zetaBelowThreeHalves
    outerErrorPositive := outerErrorPositive
    estimationErrorPositive := estimationErrorPositive
    estimationError_le_zeta := estimationError_le_zeta
    thresholdAboveMidpoint := le_of_lt thresholdAboveMidpoint
    soundReserve := ?_
    completenessReserve := ?_
  }⟩
  · dsimp [gapSize] at roundingReserve estimationGapReserve outerErrorSmall ⊢
    linarith
  · dsimp [gapSize] at roundingReserve
    dsimp [gapSize] at estimationGapReserve
    dsimp [gapSize] at thresholdBelowUpper
    dsimp [gapSize] at gapPositive
    linarith

/-! ## Bounds derived from the executable PCPP source -/

def constantBooleanCircuit (value : Bool) : BooleanCircuit 1 where
  nodes := [.const value]
  output := ⟨0, by simp⟩
  wellFormed := by
    intro index
    simp [BooleanNode.WellFormedAt]

@[simp] theorem constantBooleanCircuit_size (value : Bool) :
    (constantBooleanCircuit value).size = 1 := by
  rfl

@[simp] theorem constantBooleanCircuit_eval
    (value : Bool) (input : BitInput 1) :
    (constantBooleanCircuit value).eval input = value := by
  rfl

theorem pointwiseSatisfiedFraction_nonnegative
    {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit) (input : BitInput n)
    (auxiliary : BitInput pcpp.auxiliaryBits) :
    0 ≤ pcpp.satisfiedFraction input auxiliary := by
  unfold PointwisePCPP.satisfiedFraction
  positivity

theorem pointwiseSatisfiedFraction_le_one
    {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit) (input : BitInput n)
    (auxiliary : BitInput pcpp.auxiliaryBits) :
    pcpp.satisfiedFraction input auxiliary ≤ 1 := by
  unfold PointwisePCPP.satisfiedFraction
  apply (div_le_one (by positivity)).2
  have hcard :
      (Finset.univ.filter fun i =>
        (pcpp.clauses i).eval
          (pcpp.assignment input auxiliary)).card ≤
        2 ^ pcpp.clauseBits := by
    simpa using
      (Finset.card_filter_le (Finset.univ : Finset (Fin (2 ^ pcpp.clauseBits)))
        (fun i => (pcpp.clauses i).eval
          (pcpp.assignment input auxiliary)))
  exact_mod_cast hcard

theorem uniformPointwisePCPPSource_soundness_nonnegative
    (source : UniformPointwisePCPPSource) :
    0 ≤ source.soundness := by
  let circuit := constantBooleanCircuit false
  have hsize : 1 ≤ circuit.size := by simp [circuit]
  obtain ⟨supportBound, _, _, _, _, _, _, _, _, sound, _⟩ :=
    source.guarantee circuit hsize
  let pcpp := (source.factory.forCircuit circuit).toSemantic supportBound
  let input : BitInput 1 := fun _ => false
  let auxiliary : BitInput pcpp.auxiliaryBits := fun _ => false
  have hreject : ¬circuit.eval input := by simp [circuit]
  exact (pointwiseSatisfiedFraction_nonnegative pcpp input auxiliary).trans
    (sound input hreject auxiliary)

theorem uniformPointwisePCPPSource_completeness_le_one
    (source : UniformPointwisePCPPSource) :
    source.completeness ≤ 1 := by
  let circuit := constantBooleanCircuit true
  have hsize : 1 ≤ circuit.size := by simp [circuit]
  obtain ⟨supportBound, _, _, _, _, _, _, _, complete, _, _⟩ :=
    source.guarantee circuit hsize
  let pcpp := (source.factory.forCircuit circuit).toSemantic supportBound
  let input : BitInput 1 := fun _ => false
  have haccept : circuit.eval input := by simp [circuit]
  exact (complete input haccept).trans
    (pointwiseSatisfiedFraction_le_one pcpp input
      (pcpp.honestAuxiliary input))

noncomputable def executableParametersOfSource
    (source : UniformPointwisePCPPSource) :
    ExecutableSoundnessParameters source.completeness source.soundness :=
  Classical.choice (existsExecutableSoundnessParameters source.gap)

theorem executableParametersOfSource_thresholdPositive
    (source : UniformPointwisePCPPSource) :
    0 < (executableParametersOfSource source).threshold :=
  (executableParametersOfSource source).thresholdPositive
    (uniformPointwisePCPPSource_soundness_nonnegative source) source.gap

theorem executableParametersOfSource_thresholdBelowOne
    (source : UniformPointwisePCPPSource) :
    (executableParametersOfSource source).threshold < 1 :=
  (executableParametersOfSource source).thresholdBelowOne
    (uniformPointwisePCPPSource_completeness_le_one source)

end NearCubicWires.ComponentwiseVerifierParameters
