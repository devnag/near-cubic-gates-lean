import Proof.Circuits.ComponentwiseBranchExtraction
import Proof.Foundations.RecoveryScheduleEnvelope

namespace NearCubicWires.VerifierThresholdSeam

open Finset
open scoped BigOperators
open NearCubicWires
open NearCubicWires.ComponentwiseBranchExtraction
open NearCubicWires.ComponentwiseValidity
open NearCubicWires.ComponentwiseVerifierParameters
open NearCubicWires.ComponentwiseWeakMachine
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.SourceInterfaces

/-! ## §1 The clause-marginal `ℓ¹` error

The Case-2 seed is the honest *occurrence* table, so its uniform measure is
exactly the clause marginal crossed with the left/right position.  The budget
below is therefore the quantity the approximation hypothesis controls; it is
the sum over the two clause sides, matching `totalClausePenaltyMean`. -/

/-- Mean `ℓ¹` error between a guessed proof and a reference proof, under the
clause marginal of one selected clause side. -/
noncomputable def clauseErrorMean {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit)
    (value reference : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ)
    (side : TwoLiteralClause (pcpp.systematicBits + pcpp.auxiliaryBits) →
      Literal (pcpp.systematicBits + pcpp.auxiliaryBits)) : ℝ :=
  𝔼 i ∈ (univ : Finset (Fin (2 ^ pcpp.clauseBits))),
    |value (literalIndex (side (pcpp.clauses i))) -
      reference (literalIndex (side (pcpp.clauses i)))|

/-- Total clause-marginal `ℓ¹` error charged jointly on both clause sides.
This is the exact analogue of `totalClausePenaltyMean` and the quantity the
Case-2 approximation hypothesis bounds. -/
noncomputable def totalClauseErrorMean {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit)
    (value reference : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ) :
    ℝ :=
  clauseErrorMean pcpp value reference TwoLiteralClause.left +
    clauseErrorMean pcpp value reference TwoLiteralClause.right

/-- The same error under the uniform measure on clause *occurrences*, i.e. the
uniform pair (clause index, left/right position).  This is exactly the measure
carried by `honestOccurrenceFunction`, so it is the quantity the Case-2
approximation parameter bounds. -/
noncomputable def clauseOccurrenceErrorMean {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (value reference : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ) :
    ℝ :=
  (clauseErrorMean pcpp value reference TwoLiteralClause.left +
      clauseErrorMean pcpp value reference TwoLiteralClause.right) / 2

/-- Charging both clause sides doubles the occurrence-uniform error.  This is
the whole content of the budget conversion `delta ↦ 2 * delta` between the seed
metric and the verifier's joint ledger. -/
theorem totalClauseErrorMean_eq_two_mul_occurrence {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (value reference : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ) :
    totalClauseErrorMean pcpp value reference =
      2 * clauseOccurrenceErrorMean pcpp value reference := by
  unfold totalClauseErrorMean clauseOccurrenceErrorMean
  ring

theorem clauseErrorMean_nonnegative {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit)
    (value reference : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ)
    (side : TwoLiteralClause (pcpp.systematicBits + pcpp.auxiliaryBits) →
      Literal (pcpp.systematicBits + pcpp.auxiliaryBits)) :
    0 ≤ clauseErrorMean pcpp value reference side := by
  unfold clauseErrorMean
  exact Finset.expect_nonneg fun i _ => abs_nonneg _

theorem totalClauseErrorMean_nonnegative {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit)
    (value reference : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ) :
    0 ≤ totalClauseErrorMean pcpp value reference := by
  unfold totalClauseErrorMean
  have hleft := clauseErrorMean_nonnegative pcpp value reference
    TwoLiteralClause.left
  have hright := clauseErrorMean_nonnegative pcpp value reference
    TwoLiteralClause.right
  linarith

/-! ## §2 The validity charge is dominated by the `ℓ¹` budget

The verifier's componentwise test charges a square penalty.  Against any
Boolean proof that respects the prescribed systematic parities, that penalty is
below the pointwise `ℓ¹` error, so the whole validity ladder is paid by the
same budget. -/

/-- The prescribed rounding constraint at a coordinate is satisfied by every
genuine PCPP assignment for the same input. -/
private theorem systematicConstraint_eq_some_imp {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (input : BitInput n) (auxiliary : BitInput pcpp.auxiliaryBits)
    (index : Fin (pcpp.systematicBits + pcpp.auxiliaryBits))
    (expected : Bool)
    (hconstraint : systematicConstraint pcpp input index = some expected) :
    pcpp.assignment input auxiliary index = expected := by
  refine Fin.addCases ?_ ?_ index expected hconstraint
  · intro i expected hconstraint
    simp only [systematicConstraint, Fin.addCases_left] at hconstraint
    simp [PointwisePCPP.assignment, ← Option.some_inj.mp hconstraint]
  · intro i expected hconstraint
    simp only [systematicConstraint, Fin.addCases_right] at hconstraint
    exact absurd hconstraint (by simp)

private theorem validityPenalty_le_assignment_distance {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (input : BitInput n) (auxiliary : BitInput pcpp.auxiliaryBits)
    (value : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ)
    (hnonneg : ∀ j, 0 ≤ value j) (hleOne : ∀ j, value j ≤ 1)
    (index : Fin (pcpp.systematicBits + pcpp.auxiliaryBits)) :
    validityPenalty (systematicConstraint pcpp input index) (value index) ≤
      |value index -
        bitAsReal (pcpp.assignment input auxiliary index)| :=
  validityPenalty_le_nearby_distance _
    (pcpp.assignment input auxiliary index) (value index)
    (hnonneg index) (hleOne index)
    (fun expected hexpected =>
      systematicConstraint_eq_some_imp pcpp input auxiliary index expected
        hexpected)

theorem clausePenaltyMean_le_clauseErrorMean {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (input : BitInput n) (auxiliary : BitInput pcpp.auxiliaryBits)
    (value : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ)
    (hnonneg : ∀ j, 0 ≤ value j) (hleOne : ∀ j, value j ≤ 1)
    (side : TwoLiteralClause (pcpp.systematicBits + pcpp.auxiliaryBits) →
      Literal (pcpp.systematicBits + pcpp.auxiliaryBits)) :
    clausePenaltyMean pcpp input value side ≤
      clauseErrorMean pcpp value
        (fun j => bitAsReal (pcpp.assignment input auxiliary j)) side := by
  unfold clausePenaltyMean clauseErrorMean
  exact Finset.expect_le_expect fun i _ =>
    validityPenalty_le_assignment_distance pcpp input auxiliary value
      hnonneg hleOne (literalIndex (side (pcpp.clauses i)))

/-- The verifier's joint validity charge never exceeds the clause-marginal
`ℓ¹` budget against any genuine PCPP assignment. -/
theorem totalClausePenaltyMean_le_totalClauseErrorMean {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (input : BitInput n) (auxiliary : BitInput pcpp.auxiliaryBits)
    (value : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ)
    (hnonneg : ∀ j, 0 ≤ value j) (hleOne : ∀ j, value j ≤ 1) :
    totalClausePenaltyMean pcpp input value ≤
      totalClauseErrorMean pcpp value
        (fun j => bitAsReal (pcpp.assignment input auxiliary j)) := by
  unfold totalClausePenaltyMean totalClauseErrorMean
  have hleft := clausePenaltyMean_le_clauseErrorMean pcpp input auxiliary
    value hnonneg hleOne TwoLiteralClause.left
  have hright := clausePenaltyMean_le_clauseErrorMean pcpp input auxiliary
    value hnonneg hleOne TwoLiteralClause.right
  linarith

/-! ## §3 The clause mean moves by at most the `ℓ¹` budget

The arithmetized two-literal clause is one-Lipschitz in each literal on the
unit cube, so the same budget that pays the validity ladder also caps the
movement of the estimated quantity. -/

private theorem bitAsReal_nonnegative (value : Bool) :
    0 ≤ bitAsReal value := by
  cases value <;> norm_num [bitAsReal]

private theorem bitAsReal_le_one (value : Bool) :
    bitAsReal value ≤ 1 := by
  cases value <;> norm_num [bitAsReal]

private theorem literalValue_nonnegative (negative : Bool) (value : ℝ)
    (hzero : 0 ≤ value) (hone : value ≤ 1) :
    0 ≤ literalValue negative value := by
  cases negative
  · simpa [literalValue] using hzero
  · have hvalue : literalValue true value = 1 - value := by
      simp [literalValue]
    rw [hvalue]
    linarith

private theorem literalValue_le_one (negative : Bool) (value : ℝ)
    (hzero : 0 ≤ value) (hone : value ≤ 1) :
    literalValue negative value ≤ 1 := by
  cases negative
  · simpa [literalValue] using hone
  · have hvalue : literalValue true value = 1 - value := by
      simp [literalValue]
    rw [hvalue]
    linarith

/-- One-Lipschitz movement of the arithmetized clause on the unit cube.  This
is the completeness-side counterpart of `clauseValue_sub_le`, which is stated
with the quadratic remainder needed by the rounding ledger. -/
theorem abs_clauseValue_sub_le
    (leftNegative rightNegative : Bool)
    (left right otherLeft otherRight : ℝ)
    (hright : 0 ≤ right) (hrightOne : right ≤ 1)
    (hotherLeft : 0 ≤ otherLeft) (hotherLeftOne : otherLeft ≤ 1) :
    |clauseValue leftNegative rightNegative left right -
        clauseValue leftNegative rightNegative otherLeft otherRight| ≤
      |left - otherLeft| + |right - otherRight| := by
  have hidentity :
      clauseValue leftNegative rightNegative left right -
          clauseValue leftNegative rightNegative otherLeft otherRight =
        (literalValue leftNegative left -
              literalValue leftNegative otherLeft) *
            (1 - literalValue rightNegative right) +
          (literalValue rightNegative right -
              literalValue rightNegative otherRight) *
            (1 - literalValue leftNegative otherLeft) := by
    simp only [clauseValue]
    ring
  have hrightBound : |1 - literalValue rightNegative right| ≤ 1 := by
    rw [abs_of_nonneg
      (by linarith [literalValue_le_one rightNegative right hright hrightOne] :
        (0 : ℝ) ≤ 1 - literalValue rightNegative right)]
    linarith [literalValue_nonnegative rightNegative right hright hrightOne]
  have hleftBound : |1 - literalValue leftNegative otherLeft| ≤ 1 := by
    rw [abs_of_nonneg
      (by
        linarith [literalValue_le_one leftNegative otherLeft hotherLeft
          hotherLeftOne] :
        (0 : ℝ) ≤ 1 - literalValue leftNegative otherLeft)]
    linarith [literalValue_nonnegative leftNegative otherLeft hotherLeft
      hotherLeftOne]
  rw [hidentity]
  calc
    |(literalValue leftNegative left -
            literalValue leftNegative otherLeft) *
          (1 - literalValue rightNegative right) +
        (literalValue rightNegative right -
            literalValue rightNegative otherRight) *
          (1 - literalValue leftNegative otherLeft)| ≤
        |(literalValue leftNegative left -
              literalValue leftNegative otherLeft) *
            (1 - literalValue rightNegative right)| +
          |(literalValue rightNegative right -
              literalValue rightNegative otherRight) *
            (1 - literalValue leftNegative otherLeft)| :=
      abs_add_le _ _
    _ = |literalValue leftNegative left -
            literalValue leftNegative otherLeft| *
          |1 - literalValue rightNegative right| +
        |literalValue rightNegative right -
            literalValue rightNegative otherRight| *
          |1 - literalValue leftNegative otherLeft| := by
      rw [abs_mul, abs_mul]
    _ ≤ |literalValue leftNegative left -
            literalValue leftNegative otherLeft| * 1 +
        |literalValue rightNegative right -
            literalValue rightNegative otherRight| * 1 := by
      gcongr
    _ = |left - otherLeft| + |right - otherRight| := by
      rw [mul_one, mul_one, abs_literalValue_sub, abs_literalValue_sub]

/-- Movement of the estimated clause mean is charged entirely to the
clause-marginal `ℓ¹` budget. -/
theorem abs_clauseMean_sub_le_totalClauseErrorMean {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (value reference : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ)
    (hnonneg : ∀ j, 0 ≤ value j) (hleOne : ∀ j, value j ≤ 1)
    (hreferenceNonneg : ∀ j, 0 ≤ reference j)
    (hreferenceLeOne : ∀ j, reference j ≤ 1) :
    |clauseMean pcpp value - clauseMean pcpp reference| ≤
      totalClauseErrorMean pcpp value reference := by
  set index : Finset (Fin (2 ^ pcpp.clauseBits)) := univ with hindex
  calc
    |clauseMean pcpp value - clauseMean pcpp reference| =
        |𝔼 i ∈ index,
          (clauseRealValue (pcpp.clauses i) value -
            clauseRealValue (pcpp.clauses i) reference)| := by
      rw [Finset.expect_sub_distrib]
      rfl
    _ ≤ 𝔼 i ∈ index,
          |clauseRealValue (pcpp.clauses i) value -
            clauseRealValue (pcpp.clauses i) reference| :=
      Finset.abs_expect_le _ _
    _ ≤ 𝔼 i ∈ index,
          (|value (literalIndex (pcpp.clauses i).left) -
              reference (literalIndex (pcpp.clauses i).left)| +
            |value (literalIndex (pcpp.clauses i).right) -
              reference (literalIndex (pcpp.clauses i).right)|) :=
      Finset.expect_le_expect fun i _ =>
        abs_clauseValue_sub_le _ _ _ _ _ _
          (hnonneg _) (hleOne _) (hreferenceNonneg _) (hreferenceLeOne _)
    _ = totalClauseErrorMean pcpp value reference := by
      rw [Finset.expect_add_distrib]
      rfl

/-! ## §4 The completeness direction closes at budget `6 * zeta`

Every constant below is the published one.  The only hypothesis is that the
clause-marginal `ℓ¹` budget of the guessed proof against the honest table is at
most `6 * zeta`; nothing else about the guessed proof is used. -/

theorem completeness_le_clauseMean_of_satisfiedFraction {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (input : BitInput n) (auxiliary : BitInput pcpp.auxiliaryBits)
    (completeness : ℝ)
    (hcomplete : completeness ≤ pcpp.satisfiedFraction input auxiliary) :
    completeness ≤
      clauseMean pcpp
        (fun j => bitAsReal (pcpp.assignment input auxiliary j)) := by
  rw [clauseMean_bitAsReal_eq_satisfiedFraction]
  exact hcomplete

private theorem zeta_le_sqrt_twelveZeta
    {completeness soundness : ℝ}
    (parameters : ExecutableSoundnessParameters completeness soundness) :
    (parameters.zeta : ℝ) ≤ Real.sqrt (12 * (parameters.zeta : ℝ)) := by
  have hzeta : (0 : ℝ) < (parameters.zeta : ℝ) := by
    exact_mod_cast parameters.zetaPositive
  have hsmall := parameters.zetaBelowThreeHalves
  have hsquare : (parameters.zeta : ℝ) ^ 2 ≤ 12 * (parameters.zeta : ℝ) := by
    nlinarith
  calc
    (parameters.zeta : ℝ) = Real.sqrt ((parameters.zeta : ℝ) ^ 2) :=
      (Real.sqrt_sq (le_of_lt hzeta)).symm
    _ ≤ Real.sqrt (12 * (parameters.zeta : ℝ)) :=
      Real.sqrt_le_sqrt hsquare

/-- **Completeness seam.**  A guessed proof whose clause-marginal `ℓ¹` budget
against an honest PCPP assignment is at most `6 * zeta` forces the verifier's
final comparison, at the published threshold, estimation error and validity
constant. -/
theorem threshold_le_estimate_of_clauseErrorBudget {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (input : BitInput n) (auxiliary : BitInput pcpp.auxiliaryBits)
    {completeness soundness : ℝ}
    (parameters : ExecutableSoundnessParameters completeness soundness)
    (value : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ)
    (estimate : ℝ)
    (hnonneg : ∀ j, 0 ≤ value j) (hleOne : ∀ j, value j ≤ 1)
    (hhonest :
      completeness ≤
        clauseMean pcpp
          (fun j => bitAsReal (pcpp.assignment input auxiliary j)))
    (hbudget :
      totalClauseErrorMean pcpp value
          (fun j => bitAsReal (pcpp.assignment input auxiliary j)) ≤
        6 * (parameters.zeta : ℝ))
    (haccurate :
      |estimate - clauseMean pcpp value| ≤
        (parameters.estimationError : ℝ)) :
    (parameters.threshold : ℝ) ≤ estimate := by
  have hmove :=
    abs_clauseMean_sub_le_totalClauseErrorMean pcpp value
      (fun j => bitAsReal (pcpp.assignment input auxiliary j))
      hnonneg hleOne
      (fun j => bitAsReal_nonnegative _) (fun j => bitAsReal_le_one _)
  have hmoveLower :
      clauseMean pcpp
          (fun j => bitAsReal (pcpp.assignment input auxiliary j)) -
          clauseMean pcpp value ≤
        6 * (parameters.zeta : ℝ) := by
    have hupper := (abs_le.mp (hmove.trans hbudget)).1
    linarith
  have hestimateLower :
      clauseMean pcpp value - (parameters.estimationError : ℝ) ≤ estimate := by
    have := (abs_le.mp haccurate).1
    linarith
  have hrounding :
      6 * (parameters.zeta : ℝ) ≤
        6 * Real.sqrt (12 * (parameters.zeta : ℝ)) := by
    have := zeta_le_sqrt_twelveZeta parameters
    linarith
  have hreserve := parameters.completenessReserve
  linarith

/-- Accepting trace of the fixed componentwise verifier on a guessed proof
that stays inside the clause-marginal budget of an honest PCPP assignment. -/
noncomputable def honestApproximationTrace {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (input : BitInput n) (auxiliary : BitInput pcpp.auxiliaryBits)
    {completeness soundness : ℝ}
    (parameters : ExecutableSoundnessParameters completeness soundness)
    (value : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ)
    (estimateCode : ℚ)
    (hnonneg : ∀ j, 0 ≤ value j) (hleOne : ∀ j, value j ≤ 1)
    (hhonest :
      completeness ≤
        clauseMean pcpp
          (fun j => bitAsReal (pcpp.assignment input auxiliary j)))
    (hbudget :
      totalClauseErrorMean pcpp value
          (fun j => bitAsReal (pcpp.assignment input auxiliary j)) ≤
        6 * (parameters.zeta : ℝ))
    (haccurate :
      |(estimateCode : ℝ) - clauseMean pcpp value| ≤
        (parameters.estimationError : ℝ)) :
    ComponentwiseVerifierTrace pcpp input parameters where
  proofValue := value
  proofValueNonneg := hnonneg
  proofValueLeOne := hleOne
  validityChecked :=
    (totalClausePenaltyMean_le_totalClauseErrorMean pcpp input auxiliary value
      hnonneg hleOne).trans hbudget
  estimateCode := estimateCode
  estimateAccurate := haccurate
  thresholdReached := by
    exact_mod_cast
      threshold_le_estimate_of_clauseErrorBudget pcpp input auxiliary
        parameters value (estimateCode : ℝ) hnonneg hleOne hhonest hbudget
        haccurate

/-! ## §6 The soundness direction closes unconditionally

The published reserves put the whole NO-instance ledger strictly below the
threshold, so the accepting comparison is contradictory exactly where the
imported PCPP soundness applies. -/

/-- Explicit soundness-side ladder with the published constants. -/
theorem noInstanceCeiling_lt_threshold
    {completeness soundness : ℝ}
    (parameters : ExecutableSoundnessParameters completeness soundness) :
    soundness + (parameters.outerError : ℝ) +
          6 * Real.sqrt (12 * (parameters.zeta : ℝ)) +
          (parameters.estimationError : ℝ) <
        (parameters.threshold : ℝ) := by
  have hmidpoint := parameters.thresholdAboveMidpoint
  have hreserve := parameters.soundReserve
  linarith

/-- The verifier's estimate on a NO-instance branch is strictly below the
published threshold, so the exact rational comparison cannot fire. -/
theorem estimate_lt_threshold_of_ledgerData
    {completeness soundness : ℝ}
    (parameters : ExecutableSoundnessParameters completeness soundness)
    (roundedMean realMean estimate : ℝ)
    (hrounded : roundedMean ≤ soundness + (parameters.outerError : ℝ))
    (hvalidity :
      |realMean - roundedMean| ≤
        6 * Real.sqrt (12 * (parameters.zeta : ℝ)))
    (hestimate :
      |estimate - realMean| ≤ (parameters.estimationError : ℝ)) :
    estimate < (parameters.threshold : ℝ) := by
  have hrealUpper := (abs_le.mp hvalidity).2
  have hestimateUpper := (abs_le.mp hestimate).2
  have hladder := noInstanceCeiling_lt_threshold parameters
  linarith

/-- **Soundness seam.**  The accepting branch evidence of
`ComponentwiseBranchExtraction` is uninhabited at the published parameters, so
the contradiction really fires. -/
theorem acceptingBranchEvidence_isEmpty
    {completeness soundness : ℝ}
    (parameters : ExecutableSoundnessParameters completeness soundness) :
    IsEmpty (AcceptingBranchEvidence parameters) :=
  ⟨fun evidence =>
    (executableNoInstanceBranchLedger_empty parameters).false
      (executableNoInstanceBranchLedger_of_evidence evidence)⟩

theorem not_thresholdReached_of_noInstanceTrace {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (input : BitInput n) {completeness soundness : ℝ}
    (parameters : ExecutableSoundnessParameters completeness soundness)
    (roundedSoundness :
      ∀ auxiliary : BitInput pcpp.auxiliaryBits,
        pcpp.satisfiedFraction input auxiliary ≤
          soundness + (parameters.outerError : ℝ))
    (trace : ComponentwiseVerifierTrace pcpp input parameters) : False :=
  (executableNoInstanceBranchLedger_empty parameters).false
    (executableNoInstanceBranchLedger_of_trace roundedSoundness trace)

/-! ## §7 The published approximation parameter does not fit

The Case-2 seed is the honest *occurrence* table, so a uniform `ℓ¹` ball of
radius `recoveryDelta` around it is a clause-marginal ball of radius
`2 * recoveryDelta` once both clause sides are charged.  With
`recoveryDelta = 1 / 4` that budget is `1 / 2`, and no parameter package for a
source with `0 ≤ soundness` and `completeness ≤ 1` can absorb it. -/

/-- Clause-marginal `ℓ¹` budget produced by the published Case-2 approximation
parameter `recoveryDelta`. -/
noncomputable def recoveryClauseErrorBudget : ℝ := 2 * recoveryDelta

theorem recoveryClauseErrorBudget_eq :
    recoveryClauseErrorBudget = 1 / 2 := by
  rw [recoveryClauseErrorBudget, recoveryDelta_eq_quarter]
  norm_num

/-- The soundness reserve alone pins the published validity constant below
`1 / 1728` whenever the source gap fits in the unit interval. -/
theorem zeta_lt_of_unitGap
    {completeness soundness : ℝ}
    (parameters : ExecutableSoundnessParameters completeness soundness)
    (hsoundness : 0 ≤ soundness) (hcompleteness : completeness ≤ 1) :
    (parameters.zeta : ℝ) < 1 / 1728 := by
  have houter : (0 : ℝ) < (parameters.outerError : ℝ) := by
    exact_mod_cast parameters.outerErrorPositive
  have hestimation : (0 : ℝ) < (parameters.estimationError : ℝ) := by
    exact_mod_cast parameters.estimationErrorPositive
  have hreserve := parameters.soundReserve
  have hsqrt : Real.sqrt (12 * (parameters.zeta : ℝ)) < 1 / 12 := by
    linarith
  have hsquare : 12 * (parameters.zeta : ℝ) < (1 / 12 : ℝ) ^ 2 :=
    (Real.sqrt_lt' (by norm_num)).1 hsqrt
  norm_num at hsquare
  linarith

/-- **Negative result, validity ladder.**  The verifier's componentwise
validity test cannot allow the published approximation budget: the charge a
`recoveryDelta`-close guess may carry exceeds `6 * zeta` at every admissible
parameter package. -/
theorem recoveryClauseErrorBudget_not_le_validityCharge
    {completeness soundness : ℝ}
    (parameters : ExecutableSoundnessParameters completeness soundness)
    (hsoundness : 0 ≤ soundness) (hcompleteness : completeness ≤ 1) :
    ¬recoveryClauseErrorBudget ≤ 6 * (parameters.zeta : ℝ) := by
  intro hbudget
  have hzeta := zeta_lt_of_unitGap parameters hsoundness hcompleteness
  rw [recoveryClauseErrorBudget_eq] at hbudget
  linarith

/-- The same failure without the factor two, so it does not depend on how the
two clause sides are normalized: even a one-sided reading of the published
approximation parameter overshoots the validity constant. -/
theorem recoveryDelta_not_le_validityCharge
    {completeness soundness : ℝ}
    (parameters : ExecutableSoundnessParameters completeness soundness)
    (hsoundness : 0 ≤ soundness) (hcompleteness : completeness ≤ 1) :
    ¬recoveryDelta ≤ 6 * (parameters.zeta : ℝ) := by
  intro hbudget
  have hzeta := zeta_lt_of_unitGap parameters hsoundness hcompleteness
  rw [recoveryDelta_eq_quarter] at hbudget
  linarith

/-- The failing inequality with the published constants substituted.  The
validity ladder needs `recoveryClauseErrorBudget ≤ 6 * zeta`; the soundness
reserve forces `6 * zeta < 1 / 288`, so the two sides are separated by at least
`143 / 288`. -/
theorem recoverySeam_numericGap
    {completeness soundness : ℝ}
    (parameters : ExecutableSoundnessParameters completeness soundness)
    (hsoundness : 0 ≤ soundness) (hcompleteness : completeness ≤ 1) :
    6 * (parameters.zeta : ℝ) + 143 / 288 < recoveryClauseErrorBudget := by
  have hzeta := zeta_lt_of_unitGap parameters hsoundness hcompleteness
  rw [recoveryClauseErrorBudget_eq]
  linarith

theorem completeness_lt_threshold_add_recoveryClauseErrorBudget
    {completeness soundness : ℝ}
    (parameters : ExecutableSoundnessParameters completeness soundness)
    (hsoundness : 0 ≤ soundness) (hcompleteness : completeness ≤ 1) :
    completeness <
      (parameters.threshold : ℝ) + (parameters.estimationError : ℝ) +
        recoveryClauseErrorBudget := by
  have hestimation : (0 : ℝ) < (parameters.estimationError : ℝ) := by
    exact_mod_cast parameters.estimationErrorPositive
  have hmidpoint := parameters.thresholdAboveMidpoint
  rw [recoveryClauseErrorBudget_eq]
  linarith

/-- The same two failures at the one parameter package the pipeline selects. -/
theorem executableParametersOfSource_validityCharge_fails
    (source : UniformPointwisePCPPSource) :
    ¬recoveryClauseErrorBudget ≤
      6 * ((executableParametersOfSource source).zeta : ℝ) :=
  recoveryClauseErrorBudget_not_le_validityCharge
    (executableParametersOfSource source)
    (uniformPointwisePCPPSource_soundness_nonnegative source)
    (uniformPointwisePCPPSource_completeness_le_one source)

theorem executableParametersOfSource_completenessReserve_fails
    (source : UniformPointwisePCPPSource) :
    source.completeness <
      ((executableParametersOfSource source).threshold : ℝ) +
        ((executableParametersOfSource source).estimationError : ℝ) +
        recoveryClauseErrorBudget :=
  completeness_lt_threshold_add_recoveryClauseErrorBudget
    (executableParametersOfSource source)
    (uniformPointwisePCPPSource_soundness_nonnegative source)
    (uniformPointwisePCPPSource_completeness_le_one source)

/-! ### Tightness of the budget

The two failures above are not artefacts of a lossy estimate.  The single
clause below realizes the whole `§3` bound: a guess at clause-marginal `ℓ¹`
distance exactly `recoveryClauseErrorBudget` from a perfectly satisfying
Boolean table loses exactly that much clause mean, while its booleanity
penalty already exceeds the published validity constant. -/

/-- A one-clause, two-coordinate PCPP used only to realize the seam bound. -/
private noncomputable def seamWitnessPCPP :
    PointwisePCPP (constantBooleanCircuit true) where
  systematicBits := 0
  auxiliaryBits := 2
  clauseBits := 0
  systematicSupport := fun i => i.elim0
  systematicSupportBound := fun i => i.elim0
  clauses := fun _ =>
    ⟨.positive ⟨0, by omega⟩, .positive ⟨1, by omega⟩⟩
  honestAuxiliary := fun _ i => decide (i.val = 0)
  constructionSteps := 0
  honestSteps := fun _ => 0

/-- The honest Boolean table of `seamWitnessPCPP`: its single clause is
satisfied through the left literal only. -/
private noncomputable def seamWitnessHonest :
    Fin (seamWitnessPCPP.systematicBits +
      seamWitnessPCPP.auxiliaryBits) → ℝ :=
  fun j => if j.val = 0 then 1 else 0

/-- A guess inside the published approximation ball that halves the only
satisfying literal. -/
private noncomputable def seamWitnessGuess :
    Fin (seamWitnessPCPP.systematicBits +
      seamWitnessPCPP.auxiliaryBits) → ℝ :=
  fun j => if j.val = 0 then 1 / 2 else 0

private theorem seamRegression_totalClauseErrorMean :
    totalClauseErrorMean seamWitnessPCPP seamWitnessGuess
        seamWitnessHonest =
      recoveryClauseErrorBudget := by
  rw [recoveryClauseErrorBudget, recoveryDelta_eq_quarter]
  simp [totalClauseErrorMean, clauseErrorMean, seamWitnessPCPP,
    seamWitnessGuess, seamWitnessHonest, literalIndex]
  norm_num

private theorem seamRegression_clauseMean_honest :
    clauseMean seamWitnessPCPP seamWitnessHonest = 1 := by
  simp [clauseMean, clauseRealValue, clauseValue, literalValue,
    literalNegated, literalIndex, seamWitnessPCPP, seamWitnessHonest]

private theorem seamRegression_clauseMean_guess :
    clauseMean seamWitnessPCPP seamWitnessGuess = 1 / 2 := by
  simp [clauseMean, clauseRealValue, clauseValue, literalValue,
    literalNegated, literalIndex, seamWitnessPCPP, seamWitnessGuess]

/-- The `§3` movement bound is attained at the published budget: an admissible
Case-2 approximation can cost the estimated clause mean the entire
`recoveryClauseErrorBudget`. -/
theorem seamRegression_clauseMean_drop_eq_budget :
    clauseMean seamWitnessPCPP seamWitnessHonest -
        clauseMean seamWitnessPCPP seamWitnessGuess =
      totalClauseErrorMean seamWitnessPCPP seamWitnessGuess
        seamWitnessHonest := by
  rw [seamRegression_clauseMean_honest, seamRegression_clauseMean_guess,
    seamRegression_totalClauseErrorMean, recoveryClauseErrorBudget_eq]
  norm_num

/-- A single half-valued coordinate, well inside the published approximation
ball, already breaks the componentwise validity test. -/
theorem booleanityPenalty_half_not_le_validityCharge
    {completeness soundness : ℝ}
    (parameters : ExecutableSoundnessParameters completeness soundness)
    (hsoundness : 0 ≤ soundness) (hcompleteness : completeness ≤ 1) :
    ¬booleanityPenalty (1 / 2 : ℝ) ≤ 6 * (parameters.zeta : ℝ) := by
  intro hcharge
  have hzeta := zeta_lt_of_unitGap parameters hsoundness hcompleteness
  rw [show booleanityPenalty (1 / 2 : ℝ) = 1 / 16 by
    norm_num [booleanityPenalty]] at hcharge
  linarith

/-! ## §8 The smallest repair

Nothing in the ladder has to move except the approximation parameter.  The
completeness direction closes verbatim once `delta ≤ 3 * zeta`, and such a
`delta` is always available, strictly positive and below `1 / 2`, so the
imported XOR contract still applies.  The published `recoveryDelta = 1 / 4`
misses that condition by a factor of at least `576`. -/

/-- **Repaired completeness seam.**  With `delta ≤ 3 * zeta` the published
threshold, estimation error and validity constant close the completeness
direction for every `delta`-close guess. -/
theorem threshold_le_estimate_of_approximationDelta {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (input : BitInput n) (auxiliary : BitInput pcpp.auxiliaryBits)
    {completeness soundness : ℝ}
    (parameters : ExecutableSoundnessParameters completeness soundness)
    (value : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ)
    (delta estimate : ℝ)
    (hnonneg : ∀ j, 0 ≤ value j) (hleOne : ∀ j, value j ≤ 1)
    (hhonest :
      completeness ≤
        clauseMean pcpp
          (fun j => bitAsReal (pcpp.assignment input auxiliary j)))
    (hdelta : delta ≤ 3 * (parameters.zeta : ℝ))
    (hclose :
      totalClauseErrorMean pcpp value
          (fun j => bitAsReal (pcpp.assignment input auxiliary j)) ≤
        2 * delta)
    (haccurate :
      |estimate - clauseMean pcpp value| ≤
        (parameters.estimationError : ℝ)) :
    (parameters.threshold : ℝ) ≤ estimate :=
  threshold_le_estimate_of_clauseErrorBudget pcpp input auxiliary parameters
    value estimate hnonneg hleOne hhonest
    (hclose.trans (by linarith)) haccurate

/-- The repaired seam in the seed metric: an approximation parameter `delta`
measured on clause occurrences closes the completeness direction exactly when
`delta ≤ 3 * zeta`. -/
theorem threshold_le_estimate_of_occurrenceDelta {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (input : BitInput n) (auxiliary : BitInput pcpp.auxiliaryBits)
    {completeness soundness : ℝ}
    (parameters : ExecutableSoundnessParameters completeness soundness)
    (value : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ)
    (delta estimate : ℝ)
    (hnonneg : ∀ j, 0 ≤ value j) (hleOne : ∀ j, value j ≤ 1)
    (hhonest :
      completeness ≤
        clauseMean pcpp
          (fun j => bitAsReal (pcpp.assignment input auxiliary j)))
    (hdelta : delta ≤ 3 * (parameters.zeta : ℝ))
    (hclose :
      clauseOccurrenceErrorMean pcpp value
          (fun j => bitAsReal (pcpp.assignment input auxiliary j)) ≤
        delta)
    (haccurate :
      |estimate - clauseMean pcpp value| ≤
        (parameters.estimationError : ℝ)) :
    (parameters.threshold : ℝ) ≤ estimate := by
  refine threshold_le_estimate_of_approximationDelta pcpp input auxiliary
    parameters value delta estimate hnonneg hleOne hhonest hdelta ?_ haccurate
  rw [totalClauseErrorMean_eq_two_mul_occurrence]
  linarith

/-- The published approximation parameter misses the repaired condition. -/
theorem recoveryDelta_not_le_threeZeta
    {completeness soundness : ℝ}
    (parameters : ExecutableSoundnessParameters completeness soundness)
    (hsoundness : 0 ≤ soundness) (hcompleteness : completeness ≤ 1) :
    ¬recoveryDelta ≤ 3 * (parameters.zeta : ℝ) := by
  intro hdelta
  have hzeta := zeta_lt_of_unitGap parameters hsoundness hcompleteness
  rw [recoveryDelta_eq_quarter] at hdelta
  linarith

/-- The repaired condition is always satisfiable inside the range the imported
XOR contract requires, so only the approximation parameter and the schedule
constants that depend on it have to move. -/
theorem exists_repairedApproximationDelta
    {completeness soundness : ℝ}
    (parameters : ExecutableSoundnessParameters completeness soundness)
    (hsoundness : 0 ≤ soundness) (hcompleteness : completeness ≤ 1) :
    ∃ delta : ℚ, 0 < delta ∧ (delta : ℝ) < 1 / 2 ∧
      (delta : ℝ) ≤ 3 * (parameters.zeta : ℝ) := by
  have hzeta := zeta_lt_of_unitGap parameters hsoundness hcompleteness
  have hpositive : (0 : ℝ) < (parameters.zeta : ℝ) := by
    exact_mod_cast parameters.zetaPositive
  exact ⟨parameters.zeta, parameters.zetaPositive, by linarith, by linarith⟩

/-! ## §9 The repaired approximation radius, and the schedule it selects

`§8` shows the repair is admissible; this section names it, discharges every
side condition the imported XOR contract asks of an approximation radius, and
closes the completeness direction at the one parameter package the pipeline
selects.  `RecoveryScheduleEnvelope` supplies the copy schedule at an arbitrary
radius (`recoveryBlockOf`, `inverseCopiesOf`, `fixedCopiesOf`), so the repaired
radius inherits the published factor-four reserve verbatim; the only cost is
that the block length grows like `1 / zeta`.

Nothing in `ExecutableSoundnessParameters` moves.  The fixed radius
`recoveryDelta = 1 / 4` survives only as the object refuted in `§7`: the XOR
ledger of `Proof/Amplification/CaseTwoRecoveryAssembly.lean` has been migrated onto
`RecoveryScheduleEnvelope.repairedDelta`, which is definitionally the radius
below at the scheduled pointwise-PCPP source. -/

/-- **The repaired Case-2 approximation radius.**  It is the validity constant
of the selected package, which is the largest choice that stays inside the
condition `delta ≤ 3 * zeta` of `§8` without any further arithmetic. -/
def repairedRecoveryDelta {completeness soundness : ℝ}
    (parameters : ExecutableSoundnessParameters completeness soundness) : ℚ :=
  parameters.zeta

theorem repairedRecoveryDelta_positive
    {completeness soundness : ℝ}
    (parameters : ExecutableSoundnessParameters completeness soundness) :
    0 < repairedRecoveryDelta parameters :=
  parameters.zetaPositive

theorem repairedRecoveryDelta_nonnegative
    {completeness soundness : ℝ}
    (parameters : ExecutableSoundnessParameters completeness soundness) :
    (0 : ℝ) ≤ (repairedRecoveryDelta parameters : ℝ) := by
  exact_mod_cast le_of_lt (repairedRecoveryDelta_positive parameters)

/-- The repaired radius satisfies the repair condition of `§8` by definition,
so `threshold_le_estimate_of_occurrenceDelta` applies to it. -/
theorem repairedRecoveryDelta_le_threeZeta
    {completeness soundness : ℝ}
    (parameters : ExecutableSoundnessParameters completeness soundness) :
    (repairedRecoveryDelta parameters : ℝ) ≤ 3 * (parameters.zeta : ℝ) := by
  have hpositive : (0 : ℝ) < (parameters.zeta : ℝ) := by
    exact_mod_cast parameters.zetaPositive
  simp only [repairedRecoveryDelta]
  linarith

/-- The repaired radius is strictly below one half, so the imported XOR
contract still applies to it unchanged. -/
theorem repairedRecoveryDelta_belowHalf
    {completeness soundness : ℝ}
    (parameters : ExecutableSoundnessParameters completeness soundness)
    (hsoundness : 0 ≤ soundness) (hcompleteness : completeness ≤ 1) :
    (repairedRecoveryDelta parameters : ℝ) < 1 / 2 := by
  have hzeta := zeta_lt_of_unitGap parameters hsoundness hcompleteness
  simp only [repairedRecoveryDelta]
  linarith

theorem repairedRecoveryDelta_le_half
    {completeness soundness : ℝ}
    (parameters : ExecutableSoundnessParameters completeness soundness)
    (hsoundness : 0 ≤ soundness) (hcompleteness : completeness ≤ 1) :
    (repairedRecoveryDelta parameters : ℝ) ≤ 1 / 2 :=
  le_of_lt (repairedRecoveryDelta_belowHalf parameters hsoundness hcompleteness)

/-- One repaired block halves the geometric factor.  The block length is
`⌈1 / zeta⌉`, which is the whole quantitative price of the repair. -/
theorem repairedRecoveryDelta_block_halves
    {completeness soundness : ℝ}
    (parameters : ExecutableSoundnessParameters completeness soundness)
    (hsoundness : 0 ≤ soundness) (hcompleteness : completeness ≤ 1) :
    (1 - (repairedRecoveryDelta parameters : ℝ)) ^
        recoveryBlockOf (repairedRecoveryDelta parameters) ≤ (1 / 2 : ℝ) :=
  recoveryBlockOf_halves (repairedRecoveryDelta_positive parameters)
    (repairedRecoveryDelta_le_half parameters hsoundness hcompleteness)

/-- The logarithmic copy schedule keeps the published factor-four reserve at
the repaired radius. -/
theorem repairedRecoveryDelta_xorEpsilon_inverseCopiesOf_le
    {completeness soundness : ℝ}
    (parameters : ExecutableSoundnessParameters completeness soundness)
    (hsoundness : 0 ≤ soundness) (hcompleteness : completeness ≤ 1)
    {clockDepth : ℕ}
    {refuterSource : ExecutableRefuterSource (PolynomialClock.pairClock
      clockDepth)}
    (outer : OuterPCPRecovery.HierarchyOuterPCP refuterSource)
    (rate sourceIndex : ℕ) :
    xorEpsilon (repairedRecoveryDelta parameters : ℝ)
        (inverseCopiesOf (repairedRecoveryDelta parameters) outer rate
          sourceIndex) ≤
      1 / (2 : ℝ) ^
        (rate * logScale (scheduledWidth outer sourceIndex)) / 4 :=
  xorEpsilon_inverseCopiesOf_le (repairedRecoveryDelta_positive parameters)
    (repairedRecoveryDelta_le_half parameters hsoundness hcompleteness) outer
    rate sourceIndex

/-- The constant copy schedule keeps the published factor-four reserve at the
repaired radius. -/
theorem repairedRecoveryDelta_xorEpsilon_fixedCopiesOf_le
    {completeness soundness : ℝ}
    (parameters : ExecutableSoundnessParameters completeness soundness)
    (hsoundness : 0 ≤ soundness) (hcompleteness : completeness ≤ 1)
    (rate : ℕ) :
    xorEpsilon (repairedRecoveryDelta parameters : ℝ)
        (fixedCopiesOf (repairedRecoveryDelta parameters) rate) ≤
      1 / (2 : ℝ) ^ rate / 4 :=
  xorEpsilon_fixedCopiesOf_le (repairedRecoveryDelta_positive parameters)
    (repairedRecoveryDelta_le_half parameters hsoundness hcompleteness) rate

/-- The completeness direction at the repaired radius, for an arbitrary
package.  This is `threshold_le_estimate_of_occurrenceDelta` with its numeric
hypothesis discharged. -/
theorem threshold_le_estimate_of_repairedDelta {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (input : BitInput n) (auxiliary : BitInput pcpp.auxiliaryBits)
    {completeness soundness : ℝ}
    (parameters : ExecutableSoundnessParameters completeness soundness)
    (value : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ)
    (estimate : ℝ)
    (hnonneg : ∀ j, 0 ≤ value j) (hleOne : ∀ j, value j ≤ 1)
    (hhonest :
      completeness ≤
        clauseMean pcpp
          (fun j => bitAsReal (pcpp.assignment input auxiliary j)))
    (hclose :
      clauseOccurrenceErrorMean pcpp value
          (fun j => bitAsReal (pcpp.assignment input auxiliary j)) ≤
        (repairedRecoveryDelta parameters : ℝ))
    (haccurate :
      |estimate - clauseMean pcpp value| ≤
        (parameters.estimationError : ℝ)) :
    (parameters.threshold : ℝ) ≤ estimate :=
  threshold_le_estimate_of_occurrenceDelta pcpp input auxiliary parameters
    value (repairedRecoveryDelta parameters : ℝ) estimate hnonneg hleOne
    hhonest (repairedRecoveryDelta_le_threeZeta parameters) hclose haccurate

/-- **The seam closes at the repaired radius.**  At the one parameter package
the pipeline selects, `executableParametersOfSource source`, every guessed
proof whose clause-occurrence `ℓ¹` error against the honest table is inside the
repaired approximation radius forces the verifier's exact rational comparison.
This is the completeness direction that `§7` shows fails at the published
radius `recoveryDelta = 1 / 4`. -/
theorem repairedDelta_completeness_seam {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (input : BitInput n) (auxiliary : BitInput pcpp.auxiliaryBits)
    (source : UniformPointwisePCPPSource)
    (value : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ)
    (estimate : ℝ)
    (hnonneg : ∀ j, 0 ≤ value j) (hleOne : ∀ j, value j ≤ 1)
    (hhonest :
      source.completeness ≤
        clauseMean pcpp
          (fun j => bitAsReal (pcpp.assignment input auxiliary j)))
    (hclose :
      clauseOccurrenceErrorMean pcpp value
          (fun j => bitAsReal (pcpp.assignment input auxiliary j)) ≤
        (repairedRecoveryDelta (executableParametersOfSource source) : ℝ))
    (haccurate :
      |estimate - clauseMean pcpp value| ≤
        ((executableParametersOfSource source).estimationError : ℝ)) :
    ((executableParametersOfSource source).threshold : ℝ) ≤ estimate :=
  threshold_le_estimate_of_repairedDelta pcpp input auxiliary
    (executableParametersOfSource source) value estimate hnonneg hleOne
    hhonest hclose haccurate

noncomputable def repairedDelta_honestApproximationTrace {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (input : BitInput n) (auxiliary : BitInput pcpp.auxiliaryBits)
    (source : UniformPointwisePCPPSource)
    (value : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ)
    (estimateCode : ℚ)
    (hnonneg : ∀ j, 0 ≤ value j) (hleOne : ∀ j, value j ≤ 1)
    (hhonest :
      source.completeness ≤
        clauseMean pcpp
          (fun j => bitAsReal (pcpp.assignment input auxiliary j)))
    (hclose :
      clauseOccurrenceErrorMean pcpp value
          (fun j => bitAsReal (pcpp.assignment input auxiliary j)) ≤
        (repairedRecoveryDelta (executableParametersOfSource source) : ℝ))
    (haccurate :
      |(estimateCode : ℝ) - clauseMean pcpp value| ≤
        ((executableParametersOfSource source).estimationError : ℝ)) :
    ComponentwiseVerifierTrace pcpp input
      (executableParametersOfSource source) :=
  honestApproximationTrace pcpp input auxiliary
    (executableParametersOfSource source) value estimateCode hnonneg hleOne
    hhonest
    (by
      have hzeta :
          (0 : ℝ) < ((executableParametersOfSource source).zeta : ℝ) := by
        exact_mod_cast (executableParametersOfSource source).zetaPositive
      have hoccurrence :
          clauseOccurrenceErrorMean pcpp value
              (fun j => bitAsReal (pcpp.assignment input auxiliary j)) ≤
            ((executableParametersOfSource source).zeta : ℝ) := hclose
      rw [totalClauseErrorMean_eq_two_mul_occurrence]
      linarith)
    haccurate

/-- The published fixed radius and the repaired radius cannot coincide: the
former is `1 / 4`, the latter is below `1 / 1728`.  Recorded so the migration
cannot be mistaken for a no-op. -/
theorem repairedRecoveryDelta_ne_recoveryDelta
    (source : UniformPointwisePCPPSource) :
    (repairedRecoveryDelta (executableParametersOfSource source) : ℝ) ≠
      recoveryDelta := by
  have hzeta :=
    zeta_lt_of_unitGap (executableParametersOfSource source)
      (uniformPointwisePCPPSource_soundness_nonnegative source)
      (uniformPointwisePCPPSource_completeness_le_one source)
  have hvalue : recoveryDelta = (1 / 4 : ℝ) := recoveryDelta_eq_quarter
  intro hequal
  rw [hvalue] at hequal
  simp only [repairedRecoveryDelta] at hequal
  rw [hequal] at hzeta
  norm_num at hzeta

end NearCubicWires.VerifierThresholdSeam
