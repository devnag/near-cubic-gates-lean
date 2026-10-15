import Proof.MachineModel.ExecutableRecoveryMachine
import Proof.MachineModel.SharedNormalizedEstimatorProgram

namespace NearCubicWires.ComponentwiseEstimatorAccuracy

open Finset
open scoped BigOperators
open NearCubicWires
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoRecoveryAssembly
open NearCubicWires.CaseTwoWitnessCompleteness
open NearCubicWires.ComponentwiseBranchExtraction
open NearCubicWires.ComponentwiseValidity
open NearCubicWires.ComponentwiseVerifierParameters
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.ExecutableRecoveryMachine
open NearCubicWires.RecoveryPipeline
open NearCubicWires.SharedNormalizedEstimatorProgram
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPipeline

/-! ## §1 Exact rational clause arithmetic

The verifier stores the guessed proof as exact rationals.  These definitions
mirror `rationalValidityPenalty` and `rationalTotalClausePenaltyCharge`: they
are the only permitted bridge between the register arithmetic and the
real-valued clause ledger, so no second arithmetization is introduced. -/

/-- Exact rational form of `literalValue`. -/
def rationalLiteralValue (negative : Bool) (value : ℚ) : ℚ :=
  if negative then 1 - value else value

theorem literalValue_ratCast (negative : Bool) (value : ℚ) :
    literalValue negative (value : ℝ) =
      ((rationalLiteralValue negative value : ℚ) : ℝ) := by
  cases negative <;> simp [literalValue, rationalLiteralValue]

/-- Exact rational form of the arithmetized two-literal clause polynomial. -/
def rationalClauseValue (leftNegative rightNegative : Bool)
    (left right : ℚ) : ℚ :=
  rationalLiteralValue leftNegative left +
      rationalLiteralValue rightNegative right -
    rationalLiteralValue leftNegative left *
      rationalLiteralValue rightNegative right

theorem clauseValue_ratCast (leftNegative rightNegative : Bool)
    (left right : ℚ) :
    clauseValue leftNegative rightNegative (left : ℝ) (right : ℝ) =
      ((rationalClauseValue leftNegative rightNegative left right : ℚ) : ℝ) := by
  have hleft : literalValue leftNegative (left : ℝ) =
      ((rationalLiteralValue leftNegative left : ℚ) : ℝ) :=
    literalValue_ratCast leftNegative left
  have hright : literalValue rightNegative (right : ℝ) =
      ((rationalLiteralValue rightNegative right : ℚ) : ℝ) :=
    literalValue_ratCast rightNegative right
  change
      literalValue leftNegative (left : ℝ) +
            literalValue rightNegative (right : ℝ) -
          literalValue leftNegative (left : ℝ) *
            literalValue rightNegative (right : ℝ) = _
  rw [hleft, hright, rationalClauseValue]
  push_cast
  ring

/-- Exact rational form of `clauseRealValue`. -/
def rationalClauseRealValue {arity : ℕ} (clause : TwoLiteralClause arity)
    (value : Fin arity → ℚ) : ℚ :=
  rationalClauseValue (literalNegated clause.left)
    (literalNegated clause.right) (value (literalIndex clause.left))
    (value (literalIndex clause.right))

theorem clauseRealValue_ratCast {arity : ℕ}
    (clause : TwoLiteralClause arity) (value : Fin arity → ℚ) :
    clauseRealValue clause (fun j => (value j : ℝ)) =
      ((rationalClauseRealValue clause value : ℚ) : ℝ) :=
  clauseValue_ratCast _ _ _ _

/-- Exact rational clause total the register program accumulates before its
single division. -/
noncomputable def rationalClauseSum {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit)
    (value : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℚ) : ℚ :=
  ∑ i ∈ (univ : Finset (Fin (2 ^ pcpp.clauseBits))),
    rationalClauseRealValue (pcpp.clauses i) value

/-- **The exact rational clause mean.**  This is the quantity the semantic
stage evaluates; it is the estimated quantity itself, not a surrogate. -/
noncomputable def rationalClauseMean {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit)
    (value : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℚ) : ℚ :=
  rationalClauseSum pcpp value / (2 ^ pcpp.clauseBits : ℚ)

/-- **The codec bridge.**  The real clause mean of a rational proof is the cast
of its exact rational clause mean. -/
theorem clauseMean_eq_ratCast {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit)
    (value : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℚ) :
    clauseMean pcpp (fun j => (value j : ℝ)) =
      ((rationalClauseMean pcpp value : ℚ) : ℝ) := by
  rw [clauseMean, Finset.expect_eq_sum_div_card, rationalClauseMean,
    rationalClauseSum]
  push_cast
  congr 1
  · exact Finset.sum_congr rfl fun i _ => clauseRealValue_ratCast _ _
  · simp

/-! ## §2 The accuracy theorem -/

/-- **The estimator accuracy bound.**  Any executed estimate code within the
published budget of the exact rational clause mean satisfies the trace's
`estimateAccurate` field.  The real-valued content is entirely the codec
identification of §1. -/
theorem estimateAccurate_of_rationalTolerance {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (value : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℚ)
    (estimateCode : ℚ) {completeness soundness : ℝ}
    (parameters : ExecutableSoundnessParameters completeness soundness)
    (htolerance :
      |estimateCode - rationalClauseMean pcpp value| ≤
        parameters.estimationError) :
    |(estimateCode : ℝ) - clauseMean pcpp (fun j => (value j : ℝ))| ≤
      (parameters.estimationError : ℝ) := by
  rw [clauseMean_eq_ratCast pcpp value]
  exact_mod_cast htolerance

/-- **The exact-evaluator instance.**  A semantic stage that evaluates the
clause mean exactly spends none of the estimator budget. -/
theorem estimateAccurate_of_exactRationalMean {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (value : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℚ)
    (estimateCode : ℚ) {completeness soundness : ℝ}
    (parameters : ExecutableSoundnessParameters completeness soundness)
    (hstage : estimateCode = rationalClauseMean pcpp value) :
    |(estimateCode : ℝ) - clauseMean pcpp (fun j => (value j : ℝ))| ≤
      (parameters.estimationError : ℝ) := by
  refine estimateAccurate_of_rationalTolerance pcpp value estimateCode
    parameters ?_
  rw [hstage, sub_self, abs_zero]
  exact le_of_lt parameters.estimationErrorPositive

/-! ## §3 The executed ratio code at the PCPP clause range

The canonical nonnegative rational codec of the supplier boundary —
`encodeNaturalRatio`, decoded by `decodeSupplierRational` — is reused verbatim
here, at the PCPP clause index space instead of a circuit sample space.  On a
Boolean proof the clause mean is exactly the acceptance ratio that a Boolean
range aggregation over `Fin (2 ^ pcpp.clauseBits)` produces, so the decoded
ratio code *is* the estimated quantity. -/

/-- Exact rational form of `bitAsReal`. -/
def rationalBitValue (bit : Bool) : ℚ := if bit then 1 else 0

theorem bitAsReal_eq_ratCast (bit : Bool) :
    bitAsReal bit = ((rationalBitValue bit : ℚ) : ℝ) := by
  cases bit <;> simp [bitAsReal, rationalBitValue]

theorem rationalClauseRealValue_bitValue {arity : ℕ}
    (clause : TwoLiteralClause arity) (assignment : BitInput arity) :
    rationalClauseRealValue clause
        (fun j => rationalBitValue (assignment j)) =
      rationalBitValue (clause.eval assignment) := by
  have hfun :
      (fun j => ((rationalBitValue (assignment j) : ℚ) : ℝ)) =
        fun j => bitAsReal (assignment j) := by
    funext j
    rw [← bitAsReal_eq_ratCast]
  have hcast :
      ((rationalClauseRealValue clause
            (fun j => rationalBitValue (assignment j)) : ℚ) : ℝ) =
        ((rationalBitValue (clause.eval assignment) : ℚ) : ℝ) := by
    rw [← clauseRealValue_ratCast, hfun, clauseRealValue_bitAsReal,
      bitAsReal_eq_ratCast]
  exact_mod_cast hcast

/-- The numerator a Boolean range aggregation over the clause index space
returns: the number of clauses the Boolean proof satisfies. -/
noncomputable def clauseAcceptanceCount {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit)
    (assignment : BitInput (pcpp.systematicBits + pcpp.auxiliaryBits)) : ℕ :=
  ((univ : Finset (Fin (2 ^ pcpp.clauseBits))).filter fun i =>
    (pcpp.clauses i).eval assignment).card

private theorem rationalClauseSum_bitValue {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (assignment : BitInput (pcpp.systematicBits + pcpp.auxiliaryBits)) :
    rationalClauseSum pcpp (fun j => rationalBitValue (assignment j)) =
      (clauseAcceptanceCount pcpp assignment : ℚ) := by
  rw [rationalClauseSum, clauseAcceptanceCount]
  simp_rw [rationalClauseRealValue_bitValue]
  simp [rationalBitValue, Finset.sum_boole]

theorem rationalClauseMean_bitValue {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit)
    (assignment : BitInput (pcpp.systematicBits + pcpp.auxiliaryBits)) :
    rationalClauseMean pcpp (fun j => rationalBitValue (assignment j)) =
      (clauseAcceptanceCount pcpp assignment : ℚ) /
        ((2 ^ pcpp.clauseBits : ℕ) : ℚ) := by
  rw [rationalClauseMean, rationalClauseSum_bitValue]
  push_cast
  ring

/-- **The executed ratio code carries the clause mean.**  With the numerator
the clause acceptance count and the denominator predecessor
`2 ^ pcpp.clauseBits - 1`, the canonical supplier rational decodes to the
estimated quantity exactly. -/
theorem decodeSupplierRational_clauseRatioCode {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (assignment : BitInput (pcpp.systematicBits + pcpp.auxiliaryBits)) :
    decodeSupplierRational
        (encodeNaturalRatio (clauseAcceptanceCount pcpp assignment)
          (2 ^ pcpp.clauseBits - 1)) =
      rationalClauseMean pcpp (fun j => rationalBitValue (assignment j)) := by
  have hpositive : 1 ≤ 2 ^ pcpp.clauseBits := Nat.one_le_two_pow
  rw [decodeSupplierRational_encodeNaturalRatio, rationalClauseMean_bitValue,
    Nat.sub_add_cancel hpositive]

/-- The same statement through the canonical packer's output word, which is the
shape `canonicalRatioPackerProgram` writes and the shape
`FourfoldRowPreprocessor.outputCode` uses. -/
theorem decodeSupplierRational_clausePackerOutput {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (assignment : BitInput (pcpp.systematicBits + pcpp.auxiliaryBits)) :
    decodeSupplierRational
        (canonicalRatioPackerOutput (clauseAcceptanceCount pcpp assignment)
          (2 ^ pcpp.clauseBits - 1)) =
      rationalClauseMean pcpp (fun j => rationalBitValue (assignment j)) :=
  decodeSupplierRational_clauseRatioCode pcpp assignment

/-- **Accuracy from the executed ratio code.**  Every executed Boolean range
aggregation over the clause index space whose numerator is the clause
acceptance count discharges the trace's estimator field, at error `0`. -/
theorem estimateAccurate_of_clauseRatioCode {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (assignment : BitInput (pcpp.systematicBits + pcpp.auxiliaryBits))
    (numerator denominatorTail : ℕ) {completeness soundness : ℝ}
    (parameters : ExecutableSoundnessParameters completeness soundness)
    (hnumerator : numerator = clauseAcceptanceCount pcpp assignment)
    (hdenominator : denominatorTail = 2 ^ pcpp.clauseBits - 1) :
    |((decodeSupplierRational
          (encodeNaturalRatio numerator denominatorTail) : ℚ) : ℝ) -
        clauseMean pcpp (fun j => bitAsReal (assignment j))| ≤
      (parameters.estimationError : ℝ) := by
  have hfun :
      (fun j => bitAsReal (assignment j)) =
        fun j => ((rationalBitValue (assignment j) : ℚ) : ℝ) := by
    funext j
    rw [← bitAsReal_eq_ratCast]
  rw [hnumerator, hdenominator, hfun,
    decodeSupplierRational_clauseRatioCode pcpp assignment]
  exact estimateAccurate_of_exactRationalMean pcpp
    (fun j => rationalBitValue (assignment j)) _ parameters rfl

/-! ## §4 The numerator is pinned

No other aggregation's acceptance count can be substituted for the clause
acceptance count at this denominator, so the identification of §3 is the only
one available.  This is the compiled form of the routing decision of §0. -/

theorem clauseRatioCode_numerator_unique {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (assignment : BitInput (pcpp.systematicBits + pcpp.auxiliaryBits))
    (numerator : ℕ)
    (hmatch :
      decodeSupplierRational
          (encodeNaturalRatio numerator (2 ^ pcpp.clauseBits - 1)) =
        rationalClauseMean pcpp
          (fun j => rationalBitValue (assignment j))) :
    numerator = clauseAcceptanceCount pcpp assignment := by
  have hpositive : 1 ≤ 2 ^ pcpp.clauseBits := Nat.one_le_two_pow
  rw [decodeSupplierRational_encodeNaturalRatio, rationalClauseMean_bitValue,
    Nat.sub_add_cancel hpositive] at hmatch
  have hdenominator : ((2 ^ pcpp.clauseBits : ℕ) : ℚ) ≠ 0 := by
    positivity
  rw [div_eq_div_iff hdenominator hdenominator] at hmatch
  have hnumerator :
      (numerator : ℚ) = (clauseAcceptanceCount pcpp assignment : ℚ) :=
    mul_right_cancel₀ hdenominator hmatch
  exact_mod_cast hnumerator

/-- **Completeness comparison at the published parameters.**  This is
`threshold_le_estimate_of_publishedRecoveryDelta` with its `haccurate` premise
removed, and with the conclusion in the exact rational shape the verifier's
final comparison has (`ComponentwiseVerifierTrace.thresholdReached`). -/
theorem threshold_le_rationalClauseMean_of_publishedRecoveryDelta
    (contracts : PublishedContracts)
    {n : ℕ} {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (input : BitInput n) (auxiliary : BitInput pcpp.auxiliaryBits)
    (value : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℚ)
    (hnonneg : ∀ j, 0 ≤ value j) (hleOne : ∀ j, value j ≤ 1)
    (hhonest :
      (publishedPointwisePCPP contracts).completeness ≤
        clauseMean pcpp
          (fun j => bitAsReal (pcpp.assignment input auxiliary j)))
    (hclose :
      VerifierThresholdSeam.clauseOccurrenceErrorMean pcpp
          (fun j => (value j : ℝ))
          (fun j => bitAsReal (pcpp.assignment input auxiliary j)) ≤
        publishedRecoveryDelta contracts) :
    (executableParametersOfSource
        (publishedPointwisePCPP contracts)).threshold ≤
      rationalClauseMean pcpp value := by
  have hreal :
      ((executableParametersOfSource
          (publishedPointwisePCPP contracts)).threshold : ℝ) ≤
        ((rationalClauseMean pcpp value : ℚ) : ℝ) :=
    threshold_le_estimate_of_publishedRecoveryDelta contracts pcpp input
      auxiliary (fun j => (value j : ℝ))
      ((rationalClauseMean pcpp value : ℚ) : ℝ)
      (fun j => by exact_mod_cast hnonneg j)
      (fun j => by exact_mod_cast hleOne j) hhonest hclose
      (estimateAccurate_of_exactRationalMean pcpp value
        (rationalClauseMean pcpp value)
        (executableParametersOfSource (publishedPointwisePCPP contracts)) rfl)
  exact_mod_cast hreal

/-- **The accepting trace with the estimator field discharged.**  Every
hypothesis is a decidable rational comparison the register program performs. -/
noncomputable def componentwiseVerifierTraceOfExactEstimate {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (input : BitInput n) {completeness soundness : ℝ}
    (parameters : ExecutableSoundnessParameters completeness soundness)
    (proofValue : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℚ)
    (hnonneg : ∀ j, 0 ≤ proofValue j) (hleOne : ∀ j, proofValue j ≤ 1)
    (hvalidity :
      rationalTotalClausePenaltyCharge pcpp input proofValue ≤
        6 * parameters.zeta)
    (hthreshold :
      parameters.threshold ≤ rationalClauseMean pcpp proofValue) :
    ComponentwiseVerifierTrace pcpp input parameters :=
  ComponentwiseVerifierTrace.ofRationalChecks pcpp input parameters proofValue
    hnonneg hleOne hvalidity (rationalClauseMean pcpp proofValue)
    (estimateAccurate_of_exactRationalMean pcpp proofValue
      (rationalClauseMean pcpp proofValue) parameters rfl)
    hthreshold

/-- **Accepting-branch evidence with the estimator field discharged.**  This is
`acceptingBranchEvidenceOfRationalChecks` with `haccurate` removed. -/
noncomputable def acceptingBranchEvidenceOfExactEstimate
    (source : UniformPointwisePCPPSource) {n : ℕ}
    (circuit : BooleanCircuit n) (hsize : n ≤ circuit.size)
    (input : BitInput n) (hreject : ¬circuit.eval input)
    (supportBound :
      ∀ i,
        ((source.factory.forCircuit circuit).systematicSupport i).card ≤
          n / 2)
    (proofValue :
      Fin
        (((source.factory.forCircuit circuit).toSemantic
            supportBound).systematicBits +
          ((source.factory.forCircuit circuit).toSemantic
            supportBound).auxiliaryBits) → ℚ)
    (hnonneg : ∀ j, 0 ≤ proofValue j) (hleOne : ∀ j, proofValue j ≤ 1)
    (hvalidity :
      rationalTotalClausePenaltyCharge
          ((source.factory.forCircuit circuit).toSemantic supportBound) input
          proofValue ≤
        6 * (executableParametersOfSource source).zeta)
    (hthreshold :
      (executableParametersOfSource source).threshold ≤
        rationalClauseMean
          ((source.factory.forCircuit circuit).toSemantic supportBound)
          proofValue) :
    AcceptingBranchEvidence (executableParametersOfSource source) :=
  acceptingBranchEvidenceOfRationalChecks source circuit hsize input hreject
    supportBound proofValue hnonneg hleOne hvalidity
    (rationalClauseMean
      ((source.factory.forCircuit circuit).toSemantic supportBound) proofValue)
    (estimateAccurate_of_exactRationalMean
      ((source.factory.forCircuit circuit).toSemantic supportBound) proofValue
      (rationalClauseMean
        ((source.factory.forCircuit circuit).toSemantic supportBound)
        proofValue)
      (executableParametersOfSource source) rfl)
    hthreshold

/-- **The soundness-side premise, estimator-free.**  `hsemanticEvidence` of
`eventuallyOneSided_of_semanticStageEvidence` reduces to the statement that an
accepting semantic stage exposes exact rational checks on a decoded proof: two
range checks, the rational validity charge, and the rational threshold
comparison against the exact clause mean.  No estimator constant, no real
comparison and no probabilistic content survives in the premise. -/
theorem eventuallyOneSided_of_exactRationalStage {hierarchy : Language}
    (source : UniformPointwisePCPPSource)
    (machine : ExecutableWeakNondeterministicMachine)
    (semanticOutput : WeakVerifierRequest → ℕ)
    (hexecute : ∀ request : WeakVerifierRequest,
      machine.verifier.execute request = semanticOutput request)
    (onset : ℕ)
    (hstageChecks :
      ∀ n, onset ≤ n → ∀ input : BitInput n,
        hierarchy n input = false →
        ∀ witness : BitInput (machine.witnessBits n),
          semanticOutput (machine.verifierRequest input witness) ≠ 0 →
            ∃ (arity : ℕ) (branchCircuit : BooleanCircuit arity)
              (_ : arity ≤ branchCircuit.size) (branchInput : BitInput arity)
              (_ : ¬branchCircuit.eval branchInput)
              (supportBound :
                ∀ i,
                  ((source.factory.forCircuit
                    branchCircuit).systematicSupport i).card ≤ arity / 2)
              (proofValue :
                Fin
                  (((source.factory.forCircuit branchCircuit).toSemantic
                      supportBound).systematicBits +
                    ((source.factory.forCircuit branchCircuit).toSemantic
                      supportBound).auxiliaryBits) → ℚ),
              (∀ j, 0 ≤ proofValue j) ∧ (∀ j, proofValue j ≤ 1) ∧
                rationalTotalClausePenaltyCharge
                    ((source.factory.forCircuit branchCircuit).toSemantic
                      supportBound) branchInput proofValue ≤
                  6 * (executableParametersOfSource source).zeta ∧
                (executableParametersOfSource source).threshold ≤
                  rationalClauseMean
                    ((source.factory.forCircuit branchCircuit).toSemantic
                      supportBound) proofValue) :
    EventuallyOneSided hierarchy machine := by
  refine eventuallyOneSided_of_semanticStageEvidence source machine
    semanticOutput hexecute onset ?_
  intro n hn input hno witness haccepts
  obtain ⟨arity, branchCircuit, hsize, branchInput, hreject, supportBound,
    proofValue, hnonneg, hleOne, hvalidity, hthreshold⟩ :=
    hstageChecks n hn input hno witness haccepts
  exact
    ⟨acceptingBranchEvidenceOfExactEstimate source branchCircuit hsize
      branchInput hreject supportBound proofValue hnonneg hleOne hvalidity
      hthreshold⟩

end NearCubicWires.ComponentwiseEstimatorAccuracy
