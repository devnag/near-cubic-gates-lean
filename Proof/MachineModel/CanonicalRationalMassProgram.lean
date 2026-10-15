import Proof.Circuits.CanonicalBalancedTraversal
import Proof.Circuits.CanonicalBalancedCall
import Proof.MachineModel.CanonicalBinaryArithmeticProgram
import Proof.MachineModel.CanonicalBitSerialMulProgram
import Proof.MachineModel.CanonicalRationalValidationProgram
import Proof.MachineModel.PreserveRightProgram
import Proof.Foundations.VerifiedLinker

/-!
# Exact rational coefficient-mass accounting

Canonical rational validation exposes one summary
`pair 1 (pair sign (pair magnitude denominator))`.  Coefficient mass ignores
the sign, so this module folds the exact nonnegative fractions without
rounding.  The accumulator deliberately need not be reduced: cross
multiplication preserves its value and avoids a second normalization path.
-/

namespace NearCubicWires.CanonicalRationalMassProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryArithmeticProgram
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBitSerialMulProgram
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalRationalValidationProgram
open NearCubicWires.CanonicalTaggedTupleProgram
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.CallableRelocation
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.VerifiedLinker

def rationalSummaryFlag (summary : ℕ) : ℕ :=
  (Nat.unpair summary).1

def rationalSummarySign (summary : ℕ) : ℕ :=
  (Nat.unpair (Nat.unpair summary).2).1

def rationalSummaryMagnitude (summary : ℕ) : ℕ :=
  (Nat.unpair (Nat.unpair (Nat.unpair summary).2).2).1

def rationalSummaryDenominator (summary : ℕ) : ℕ :=
  (Nat.unpair (Nat.unpair (Nat.unpair summary).2).2).2

def rationalSummaryValid (summary : ℕ) : Prop :=
  rationalSummaryFlag summary = 1 ∧
    rationalSummaryDenominator summary ≠ 0

private instance (summary : ℕ) : Decidable (rationalSummaryValid summary) := by
  unfold rationalSummaryValid
  infer_instance

def rationalMassAccumulatorValid (accumulator : ℕ) : Prop :=
  (Nat.unpair accumulator).2 ≠ 0

private instance (accumulator : ℕ) :
    Decidable (rationalMassAccumulatorValid accumulator) := by
  unfold rationalMassAccumulatorValid
  infer_instance

def rationalMassStep (accumulator summary : ℕ) : ℕ :=
  if rationalMassAccumulatorValid accumulator ∧
      rationalSummaryValid summary then
    let numerator := (Nat.unpair accumulator).1
    let denominator := (Nat.unpair accumulator).2
    let magnitude := rationalSummaryMagnitude summary
    let termDenominator := rationalSummaryDenominator summary
    Nat.pair
      (numerator * termDenominator + magnitude * denominator)
      (denominator * termDenominator)
  else
    0

def rationalMassFold (summaries : List ℕ) : ℕ :=
  summaries.foldl rationalMassStep (Nat.pair 0 1)

def rationalMassNumerator (summaries : List ℕ) : ℕ :=
  (Nat.unpair (rationalMassFold summaries)).1

def rationalMassDenominator (summaries : List ℕ) : ℕ :=
  (Nat.unpair (rationalMassFold summaries)).2

/-! ## One exact accumulator update -/

private def rationalMassLeafContext (accumulator summary : ℕ) : ℕ :=
  Nat.pair (rationalSummaryFlag summary) <|
    Nat.pair (rationalSummaryMagnitude summary) <|
      Nat.pair (Nat.unpair accumulator).2
        (rationalSummaryDenominator summary)

private def rationalMassLeafProjectionOutput
    (accumulator summary : ℕ) : ℕ :=
  Nat.pair
    (Nat.pair (Nat.unpair accumulator).1
      (rationalSummaryDenominator summary))
    (rationalMassLeafContext accumulator summary)

def rationalMassLeafProjectionProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 2 4 3
  , .unpairRight 2 5 4
  , .unpairLeft 3 6 5
  , .unpairRight 3 7 6
  , .unpairLeft 7 8 7
  , .unpairRight 7 9 8
  , .unpairLeft 9 10 9
  , .unpairRight 9 11 10
  , .pair 5 11 14 11
  , .pair 10 14 15 12
  , .pair 6 15 16 13
  , .pair 4 11 17 14
  , .pair 17 16 0 15
  , .halt 0
  ]

@[simp] private theorem rationalMassLeafProjectionProgram_oracleFree :
    OracleFree rationalMassLeafProjectionProgram := by
  rfl

def rationalMassLeafProjectionFuel : ℕ := 16

private def rationalMassLeafProjectionValues
    (inputLength accumulator summary : ℕ) : List ℕ :=
  [ inputLength
  , Nat.pair accumulator summary
  , accumulator
  , summary
  , (Nat.unpair accumulator).1
  , (Nat.unpair accumulator).2
  , rationalSummaryFlag summary
  , (Nat.unpair summary).2
  , (Nat.unpair (Nat.unpair summary).2).1
  , (Nat.unpair (Nat.unpair summary).2).2
  , rationalSummaryMagnitude summary
  , rationalSummaryDenominator summary
  , rationalMassLeafContext accumulator summary
  , Nat.pair (rationalSummaryMagnitude summary) <|
      Nat.pair (Nat.unpair accumulator).2
        (rationalSummaryDenominator summary)
  , Nat.pair (Nat.unpair accumulator).2
      (rationalSummaryDenominator summary)
  , Nat.pair (Nat.unpair accumulator).1
      (rationalSummaryDenominator summary)
  , rationalMassLeafProjectionOutput accumulator summary
  ]

private def rationalMassLeafProjectionBits
    (inputLength accumulator summary : ℕ) : ℕ :=
  natBitLength <|
    (rationalMassLeafProjectionValues
      inputLength accumulator summary).foldr max 0

private theorem rationalMassValue_bits
    {values : List ℕ} {value : ℕ} (hvalue : value ∈ values) :
    natBitLength value ≤ natBitLength (values.foldr max 0) := by
  apply natBitLength_mono
  induction values with
  | nil => simp at hvalue
  | cons head tail ih =>
      simp only [List.foldr_cons]
      rcases List.mem_cons.mp hvalue with rfl | htail
      · exact Nat.le_max_left _ _
      · exact (ih htail).trans (Nat.le_max_right _ _)

private theorem run_rationalMassLeafProjectionProgram
    (inputLength accumulator summary : ℕ) :
    runNPOracleProgram rationalMassLeafProjectionProgram
        (rationalMassLeafProjectionBits inputLength accumulator summary)
        rationalMassLeafProjectionFuel
        (initialNPOracleState inputLength
          (Nat.pair accumulator summary)) =
      some (rationalMassLeafProjectionOutput accumulator summary) := by
  have hbits :
      ∀ value ∈ rationalMassLeafProjectionValues
          inputLength accumulator summary,
        natBitLength value ≤
          rationalMassLeafProjectionBits
            inputLength accumulator summary := by
    intro value hvalue
    exact rationalMassValue_bits hvalue
  simp [rationalMassLeafProjectionProgram,
    rationalMassLeafProjectionFuel, runNPOracleProgram,
    initialNPOracleState, NPOracleState.boundedWrite,
    rationalMassLeafProjectionValues, hbits,
    rationalMassLeafProjectionOutput,
    rationalMassLeafContext, rationalSummaryFlag,
    rationalSummaryMagnitude, rationalSummaryDenominator]

private def rationalMassFirstProduct
    (accumulator summary : ℕ) : ℕ :=
  (Nat.unpair accumulator).1 * rationalSummaryDenominator summary

private def rationalMassFirstStageOutput
    (accumulator summary : ℕ) : ℕ :=
  Nat.pair (rationalMassFirstProduct accumulator summary)
    (rationalMassLeafContext accumulator summary)

private def rationalMassSecondLoweringOutput
    (accumulator summary : ℕ) : ℕ :=
  Nat.pair
    (Nat.pair (rationalSummaryMagnitude summary)
      (Nat.unpair accumulator).2)
    (rationalMassFirstStageOutput accumulator summary)

def rationalMassSecondLoweringProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairRight 3 4 3
  , .unpairLeft 4 5 4
  , .unpairRight 4 6 5
  , .unpairLeft 6 7 6
  , .pair 5 7 8 7
  , .pair 8 0 0 8
  , .halt 0
  ]

@[simp] private theorem rationalMassSecondLoweringProgram_oracleFree :
    OracleFree rationalMassSecondLoweringProgram := by
  rfl

private def rationalMassSecondLoweringValues
    (inputLength accumulator summary : ℕ) : List ℕ :=
  [ inputLength
  , rationalMassFirstStageOutput accumulator summary
  , rationalMassFirstProduct accumulator summary
  , rationalMassLeafContext accumulator summary
  , Nat.pair (rationalSummaryMagnitude summary) <|
      Nat.pair (Nat.unpair accumulator).2
        (rationalSummaryDenominator summary)
  , Nat.pair (Nat.unpair accumulator).2
      (rationalSummaryDenominator summary)
  , rationalSummaryMagnitude summary
  , (Nat.unpair accumulator).2
  , Nat.pair (rationalSummaryMagnitude summary)
      (Nat.unpair accumulator).2
  , rationalMassSecondLoweringOutput accumulator summary
  ]

private def rationalMassSecondLoweringBits
    (inputLength accumulator summary : ℕ) : ℕ :=
  natBitLength <|
    (rationalMassSecondLoweringValues
      inputLength accumulator summary).foldr max 0

private theorem run_rationalMassSecondLoweringProgram
    (inputLength accumulator summary : ℕ) :
    runNPOracleProgram rationalMassSecondLoweringProgram
        (rationalMassSecondLoweringBits inputLength accumulator summary) 9
        (initialNPOracleState inputLength
          (rationalMassFirstStageOutput accumulator summary)) =
      some (rationalMassSecondLoweringOutput accumulator summary) := by
  have hbits :
      ∀ value ∈ rationalMassSecondLoweringValues
          inputLength accumulator summary,
        natBitLength value ≤
          rationalMassSecondLoweringBits
            inputLength accumulator summary := by
    intro value hvalue
    exact rationalMassValue_bits hvalue
  simp [rationalMassSecondLoweringProgram, runNPOracleProgram,
    initialNPOracleState, NPOracleState.boundedWrite,
    rationalMassSecondLoweringValues, hbits,
    rationalMassSecondLoweringOutput,
    rationalMassFirstStageOutput, rationalMassLeafContext]

private def rationalMassSecondProduct
    (accumulator summary : ℕ) : ℕ :=
  rationalSummaryMagnitude summary * (Nat.unpair accumulator).2

private def rationalMassSecondStageOutput
    (accumulator summary : ℕ) : ℕ :=
  Nat.pair (rationalMassSecondProduct accumulator summary)
    (rationalMassFirstStageOutput accumulator summary)

private def rationalMassNumeratorStageOutput
    (accumulator summary : ℕ) : ℕ :=
  Nat.pair
    (rationalMassFirstProduct accumulator summary +
      rationalMassSecondProduct accumulator summary)
    (rationalMassLeafContext accumulator summary)

def rationalMassNumeratorProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .add 4 2 6 5
  , .pair 6 5 0 6
  , .halt 0
  ]

@[simp] private theorem rationalMassNumeratorProgram_oracleFree :
    OracleFree rationalMassNumeratorProgram := by
  rfl

private def rationalMassNumeratorValues
    (inputLength accumulator summary : ℕ) : List ℕ :=
  [ inputLength
  , rationalMassSecondStageOutput accumulator summary
  , rationalMassSecondProduct accumulator summary
  , rationalMassFirstStageOutput accumulator summary
  , rationalMassFirstProduct accumulator summary
  , rationalMassLeafContext accumulator summary
  , Nat.pair (rationalSummaryMagnitude summary) <|
      Nat.pair (Nat.unpair accumulator).2
        (rationalSummaryDenominator summary)
  , Nat.pair (Nat.unpair accumulator).2
      (rationalSummaryDenominator summary)
  , rationalMassFirstProduct accumulator summary +
      rationalMassSecondProduct accumulator summary
  , rationalMassNumeratorStageOutput accumulator summary
  ]

private def rationalMassNumeratorBits
    (inputLength accumulator summary : ℕ) : ℕ :=
  natBitLength <|
    (rationalMassNumeratorValues
      inputLength accumulator summary).foldr max 0

private theorem run_rationalMassNumeratorProgram
    (inputLength accumulator summary : ℕ) :
    runNPOracleProgram rationalMassNumeratorProgram
        (rationalMassNumeratorBits inputLength accumulator summary) 7
        (initialNPOracleState inputLength
          (rationalMassSecondStageOutput accumulator summary)) =
      some (rationalMassNumeratorStageOutput accumulator summary) := by
  have hbits :
      ∀ value ∈ rationalMassNumeratorValues
          inputLength accumulator summary,
        natBitLength value ≤
          rationalMassNumeratorBits inputLength accumulator summary := by
    intro value hvalue
    exact rationalMassValue_bits hvalue
  simp [rationalMassNumeratorProgram, runNPOracleProgram,
    initialNPOracleState, NPOracleState.boundedWrite,
    rationalMassNumeratorValues, hbits,
    rationalMassNumeratorStageOutput,
    rationalMassSecondStageOutput, rationalMassFirstStageOutput]

private def rationalMassDenominatorLoweringOutput
    (accumulator summary : ℕ) : ℕ :=
  Nat.pair
    (Nat.pair (Nat.unpair accumulator).2
      (rationalSummaryDenominator summary))
    (rationalMassNumeratorStageOutput accumulator summary)

def rationalMassDenominatorLoweringProgram : NPOracleProgram :=
  [ .unpairRight 0 2 1
  , .unpairRight 2 3 2
  , .unpairRight 3 4 3
  , .unpairLeft 4 5 4
  , .unpairRight 4 6 5
  , .pair 5 6 9 6
  , .pair 9 0 0 7
  , .halt 0
  ]

@[simp] private theorem rationalMassDenominatorLoweringProgram_oracleFree :
    OracleFree rationalMassDenominatorLoweringProgram := by
  rfl

private def rationalMassDenominatorLoweringValues
    (inputLength accumulator summary : ℕ) : List ℕ :=
  [ inputLength
  , rationalMassNumeratorStageOutput accumulator summary
  , rationalMassLeafContext accumulator summary
  , Nat.pair (rationalSummaryMagnitude summary) <|
      Nat.pair (Nat.unpair accumulator).2
        (rationalSummaryDenominator summary)
  , Nat.pair (Nat.unpair accumulator).2
      (rationalSummaryDenominator summary)
  , (Nat.unpair accumulator).2
  , rationalSummaryDenominator summary
  , Nat.pair (Nat.unpair accumulator).2
      (rationalSummaryDenominator summary)
  , rationalMassDenominatorLoweringOutput accumulator summary
  ]

private def rationalMassDenominatorLoweringBits
    (inputLength accumulator summary : ℕ) : ℕ :=
  natBitLength <|
    (rationalMassDenominatorLoweringValues
      inputLength accumulator summary).foldr max 0

private theorem run_rationalMassDenominatorLoweringProgram
    (inputLength accumulator summary : ℕ) :
    runNPOracleProgram rationalMassDenominatorLoweringProgram
        (rationalMassDenominatorLoweringBits
          inputLength accumulator summary) 8
        (initialNPOracleState inputLength
          (rationalMassNumeratorStageOutput accumulator summary)) =
      some (rationalMassDenominatorLoweringOutput accumulator summary) := by
  have hbits :
      ∀ value ∈ rationalMassDenominatorLoweringValues
          inputLength accumulator summary,
        natBitLength value ≤
          rationalMassDenominatorLoweringBits
            inputLength accumulator summary := by
    intro value hvalue
    exact rationalMassValue_bits hvalue
  simp [rationalMassDenominatorLoweringProgram, runNPOracleProgram,
    initialNPOracleState, NPOracleState.boundedWrite,
    rationalMassDenominatorLoweringValues, hbits,
    rationalMassDenominatorLoweringOutput,
    rationalMassNumeratorStageOutput, rationalMassLeafContext]

private def rationalMassDenominatorProduct
    (accumulator summary : ℕ) : ℕ :=
  (Nat.unpair accumulator).2 * rationalSummaryDenominator summary

private def rationalMassDenominatorStageOutput
    (accumulator summary : ℕ) : ℕ :=
  Nat.pair (rationalMassDenominatorProduct accumulator summary)
    (rationalMassNumeratorStageOutput accumulator summary)

private def rationalMassLeafFinalOutput
    (accumulator summary : ℕ) : ℕ :=
  if rationalSummaryFlag summary = 1 ∧
      rationalMassDenominatorProduct accumulator summary ≠ 0 then
    Nat.pair
      (rationalMassFirstProduct accumulator summary +
        rationalMassSecondProduct accumulator summary)
      (rationalMassDenominatorProduct accumulator summary)
  else
    0

def rationalMassLeafFinalProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .unpairLeft 5 6 5
  , .branchZero 6 13 6
  , .copy 6 7 7
  , .decrement 7 8
  , .branchZero 7 9 13
  , .branchZero 2 13 10
  , .pair 4 2 0 11
  , .halt 0
  , .branchZero 0 13 13
  , .set 0 0 14
  , .halt 0
  ]

@[simp] private theorem rationalMassLeafFinalProgram_oracleFree :
    OracleFree rationalMassLeafFinalProgram := by
  rfl

private def rationalMassLeafFinalValues
    (inputLength accumulator summary : ℕ) : List ℕ :=
  [ inputLength
  , rationalMassDenominatorStageOutput accumulator summary
  , rationalMassDenominatorProduct accumulator summary
  , rationalMassNumeratorStageOutput accumulator summary
  , rationalMassFirstProduct accumulator summary +
      rationalMassSecondProduct accumulator summary
  , rationalMassLeafContext accumulator summary
  , Nat.pair (rationalSummaryMagnitude summary) <|
      Nat.pair (Nat.unpair accumulator).2
        (rationalSummaryDenominator summary)
  , Nat.pair (Nat.unpair accumulator).2
      (rationalSummaryDenominator summary)
  , rationalSummaryFlag summary
  , (rationalSummaryFlag summary).pred
  , rationalMassLeafFinalOutput accumulator summary
  , 0
  ]

private def rationalMassLeafFinalBits
    (inputLength accumulator summary : ℕ) : ℕ :=
  natBitLength <|
    (rationalMassLeafFinalValues
      inputLength accumulator summary).foldr max 0

def rationalMassLeafFinalFuel (summary : ℕ) : ℕ :=
  if rationalSummaryFlag summary = 0 then 8
  else if rationalSummaryFlag summary = 1 then 12
  else 11

set_option maxHeartbeats 1000000 in
-- The explicit branch trace discharges every bounded-write side condition.
private theorem run_rationalMassLeafFinalProgram
    (inputLength accumulator summary : ℕ) :
    runNPOracleProgram rationalMassLeafFinalProgram
        (rationalMassLeafFinalBits inputLength accumulator summary)
        (rationalMassLeafFinalFuel summary)
        (initialNPOracleState inputLength
          (rationalMassDenominatorStageOutput accumulator summary)) =
      some (rationalMassLeafFinalOutput accumulator summary) := by
  have hbits :
      ∀ value ∈ rationalMassLeafFinalValues
          inputLength accumulator summary,
        natBitLength value ≤
          rationalMassLeafFinalBits inputLength accumulator summary := by
    intro value hvalue
    exact rationalMassValue_bits hvalue
  by_cases hzero : rationalSummaryFlag summary = 0
  · simp [rationalMassLeafFinalProgram, runNPOracleProgram,
      initialNPOracleState, NPOracleState.boundedWrite,
      rationalMassLeafFinalValues, hbits,
      rationalMassLeafFinalOutput,
      rationalMassDenominatorStageOutput,
      rationalMassNumeratorStageOutput, rationalMassLeafContext,
      rationalMassLeafFinalFuel, hzero]
  · by_cases hone : rationalSummaryFlag summary = 1
    · by_cases hdenominator :
        rationalMassDenominatorProduct accumulator summary = 0
      · simp [rationalMassLeafFinalProgram, runNPOracleProgram,
          initialNPOracleState, NPOracleState.boundedWrite,
          rationalMassLeafFinalValues, hbits,
          rationalMassLeafFinalOutput,
          rationalMassDenominatorStageOutput,
          rationalMassNumeratorStageOutput, rationalMassLeafContext,
          rationalMassLeafFinalFuel, hone, hdenominator]
      · simp [rationalMassLeafFinalProgram, runNPOracleProgram,
          initialNPOracleState, NPOracleState.boundedWrite,
          rationalMassLeafFinalValues, hbits,
          rationalMassLeafFinalOutput,
          rationalMassDenominatorStageOutput,
          rationalMassNumeratorStageOutput, rationalMassLeafContext,
          rationalMassLeafFinalFuel, hone, hdenominator]
    · have hpred : (rationalSummaryFlag summary).pred ≠ 0 := by
        intro hpred
        have hpositive : 0 < rationalSummaryFlag summary :=
          Nat.pos_of_ne_zero hzero
        have hsucc := Nat.succ_pred_eq_of_pos hpositive
        rw [hpred] at hsucc
        exact hone (by simpa using hsucc.symm)
      have hsub : rationalSummaryFlag summary - 1 ≠ 0 := by
        simpa [Nat.pred_eq_sub_one] using hpred
      simp (config := { maxSteps := 1000000 })
        [rationalMassLeafFinalProgram, runNPOracleProgram,
        initialNPOracleState, NPOracleState.boundedWrite,
        rationalMassLeafFinalValues, hbits,
        rationalMassLeafFinalOutput,
        rationalMassDenominatorStageOutput,
        rationalMassNumeratorStageOutput, rationalMassLeafContext,
        rationalMassLeafFinalFuel, hzero, hone, hsub]

def rationalMassLeafProgram : NPOracleProgram :=
  linkPrograms rationalMassLeafProjectionProgram <|
    linkPrograms (preserveRightProgram bitSerialMulProgram) <|
      linkPrograms rationalMassSecondLoweringProgram <|
        linkPrograms (preserveRightProgram bitSerialMulProgram) <|
          linkPrograms rationalMassNumeratorProgram <|
            linkPrograms rationalMassDenominatorLoweringProgram <|
              linkPrograms (preserveRightProgram bitSerialMulProgram)
                rationalMassLeafFinalProgram

@[simp] theorem rationalMassLeafProgram_oracleFree :
    OracleFree rationalMassLeafProgram := by
  exact oracleFree_linkPrograms rationalMassLeafProjectionProgram_oracleFree <|
    oracleFree_linkPrograms
      (preserveRightProgram_oracleFree bitSerialMulProgram
        bitSerialMulProgram_oracleFree) <|
      oracleFree_linkPrograms rationalMassSecondLoweringProgram_oracleFree <|
        oracleFree_linkPrograms
          (preserveRightProgram_oracleFree bitSerialMulProgram
            bitSerialMulProgram_oracleFree) <|
          oracleFree_linkPrograms rationalMassNumeratorProgram_oracleFree <|
            oracleFree_linkPrograms
              rationalMassDenominatorLoweringProgram_oracleFree <|
                oracleFree_linkPrograms
                  (preserveRightProgram_oracleFree bitSerialMulProgram
                    bitSerialMulProgram_oracleFree)
                  rationalMassLeafFinalProgram_oracleFree

def rationalMassLeafFuel (accumulator summary : ℕ) : ℕ :=
  linkFuel
    (linkPrograms (preserveRightProgram bitSerialMulProgram) <|
      linkPrograms rationalMassSecondLoweringProgram <|
        linkPrograms (preserveRightProgram bitSerialMulProgram) <|
          linkPrograms rationalMassNumeratorProgram <|
            linkPrograms rationalMassDenominatorLoweringProgram <|
              linkPrograms (preserveRightProgram bitSerialMulProgram)
                rationalMassLeafFinalProgram)
    rationalMassLeafProjectionFuel <|
      linkFuel
        (linkPrograms rationalMassSecondLoweringProgram <|
          linkPrograms (preserveRightProgram bitSerialMulProgram) <|
            linkPrograms rationalMassNumeratorProgram <|
              linkPrograms rationalMassDenominatorLoweringProgram <|
                linkPrograms (preserveRightProgram bitSerialMulProgram)
                  rationalMassLeafFinalProgram)
        (preserveRightFuel <|
          bitSerialMulFuel (rationalSummaryDenominator summary)) <|
        linkFuel
          (linkPrograms (preserveRightProgram bitSerialMulProgram) <|
            linkPrograms rationalMassNumeratorProgram <|
              linkPrograms rationalMassDenominatorLoweringProgram <|
                linkPrograms (preserveRightProgram bitSerialMulProgram)
                  rationalMassLeafFinalProgram)
          9 <|
          linkFuel
            (linkPrograms rationalMassNumeratorProgram <|
              linkPrograms rationalMassDenominatorLoweringProgram <|
                linkPrograms (preserveRightProgram bitSerialMulProgram)
                  rationalMassLeafFinalProgram)
            (preserveRightFuel <|
              bitSerialMulFuel (Nat.unpair accumulator).2) <|
            linkFuel
              (linkPrograms rationalMassDenominatorLoweringProgram <|
                linkPrograms (preserveRightProgram bitSerialMulProgram)
                  rationalMassLeafFinalProgram)
              7 <|
              linkFuel
                (linkPrograms (preserveRightProgram bitSerialMulProgram)
                  rationalMassLeafFinalProgram)
                8 <|
                linkFuel rationalMassLeafFinalProgram
                  (preserveRightFuel <|
                    bitSerialMulFuel
                      (rationalSummaryDenominator summary))
                  (rationalMassLeafFinalFuel summary)

def rationalMassLeafBits
    (inputLength accumulator summary : ℕ) : ℕ :=
  let firstInput :=
    Nat.pair (Nat.unpair accumulator).1
      (rationalSummaryDenominator summary)
  let secondInput :=
    Nat.pair (rationalSummaryMagnitude summary)
      (Nat.unpair accumulator).2
  let denominatorInput :=
    Nat.pair (Nat.unpair accumulator).2
      (rationalSummaryDenominator summary)
  [ 1
  , natBitLength inputLength
  , rationalMassLeafProjectionBits inputLength accumulator summary
  , preserveRightBits
      (bitSerialMulBits inputLength (Nat.unpair accumulator).1
        (rationalSummaryDenominator summary))
      firstInput (rationalMassLeafContext accumulator summary)
      (rationalMassFirstProduct accumulator summary)
  , rationalMassSecondLoweringBits inputLength accumulator summary
  , preserveRightBits
      (bitSerialMulBits inputLength (rationalSummaryMagnitude summary)
        (Nat.unpair accumulator).2)
      secondInput (rationalMassFirstStageOutput accumulator summary)
      (rationalMassSecondProduct accumulator summary)
  , rationalMassNumeratorBits inputLength accumulator summary
  , rationalMassDenominatorLoweringBits inputLength accumulator summary
  , preserveRightBits
      (bitSerialMulBits inputLength (Nat.unpair accumulator).2
        (rationalSummaryDenominator summary))
      denominatorInput (rationalMassNumeratorStageOutput accumulator summary)
      (rationalMassDenominatorProduct accumulator summary)
  , rationalMassLeafFinalBits inputLength accumulator summary
  ].foldr max 1

private theorem rationalMassLeafFinalOutput_eq_step
    (accumulator summary : ℕ) :
    rationalMassLeafFinalOutput accumulator summary =
      rationalMassStep accumulator summary := by
  by_cases hflag : rationalSummaryFlag summary = 1
  · by_cases haccumulator : (Nat.unpair accumulator).2 = 0
    · simp [rationalMassLeafFinalOutput, rationalMassStep,
        rationalMassAccumulatorValid, rationalSummaryValid,
        rationalMassDenominatorProduct, hflag, haccumulator]
    · by_cases hdenominator : rationalSummaryDenominator summary = 0
      · simp [rationalMassLeafFinalOutput, rationalMassStep,
          rationalMassAccumulatorValid, rationalSummaryValid,
          rationalMassDenominatorProduct, hflag, haccumulator, hdenominator]
      · simp [rationalMassLeafFinalOutput, rationalMassStep,
          rationalMassAccumulatorValid, rationalSummaryValid,
          rationalMassFirstProduct, rationalMassSecondProduct,
          rationalMassDenominatorProduct, hflag, haccumulator, hdenominator]
  · simp [rationalMassLeafFinalOutput, rationalMassStep,
      rationalMassAccumulatorValid, rationalSummaryValid,
      rationalMassDenominatorProduct, hflag]

set_option maxHeartbeats 1000000 in
-- The staged composition carries all intermediate bit bounds explicitly.
theorem run_rationalMassLeafProgram
    (inputLength accumulator summary : ℕ) :
    runNPOracleProgram rationalMassLeafProgram
        (rationalMassLeafBits inputLength accumulator summary)
        (rationalMassLeafFuel accumulator summary)
        (initialNPOracleState inputLength
          (Nat.pair accumulator summary)) =
      some (rationalMassStep accumulator summary) := by
  let maximumBits :=
    rationalMassLeafBits inputLength accumulator summary
  have hpositive : 1 ≤ maximumBits := by
    simp [maximumBits, rationalMassLeafBits]
  have hinputLength : natBitLength inputLength ≤ maximumBits := by
    simp [maximumBits, rationalMassLeafBits]
  have hprojectionBits :
      rationalMassLeafProjectionBits inputLength accumulator summary ≤
        maximumBits := by
    simp [maximumBits, rationalMassLeafBits]
  have hfirstBits :
      preserveRightBits
          (bitSerialMulBits inputLength (Nat.unpair accumulator).1
            (rationalSummaryDenominator summary))
          (Nat.pair (Nat.unpair accumulator).1
            (rationalSummaryDenominator summary))
          (rationalMassLeafContext accumulator summary)
          (rationalMassFirstProduct accumulator summary) ≤
        maximumBits := by
    simp [maximumBits, rationalMassLeafBits]
  have hsecondLoweringBits :
      rationalMassSecondLoweringBits inputLength accumulator summary ≤
        maximumBits := by
    simp [maximumBits, rationalMassLeafBits]
  have hsecondBits :
      preserveRightBits
          (bitSerialMulBits inputLength
            (rationalSummaryMagnitude summary)
            (Nat.unpair accumulator).2)
          (Nat.pair (rationalSummaryMagnitude summary)
            (Nat.unpair accumulator).2)
          (rationalMassFirstStageOutput accumulator summary)
          (rationalMassSecondProduct accumulator summary) ≤
        maximumBits := by
    simp [maximumBits, rationalMassLeafBits]
  have hnumeratorBits :
      rationalMassNumeratorBits inputLength accumulator summary ≤
        maximumBits := by
    simp [maximumBits, rationalMassLeafBits]
  have hdenominatorLoweringBits :
      rationalMassDenominatorLoweringBits
          inputLength accumulator summary ≤ maximumBits := by
    simp [maximumBits, rationalMassLeafBits]
  have hdenominatorBits :
      preserveRightBits
          (bitSerialMulBits inputLength (Nat.unpair accumulator).2
            (rationalSummaryDenominator summary))
          (Nat.pair (Nat.unpair accumulator).2
            (rationalSummaryDenominator summary))
          (rationalMassNumeratorStageOutput accumulator summary)
          (rationalMassDenominatorProduct accumulator summary) ≤
        maximumBits := by
    simp [maximumBits, rationalMassLeafBits]
  have hfinalBits :
      rationalMassLeafFinalBits inputLength accumulator summary ≤
        maximumBits := by
    simp [maximumBits, rationalMassLeafBits]
  have hprojection :=
    run_bits_mono
      (run_rationalMassLeafProjectionProgram
        inputLength accumulator summary) hprojectionBits
  have hfirstBase :=
    run_preserveRightProgram bitSerialMulProgram inputLength
      (bitSerialMulBits inputLength (Nat.unpair accumulator).1
        (rationalSummaryDenominator summary))
      (bitSerialMulFuel (rationalSummaryDenominator summary))
      (Nat.pair (Nat.unpair accumulator).1
        (rationalSummaryDenominator summary))
      (rationalMassLeafContext accumulator summary)
      (rationalMassFirstProduct accumulator summary)
      (run_bitSerialMulProgram inputLength (Nat.unpair accumulator).1
        (rationalSummaryDenominator summary))
  have hfirst :
      runNPOracleProgram (preserveRightProgram bitSerialMulProgram)
          maximumBits
          (preserveRightFuel <|
            bitSerialMulFuel (rationalSummaryDenominator summary))
          (initialNPOracleState inputLength
            (rationalMassLeafProjectionOutput accumulator summary)) =
        some (rationalMassFirstStageOutput accumulator summary) := by
    exact run_bits_mono (by
      simpa [rationalMassLeafProjectionOutput,
        rationalMassFirstStageOutput] using hfirstBase) hfirstBits
  have hsecondLowering :=
    run_bits_mono
      (run_rationalMassSecondLoweringProgram
        inputLength accumulator summary) hsecondLoweringBits
  have hsecondBase :=
    run_preserveRightProgram bitSerialMulProgram inputLength
      (bitSerialMulBits inputLength
        (rationalSummaryMagnitude summary)
        (Nat.unpair accumulator).2)
      (bitSerialMulFuel (Nat.unpair accumulator).2)
      (Nat.pair (rationalSummaryMagnitude summary)
        (Nat.unpair accumulator).2)
      (rationalMassFirstStageOutput accumulator summary)
      (rationalMassSecondProduct accumulator summary)
      (run_bitSerialMulProgram inputLength
        (rationalSummaryMagnitude summary)
        (Nat.unpair accumulator).2)
  have hsecond :
      runNPOracleProgram (preserveRightProgram bitSerialMulProgram)
          maximumBits
          (preserveRightFuel <|
            bitSerialMulFuel (Nat.unpair accumulator).2)
          (initialNPOracleState inputLength
            (rationalMassSecondLoweringOutput accumulator summary)) =
        some (rationalMassSecondStageOutput accumulator summary) := by
    exact run_bits_mono (by
      simpa [rationalMassSecondLoweringOutput,
        rationalMassSecondStageOutput] using hsecondBase) hsecondBits
  have hnumerator :=
    run_bits_mono
      (run_rationalMassNumeratorProgram
        inputLength accumulator summary) hnumeratorBits
  have hdenominatorLowering :=
    run_bits_mono
      (run_rationalMassDenominatorLoweringProgram
        inputLength accumulator summary) hdenominatorLoweringBits
  have hdenominatorBase :=
    run_preserveRightProgram bitSerialMulProgram inputLength
      (bitSerialMulBits inputLength (Nat.unpair accumulator).2
        (rationalSummaryDenominator summary))
      (bitSerialMulFuel (rationalSummaryDenominator summary))
      (Nat.pair (Nat.unpair accumulator).2
        (rationalSummaryDenominator summary))
      (rationalMassNumeratorStageOutput accumulator summary)
      (rationalMassDenominatorProduct accumulator summary)
      (run_bitSerialMulProgram inputLength (Nat.unpair accumulator).2
        (rationalSummaryDenominator summary))
  have hdenominator :
      runNPOracleProgram (preserveRightProgram bitSerialMulProgram)
          maximumBits
          (preserveRightFuel <|
            bitSerialMulFuel (rationalSummaryDenominator summary))
          (initialNPOracleState inputLength
            (rationalMassDenominatorLoweringOutput accumulator summary)) =
        some (rationalMassDenominatorStageOutput accumulator summary) := by
    exact run_bits_mono (by
      simpa [rationalMassDenominatorLoweringOutput,
        rationalMassDenominatorStageOutput] using hdenominatorBase)
      hdenominatorBits
  have hfinal :=
    run_bits_mono
      (run_rationalMassLeafFinalProgram
        inputLength accumulator summary) hfinalBits
  have hdenominatorTail :=
    run_linkPrograms hpositive hinputLength hdenominator hfinal
  have hdenominatorLoweringTail :=
    run_linkPrograms hpositive hinputLength
      hdenominatorLowering hdenominatorTail
  have hnumeratorTail :=
    run_linkPrograms hpositive hinputLength
      hnumerator hdenominatorLoweringTail
  have hsecondTail :=
    run_linkPrograms hpositive hinputLength hsecond hnumeratorTail
  have hsecondLoweringTail :=
    run_linkPrograms hpositive hinputLength
      hsecondLowering hsecondTail
  have hfirstTail :=
    run_linkPrograms hpositive hinputLength hfirst hsecondLoweringTail
  have hrun :=
    run_linkPrograms hpositive hinputLength hprojection hfirstTail
  simpa [rationalMassLeafProgram, rationalMassLeafFuel,
    rationalMassLeafFinalOutput_eq_step] using hrun

/-! ## Unique balanced accumulator controller -/

structure RationalMassFoldLayout where
  calleeSpan : ℕ
  leafPc : ℕ
  resetBase : ℕ
  prepareBase : ℕ
  calleeBase : ℕ
  returnPc : ℕ
  donePc : ℕ
  calleeRegisterBase : ℕ
  deriving Repr

def rationalMassFoldLayout : RationalMassFoldLayout :=
  let calleeSpan := programRegisterSpan rationalMassLeafProgram
  let leafPc := 34
  let resetBase := leafPc
  let prepareBase := resetBase + calleeSpan
  let calleeBase := prepareBase + 2
  let returnPc := calleeBase + rationalMassLeafProgram.length
  { calleeSpan
    leafPc
    resetBase
    prepareBase
    calleeBase
    returnPc
    donePc := returnPc + 1
    calleeRegisterBase := 10 }

def rationalMassFoldProgram : NPOracleProgram :=
  let layout := rationalMassFoldLayout
  (((balancedTraversalController layout.leafPc layout.donePc ++
      resetRegisters layout.calleeRegisterBase layout.calleeSpan
        layout.resetBase) ++
      [ .copy 1 (layout.calleeRegisterBase + 1)
          (layout.prepareBase + 1)
      , .pair 9 3 layout.calleeRegisterBase layout.calleeBase
      ]) ++
      rationalMassLeafProgram.map
        (callableInstruction layout.calleeBase layout.calleeRegisterBase
          9 layout.returnPc)) ++
      [ .unpairRight 9 9 balancedTraversalLeafReturnPc
      , .halt 9
      ]

theorem rationalMassFoldProgram_controllerAt :
    BalancedTraversalControllerAt rationalMassFoldProgram
      rationalMassFoldLayout.leafPc rationalMassFoldLayout.donePc := by
  intro pc instruction hlookup
  have hpc :
      pc <
        (balancedTraversalController rationalMassFoldLayout.leafPc
          rationalMassFoldLayout.donePc).length :=
    (List.getElem?_eq_some_iff.mp hlookup).choose
  simp only [rationalMassFoldProgram]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_map, List.length_cons,
      List.length_nil]
    omega)]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega)]
  rw [List.getElem?_append_left (by
    simp only [List.length_append]
    omega)]
  rw [List.getElem?_append_left hpc]
  exact hlookup

private theorem rationalMassFoldProgram_resetAt :
    ResetProgramAt rationalMassFoldProgram
      rationalMassFoldLayout.calleeRegisterBase
      rationalMassFoldLayout.calleeSpan
      rationalMassFoldLayout.resetBase := by
  intro index hindex
  change index < programRegisterSpan rationalMassLeafProgram at hindex
  simp only [rationalMassFoldProgram, rationalMassFoldLayout]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, balancedTraversalController_length,
      resetRegisters_length, List.length_cons, List.length_nil,
      List.length_map]
    omega)]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, balancedTraversalController_length,
      resetRegisters_length, List.length_cons, List.length_nil]
    omega)]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, balancedTraversalController_length,
      resetRegisters_length]
    omega)]
  rw [List.getElem?_append_right (by
    simp only [balancedTraversalController_length]
    omega)]
  simp only [balancedTraversalController_length]
  rw [show 34 + index - 34 = index by omega]
  simp only [resetRegisters, List.getElem?_map]
  rw [List.getElem?_range hindex]
  rfl

private theorem rationalMassFoldProgram_prepareAt
    (index : ℕ) (hindex : index < 2) :
    rationalMassFoldProgram[rationalMassFoldLayout.prepareBase + index]? =
      ([
        .copy 1 (rationalMassFoldLayout.calleeRegisterBase + 1)
          (rationalMassFoldLayout.prepareBase + 1),
        .pair 9 3 rationalMassFoldLayout.calleeRegisterBase
          rationalMassFoldLayout.calleeBase
      ] : NPOracleProgram)[index]? := by
  simp only [rationalMassFoldProgram, rationalMassFoldLayout]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, balancedTraversalController_length,
      resetRegisters_length, List.length_cons, List.length_nil,
      List.length_map]
    omega)]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, balancedTraversalController_length,
      resetRegisters_length, List.length_cons, List.length_nil]
    omega)]
  rw [List.getElem?_append_right (by
    simp only [List.length_append, balancedTraversalController_length,
      resetRegisters_length]
    omega)]
  simp only [List.length_append, balancedTraversalController_length,
    resetRegisters_length]
  rw [show 34 + programRegisterSpan rationalMassLeafProgram + index -
      (34 + programRegisterSpan rationalMassLeafProgram) = index by omega]

private theorem rationalMassFoldProgram_callableAt :
    ProgramCallableAt rationalMassFoldProgram rationalMassLeafProgram
      rationalMassFoldLayout.calleeBase
      rationalMassFoldLayout.calleeRegisterBase 9
      rationalMassFoldLayout.returnPc := by
  intro pc instruction hlookup
  have hpc : pc < rationalMassLeafProgram.length :=
    (List.getElem?_eq_some_iff.mp hlookup).choose
  simp only [rationalMassFoldProgram, rationalMassFoldLayout]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, balancedTraversalController_length,
      resetRegisters_length, List.length_cons, List.length_nil,
      List.length_map]
    omega)]
  rw [List.getElem?_append_right (by
    simp only [List.length_append, balancedTraversalController_length,
      resetRegisters_length, List.length_cons, List.length_nil]
    omega)]
  simp only [List.length_append, balancedTraversalController_length,
    resetRegisters_length, List.length_cons, List.length_nil]
  rw [show 34 + programRegisterSpan rationalMassLeafProgram + 2 + pc -
      (34 + programRegisterSpan rationalMassLeafProgram + 2) = pc by omega]
  rw [List.getElem?_map, hlookup]
  rfl

private theorem rationalMassFoldProgram_return :
    rationalMassFoldProgram[rationalMassFoldLayout.returnPc]? =
      some (.unpairRight 9 9 balancedTraversalLeafReturnPc) := by
  simp only [rationalMassFoldProgram, rationalMassFoldLayout]
  rw [List.getElem?_append_right (by
    simp only [List.length_append, balancedTraversalController_length,
      resetRegisters_length, List.length_cons, List.length_nil,
      List.length_map]
    omega)]
  simp only [List.length_append, balancedTraversalController_length,
    resetRegisters_length, List.length_cons, List.length_nil,
    List.length_map]
  rw [show 34 + programRegisterSpan rationalMassLeafProgram + 2 +
      rationalMassLeafProgram.length -
      (34 + programRegisterSpan rationalMassLeafProgram + 2 +
        rationalMassLeafProgram.length) = 0 by omega]
  rfl

private theorem rationalMassFoldProgram_halt :
    rationalMassFoldProgram[rationalMassFoldLayout.donePc]? =
      some (.halt 9) := by
  simp only [rationalMassFoldProgram, rationalMassFoldLayout]
  rw [List.getElem?_append_right (by
    simp only [List.length_append, balancedTraversalController_length,
      resetRegisters_length, List.length_cons, List.length_nil,
      List.length_map]
    omega)]
  simp only [List.length_append, balancedTraversalController_length,
    resetRegisters_length, List.length_cons, List.length_nil,
    List.length_map]
  rw [show 34 + programRegisterSpan rationalMassLeafProgram + 2 +
      rationalMassLeafProgram.length + 1 -
      (34 + programRegisterSpan rationalMassLeafProgram + 2 +
        rationalMassLeafProgram.length) = 1 by omega]
  rfl

private theorem rationalMassOracleFree_append
    {first second : NPOracleProgram}
    (hfirst : OracleFree first) (hsecond : OracleFree second) :
    OracleFree (first ++ second) := by
  unfold OracleFree at hfirst hsecond ⊢
  simp [hfirst, hsecond]

private theorem rationalMassOracleFree_reset
    (firstRegister count startPc : ℕ) :
    OracleFree (resetRegisters firstRegister count startPc) := by
  unfold OracleFree
  simp [resetRegisters, List.all_map]

private theorem rationalMassOracleFree_callable
    {callee : NPOracleProgram} (hcallee : OracleFree callee)
    (pcOffset registerOffset accumulatorRegister returnPc : ℕ) :
    OracleFree
      (callee.map (callableInstruction pcOffset registerOffset
        accumulatorRegister returnPc)) := by
  rw [oracleFree_iff_containsSAT_false] at hcallee ⊢
  unfold containsSAT at hcallee ⊢
  rw [List.any_map]
  exact (any_callableInstruction callee pcOffset registerOffset
    accumulatorRegister returnPc).trans hcallee

@[simp] theorem rationalMassFoldProgram_oracleFree :
    OracleFree rationalMassFoldProgram := by
  let layout := rationalMassFoldLayout
  have hcontroller :=
    balancedTraversalController_oracleFree layout.leafPc layout.donePc
  have hreset :=
    rationalMassOracleFree_reset layout.calleeRegisterBase
      layout.calleeSpan layout.resetBase
  have hprepare : OracleFree
      [ .copy 1 (layout.calleeRegisterBase + 1) (layout.prepareBase + 1)
      , .pair 9 3 layout.calleeRegisterBase layout.calleeBase
      ] := by rfl
  have hcallee :=
    rationalMassOracleFree_callable rationalMassLeafProgram_oracleFree
      layout.calleeBase layout.calleeRegisterBase 9 layout.returnPc
  have htail : OracleFree
      [ .unpairRight 9 9 balancedTraversalLeafReturnPc
      , .halt 9
      ] := by rfl
  simpa [rationalMassFoldProgram, layout] using
    rationalMassOracleFree_append
      (rationalMassOracleFree_append
        (rationalMassOracleFree_append
          (rationalMassOracleFree_append hcontroller hreset) hprepare)
        hcallee)
      htail

def rationalMassFoldPersistentBase : ℕ :=
  max 10 (programRegisterSpan rationalMassFoldProgram)

theorem ten_le_rationalMassFoldPersistentBase :
    10 ≤ rationalMassFoldPersistentBase :=
  le_max_left _ _

def rationalMassFoldLeafBudget (accumulator summary : ℕ) : ℕ :=
  rationalMassFoldLayout.calleeSpan + 2 +
    rationalMassLeafFuel accumulator summary + 1

private def rationalMassFoldEntryState
    (inputLength accumulator summary : ℕ)
    (state : NPOracleState) : NPOracleState :=
  let layout := rationalMassFoldLayout
  (((zeroRegisterRange layout.calleeRegisterBase layout.calleeSpan state).write
      (layout.calleeRegisterBase + 1) inputLength).write
      layout.calleeRegisterBase (Nat.pair accumulator summary)).jump
        layout.calleeBase

private theorem rationalMassFoldEntryState_eq_active
    (inputLength accumulator summary : ℕ) (state : NPOracleState) :
    let layout := rationalMassFoldLayout
    let entry :=
      rationalMassFoldEntryState inputLength accumulator summary state
    entry =
      relocateActiveState layout.calleeBase layout.calleeRegisterBase
        layout.calleeSpan entry.registers
        (initialNPOracleState inputLength
          (Nat.pair accumulator summary)) := by
  let layout := rationalMassFoldLayout
  let entry :=
    rationalMassFoldEntryState inputLength accumulator summary state
  change entry =
    relocateActiveState layout.calleeBase layout.calleeRegisterBase
      layout.calleeSpan entry.registers
      (initialNPOracleState inputLength (Nat.pair accumulator summary))
  apply CallableRelocation.state_ext
  · simp [entry, rationalMassFoldEntryState, relocateActiveState,
      initialNPOracleState, layout, rationalMassFoldLayout]
  · funext candidate
    by_cases hinside :
        layout.calleeRegisterBase ≤ candidate ∧
          candidate < layout.calleeRegisterBase + layout.calleeSpan
    · rcases hinside with ⟨hlower, hupper⟩
      by_cases hzero : candidate = layout.calleeRegisterBase
      · subst candidate
        simp [entry, rationalMassFoldEntryState, relocateActiveState,
          initialNPOracleState, layout, rationalMassFoldLayout]
      · by_cases hone :
          candidate = layout.calleeRegisterBase + 1
        · subst candidate
          simp [entry, rationalMassFoldEntryState, relocateActiveState,
            initialNPOracleState, layout, rationalMassFoldLayout]
        · have hreset :
              (zeroRegisterRange layout.calleeRegisterBase
                layout.calleeSpan state).registers candidate = 0 :=
            zeroRegisterRange_inside state hlower hupper
          have hzero' : candidate ≠ 10 := by
            simpa [layout, rationalMassFoldLayout] using hzero
          have hone' : candidate ≠ 11 := by
            simpa [layout, rationalMassFoldLayout] using hone
          have hlower' : 10 ≤ candidate := by
            simpa [layout, rationalMassFoldLayout] using hlower
          have hsubZero : candidate - 10 ≠ 0 := by omega
          have hsubOne : candidate - 10 ≠ 1 := by omega
          have hreset' :
              (zeroRegisterRange 10
                (programRegisterSpan rationalMassLeafProgram) state).registers
                  candidate = 0 := by
            simpa [layout, rationalMassFoldLayout] using hreset
          simp [entry, rationalMassFoldEntryState, relocateActiveState,
            initialNPOracleState, layout, rationalMassFoldLayout,
            hzero', hone', hsubZero, hsubOne, hreset']
    · simp [relocateActiveState, hinside]

private theorem rationalMassFold_jump_write
    (state : NPOracleState) (pc register value : ℕ) :
    (state.jump pc).write register value =
      (state.write register value).jump pc := by
  rfl

private theorem rationalMassFold_jump_jump
    (state : NPOracleState) (first second : ℕ) :
    (state.jump first).jump second = state.jump second := by
  rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- Relocation expands the callable trace into register-level frame obligations.
private theorem run_rationalMassFoldLeaf
    {maximumBits inputLength accumulator summary : ℕ}
    (state : NPOracleState)
    (hpc : state.pc = rationalMassFoldLayout.leafPc)
    (hcurrent : state.registers 0 = Nat.pair 1 summary)
    (hsummary : state.registers 3 = summary)
    (hinputLength : state.registers 1 = inputLength)
    (haccumulator : state.registers 9 = accumulator)
    (haccumulatorBits : natBitLength accumulator ≤ maximumBits)
    (hresultBits :
      natBitLength (rationalMassStep accumulator summary) ≤ maximumBits)
    (hinputBits :
      natBitLength (Nat.pair accumulator summary) ≤ maximumBits)
    (hreturnBits :
      natBitLength
          (Nat.pair accumulator (rationalMassStep accumulator summary)) ≤
        maximumBits)
    (hleafBits :
      rationalMassLeafBits inputLength accumulator summary ≤ maximumBits) :
    RunsWithin rationalMassFoldProgram maximumBits
      (rationalMassFoldLeafBudget accumulator summary) state
      (fun finish =>
        finish.pc = balancedTraversalLeafReturnPc ∧
          finish.registers 0 = state.registers 0 ∧
          finish.registers 2 = state.registers 2 ∧
          finish.registers 3 = summary ∧
          finish.registers 9 = rationalMassStep accumulator summary ∧
          SameTraversalContextFrom rationalMassFoldPersistentBase
            state finish) := by
  let layout := rationalMassFoldLayout
  let resetState :=
    (zeroRegisterRange layout.calleeRegisterBase layout.calleeSpan
      state).jump layout.prepareBase
  let lengthState :=
    (resetState.write (layout.calleeRegisterBase + 1)
      inputLength).jump (layout.prepareBase + 1)
  let callEntry :=
    (lengthState.write layout.calleeRegisterBase
      (Nat.pair accumulator summary)).jump layout.calleeBase
  have hlayoutBase : layout.calleeRegisterBase = 10 := by
    rfl
  have hbitsPositive : 1 ≤ maximumBits := by
    have hpositive : 1 ≤ natBitLength accumulator := by
      unfold natBitLength
      omega
    exact hpositive.trans haccumulatorBits
  have hstateJump :
      state.jump layout.resetBase = state := by
    cases state with
    | mk statePc registers =>
        simp only [NPOracleState.jump] at hpc ⊢
        simp only [layout, rationalMassFoldLayout] at hpc ⊢
        subst statePc
        rfl
  have hresetWithin :
      RunsWithin rationalMassFoldProgram maximumBits
        layout.calleeSpan state (· = resetState) := by
    intro extra finalOutput hcontinuation
    have hafter :
        runNPOracleProgram rationalMassFoldProgram maximumBits extra
          resetState = some finalOutput := by
      simpa using hcontinuation resetState 0 rfl
    have hreset :=
      run_resetProgramAt hbitsPositive rationalMassFoldProgram_resetAt hafter
    rw [hstateJump] at hreset
    simpa [layout, rationalMassFoldLayout, resetState,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hreset
  have hresetInputLength : resetState.registers 1 = inputLength := by
    rw [show resetState.registers 1 =
      (zeroRegisterRange layout.calleeRegisterBase layout.calleeSpan
        state).registers 1 by rfl]
    rw [zeroRegisterRange_below state (by
      simp [layout, rationalMassFoldLayout])]
    exact hinputLength
  have hresetAccumulator : resetState.registers 9 = accumulator := by
    rw [show resetState.registers 9 =
      (zeroRegisterRange layout.calleeRegisterBase layout.calleeSpan
        state).registers 9 by rfl]
    rw [zeroRegisterRange_below state (by
      simp [layout, rationalMassFoldLayout])]
    exact haccumulator
  have hresetSummary : resetState.registers 3 = summary := by
    rw [show resetState.registers 3 =
      (zeroRegisterRange layout.calleeRegisterBase layout.calleeSpan
        state).registers 3 by rfl]
    rw [zeroRegisterRange_below state (by
      simp [layout, rationalMassFoldLayout])]
    exact hsummary
  have hcopy :
      RunsToIn rationalMassFoldProgram maximumBits 1
        resetState lengthState := by
    apply runsTo_copy
    · simpa [layout] using
        rationalMassFoldProgram_prepareAt 0 (by omega)
    · simp [resetState, layout, rationalMassFoldLayout]
    · exact hresetInputLength
    · have hinputLengthBits :
          natBitLength inputLength ≤ maximumBits := by
        apply le_trans ?_ hleafBits
        simp [rationalMassLeafBits]
      exact hinputLengthBits
  have hlengthAccumulator : lengthState.registers 9 = accumulator := by
    simp [lengthState, hresetAccumulator, layout, rationalMassFoldLayout]
  have hlengthSummary : lengthState.registers 3 = summary := by
    simp [lengthState, hresetSummary, layout, rationalMassFoldLayout]
  have hpair :
      RunsToIn rationalMassFoldProgram maximumBits 1
        lengthState callEntry := by
    apply runsTo_pair
    · simpa [layout] using
        rationalMassFoldProgram_prepareAt 1 (by omega)
    · simp [lengthState, layout, rationalMassFoldLayout]
    · simp [hlengthAccumulator, hlengthSummary]
    · exact hinputBits
  have hthroughPrepare :
      RunsWithin rationalMassFoldProgram maximumBits
        (layout.calleeSpan + 2) state (· = callEntry) := by
    have hthroughCopy :=
      hresetWithin.trans (fun candidate heq => by
        subst candidate
        exact hcopy.toRunsWithin)
    have hthroughPair :=
      hthroughCopy.trans (fun candidate heq => by
        subst candidate
        exact hpair.toRunsWithin)
    simpa [Nat.add_assoc] using hthroughPair
  have hcallEntry :
      callEntry =
        rationalMassFoldEntryState
          inputLength accumulator summary state := by
    simp [callEntry, lengthState, resetState,
      rationalMassFoldEntryState, layout, rationalMassFoldLayout,
      rationalMassFold_jump_write, rationalMassFold_jump_jump]
  have hentryActive :
      callEntry =
        relocateActiveState layout.calleeBase
          layout.calleeRegisterBase layout.calleeSpan
          callEntry.registers
          (initialNPOracleState inputLength
            (Nat.pair accumulator summary)) := by
    rw [hcallEntry]
    simpa [layout] using
      rationalMassFoldEntryState_eq_active
        inputLength accumulator summary state
  have hentryAccumulator : callEntry.registers 9 = accumulator := by
    simp [callEntry, lengthState, hresetAccumulator,
      layout, rationalMassFoldLayout]
  have hentrySummary : callEntry.registers 3 = summary := by
    simp [callEntry, lengthState, hresetSummary,
      layout, rationalMassFoldLayout]
  have hcallEntryBelow :
      ∀ register, register < 10 →
        callEntry.registers register = state.registers register := by
    intro register hregister
    have hresetBelow :
        resetState.registers register = state.registers register := by
      change
        (zeroRegisterRange layout.calleeRegisterBase
          layout.calleeSpan state).registers register =
            state.registers register
      apply zeroRegisterRange_below
      rw [hlayoutBase]
      exact hregister
    have hlengthBelow :
        lengthState.registers register = state.registers register := by
      change
        (resetState.write (layout.calleeRegisterBase + 1)
          inputLength).registers register = state.registers register
      simp [NPOracleState.write,
        show register ≠ layout.calleeRegisterBase + 1 by omega,
        hresetBelow]
    change
      (lengthState.write layout.calleeRegisterBase
        (Nat.pair accumulator summary)).registers register =
          state.registers register
    simp [NPOracleState.write,
      show register ≠ layout.calleeRegisterBase by omega,
      hlengthBelow]
  have hleafExec :
      runNPOracleProgram rationalMassLeafProgram maximumBits
          (rationalMassLeafFuel accumulator summary)
          (initialNPOracleState inputLength
            (Nat.pair accumulator summary)) =
        some (rationalMassStep accumulator summary) :=
    run_bits_mono
      (run_rationalMassLeafProgram inputLength accumulator summary)
      hleafBits
  have hcalleeWithin :
      RunsWithin rationalMassFoldProgram maximumBits
        (rationalMassLeafFuel accumulator summary + 1) callEntry
        (fun finish =>
          finish.pc = balancedTraversalLeafReturnPc ∧
            finish.registers 0 = callEntry.registers 0 ∧
            finish.registers 2 = callEntry.registers 2 ∧
            finish.registers 3 = summary ∧
            finish.registers 9 = rationalMassStep accumulator summary ∧
            SameTraversalContextFrom rationalMassFoldPersistentBase
              state finish) := by
    intro extra finalOutput hcontinuation
    rw [show rationalMassLeafFuel accumulator summary + 1 + extra =
      rationalMassLeafFuel accumulator summary + (1 + extra) by omega]
    rw [hentryActive]
    apply run_callable_active
      (pcOffset := layout.calleeBase)
      (registerOffset := layout.calleeRegisterBase)
      (span := layout.calleeSpan)
      (accumulatorRegister := 9)
      (returnPc := layout.returnPc)
      callEntry.registers
      (by simp [layout, rationalMassFoldLayout])
      (le_refl layout.calleeSpan)
      (by simpa [layout] using rationalMassFoldProgram_callableAt)
      hleafExec
    · simpa [hentryAccumulator] using hreturnBits
    · intro haltState unused
      let atReturn :=
        (((relocateState layout.calleeBase layout.calleeRegisterBase
          callEntry.registers haltState).write 9
            (Nat.pair accumulator
              (rationalMassStep accumulator summary))).jump layout.returnPc)
      let returned :=
        (atReturn.write 9 (rationalMassStep accumulator summary)).jump
          balancedTraversalLeafReturnPc
      let restored :=
        restoreRegistersFrom rationalMassFoldPersistentBase state returned
      have hreturnLookup :
          rationalMassFoldProgram[layout.returnPc]? =
            some (.unpairRight 9 9 balancedTraversalLeafReturnPc) := by
        simpa [layout] using rationalMassFoldProgram_return
      have hatReturnPc : atReturn.pc = layout.returnPc := by
        simp [atReturn]
      have hatReturnValue :
          (Nat.unpair (atReturn.registers 9)).2 =
            rationalMassStep accumulator summary := by
        simp [atReturn]
      have hstep :
          runNPOracleProgram rationalMassFoldProgram maximumBits
              (unused + (1 + extra)) atReturn =
            runNPOracleProgram rationalMassFoldProgram maximumBits
              (unused + extra) returned := by
        rw [show unused + (1 + extra) = (unused + extra) + 1 by omega]
        simp only [runNPOracleProgram]
        rw [hatReturnPc, hreturnLookup]
        simp only
        rw [show atReturn.boundedWrite maximumBits 9
              (Nat.unpair (atReturn.registers 9)).2 =
            some (atReturn.write 9
              (rationalMassStep accumulator summary)) by
          simp [NPOracleState.boundedWrite, hatReturnValue, hresultBits]]
      rw [hentryAccumulator]
      change
        runNPOracleProgram rationalMassFoldProgram maximumBits
            (unused + (1 + extra)) atReturn =
          some finalOutput
      rw [hstep]
      have hagrees :
          StateAgreesBelow
            (programRegisterSpan rationalMassFoldProgram)
            returned restored := by
        have hfull :=
          stateAgreesBelow_restoreRegistersFrom
            (first := rationalMassFoldPersistentBase)
            (reference := state) (state := returned) |>.2
        refine ⟨rfl, ?_⟩
        intro register hregister
        apply hfull
        exact hregister.trans_le (le_max_right _ _)
      rw [run_congr_of_stateAgreesBelow
        (le_refl (programRegisterSpan rationalMassFoldProgram)) hagrees]
      have hatReturnBelow :
          ∀ register, register < 9 →
            atReturn.registers register = callEntry.registers register := by
        intro register hregister
        simp only [atReturn, NPOracleState.jump, NPOracleState.write]
        rw [if_neg (by omega)]
        exact relocateState_below (by
          rw [hlayoutBase]
          omega)
      have hreturnedBelow :
          ∀ register, register < 9 →
            returned.registers register = callEntry.registers register := by
        intro register hregister
        simp only [returned, NPOracleState.jump, NPOracleState.write]
        rw [if_neg (by omega)]
        exact hatReturnBelow register hregister
      have hrestoredBelow :
          ∀ register, register < 10 →
            restored.registers register = returned.registers register := by
        intro register hregister
        simp [restored, restoreRegistersFrom,
          Nat.not_le.mpr
            (hregister.trans_le ten_le_rationalMassFoldPersistentBase)]
      apply hcontinuation restored unused
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [restored, restoreRegistersFrom, returned]
      · rw [hrestoredBelow 0 (by omega), hreturnedBelow 0 (by omega)]
      · rw [hrestoredBelow 2 (by omega), hreturnedBelow 2 (by omega)]
      · rw [hrestoredBelow 3 (by omega), hreturnedBelow 3 (by omega),
          hentrySummary]
      · rw [hrestoredBelow 9 (by omega)]
        simp [returned]
      · refine ⟨?_, restoreRegistersFrom_same _ _ _⟩
        rw [hrestoredBelow 1 (by omega), hreturnedBelow 1 (by omega),
          hcallEntryBelow 1 (by omega)]
  have htotal :=
    hthroughPrepare.trans (fun candidate heq => by
      subst candidate
      exact hcalleeWithin)
  apply htotal.mono
  intro finish hfinish
  refine ⟨hfinish.1, ?_, ?_, hfinish.2.2.2.1,
    hfinish.2.2.2.2.1, hfinish.2.2.2.2.2⟩
  · rw [hfinish.2.1, hcallEntryBelow 0 (by omega)]
  · rw [hfinish.2.2.1, hcallEntryBelow 2 (by omega)]

def rationalMassInitialAccumulator : ℕ :=
  Nat.pair 0 1

def rationalMassFoldInitialState
    (inputLength : ℕ) (summaries : List ℕ) : NPOracleState :=
  (initialNPOracleState inputLength
    (encodeBalancedList summaries)).write 9 rationalMassInitialAccumulator

def rationalMassFoldLeafRequiredBits
    (inputLength accumulator summary : ℕ) : ℕ :=
  max (rationalMassLeafBits inputLength accumulator summary) <|
    max (natBitLength accumulator) <|
      max (natBitLength (rationalMassStep accumulator summary)) <|
        max (natBitLength (Nat.pair accumulator summary))
          (natBitLength
            (Nat.pair accumulator (rationalMassStep accumulator summary)))

private def rationalMassFoldTraceBits
    (inputLength : ℕ) : ℕ → List ℕ → ℕ
  | accumulator, [] => natBitLength accumulator
  | accumulator, summary :: summaries =>
      max (rationalMassFoldLeafRequiredBits
        inputLength accumulator summary) <|
        rationalMassFoldTraceBits inputLength
          (rationalMassStep accumulator summary) summaries

def rationalMassFoldBits
    (inputLength : ℕ) (summaries : List ℕ) : ℕ :=
  max 1 <| max (natBitLength inputLength) <|
    max
      (balancedTraversalRequiredBits (fun value => value)
        (balancedTraversalTree summaries) [])
      (rationalMassFoldTraceBits inputLength
        rationalMassInitialAccumulator summaries)

def rationalMassFoldFuel (summaries : List ℕ) : ℕ :=
  balancedTraversalStructuralSteps (balancedTraversalTree summaries) +
    balancedFoldLeafSteps rationalMassStep rationalMassFoldLeafBudget
      rationalMassInitialAccumulator summaries + 2

private theorem rationalMassFoldTraceFits
    (inputLength maximumBits accumulator : ℕ)
    (summaries : List ℕ)
    (htrace :
      rationalMassFoldTraceBits inputLength accumulator summaries ≤
        maximumBits) :
    BalancedFoldFits maximumBits rationalMassStep accumulator summaries ∧
      BalancedFoldLeafFits maximumBits rationalMassStep
        (rationalMassFoldLeafRequiredBits inputLength)
        accumulator summaries := by
  induction summaries generalizing accumulator with
  | nil =>
      simpa [rationalMassFoldTraceBits, BalancedFoldFits,
        BalancedFoldLeafFits] using htrace
  | cons summary summaries ih =>
      have hrequired :
          rationalMassFoldLeafRequiredBits inputLength accumulator summary ≤
            maximumBits :=
        (Nat.le_max_left _ _).trans htrace
      have htail :
          rationalMassFoldTraceBits inputLength
              (rationalMassStep accumulator summary) summaries ≤
            maximumBits :=
        (Nat.le_max_right _ _).trans htrace
      have haccumulator :
          natBitLength accumulator ≤ maximumBits := by
        apply le_trans ?_ hrequired
        simp [rationalMassFoldLeafRequiredBits]
      have hresult :
          natBitLength (rationalMassStep accumulator summary) ≤
            maximumBits := by
        apply le_trans ?_ hrequired
        simp [rationalMassFoldLeafRequiredBits]
      rcases ih (rationalMassStep accumulator summary) htail with
        ⟨hfoldTail, hleafTail⟩
      exact
        ⟨by
          simp only [BalancedFoldFits]
          exact ⟨haccumulator, hresult, hfoldTail⟩,
        by
          simp only [BalancedFoldLeafFits]
          exact ⟨hrequired, hleafTail⟩⟩

set_option maxHeartbeats 2000000 in
-- The fold proof instantiates all prefix-dependent fuel and width invariants.
theorem run_rationalMassFoldProgram
    (inputLength : ℕ) (summaries : List ℕ) :
    runNPOracleProgram rationalMassFoldProgram
        (rationalMassFoldBits inputLength summaries)
        (rationalMassFoldFuel summaries)
        (rationalMassFoldInitialState inputLength summaries) =
      some (rationalMassFold summaries) := by
  let maximumBits := rationalMassFoldBits inputLength summaries
  let initial := rationalMassFoldInitialState inputLength summaries
  have hrequired :
      balancedTraversalRequiredBits (fun value => value)
          (balancedTraversalTree summaries) [] ≤ maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _)
  have hfit :
      BalancedTraversalFits maximumBits (fun value => value)
        (balancedTraversalTree summaries) [] :=
    (balancedTraversalRequiredBits_le_iff maximumBits
      (fun value => value) (balancedTraversalTree summaries) []).mp hrequired
  have htrace :
      rationalMassFoldTraceBits inputLength
          rationalMassInitialAccumulator summaries ≤ maximumBits :=
    (Nat.le_max_right _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _)
  rcases rationalMassFoldTraceFits inputLength maximumBits
      rationalMassInitialAccumulator summaries htrace with
    ⟨hfoldFit, hleafFit⟩
  have hwithin :=
    run_balancedTraversalFoldWithin rationalMassStep
      rationalMassFoldLeafBudget
      (rationalMassFoldLeafRequiredBits inputLength)
      summaries initial inputLength rationalMassFoldPersistentBase
      ten_le_rationalMassFoldPersistentBase
      rationalMassFoldProgram_controllerAt
      (by simp [initial, rationalMassFoldInitialState,
        initialNPOracleState])
      (by simp [initial, rationalMassFoldInitialState,
        initialNPOracleState])
      (by simp [initial, rationalMassFoldInitialState,
        initialNPOracleState])
      (by simp [initial, rationalMassFoldInitialState,
        initialNPOracleState])
      hfit
      (by simpa [initial, rationalMassFoldInitialState,
        initialNPOracleState, rationalMassInitialAccumulator] using hfoldFit)
      (by simpa [initial, rationalMassFoldInitialState,
        initialNPOracleState, rationalMassInitialAccumulator] using hleafFit)
      (by
        intro summary _ entry hpc hcurrent hsummary hinputLength
          haccumulatorBits hresultBits hleafRequired
        have hleafBits :
            rationalMassLeafBits inputLength (entry.registers 9) summary ≤
              maximumBits := by
          apply le_trans ?_ hleafRequired
          simp [rationalMassFoldLeafRequiredBits]
        have hinputBits :
            natBitLength (Nat.pair (entry.registers 9) summary) ≤
              maximumBits := by
          apply le_trans ?_ hleafRequired
          simp [rationalMassFoldLeafRequiredBits]
        have hreturnBits :
            natBitLength
                (Nat.pair (entry.registers 9)
                  (rationalMassStep (entry.registers 9) summary)) ≤
              maximumBits := by
          apply le_trans ?_ hleafRequired
          simp [rationalMassFoldLeafRequiredBits]
        exact run_rationalMassFoldLeaf entry hpc hcurrent hsummary
          hinputLength rfl haccumulatorBits hresultBits
          hinputBits hreturnBits hleafBits)
  have hhalt :
      ∀ finish unused,
        (finish.pc = rationalMassFoldLayout.donePc ∧
          finish.registers 0 = encodeBalancedList summaries ∧
          finish.registers 2 = 0 ∧
          finish.registers 9 =
            summaries.foldl rationalMassStep rationalMassInitialAccumulator ∧
          SameTraversalContextFrom rationalMassFoldPersistentBase
            initial finish) →
        runNPOracleProgram rationalMassFoldProgram maximumBits
            (unused + 1) finish =
          some (rationalMassFold summaries) := by
    intro finish unused hfinish
    apply run_halt_instruction (fuel := unused)
      rationalMassFoldProgram_halt
      hfinish.1
      (by simpa [rationalMassFold, rationalMassInitialAccumulator] using
        hfinish.2.2.2.1)
    have houtputBits :
        natBitLength
            (summaries.foldl rationalMassStep rationalMassInitialAccumulator) ≤
          maximumBits :=
      hfoldFit.final
    simpa [rationalMassFold, rationalMassInitialAccumulator] using houtputBits
  unfold rationalMassFoldFuel
  apply hwithin 1 (rationalMassFold summaries)
  intro finish unused hfinish
  simpa [Nat.add_comm] using hhalt finish unused hfinish

/-! ## Exact canonical-rational semantics -/

def canonicalRationalSummary (coefficient : ℚ) : ℕ :=
  rationalValidationOutput (encodeCanonicalRational coefficient)

theorem canonicalRationalSummary_eq (coefficient : ℚ) :
    canonicalRationalSummary coefficient =
      (Nat.pair 1 <|
        Nat.pair (if coefficient.num < 0 then 1 else 0) <|
          Nat.pair coefficient.num.natAbs coefficient.den) := by
  have htuple :
      rationalTupleOutput (encodeCanonicalRational coefficient) =
        Nat.pair 1
          (Nat.pair (Nat.pair 0 (encodeInt coefficient.num))
            (encodeNat coefficient.den)) := by
    unfold rationalTupleOutput taggedTupleOutput encodeCanonicalRational
    rw [show (2 : ℕ) =
      [encodeInt coefficient.num, encodeNat coefficient.den].length by rfl]
    rw [decodeTaggedTuple_encode]
    rfl
  unfold canonicalRationalSummary rationalValidationOutput
  rw [if_pos (rationalValidationAccepts_encodeCanonicalRational coefficient)]
  by_cases hnegative : coefficient.num < 0
  · simp [rationalSign, rationalMagnitudeValue,
      rationalDenominatorValue, rationalNumeratorFrame,
      rationalTupleFields, rationalNumeratorCode,
      rationalDenominatorCode, rationalMagnitudeCode,
      rationalMagnitudeValidation, rationalDenominatorValidation,
      htuple, encodeInt, hnegative]
  · simp [rationalSign, rationalMagnitudeValue,
      rationalDenominatorValue, rationalNumeratorFrame,
      rationalTupleFields, rationalNumeratorCode,
      rationalDenominatorCode, rationalMagnitudeCode,
      rationalMagnitudeValidation, rationalDenominatorValidation,
      htuple, encodeInt, hnegative]

@[simp] theorem rationalSummaryFlag_canonical
    (coefficient : ℚ) :
    rationalSummaryFlag (canonicalRationalSummary coefficient) = 1 := by
  rw [canonicalRationalSummary_eq]
  simp [rationalSummaryFlag]

@[simp] theorem rationalSummaryMagnitude_canonical
    (coefficient : ℚ) :
    rationalSummaryMagnitude (canonicalRationalSummary coefficient) =
      coefficient.num.natAbs := by
  rw [canonicalRationalSummary_eq]
  simp [rationalSummaryMagnitude]

@[simp] theorem rationalSummaryDenominator_canonical
    (coefficient : ℚ) :
    rationalSummaryDenominator (canonicalRationalSummary coefficient) =
      coefficient.den := by
  rw [canonicalRationalSummary_eq]
  simp [rationalSummaryDenominator]

@[simp] theorem rationalSummaryValid_canonical
    (coefficient : ℚ) :
    rationalSummaryValid (canonicalRationalSummary coefficient) := by
  simp [rationalSummaryValid, coefficient.den_nz]

def rationalMassValue (accumulator : ℕ) : ℚ :=
  Rat.divInt (Nat.unpair accumulator).1 (Nat.unpair accumulator).2

theorem rationalMassStep_canonical_value
    (accumulator : ℕ) (coefficient : ℚ)
    (haccumulator : rationalMassAccumulatorValid accumulator) :
    rationalMassValue
        (rationalMassStep accumulator
          (canonicalRationalSummary coefficient)) =
      rationalMassValue accumulator + |coefficient| := by
  have hdenominator :
      ((Nat.unpair accumulator).2 : ℤ) ≠ 0 := by
    exact_mod_cast haccumulator
  have hcoefficientDenominator : (coefficient.den : ℤ) ≠ 0 := by
    exact_mod_cast coefficient.den_nz
  rw [rationalMassStep, if_pos
    ⟨haccumulator, rationalSummaryValid_canonical coefficient⟩]
  rw [Rat.abs_def]
  unfold rationalMassValue
  rw [
    Rat.divInt_add_divInt _ _ hdenominator hcoefficientDenominator]
  simp

theorem rationalMassStep_canonical_valid
    (accumulator : ℕ) (coefficient : ℚ)
    (haccumulator : rationalMassAccumulatorValid accumulator) :
    rationalMassAccumulatorValid
      (rationalMassStep accumulator
        (canonicalRationalSummary coefficient)) := by
  rw [rationalMassStep, if_pos
    ⟨haccumulator, rationalSummaryValid_canonical coefficient⟩]
  simp [rationalMassAccumulatorValid,
    Nat.mul_ne_zero haccumulator coefficient.den_nz]

private theorem rationalMassFoldCanonical_from
    (coefficients : List ℚ) (accumulator : ℕ)
    (haccumulator : rationalMassAccumulatorValid accumulator) :
    rationalMassValue
        ((coefficients.map canonicalRationalSummary).foldl
          rationalMassStep accumulator) =
      rationalMassValue accumulator +
        (coefficients.map abs).sum ∧
      rationalMassAccumulatorValid
        ((coefficients.map canonicalRationalSummary).foldl
          rationalMassStep accumulator) := by
  induction coefficients generalizing accumulator with
  | nil =>
      simpa using haccumulator
  | cons coefficient coefficients ih =>
      simp only [List.map_cons, List.foldl_cons]
      have hstepValid :=
        rationalMassStep_canonical_valid accumulator coefficient haccumulator
      rcases ih
          (rationalMassStep accumulator
            (canonicalRationalSummary coefficient))
          hstepValid with
        ⟨hvalue, hvalid⟩
      refine ⟨?_, hvalid⟩
      rw [hvalue, rationalMassStep_canonical_value accumulator coefficient
        haccumulator]
      simp [add_assoc]

theorem rationalMassFold_canonical_value (coefficients : List ℚ) :
    rationalMassValue
        (rationalMassFold
          (coefficients.map canonicalRationalSummary)) =
      (coefficients.map abs).sum := by
  have hinitial :
      rationalMassAccumulatorValid rationalMassInitialAccumulator := by
    simp [rationalMassInitialAccumulator, rationalMassAccumulatorValid]
  have hvalue :=
    (rationalMassFoldCanonical_from coefficients
      rationalMassInitialAccumulator hinitial).1
  simpa [rationalMassFold, rationalMassInitialAccumulator,
    rationalMassValue] using hvalue

/-- Fold validity: folding canonical rational summaries never produces the
zero-denominator sentinel, so the exact cross-multiplied mass comparison is a
genuine rational comparison rather than a vacuous one. -/
theorem rationalMassFold_canonical_valid (coefficients : List ℚ) :
    rationalMassAccumulatorValid
      (rationalMassFold (coefficients.map canonicalRationalSummary)) := by
  have hinitial :
      rationalMassAccumulatorValid rationalMassInitialAccumulator := by
    simp [rationalMassInitialAccumulator, rationalMassAccumulatorValid]
  have hvalid :=
    (rationalMassFoldCanonical_from coefficients
      rationalMassInitialAccumulator hinitial).2
  rw [rationalMassFold]
  exact hvalid

theorem rationalMassFold_legalCircuitSum_coefficientMass
    {Circuit : CircuitFamily}
    (description : LegalCircuitSumDescription Circuit) :
    rationalMassValue
        (rationalMassFold
          (description.terms.map fun term =>
            canonicalRationalSummary term.coefficient)) =
      description.coefficientMass := by
  rw [show
    (description.terms.map fun term =>
      canonicalRationalSummary term.coefficient) =
      (description.terms.map (fun term => term.coefficient)).map
        canonicalRationalSummary by simp]
  rw [rationalMassFold_canonical_value]
  unfold LegalCircuitSumDescription.coefficientMass
  have hfold :
      ∀ (terms : List (LegalCircuitTerm Circuit description.q))
        (initial : ℚ),
        terms.foldl
            (fun total term => total + |term.coefficient|) initial =
          initial +
            (terms.map fun term => |term.coefficient|).sum := by
    intro terms initial
    induction terms generalizing initial with
    | nil => simp
    | cons term terms ih =>
        simp only [List.foldl_cons, List.map_cons, List.sum_cons]
        rw [ih]
        simp [add_assoc]
  rw [hfold]
  simp [Function.comp_def]

end NearCubicWires.CanonicalRationalMassProgram
