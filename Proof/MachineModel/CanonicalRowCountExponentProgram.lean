import Proof.MachineModel.CanonicalFourfoldListDenominatorProgram
import Proof.MachineModel.CanonicalNatCeilLogProgram
import Proof.Circuits.CanonicalSymmetricRowCountReduction

/-!
# The symmetric row-count exponent, executed from the typed envelope

`CanonicalSymmetricRowCountReduction` collapses the entire symmetric counting
side of the artifact to one natural number,

```text
symmetricRowCountExponent liveScale accuracyExponent request
  = 2 * toeplitzWalkSideBits
        (canonicalGradedRank population touchingCost) +
      320 * Nat.clog 2 (listDenominator + 1)
```

and to one residual program computing it from the typed envelope.  This module
supplies that program *except* for the two request-derived pool quantities.

Every arithmetic stage between those quantities and the exponent is fixed here:
the dyadic scalings `256 *` and `320 *` are single shift instructions, the
graded rank is a maximum of two ceiling logarithms, and the padded Toeplitz walk
side is a shift/add/shift triple.  Nothing in this module decodes a circuit, so
the two residual programs are the remaining hypotheses on the counting side:

* one program returning `symmetricOccurrencePopulation request`;
* one program returning `symmetricOccurrenceTouchingCost request liveScale`.

Both are quantified as link-time parameters with exact interpreter premises, in
the same style as the row counter they feed.
-/

namespace NearCubicWires.CanonicalRowCountExponentProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalFourfoldListDenominatorProgram
open NearCubicWires.CanonicalFourfoldRowCountFormula
open NearCubicWires.CanonicalFourfoldRowCountProgram
open NearCubicWires.CanonicalNatCeilLogProgram
open NearCubicWires.CanonicalSymmetricRowCountReduction
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.FixedAccuracyDenominatorProgram
open NearCubicWires.FourfoldRequestEnvelopeProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.SharedNormalizedEstimatorProgram
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierWalkBridge
open NearCubicWires.VerifiedLinker

/-! ## §1 Two dyadic register identities

The interpreter's shift instructions carry an immediate amount, so every
constant scaling used by the exponent is one instruction. -/

private theorem shiftLeft_eq_mul (value amount : ℕ) :
    Nat.shiftLeft value amount = value * 2 ^ amount :=
  Nat.shiftLeft_eq value amount

private theorem shiftRight_eq_div (value amount : ℕ) :
    Nat.shiftRight value amount = value / 2 ^ amount :=
  Nat.shiftRight_eq_div_pow value amount

private theorem bits_of_le {value bound maximumBits : ℕ}
    (hvalue : value ≤ bound) (hbits : natBitLength bound ≤ maximumBits) :
    natBitLength value ≤ maximumBits :=
  (natBitLength_mono hvalue).trans hbits

private theorem exponent_le_foldr_max_of_mem
    {value base : ℕ} {values : List ℕ} (hvalue : value ∈ values) :
    value ≤ values.foldr max base := by
  induction values with
  | nil => simp at hvalue
  | cons head tail inductionHypothesis =>
      rcases List.mem_cons.mp hvalue with rfl | hvalue
      · exact Nat.le_max_left _ _
      · exact (inductionHypothesis hvalue).trans (Nat.le_max_right _ _)

/-! ## §2 The fixed structural stages

Five straight-line adapters and one branch-free maximum.  None of them decodes
a canonical list; they only move machine words between the pair positions used
by `preserveRightProgram`. -/

/-- Duplicate the request word into both pair positions. -/
def duplicateProgram : NPOracleProgram :=
  [ .pair 0 0 0 1
  , .halt 0
  ]

@[simp] theorem duplicateProgram_oracleFree : OracleFree duplicateProgram := by
  rfl

def duplicateBits (value : ℕ) : ℕ := natBitLength (Nat.pair value value)

theorem run_duplicateProgram (inputLength value : ℕ) :
    runNPOracleProgram duplicateProgram (duplicateBits value) 2
        (initialNPOracleState inputLength value) =
      some (Nat.pair value value) := by
  have houtput : natBitLength (Nat.pair value value) ≤ duplicateBits value :=
    Nat.le_refl _
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair value value) (by rfl) rfl
    (by simp [initialNPOracleState]) houtput]
  exact run_halt_instruction (fuel := 0) (value := Nat.pair value value)
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump]) houtput

/-- Exchange the two pair positions. -/
def swapPairProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .pair 3 2 0 3
  , .halt 0
  ]

@[simp] theorem swapPairProgram_oracleFree : OracleFree swapPairProgram := by
  rfl

def swapPairBits (left right : ℕ) : ℕ :=
  natBitLength (max (Nat.pair left right) (Nat.pair right left))

theorem run_swapPairProgram (inputLength left right : ℕ) :
    runNPOracleProgram swapPairProgram (swapPairBits left right) 4
        (initialNPOracleState inputLength (Nat.pair left right)) =
      some (Nat.pair right left) := by
  have hinput :
      natBitLength (Nat.pair left right) ≤ swapPairBits left right :=
    bits_of_le (Nat.le_max_left _ _) (Nat.le_refl _)
  have houtput :
      natBitLength (Nat.pair right left) ≤ swapPairBits left right :=
    bits_of_le (Nat.le_max_right _ _) (Nat.le_refl _)
  have hleft : natBitLength left ≤ swapPairBits left right :=
    bits_of_le (Nat.left_le_pair left right) hinput
  have hright : natBitLength right ≤ swapPairBits left right :=
    bits_of_le (Nat.right_le_pair left right) hinput
  rw [show 4 = 3 + 1 by omega]
  rw [run_unpairLeft_instruction (value := left) (by rfl) rfl
    (by simp [initialNPOracleState]) hleft]
  rw [show 3 = 2 + 1 by omega]
  rw [run_unpairRight_instruction (value := right) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hright]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair right left) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput]
  exact run_halt_instruction (fuel := 0) (value := Nat.pair right left)
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump]) houtput

/-- Add the two pair positions. -/
def addPairProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .add 2 3 0 3
  , .halt 0
  ]

@[simp] theorem addPairProgram_oracleFree : OracleFree addPairProgram := by
  rfl

def addPairBits (left right : ℕ) : ℕ :=
  natBitLength (max (Nat.pair left right) (left + right))

theorem run_addPairProgram (inputLength left right : ℕ) :
    runNPOracleProgram addPairProgram (addPairBits left right) 4
        (initialNPOracleState inputLength (Nat.pair left right)) =
      some (left + right) := by
  have hinput :
      natBitLength (Nat.pair left right) ≤ addPairBits left right :=
    bits_of_le (Nat.le_max_left _ _) (Nat.le_refl _)
  have houtput : natBitLength (left + right) ≤ addPairBits left right :=
    bits_of_le (Nat.le_max_right _ _) (Nat.le_refl _)
  have hleft : natBitLength left ≤ addPairBits left right :=
    bits_of_le (Nat.left_le_pair left right) hinput
  have hright : natBitLength right ≤ addPairBits left right :=
    bits_of_le (Nat.right_le_pair left right) hinput
  rw [show 4 = 3 + 1 by omega]
  rw [run_unpairLeft_instruction (value := left) (by rfl) rfl
    (by simp [initialNPOracleState]) hleft]
  rw [show 3 = 2 + 1 by omega]
  rw [run_unpairRight_instruction (value := right) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hright]
  rw [show 2 = 1 + 1 by omega]
  rw [run_add_instruction (value := left + right) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput]
  exact run_halt_instruction (fuel := 0) (value := left + right)
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump]) houtput

/-- Exchange the pair positions and scale the retained left word by the fixed
canonical graded-depth factor `256`. -/
def swapScaleOutput (left right : ℕ) : ℕ := Nat.pair right (left * 256)

def swapScaleProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .shiftLeft 2 8 2 3
  , .pair 3 2 0 4
  , .halt 0
  ]

@[simp] theorem swapScaleProgram_oracleFree : OracleFree swapScaleProgram := by
  rfl

def swapScaleBits (left right : ℕ) : ℕ :=
  natBitLength (max (Nat.pair left right) (swapScaleOutput left right))

theorem run_swapScaleProgram (inputLength left right : ℕ) :
    runNPOracleProgram swapScaleProgram (swapScaleBits left right) 5
        (initialNPOracleState inputLength (Nat.pair left right)) =
      some (swapScaleOutput left right) := by
  have hinput :
      natBitLength (Nat.pair left right) ≤ swapScaleBits left right :=
    bits_of_le (Nat.le_max_left _ _) (Nat.le_refl _)
  have houtput :
      natBitLength (swapScaleOutput left right) ≤ swapScaleBits left right :=
    bits_of_le (Nat.le_max_right _ _) (Nat.le_refl _)
  have hleft : natBitLength left ≤ swapScaleBits left right :=
    bits_of_le (Nat.left_le_pair left right) hinput
  have hright : natBitLength right ≤ swapScaleBits left right :=
    bits_of_le (Nat.right_le_pair left right) hinput
  have hscaled : natBitLength (left * 256) ≤ swapScaleBits left right :=
    bits_of_le (Nat.right_le_pair right (left * 256)) houtput
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairLeft_instruction (value := left) (by rfl) rfl
    (by simp [initialNPOracleState]) hleft]
  rw [show 4 = 3 + 1 by omega]
  rw [run_unpairRight_instruction (value := right) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hright]
  rw [show 3 = 2 + 1 by omega]
  rw [run_shiftLeft_instruction (value := left * 256) (by rfl) rfl
    (by
      rw [shiftLeft_eq_mul]
      simp [NPOracleState.write, NPOracleState.jump])
    hscaled]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (value := swapScaleOutput left right) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, swapScaleOutput])
    houtput]
  exact run_halt_instruction (fuel := 0)
    (value := swapScaleOutput left right) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

/-- Add one, the canonical positivity shift of the list denominator. -/
def successorProgram : NPOracleProgram :=
  [ .increment 0 1
  , .halt 0
  ]

@[simp] theorem successorProgram_oracleFree : OracleFree successorProgram := by
  rfl

def successorBits (value : ℕ) : ℕ := natBitLength (value + 1)

theorem run_successorProgram (inputLength value : ℕ) :
    runNPOracleProgram successorProgram (successorBits value) 2
        (initialNPOracleState inputLength value) =
      some (value + 1) := by
  have houtput : natBitLength (value + 1) ≤ successorBits value :=
    Nat.le_refl _
  rw [show 2 = 1 + 1 by omega]
  rw [run_increment_instruction (value := value + 1) (by rfl) rfl
    (by simp [initialNPOracleState]) houtput]
  exact run_halt_instruction (fuel := 0) (value := value + 1) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

/-- Scale by the fixed powered-label exponent `320 = 2 ^ 8 + 2 ^ 6`. -/
def scale320Program : NPOracleProgram :=
  [ .shiftLeft 0 8 2 1
  , .shiftLeft 0 6 3 2
  , .add 2 3 0 3
  , .halt 0
  ]

@[simp] theorem scale320Program_oracleFree : OracleFree scale320Program := by
  rfl

def scale320Bits (value : ℕ) : ℕ := natBitLength (320 * value)

theorem run_scale320Program (inputLength value : ℕ) :
    runNPOracleProgram scale320Program (scale320Bits value) 4
        (initialNPOracleState inputLength value) =
      some (320 * value) := by
  have houtput : natBitLength (320 * value) ≤ scale320Bits value :=
    Nat.le_refl _
  have hhigh : natBitLength (value * 256) ≤ scale320Bits value :=
    bits_of_le (by omega) houtput
  have hlow : natBitLength (value * 64) ≤ scale320Bits value :=
    bits_of_le (by omega) houtput
  rw [show 4 = 3 + 1 by omega]
  rw [run_shiftLeft_instruction (value := value * 256) (by rfl) rfl
    (by
      rw [shiftLeft_eq_mul]
      simp [initialNPOracleState])
    hhigh]
  rw [show 3 = 2 + 1 by omega]
  rw [run_shiftLeft_instruction (value := value * 64) (by rfl) rfl
    (by
      rw [shiftLeft_eq_mul]
      simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hlow]
  rw [show 2 = 1 + 1 by omega]
  rw [run_add_instruction (value := 320 * value) (by rfl) rfl
    (by
      simp only [NPOracleState.write, NPOracleState.jump]
      norm_num
      omega)
    houtput]
  exact run_halt_instruction (fuel := 0) (value := 320 * value) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

/-! ## §3 The graded rank and the padded walk side

`canonicalGradedRank` is the maximum of two ceiling logarithms and
`toeplitzWalkSideBits` halves `3 *` its argument, so one branch and three shift
instructions cover both. -/

/-- The doubled padded-walk side of one graded rank. -/
def doubledWalkSideBits (rank : ℕ) : ℕ := 2 * toeplitzWalkSideBits rank

private theorem doubledWalkSideBits_shift (rank : ℕ) :
    (rank * 2 + rank) / 2 * 2 = doubledWalkSideBits rank := by
  unfold doubledWalkSideBits toeplitzWalkSideBits toeplitzSeedBits
  omega

private theorem doubledWalkSideBits_le (rank : ℕ) :
    doubledWalkSideBits rank ≤ 3 * rank := by
  rw [← doubledWalkSideBits_shift]
  omega

/-- The maximum of the two pair positions, followed by the padded walk side. -/
def gradedWalkExponentProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .subtract 2 3 4 3
  , .branchZero 4 5 4
  , .copy 2 3 6
  , .copy 3 3 6
  , .shiftLeft 3 1 2 7
  , .add 2 3 2 8
  , .shiftRight 2 1 2 9
  , .shiftLeft 2 1 0 10
  , .halt 0
  ]

@[simp] theorem gradedWalkExponentProgram_oracleFree :
    OracleFree gradedWalkExponentProgram := by
  rfl

def gradedWalkExponentBits (left right : ℕ) : ℕ :=
  natBitLength (max (Nat.pair left right) (3 * max left right))

private theorem run_gradedWalkTail
    (maximumBits rank : ℕ) (state : NPOracleState)
    (hpc : state.pc = 6)
    (hrank : state.registers 3 = rank)
    (hbound : natBitLength (3 * rank) ≤ maximumBits) :
    runNPOracleProgram gradedWalkExponentProgram maximumBits 5 state =
      some (doubledWalkSideBits rank) := by
  have hdouble : natBitLength (rank * 2) ≤ maximumBits :=
    bits_of_le (by omega) hbound
  have htriple : natBitLength (rank * 2 + rank) ≤ maximumBits :=
    bits_of_le (by omega) hbound
  have hhalf : natBitLength ((rank * 2 + rank) / 2) ≤ maximumBits :=
    bits_of_le (by omega) hbound
  have houtput : natBitLength (doubledWalkSideBits rank) ≤ maximumBits :=
    bits_of_le (doubledWalkSideBits_le rank) hbound
  rw [show 5 = 4 + 1 by omega]
  rw [run_shiftLeft_instruction (value := rank * 2) (by rfl) hpc
    (by rw [shiftLeft_eq_mul, hrank]; norm_num) hdouble]
  rw [show 4 = 3 + 1 by omega]
  rw [run_add_instruction (value := rank * 2 + rank) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hrank]) htriple]
  rw [show 3 = 2 + 1 by omega]
  rw [run_shiftRight_instruction (value := (rank * 2 + rank) / 2) (by rfl) rfl
    (by
      simp only [NPOracleState.write, NPOracleState.jump, if_true]
      rw [shiftRight_eq_div]
      norm_num)
    hhalf]
  rw [show 2 = 1 + 1 by omega]
  rw [run_shiftLeft_instruction (value := doubledWalkSideBits rank) (by rfl) rfl
    (by
      simp only [NPOracleState.write, NPOracleState.jump, if_true]
      rw [shiftLeft_eq_mul, ← doubledWalkSideBits_shift]
      norm_num)
    houtput]
  exact run_halt_instruction (fuel := 0) (value := doubledWalkSideBits rank)
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump]) houtput

theorem run_gradedWalkExponentProgram (inputLength left right : ℕ) :
    runNPOracleProgram gradedWalkExponentProgram
        (gradedWalkExponentBits left right) 10
        (initialNPOracleState inputLength (Nat.pair left right)) =
      some (doubledWalkSideBits (max left right)) := by
  have hinput :
      natBitLength (Nat.pair left right) ≤ gradedWalkExponentBits left right :=
    bits_of_le (Nat.le_max_left _ _) (Nat.le_refl _)
  have hbound :
      natBitLength (3 * max left right) ≤ gradedWalkExponentBits left right :=
    bits_of_le (Nat.le_max_right _ _) (Nat.le_refl _)
  have hleft : natBitLength left ≤ gradedWalkExponentBits left right :=
    bits_of_le (Nat.left_le_pair left right) hinput
  have hright : natBitLength right ≤ gradedWalkExponentBits left right :=
    bits_of_le (Nat.right_le_pair left right) hinput
  have hdifference :
      natBitLength (left - right) ≤ gradedWalkExponentBits left right :=
    bits_of_le (Nat.sub_le left right) hleft
  rw [show 10 = 9 + 1 by omega]
  rw [run_unpairLeft_instruction (value := left) (by rfl) rfl
    (by simp [initialNPOracleState]) hleft]
  rw [show 9 = 8 + 1 by omega]
  rw [run_unpairRight_instruction (value := right) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hright]
  rw [show 8 = 7 + 1 by omega]
  rw [run_subtract_instruction (value := left - right) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hdifference]
  rw [show 7 = 6 + 1 by omega]
  rw [run_branchZero_instruction (program := gradedWalkExponentProgram)
    (register := 4) (zeroTarget := 5) (nonzeroTarget := 4) (by rfl) rfl]
  by_cases hle : left ≤ right
  · have hzero : left - right = 0 := by omega
    have hmax : max left right = right := by omega
    rw [show 6 = 5 + 1 by omega]
    rw [run_copy_instruction (program := gradedWalkExponentProgram) (pc := 5)
      (source := 3) (destination := 3) (next := 6) (value := right) (by rfl)
      (by simp [NPOracleState.jump, NPOracleState.write, hzero])
      (by simp [NPOracleState.write, NPOracleState.jump]) hright]
    rw [hmax]
    exact run_gradedWalkTail _ right _ rfl
      (by simp [NPOracleState.write, NPOracleState.jump])
      (by rw [hmax] at hbound; exact hbound)
  · have hpositive : ¬left - right = 0 := by omega
    have hmax : max left right = left := by omega
    rw [show 6 = 5 + 1 by omega]
    rw [run_copy_instruction (program := gradedWalkExponentProgram) (pc := 4)
      (source := 2) (destination := 3) (next := 6) (value := left) (by rfl)
      (by simp [NPOracleState.jump, NPOracleState.write, hpositive])
      (by simp [NPOracleState.write, NPOracleState.jump]) hleft]
    rw [hmax]
    exact run_gradedWalkTail _ left _ rfl
      (by simp [NPOracleState.write, NPOracleState.jump])
      (by rw [hmax] at hbound; exact hbound)

/-! ## §4 The graded-rank half of the exponent

Nine fixed stages take the typed envelope to `2 * toeplitzWalkSideBits` of the
canonical graded rank.  Two of them are the residual pool programs; the rest are
the adapters of §2, the maximum of §3, and two copies of the existing ceiling
logarithm. -/

private def rankTail8 : NPOracleProgram :=
  linkPrograms (preserveRightProgram binaryNatCeilLogProgram)
    gradedWalkExponentProgram

private def rankTail7 : NPOracleProgram :=
  linkPrograms swapPairProgram rankTail8

private def rankTail6 : NPOracleProgram :=
  linkPrograms (preserveRightProgram binaryNatCeilLogProgram) rankTail7

private def rankTail5 : NPOracleProgram :=
  linkPrograms swapScaleProgram rankTail6

private def rankTail4 (costProgram : NPOracleProgram) : NPOracleProgram :=
  linkPrograms (preserveRightProgram costProgram) rankTail5

private def rankTail3 (costProgram : NPOracleProgram) : NPOracleProgram :=
  linkPrograms swapPairProgram (rankTail4 costProgram)

private def rankTail2 (populationProgram costProgram : NPOracleProgram) :
    NPOracleProgram :=
  linkPrograms (preserveRightProgram populationProgram)
    (rankTail3 costProgram)

/-- **The graded-rank exponent program.**  One occurrence-population program and
one touching-cost program, followed by fixed arithmetic only. -/
def symmetricRankExponentProgram
    (populationProgram costProgram : NPOracleProgram) : NPOracleProgram :=
  linkPrograms duplicateProgram (rankTail2 populationProgram costProgram)

private theorem rankTail8_oracleFree : OracleFree rankTail8 :=
  oracleFree_linkPrograms
    (preserveRightProgram_oracleFree _ binaryNatCeilLogProgram_oracleFree)
    gradedWalkExponentProgram_oracleFree

private theorem rankTail7_oracleFree : OracleFree rankTail7 :=
  oracleFree_linkPrograms swapPairProgram_oracleFree rankTail8_oracleFree

private theorem rankTail6_oracleFree : OracleFree rankTail6 :=
  oracleFree_linkPrograms
    (preserveRightProgram_oracleFree _ binaryNatCeilLogProgram_oracleFree)
    rankTail7_oracleFree

private theorem rankTail5_oracleFree : OracleFree rankTail5 :=
  oracleFree_linkPrograms swapScaleProgram_oracleFree rankTail6_oracleFree

private theorem rankTail4_oracleFree
    (costProgram : NPOracleProgram) (hcost : OracleFree costProgram) :
    OracleFree (rankTail4 costProgram) :=
  oracleFree_linkPrograms (preserveRightProgram_oracleFree _ hcost)
    rankTail5_oracleFree

private theorem rankTail3_oracleFree
    (costProgram : NPOracleProgram) (hcost : OracleFree costProgram) :
    OracleFree (rankTail3 costProgram) :=
  oracleFree_linkPrograms swapPairProgram_oracleFree
    (rankTail4_oracleFree costProgram hcost)

private theorem rankTail2_oracleFree
    (populationProgram costProgram : NPOracleProgram)
    (hpopulation : OracleFree populationProgram)
    (hcost : OracleFree costProgram) :
    OracleFree (rankTail2 populationProgram costProgram) :=
  oracleFree_linkPrograms (preserveRightProgram_oracleFree _ hpopulation)
    (rankTail3_oracleFree costProgram hcost)

theorem symmetricRankExponentProgram_oracleFree
    (populationProgram costProgram : NPOracleProgram)
    (hpopulation : OracleFree populationProgram)
    (hcost : OracleFree costProgram) :
    OracleFree (symmetricRankExponentProgram populationProgram costProgram) :=
  oracleFree_linkPrograms duplicateProgram_oracleFree
    (rankTail2_oracleFree populationProgram costProgram hpopulation hcost)

private def rankTail8Fuel (cost : ℕ) : ℕ :=
  linkFuel gradedWalkExponentProgram
    (preserveRightFuel (binaryNatCeilLogFuel (cost * 256))) 10

private def rankTail7Fuel (cost : ℕ) : ℕ :=
  linkFuel rankTail8 4 (rankTail8Fuel cost)

private def rankTail6Fuel (population cost : ℕ) : ℕ :=
  linkFuel rankTail7 (preserveRightFuel (binaryNatCeilLogFuel population))
    (rankTail7Fuel cost)

private def rankTail5Fuel (population cost : ℕ) : ℕ :=
  linkFuel rankTail6 5 (rankTail6Fuel population cost)

private def rankTail4Fuel (costFuel population cost : ℕ) : ℕ :=
  linkFuel rankTail5 (preserveRightFuel costFuel)
    (rankTail5Fuel population cost)

private def rankTail3Fuel
    (costProgram : NPOracleProgram) (costFuel population cost : ℕ) : ℕ :=
  linkFuel (rankTail4 costProgram) 4 (rankTail4Fuel costFuel population cost)

private def rankTail2Fuel
    (costProgram : NPOracleProgram)
    (populationFuel costFuel population cost : ℕ) : ℕ :=
  linkFuel (rankTail3 costProgram) (preserveRightFuel populationFuel)
    (rankTail3Fuel costProgram costFuel population cost)

def symmetricRankExponentFuel
    (populationProgram costProgram : NPOracleProgram)
    (populationFuel costFuel population cost : ℕ) : ℕ :=
  linkFuel (rankTail2 populationProgram costProgram) 2
    (rankTail2Fuel costProgram populationFuel costFuel population cost)

def symmetricRankExponentStageBits
    (populationBits costBits inputLength envelope population cost : ℕ) :
    List ℕ :=
  [ 1
  , natBitLength inputLength
  , duplicateBits envelope
  , preserveRightBits populationBits envelope envelope population
  , swapPairBits population envelope
  , preserveRightBits costBits envelope population cost
  , swapScaleBits cost population
  , preserveRightBits (binaryNatCeilLogBits population) population
      (cost * 256) (Nat.clog 2 population)
  , swapPairBits (Nat.clog 2 population) (cost * 256)
  , preserveRightBits (binaryNatCeilLogBits (cost * 256)) (cost * 256)
      (Nat.clog 2 population) (Nat.clog 2 (cost * 256))
  , gradedWalkExponentBits (Nat.clog 2 (cost * 256)) (Nat.clog 2 population)
  ]

def symmetricRankExponentBits
    (populationBits costBits inputLength envelope population cost : ℕ) : ℕ :=
  (symmetricRankExponentStageBits populationBits costBits inputLength envelope
    population cost).foldr max 1

private theorem canonicalGradedRank_eq (population cost : ℕ) :
    canonicalGradedRank population cost =
      max (Nat.clog 2 (cost * 256)) (Nat.clog 2 population) := by
  unfold canonicalGradedRank canonicalGradedDepth
  rw [Nat.mul_comm 256 cost]

set_option maxHeartbeats 1600000 in
-- The nine linked stages are unfolded once through their private tails.
/-- **The graded-rank exponent, executed.**  Given exact interpreter runs of the
occurrence-population and touching-cost programs on one request word, the fixed
program returns `2 * toeplitzWalkSideBits` of the canonical graded rank. -/
theorem run_symmetricRankExponentProgram
    (populationProgram costProgram : NPOracleProgram)
    (inputLength envelope population cost populationBits populationFuel
      costBits costFuel maximumBits : ℕ)
    (hbits :
      symmetricRankExponentBits populationBits costBits inputLength envelope
          population cost ≤
        maximumBits)
    (hpopulation :
      runNPOracleProgram populationProgram populationBits populationFuel
          (initialNPOracleState inputLength envelope) =
        some population)
    (hcost :
      runNPOracleProgram costProgram costBits costFuel
          (initialNPOracleState inputLength envelope) =
        some cost) :
    runNPOracleProgram
        (symmetricRankExponentProgram populationProgram costProgram)
        maximumBits
        (symmetricRankExponentFuel populationProgram costProgram populationFuel
          costFuel population cost)
        (initialNPOracleState inputLength envelope) =
      some (doubledWalkSideBits (canonicalGradedRank population cost)) := by
  have bits_of_member {value : ℕ}
      (hvalue :
        value ∈
          symmetricRankExponentStageBits populationBits costBits inputLength
            envelope population cost) :
      value ≤ maximumBits :=
    le_trans (exponent_le_foldr_max_of_mem hvalue) hbits
  have hpositive : 1 ≤ maximumBits := by
    apply bits_of_member
    simp [symmetricRankExponentStageBits]
  have hlength : natBitLength inputLength ≤ maximumBits := by
    apply bits_of_member
    simp [symmetricRankExponentStageBits]
  have hstage1 :
      runNPOracleProgram duplicateProgram maximumBits 2
          (initialNPOracleState inputLength envelope) =
        some (Nat.pair envelope envelope) :=
    run_bits_mono (run_duplicateProgram inputLength envelope)
      (by
        apply bits_of_member
        simp [symmetricRankExponentStageBits])
  have hstage2 :
      runNPOracleProgram (preserveRightProgram populationProgram) maximumBits
          (preserveRightFuel populationFuel)
          (initialNPOracleState inputLength (Nat.pair envelope envelope)) =
        some (Nat.pair population envelope) :=
    run_bits_mono
      (run_preserveRightProgram populationProgram inputLength populationBits
        populationFuel envelope envelope population hpopulation)
      (by
        apply bits_of_member
        simp [symmetricRankExponentStageBits])
  have hstage3 :
      runNPOracleProgram swapPairProgram maximumBits 4
          (initialNPOracleState inputLength (Nat.pair population envelope)) =
        some (Nat.pair envelope population) :=
    run_bits_mono (run_swapPairProgram inputLength population envelope)
      (by
        apply bits_of_member
        simp [symmetricRankExponentStageBits])
  have hstage4 :
      runNPOracleProgram (preserveRightProgram costProgram) maximumBits
          (preserveRightFuel costFuel)
          (initialNPOracleState inputLength (Nat.pair envelope population)) =
        some (Nat.pair cost population) :=
    run_bits_mono
      (run_preserveRightProgram costProgram inputLength costBits costFuel
        envelope population cost hcost)
      (by
        apply bits_of_member
        simp [symmetricRankExponentStageBits])
  have hstage5 :
      runNPOracleProgram swapScaleProgram maximumBits 5
          (initialNPOracleState inputLength (Nat.pair cost population)) =
        some (Nat.pair population (cost * 256)) :=
    run_bits_mono (run_swapScaleProgram inputLength cost population)
      (by
        apply bits_of_member
        simp [symmetricRankExponentStageBits])
  have hstage6 :
      runNPOracleProgram (preserveRightProgram binaryNatCeilLogProgram)
          maximumBits (preserveRightFuel (binaryNatCeilLogFuel population))
          (initialNPOracleState inputLength
            (Nat.pair population (cost * 256))) =
        some (Nat.pair (Nat.clog 2 population) (cost * 256)) :=
    run_bits_mono
      (run_preserveRightProgram binaryNatCeilLogProgram inputLength
        (binaryNatCeilLogBits population) (binaryNatCeilLogFuel population)
        population (cost * 256) (Nat.clog 2 population)
        (run_binaryNatCeilLogProgram inputLength population
          (binaryNatCeilLogBits population) (le_refl _)))
      (by
        apply bits_of_member
        simp [symmetricRankExponentStageBits])
  have hstage7 :
      runNPOracleProgram swapPairProgram maximumBits 4
          (initialNPOracleState inputLength
            (Nat.pair (Nat.clog 2 population) (cost * 256))) =
        some (Nat.pair (cost * 256) (Nat.clog 2 population)) :=
    run_bits_mono
      (run_swapPairProgram inputLength (Nat.clog 2 population) (cost * 256))
      (by
        apply bits_of_member
        simp [symmetricRankExponentStageBits])
  have hstage8 :
      runNPOracleProgram (preserveRightProgram binaryNatCeilLogProgram)
          maximumBits
          (preserveRightFuel (binaryNatCeilLogFuel (cost * 256)))
          (initialNPOracleState inputLength
            (Nat.pair (cost * 256) (Nat.clog 2 population))) =
        some
          (Nat.pair (Nat.clog 2 (cost * 256)) (Nat.clog 2 population)) :=
    run_bits_mono
      (run_preserveRightProgram binaryNatCeilLogProgram inputLength
        (binaryNatCeilLogBits (cost * 256))
        (binaryNatCeilLogFuel (cost * 256)) (cost * 256)
        (Nat.clog 2 population) (Nat.clog 2 (cost * 256))
        (run_binaryNatCeilLogProgram inputLength (cost * 256)
          (binaryNatCeilLogBits (cost * 256)) (le_refl _)))
      (by
        apply bits_of_member
        simp [symmetricRankExponentStageBits])
  have hstage9 :
      runNPOracleProgram gradedWalkExponentProgram maximumBits 10
          (initialNPOracleState inputLength
            (Nat.pair (Nat.clog 2 (cost * 256)) (Nat.clog 2 population))) =
        some
          (doubledWalkSideBits
            (max (Nat.clog 2 (cost * 256)) (Nat.clog 2 population))) :=
    run_bits_mono
      (run_gradedWalkExponentProgram inputLength (Nat.clog 2 (cost * 256))
        (Nat.clog 2 population))
      (by
        apply bits_of_member
        simp [symmetricRankExponentStageBits])
  rw [canonicalGradedRank_eq]
  exact run_linkPrograms hpositive hlength hstage1
    (run_linkPrograms hpositive hlength hstage2
      (run_linkPrograms hpositive hlength hstage3
        (run_linkPrograms hpositive hlength hstage4
          (run_linkPrograms hpositive hlength hstage5
            (run_linkPrograms hpositive hlength hstage6
              (run_linkPrograms hpositive hlength hstage7
                (run_linkPrograms hpositive hlength hstage8 hstage9)))))))

/-! ## §5 The denominator half of the exponent

The list denominator already has a fixed program; the exponent adds the
canonical positivity shift, one ceiling logarithm, and the powered-label
scaling `320 = 2 ^ 8 + 2 ^ 6`. -/

private def denominatorTail2 : NPOracleProgram :=
  linkPrograms binaryNatCeilLogProgram scale320Program

private def denominatorTail1 : NPOracleProgram :=
  linkPrograms successorProgram denominatorTail2

/-- **The denominator exponent program.** -/
def denominatorExponentProgram (denominatorProgram : NPOracleProgram) :
    NPOracleProgram :=
  linkPrograms denominatorProgram denominatorTail1

private theorem denominatorTail2_oracleFree : OracleFree denominatorTail2 :=
  oracleFree_linkPrograms binaryNatCeilLogProgram_oracleFree
    scale320Program_oracleFree

private theorem denominatorTail1_oracleFree : OracleFree denominatorTail1 :=
  oracleFree_linkPrograms successorProgram_oracleFree
    denominatorTail2_oracleFree

theorem denominatorExponentProgram_oracleFree
    (denominatorProgram : NPOracleProgram)
    (hdenominator : OracleFree denominatorProgram) :
    OracleFree (denominatorExponentProgram denominatorProgram) :=
  oracleFree_linkPrograms hdenominator denominatorTail1_oracleFree

private def denominatorTail2Fuel (denominator : ℕ) : ℕ :=
  linkFuel scale320Program (binaryNatCeilLogFuel (denominator + 1)) 4

private def denominatorTail1Fuel (denominator : ℕ) : ℕ :=
  linkFuel denominatorTail2 2 (denominatorTail2Fuel denominator)

def denominatorExponentFuel (denominatorFuel denominator : ℕ) : ℕ :=
  linkFuel denominatorTail1 denominatorFuel (denominatorTail1Fuel denominator)

def denominatorExponentStageBits
    (denominatorBits inputLength denominator : ℕ) : List ℕ :=
  [ 1
  , natBitLength inputLength
  , denominatorBits
  , successorBits denominator
  , binaryNatCeilLogBits (denominator + 1)
  , scale320Bits (Nat.clog 2 (denominator + 1))
  ]

def denominatorExponentBits
    (denominatorBits inputLength denominator : ℕ) : ℕ :=
  (denominatorExponentStageBits denominatorBits inputLength
    denominator).foldr max 1

/-- **The denominator exponent, executed.** -/
theorem run_denominatorExponentProgram
    (denominatorProgram : NPOracleProgram)
    (inputLength envelope denominator denominatorBits denominatorFuel
      maximumBits : ℕ)
    (hbits :
      denominatorExponentBits denominatorBits inputLength denominator ≤
        maximumBits)
    (hdenominator :
      runNPOracleProgram denominatorProgram denominatorBits denominatorFuel
          (initialNPOracleState inputLength envelope) =
        some denominator) :
    runNPOracleProgram (denominatorExponentProgram denominatorProgram)
        maximumBits (denominatorExponentFuel denominatorFuel denominator)
        (initialNPOracleState inputLength envelope) =
      some (320 * Nat.clog 2 (denominator + 1)) := by
  have bits_of_member {value : ℕ}
      (hvalue :
        value ∈
          denominatorExponentStageBits denominatorBits inputLength
            denominator) :
      value ≤ maximumBits :=
    le_trans (exponent_le_foldr_max_of_mem hvalue) hbits
  have hpositive : 1 ≤ maximumBits := by
    apply bits_of_member
    simp [denominatorExponentStageBits]
  have hlength : natBitLength inputLength ≤ maximumBits := by
    apply bits_of_member
    simp [denominatorExponentStageBits]
  have hstage1 :
      runNPOracleProgram denominatorProgram maximumBits denominatorFuel
          (initialNPOracleState inputLength envelope) =
        some denominator :=
    run_bits_mono hdenominator
      (by
        apply bits_of_member
        simp [denominatorExponentStageBits])
  have hstage2 :
      runNPOracleProgram successorProgram maximumBits 2
          (initialNPOracleState inputLength denominator) =
        some (denominator + 1) :=
    run_bits_mono (run_successorProgram inputLength denominator)
      (by
        apply bits_of_member
        simp [denominatorExponentStageBits])
  have hstage3 :
      runNPOracleProgram binaryNatCeilLogProgram maximumBits
          (binaryNatCeilLogFuel (denominator + 1))
          (initialNPOracleState inputLength (denominator + 1)) =
        some (Nat.clog 2 (denominator + 1)) :=
    run_bits_mono
      (run_binaryNatCeilLogProgram inputLength (denominator + 1)
        (binaryNatCeilLogBits (denominator + 1)) (le_refl _))
      (by
        apply bits_of_member
        simp [denominatorExponentStageBits])
  have hstage4 :
      runNPOracleProgram scale320Program maximumBits 4
          (initialNPOracleState inputLength (Nat.clog 2 (denominator + 1))) =
        some (320 * Nat.clog 2 (denominator + 1)) :=
    run_bits_mono
      (run_scale320Program inputLength (Nat.clog 2 (denominator + 1)))
      (by
        apply bits_of_member
        simp [denominatorExponentStageBits])
  exact run_linkPrograms hpositive hlength hstage1
    (run_linkPrograms hpositive hlength hstage2
      (run_linkPrograms hpositive hlength hstage3 hstage4))

/-! ## §6 The assembled exponent

The two halves are computed from the same request word by one duplication and
two count-preserving calls, and added. -/

private def exponentTail3 (denominatorExponent : NPOracleProgram) :
    NPOracleProgram :=
  linkPrograms (preserveRightProgram denominatorExponent) addPairProgram

private def exponentTail2 (denominatorExponent : NPOracleProgram) :
    NPOracleProgram :=
  linkPrograms swapPairProgram (exponentTail3 denominatorExponent)

private def exponentTail1 (rankExponent denominatorExponent : NPOracleProgram) :
    NPOracleProgram :=
  linkPrograms (preserveRightProgram rankExponent)
    (exponentTail2 denominatorExponent)

/-- **The row-count exponent program**, parametric in its two halves. -/
def rowCountExponentProgram
    (rankExponent denominatorExponent : NPOracleProgram) : NPOracleProgram :=
  linkPrograms duplicateProgram (exponentTail1 rankExponent denominatorExponent)

private theorem exponentTail3_oracleFree
    (denominatorExponent : NPOracleProgram)
    (hdenominator : OracleFree denominatorExponent) :
    OracleFree (exponentTail3 denominatorExponent) :=
  oracleFree_linkPrograms (preserveRightProgram_oracleFree _ hdenominator)
    addPairProgram_oracleFree

private theorem exponentTail2_oracleFree
    (denominatorExponent : NPOracleProgram)
    (hdenominator : OracleFree denominatorExponent) :
    OracleFree (exponentTail2 denominatorExponent) :=
  oracleFree_linkPrograms swapPairProgram_oracleFree
    (exponentTail3_oracleFree denominatorExponent hdenominator)

private theorem exponentTail1_oracleFree
    (rankExponent denominatorExponent : NPOracleProgram)
    (hrank : OracleFree rankExponent)
    (hdenominator : OracleFree denominatorExponent) :
    OracleFree (exponentTail1 rankExponent denominatorExponent) :=
  oracleFree_linkPrograms (preserveRightProgram_oracleFree _ hrank)
    (exponentTail2_oracleFree denominatorExponent hdenominator)

theorem rowCountExponentProgram_oracleFree
    (rankExponent denominatorExponent : NPOracleProgram)
    (hrank : OracleFree rankExponent)
    (hdenominator : OracleFree denominatorExponent) :
    OracleFree (rowCountExponentProgram rankExponent denominatorExponent) :=
  oracleFree_linkPrograms duplicateProgram_oracleFree
    (exponentTail1_oracleFree rankExponent denominatorExponent hrank
      hdenominator)

private def exponentTail3Fuel (denominatorFuel : ℕ) : ℕ :=
  linkFuel addPairProgram (preserveRightFuel denominatorFuel) 4

private def exponentTail2Fuel
    (denominatorExponent : NPOracleProgram) (denominatorFuel : ℕ) : ℕ :=
  linkFuel (exponentTail3 denominatorExponent) 4
    (exponentTail3Fuel denominatorFuel)

private def exponentTail1Fuel
    (denominatorExponent : NPOracleProgram) (rankFuel denominatorFuel : ℕ) :
    ℕ :=
  linkFuel (exponentTail2 denominatorExponent) (preserveRightFuel rankFuel)
    (exponentTail2Fuel denominatorExponent denominatorFuel)

def rowCountExponentFuel
    (rankExponent denominatorExponent : NPOracleProgram)
    (rankFuel denominatorFuel : ℕ) : ℕ :=
  linkFuel (exponentTail1 rankExponent denominatorExponent) 2
    (exponentTail1Fuel denominatorExponent rankFuel denominatorFuel)

def rowCountExponentStageBits
    (rankBits denominatorBits inputLength envelope rankPart
      denominatorPart : ℕ) : List ℕ :=
  [ 1
  , natBitLength inputLength
  , duplicateBits envelope
  , preserveRightBits rankBits envelope envelope rankPart
  , swapPairBits rankPart envelope
  , preserveRightBits denominatorBits envelope rankPart denominatorPart
  , addPairBits denominatorPart rankPart
  ]

def rowCountExponentBits
    (rankBits denominatorBits inputLength envelope rankPart
      denominatorPart : ℕ) : ℕ :=
  (rowCountExponentStageBits rankBits denominatorBits inputLength envelope
    rankPart denominatorPart).foldr max 1

/-- **The row-count exponent, executed**, from exact runs of its two halves. -/
theorem run_rowCountExponentProgram
    (rankExponent denominatorExponent : NPOracleProgram)
    (inputLength envelope rankPart denominatorPart rankBits rankFuel
      denominatorBits denominatorFuel maximumBits : ℕ)
    (hbits :
      rowCountExponentBits rankBits denominatorBits inputLength envelope
          rankPart denominatorPart ≤
        maximumBits)
    (hrank :
      runNPOracleProgram rankExponent rankBits rankFuel
          (initialNPOracleState inputLength envelope) =
        some rankPart)
    (hdenominator :
      runNPOracleProgram denominatorExponent denominatorBits denominatorFuel
          (initialNPOracleState inputLength envelope) =
        some denominatorPart) :
    runNPOracleProgram (rowCountExponentProgram rankExponent denominatorExponent)
        maximumBits
        (rowCountExponentFuel rankExponent denominatorExponent rankFuel
          denominatorFuel)
        (initialNPOracleState inputLength envelope) =
      some (rankPart + denominatorPart) := by
  have bits_of_member {value : ℕ}
      (hvalue :
        value ∈
          rowCountExponentStageBits rankBits denominatorBits inputLength
            envelope rankPart denominatorPart) :
      value ≤ maximumBits :=
    le_trans (exponent_le_foldr_max_of_mem hvalue) hbits
  have hpositive : 1 ≤ maximumBits := by
    apply bits_of_member
    simp [rowCountExponentStageBits]
  have hlength : natBitLength inputLength ≤ maximumBits := by
    apply bits_of_member
    simp [rowCountExponentStageBits]
  have hstage1 :
      runNPOracleProgram duplicateProgram maximumBits 2
          (initialNPOracleState inputLength envelope) =
        some (Nat.pair envelope envelope) :=
    run_bits_mono (run_duplicateProgram inputLength envelope)
      (by
        apply bits_of_member
        simp [rowCountExponentStageBits])
  have hstage2 :
      runNPOracleProgram (preserveRightProgram rankExponent) maximumBits
          (preserveRightFuel rankFuel)
          (initialNPOracleState inputLength (Nat.pair envelope envelope)) =
        some (Nat.pair rankPart envelope) :=
    run_bits_mono
      (run_preserveRightProgram rankExponent inputLength rankBits rankFuel
        envelope envelope rankPart hrank)
      (by
        apply bits_of_member
        simp [rowCountExponentStageBits])
  have hstage3 :
      runNPOracleProgram swapPairProgram maximumBits 4
          (initialNPOracleState inputLength (Nat.pair rankPart envelope)) =
        some (Nat.pair envelope rankPart) :=
    run_bits_mono (run_swapPairProgram inputLength rankPart envelope)
      (by
        apply bits_of_member
        simp [rowCountExponentStageBits])
  have hstage4 :
      runNPOracleProgram (preserveRightProgram denominatorExponent) maximumBits
          (preserveRightFuel denominatorFuel)
          (initialNPOracleState inputLength (Nat.pair envelope rankPart)) =
        some (Nat.pair denominatorPart rankPart) :=
    run_bits_mono
      (run_preserveRightProgram denominatorExponent inputLength denominatorBits
        denominatorFuel envelope rankPart denominatorPart hdenominator)
      (by
        apply bits_of_member
        simp [rowCountExponentStageBits])
  have hstage5 :
      runNPOracleProgram addPairProgram maximumBits 4
          (initialNPOracleState inputLength
            (Nat.pair denominatorPart rankPart)) =
        some (denominatorPart + rankPart) :=
    run_bits_mono (run_addPairProgram inputLength denominatorPart rankPart)
      (by
        apply bits_of_member
        simp [rowCountExponentStageBits])
  rw [Nat.add_comm rankPart denominatorPart]
  exact run_linkPrograms hpositive hlength hstage1
    (run_linkPrograms hpositive hlength hstage2
      (run_linkPrograms hpositive hlength hstage3
        (run_linkPrograms hpositive hlength hstage4 hstage5)))

/-! ## §7 The symmetric row-count exponent

Instantiating both halves at the symmetric family closes every stage of the
counting residual except the two pool quantities. -/

/-- **The symmetric row-count exponent program.** -/
def symmetricRowCountExponentProgram
    (populationProgram costProgram : NPOracleProgram) (accuracyExponent : ℕ) :
    NPOracleProgram :=
  rowCountExponentProgram
    (symmetricRankExponentProgram populationProgram costProgram)
    (denominatorExponentProgram
      (fourfoldListDenominatorProgram accuracyExponent))

theorem symmetricRowCountExponentProgram_oracleFree
    (populationProgram costProgram : NPOracleProgram) (accuracyExponent : ℕ)
    (hpopulation : OracleFree populationProgram)
    (hcost : OracleFree costProgram) :
    OracleFree
      (symmetricRowCountExponentProgram populationProgram costProgram
        accuracyExponent) :=
  rowCountExponentProgram_oracleFree _ _
    (symmetricRankExponentProgram_oracleFree populationProgram costProgram
      hpopulation hcost)
    (denominatorExponentProgram_oracleFree _
      (fourfoldListDenominatorProgram_oracleFree accuracyExponent))

/-- The request word the symmetric front end hands to every counting stage. -/
def symmetricEnvelopeCode
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) : ℕ :=
  fourfoldRequestEnvelopeOutput symmetricCircuitFamilyTag
    encodeNormalizedSymmetricThresholdCircuit request

/-- The symmetric list denominator at the fixed accuracy exponent. -/
def symmetricExponentDenominator
    (accuracyExponent : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) : ℕ :=
  symmetricListDenominator request
    (fixedTargetDenominator accuracyExponent request.q)

def symmetricRankExponentValue
    (liveScale : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) : ℕ :=
  doubledWalkSideBits
    (canonicalGradedRank (symmetricOccurrencePopulation request)
      (symmetricOccurrenceTouchingCost request liveScale))

def symmetricDenominatorExponentValue
    (accuracyExponent : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) : ℕ :=
  320 * Nat.clog 2 (symmetricExponentDenominator accuracyExponent request + 1)

def symmetricRowCountExponentBits
    (populationBits costBits liveScale accuracyExponent : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) : ℕ :=
  rowCountExponentBits
    (symmetricRankExponentBits populationBits costBits request.q
      (symmetricEnvelopeCode request) (symmetricOccurrencePopulation request)
      (symmetricOccurrenceTouchingCost request liveScale))
    (denominatorExponentBits
      (symmetricListDenominatorBits accuracyExponent request) request.q
      (symmetricExponentDenominator accuracyExponent request))
    request.q (symmetricEnvelopeCode request)
    (symmetricRankExponentValue liveScale request)
    (symmetricDenominatorExponentValue accuracyExponent request)

def symmetricRowCountExponentFuel
    (populationProgram costProgram : NPOracleProgram)
    (populationFuel costFuel liveScale accuracyExponent : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) : ℕ :=
  rowCountExponentFuel
    (symmetricRankExponentProgram populationProgram costProgram)
    (denominatorExponentProgram
      (fourfoldListDenominatorProgram accuracyExponent))
    (symmetricRankExponentFuel populationProgram costProgram populationFuel
      costFuel (symmetricOccurrencePopulation request)
      (symmetricOccurrenceTouchingCost request liveScale))
    (denominatorExponentFuel
      (symmetricListDenominatorFuel accuracyExponent request)
      (symmetricExponentDenominator accuracyExponent request))

private theorem symmetricRowCountExponent_eq
    (liveScale accuracyExponent : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) :
    symmetricRowCountExponent liveScale accuracyExponent request =
      symmetricRankExponentValue liveScale request +
        symmetricDenominatorExponentValue accuracyExponent request := by
  rfl

private theorem run_symmetricRankHalf
    (liveScale : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (populationProgram costProgram : NPOracleProgram)
    (populationBits populationFuel costBits costFuel : ℕ)
    (hpopulation :
      runNPOracleProgram populationProgram populationBits populationFuel
          (initialNPOracleState request.q (symmetricEnvelopeCode request)) =
        some (symmetricOccurrencePopulation request))
    (hcost :
      runNPOracleProgram costProgram costBits costFuel
          (initialNPOracleState request.q (symmetricEnvelopeCode request)) =
        some (symmetricOccurrenceTouchingCost request liveScale)) :
    runNPOracleProgram
        (symmetricRankExponentProgram populationProgram costProgram)
        (symmetricRankExponentBits populationBits costBits request.q
          (symmetricEnvelopeCode request)
          (symmetricOccurrencePopulation request)
          (symmetricOccurrenceTouchingCost request liveScale))
        (symmetricRankExponentFuel populationProgram costProgram populationFuel
          costFuel (symmetricOccurrencePopulation request)
          (symmetricOccurrenceTouchingCost request liveScale))
        (initialNPOracleState request.q (symmetricEnvelopeCode request)) =
      some (symmetricRankExponentValue liveScale request) :=
  run_symmetricRankExponentProgram populationProgram costProgram request.q
    (symmetricEnvelopeCode request) (symmetricOccurrencePopulation request)
    (symmetricOccurrenceTouchingCost request liveScale) populationBits
    populationFuel costBits costFuel
    (symmetricRankExponentBits populationBits costBits request.q
      (symmetricEnvelopeCode request) (symmetricOccurrencePopulation request)
      (symmetricOccurrenceTouchingCost request liveScale))
    (le_refl _) hpopulation hcost

private theorem run_symmetricDenominatorHalf
    (accuracyExponent : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) :
    runNPOracleProgram
        (denominatorExponentProgram
          (fourfoldListDenominatorProgram accuracyExponent))
        (denominatorExponentBits
          (symmetricListDenominatorBits accuracyExponent request) request.q
          (symmetricExponentDenominator accuracyExponent request))
        (denominatorExponentFuel
          (symmetricListDenominatorFuel accuracyExponent request)
          (symmetricExponentDenominator accuracyExponent request))
        (initialNPOracleState request.q (symmetricEnvelopeCode request)) =
      some (symmetricDenominatorExponentValue accuracyExponent request) :=
  run_denominatorExponentProgram
    (fourfoldListDenominatorProgram accuracyExponent) request.q
    (symmetricEnvelopeCode request)
    (symmetricExponentDenominator accuracyExponent request)
    (symmetricListDenominatorBits accuracyExponent request)
    (symmetricListDenominatorFuel accuracyExponent request)
    (denominatorExponentBits
      (symmetricListDenominatorBits accuracyExponent request) request.q
      (symmetricExponentDenominator accuracyExponent request))
    (le_refl _)
    (run_symmetricListDenominatorProgram accuracyExponent
      (symmetricListDenominatorBits accuracyExponent request) request
      (le_refl _))

/-- **The symmetric row-count exponent, executed from the typed envelope.**
Exactly two request-derived quantities remain link-time parameters: the
occurrence-pool population and its touching cost.  Every other stage — the
list denominator, both ceiling logarithms, the graded rank, the padded walk
side, and both dyadic scalings — is fixed here. -/
theorem run_symmetricRowCountExponentProgram
    (liveScale accuracyExponent : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (populationProgram costProgram : NPOracleProgram)
    (populationBits populationFuel costBits costFuel maximumBits : ℕ)
    (hbits :
      symmetricRowCountExponentBits populationBits costBits liveScale
          accuracyExponent request ≤
        maximumBits)
    (hpopulation :
      runNPOracleProgram populationProgram populationBits populationFuel
          (initialNPOracleState request.q (symmetricEnvelopeCode request)) =
        some (symmetricOccurrencePopulation request))
    (hcost :
      runNPOracleProgram costProgram costBits costFuel
          (initialNPOracleState request.q (symmetricEnvelopeCode request)) =
        some (symmetricOccurrenceTouchingCost request liveScale)) :
    runNPOracleProgram
        (symmetricRowCountExponentProgram populationProgram costProgram
          accuracyExponent)
        maximumBits
        (symmetricRowCountExponentFuel populationProgram costProgram
          populationFuel costFuel liveScale accuracyExponent request)
        (initialNPOracleState request.q (symmetricEnvelopeCode request)) =
      some (symmetricRowCountExponent liveScale accuracyExponent request) := by
  rw [symmetricRowCountExponent_eq]
  exact run_rowCountExponentProgram
    (symmetricRankExponentProgram populationProgram costProgram)
    (denominatorExponentProgram
      (fourfoldListDenominatorProgram accuracyExponent))
    request.q (symmetricEnvelopeCode request)
    (symmetricRankExponentValue liveScale request)
    (symmetricDenominatorExponentValue accuracyExponent request)
    (symmetricRankExponentBits populationBits costBits request.q
      (symmetricEnvelopeCode request) (symmetricOccurrencePopulation request)
      (symmetricOccurrenceTouchingCost request liveScale))
    (symmetricRankExponentFuel populationProgram costProgram populationFuel
      costFuel (symmetricOccurrencePopulation request)
      (symmetricOccurrenceTouchingCost request liveScale))
    (denominatorExponentBits
      (symmetricListDenominatorBits accuracyExponent request) request.q
      (symmetricExponentDenominator accuracyExponent request))
    (denominatorExponentFuel
      (symmetricListDenominatorFuel accuracyExponent request)
      (symmetricExponentDenominator accuracyExponent request))
    maximumBits hbits
    (run_symmetricRankHalf liveScale request populationProgram costProgram
      populationBits populationFuel costBits costFuel hpopulation hcost)
    (run_symmetricDenominatorHalf accuracyExponent request)

/-! ## §8 The symmetric counting side, closed to the pool quantities

Composing with `CanonicalSymmetricRowCountReduction` removes the exponent
parameter from the published row counter, the row-major atom counter, and the
shared aggregation program.  What remains on the counting side is exactly two
interpreter premises about the occurrence pool. -/

/-- **The published symmetric row count, executed from the pool programs.** -/
theorem run_symmetricRowCountProgram_of_pool
    (contracts : PublishedContracts) (liveScale accuracyExponent : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (populationProgram costProgram : NPOracleProgram)
    (populationBits populationFuel costBits costFuel exponentBits
      maximumBits : ℕ)
    (hlength : natBitLength request.q ≤ maximumBits)
    (hexponentBits :
      symmetricRowCountExponentBits populationBits costBits liveScale
          accuracyExponent request ≤
        exponentBits)
    (hbits :
      symmetricRowCountBits exponentBits
          (symmetricRowCountExponent liveScale accuracyExponent request) ≤
        maximumBits)
    (hpopulation :
      runNPOracleProgram populationProgram populationBits populationFuel
          (initialNPOracleState request.q (symmetricEnvelopeCode request)) =
        some (symmetricOccurrencePopulation request))
    (hcost :
      runNPOracleProgram costProgram costBits costFuel
          (initialNPOracleState request.q (symmetricEnvelopeCode request)) =
        some (symmetricOccurrenceTouchingCost request liveScale)) :
    runNPOracleProgram
        (symmetricRowCountProgram
          (symmetricRowCountExponentProgram populationProgram costProgram
            accuracyExponent))
        maximumBits
        (symmetricRowCountFuel
          (symmetricRowCountExponentFuel populationProgram costProgram
            populationFuel costFuel liveScale accuracyExponent request)
          (symmetricRowCountExponent liveScale accuracyExponent request))
        (initialNPOracleState request.q (symmetricEnvelopeCode request)) =
      some
        ((publishedSymmetricRows contracts liveScale accuracyExponent).rowCount
          request) :=
  run_symmetricRowCountProgram contracts liveScale accuracyExponent request
    (symmetricRowCountExponentProgram populationProgram costProgram
      accuracyExponent)
    exponentBits
    (symmetricRowCountExponentFuel populationProgram costProgram populationFuel
      costFuel liveScale accuracyExponent request)
    maximumBits hlength hbits
    (run_symmetricRowCountExponentProgram liveScale accuracyExponent request
      populationProgram costProgram populationBits populationFuel costBits
      costFuel exponentBits hexponentBits hpopulation hcost)

/-- **The discharged `hcount` premise of the symmetric aggregation program,
reduced to the two occurrence-pool quantities.** -/
theorem run_symmetricFourfoldAtomCountProgram_of_pool
    (contracts : PublishedContracts) (liveScale accuracyExponent : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (populationProgram costProgram : NPOracleProgram)
    (populationBits populationFuel costBits costFuel exponentBits countBits
      maximumBits : ℕ)
    (hlength : natBitLength request.q ≤ countBits)
    (hexponentBits :
      symmetricRowCountExponentBits populationBits costBits liveScale
          accuracyExponent request ≤
        exponentBits)
    (hrowCountBits :
      symmetricRowCountBits exponentBits
          (symmetricRowCountExponent liveScale accuracyExponent request) ≤
        countBits)
    (hbits :
      fourfoldRangeAtomCountBits countBits request.q
          ((publishedSymmetricRows contracts liveScale
            accuracyExponent).rowCount request) ≤
        maximumBits)
    (hpopulation :
      runNPOracleProgram populationProgram populationBits populationFuel
          (initialNPOracleState request.q (symmetricEnvelopeCode request)) =
        some (symmetricOccurrencePopulation request))
    (hcost :
      runNPOracleProgram costProgram costBits costFuel
          (initialNPOracleState request.q (symmetricEnvelopeCode request)) =
        some (symmetricOccurrenceTouchingCost request liveScale)) :
    runNPOracleProgram
        (symmetricFourfoldAtomCountProgram
          (symmetricRowCountExponentProgram populationProgram costProgram
            accuracyExponent))
        maximumBits
        (fourfoldRangeAtomCountFuel request.q
          (symmetricRowCountFuel
            (symmetricRowCountExponentFuel populationProgram costProgram
              populationFuel costFuel liveScale accuracyExponent request)
            (symmetricRowCountExponent liveScale accuracyExponent request)))
        (initialNPOracleState request.q (symmetricEnvelopeCode request)) =
      some
        (FourfoldRangeAggregationComposition.fourfoldRangeAtomCount
          (publishedSymmetricRows contracts liveScale accuracyExponent)
          request) :=
  run_symmetricFourfoldAtomCountProgram_of_exponent contracts liveScale
    accuracyExponent request
    (symmetricRowCountExponentProgram populationProgram costProgram
      accuracyExponent)
    exponentBits
    (symmetricRowCountExponentFuel populationProgram costProgram populationFuel
      costFuel liveScale accuracyExponent request)
    countBits maximumBits hlength hrowCountBits hbits
    (run_symmetricRowCountExponentProgram liveScale accuracyExponent request
      populationProgram costProgram populationBits populationFuel costBits
      costFuel exponentBits hexponentBits hpopulation hcost)

/-- **The artifact's symmetric execution field, counting side reduced to the
occurrence pool.**  `run_sharedFourfoldAggregationProgram_symmetric_of_exponent`
still carried one exponent program with an exact interpreter premise.  Here that
premise is replaced by the two pool quantities: no counting stage between the
typed envelope and the published ratio component takes a semantic argument, a
callback, or a fuel argument. -/
theorem run_sharedFourfoldAggregationProgram_symmetric_of_pool
    (contracts : PublishedContracts) (liveScale accuracyExponent : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (populationProgram costProgram rowEvaluator : NPOracleProgram)
    (maximumBits calleeBits atomCountBits rowCountBits exponentBits
      populationBits populationFuel costBits costFuel : ℕ)
    (evaluatorFuel : ℕ → ℕ)
    (hpositive : 1 ≤ maximumBits)
    (hlength : natBitLength request.q ≤ maximumBits)
    (hentryBits :
      CanonicalFourfoldRowTailProgram.symmetricFourfoldEntryBits contracts
          liveScale accuracyExponent request atomCountBits ≤
        maximumBits)
    (hcomponentBits :
      CanonicalFourfoldRowTailProgram.symmetricFourfoldRangeComponentBits
          contracts liveScale accuracyExponent request calleeBits ≤
        maximumBits)
    (hcalleePositive : 1 ≤ calleeBits)
    (hcalleeLength : natBitLength request.q ≤ calleeBits)
    (hbottomBits : ∀ flat : ℕ,
      flat <
        FourfoldRangeAggregationComposition.fourfoldRangeAtomCount
          (publishedSymmetricRows contracts liveScale accuracyExponent)
          request →
      CanonicalFourfoldRowEvaluationProgram.symmetricFourfoldRangeBottomBits
          (selectedExactDecompositionAlgorithm contracts) request flat
          (FourfoldRangeAggregationComposition.fourfoldRangeDenominatorTail
            (publishedSymmetricRows contracts liveScale accuracyExponent)
            request) ≤
        calleeBits)
    (hrepackBits : ∀ (rowIndex : ℕ) (input : BitInput request.q),
      CanonicalFourfoldRowTailProgram.symmetricFourfoldRowTailBits
          (selectedExactDecompositionAlgorithm contracts) request rowIndex
          input ≤
        calleeBits)
    (hevaluator : ∀ (rowIndex : ℕ) (input : BitInput request.q),
      runNPOracleProgram rowEvaluator calleeBits
          (evaluatorFuel
            (CanonicalFourfoldRowTailProgram.symmetricFourfoldRowTailHandoff
              (selectedExactDecompositionAlgorithm contracts) request
              rowIndex input))
          (initialNPOracleState request.q
            (CanonicalFourfoldRowTailProgram.symmetricFourfoldRowTailHandoff
              (selectedExactDecompositionAlgorithm contracts) request
              rowIndex input)) =
        some
          (boolCode
            (CanonicalFourfoldRowProgram.evaluateCanonicalFourfoldRow
              (selectedExactDecompositionAlgorithm contracts) liveScale
              accuracyExponent
              (CanonicalFourfoldRowProgram.symmetricFourfoldRowRequest request
                rowIndex input))))
    (hrowCountLength : natBitLength request.q ≤ rowCountBits)
    (hrowCountBits :
      symmetricRowCountBits exponentBits
          (symmetricRowCountExponent liveScale accuracyExponent request) ≤
        rowCountBits)
    (hatomCountBits :
      fourfoldRangeAtomCountBits rowCountBits request.q
          ((publishedSymmetricRows contracts liveScale
            accuracyExponent).rowCount request) ≤
        atomCountBits)
    (hexponentBits :
      symmetricRowCountExponentBits populationBits costBits liveScale
          accuracyExponent request ≤
        exponentBits)
    (hpopulation :
      runNPOracleProgram populationProgram populationBits populationFuel
          (initialNPOracleState request.q (symmetricEnvelopeCode request)) =
        some (symmetricOccurrencePopulation request))
    (hcost :
      runNPOracleProgram costProgram costBits costFuel
          (initialNPOracleState request.q (symmetricEnvelopeCode request)) =
        some (symmetricOccurrenceTouchingCost request liveScale)) :
    runNPOracleProgram
        (CanonicalFourfoldRowTailProgram.sharedFourfoldAggregationProgram
          (selectedExactDecompositionAlgorithm contracts)
          (symmetricFourfoldAtomCountProgram
            (symmetricRowCountExponentProgram populationProgram costProgram
              accuracyExponent))
          rowEvaluator)
        maximumBits
        (CanonicalFourfoldRowTailProgram.symmetricSharedFourfoldAggregationFuel
          contracts liveScale accuracyExponent request
          (symmetricFourfoldAtomCountProgram
            (symmetricRowCountExponentProgram populationProgram costProgram
              accuracyExponent))
          rowEvaluator
          (fourfoldRangeAtomCountFuel request.q
            (symmetricRowCountFuel
              (symmetricRowCountExponentFuel populationProgram costProgram
                populationFuel costFuel liveScale accuracyExponent request)
              (symmetricRowCountExponent liveScale accuracyExponent request)))
          evaluatorFuel)
        (initialNPOracleState request.q (symmetricEnvelopeCode request)) =
      some
        (symmetricRatioComponentCode
          (publishedSymmetricRows contracts liveScale accuracyExponent)
          request) :=
  run_sharedFourfoldAggregationProgram_symmetric_of_exponent contracts liveScale
    accuracyExponent request
    (symmetricRowCountExponentProgram populationProgram costProgram
      accuracyExponent)
    rowEvaluator maximumBits calleeBits atomCountBits rowCountBits exponentBits
    (symmetricRowCountExponentFuel populationProgram costProgram populationFuel
      costFuel liveScale accuracyExponent request)
    evaluatorFuel hpositive hlength hentryBits hcomponentBits hcalleePositive
    hcalleeLength hbottomBits hrepackBits hevaluator hrowCountLength
    hrowCountBits hatomCountBits
    (run_symmetricRowCountExponentProgram liveScale accuracyExponent request
      populationProgram costProgram populationBits populationFuel costBits
      costFuel exponentBits hexponentBits hpopulation hcost)

/-- Bounded-row twin of
`run_sharedFourfoldAggregationProgram_symmetric_of_pool`.  The count side is
unchanged; only the row-tail and evaluator contracts are restricted to the
finite published row family. -/
theorem run_sharedFourfoldAggregationProgram_symmetric_of_pool_bounded
    (contracts : PublishedContracts) (liveScale accuracyExponent : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (populationProgram costProgram rowEvaluator : NPOracleProgram)
    (maximumBits calleeBits atomCountBits rowCountBits exponentBits
      populationBits populationFuel costBits costFuel : ℕ)
    (evaluatorFuel : ℕ → ℕ)
    (hpositive : 1 ≤ maximumBits)
    (hlength : natBitLength request.q ≤ maximumBits)
    (hentryBits :
      CanonicalFourfoldRowTailProgram.symmetricFourfoldEntryBits contracts
          liveScale accuracyExponent request atomCountBits ≤
        maximumBits)
    (hcomponentBits :
      CanonicalFourfoldRowTailProgram.symmetricFourfoldRangeComponentBits
          contracts liveScale accuracyExponent request calleeBits ≤
        maximumBits)
    (hcalleePositive : 1 ≤ calleeBits)
    (hcalleeLength : natBitLength request.q ≤ calleeBits)
    (hbottomBits : ∀ flat : ℕ,
      flat <
        FourfoldRangeAggregationComposition.fourfoldRangeAtomCount
          (publishedSymmetricRows contracts liveScale accuracyExponent)
          request →
      CanonicalFourfoldRowEvaluationProgram.symmetricFourfoldRangeBottomBits
          (selectedExactDecompositionAlgorithm contracts) request flat
          (FourfoldRangeAggregationComposition.fourfoldRangeDenominatorTail
            (publishedSymmetricRows contracts liveScale accuracyExponent)
            request) ≤
        calleeBits)
    (hrepackBits : ∀ (rowIndex : ℕ) (input : BitInput request.q),
      rowIndex <
          (publishedSymmetricRows contracts liveScale
            accuracyExponent).rowCount request →
      CanonicalFourfoldRowTailProgram.symmetricFourfoldRowTailBits
          (selectedExactDecompositionAlgorithm contracts) request rowIndex
          input ≤
        calleeBits)
    (hevaluator : ∀ (rowIndex : ℕ) (input : BitInput request.q),
      rowIndex <
          (publishedSymmetricRows contracts liveScale
            accuracyExponent).rowCount request →
      runNPOracleProgram rowEvaluator calleeBits
          (evaluatorFuel
            (CanonicalFourfoldRowTailProgram.symmetricFourfoldRowTailHandoff
              (selectedExactDecompositionAlgorithm contracts) request
              rowIndex input))
          (initialNPOracleState request.q
            (CanonicalFourfoldRowTailProgram.symmetricFourfoldRowTailHandoff
              (selectedExactDecompositionAlgorithm contracts) request
              rowIndex input)) =
        some
          (boolCode
            (CanonicalFourfoldRowProgram.evaluateCanonicalFourfoldRow
              (selectedExactDecompositionAlgorithm contracts) liveScale
              accuracyExponent
              (CanonicalFourfoldRowProgram.symmetricFourfoldRowRequest request
                rowIndex input))))
    (hrowCountLength : natBitLength request.q ≤ rowCountBits)
    (hrowCountBits :
      symmetricRowCountBits exponentBits
          (symmetricRowCountExponent liveScale accuracyExponent request) ≤
        rowCountBits)
    (hatomCountBits :
      fourfoldRangeAtomCountBits rowCountBits request.q
          ((publishedSymmetricRows contracts liveScale
            accuracyExponent).rowCount request) ≤
        atomCountBits)
    (hexponentBits :
      symmetricRowCountExponentBits populationBits costBits liveScale
          accuracyExponent request ≤
        exponentBits)
    (hpopulation :
      runNPOracleProgram populationProgram populationBits populationFuel
          (initialNPOracleState request.q (symmetricEnvelopeCode request)) =
        some (symmetricOccurrencePopulation request))
    (hcost :
      runNPOracleProgram costProgram costBits costFuel
          (initialNPOracleState request.q (symmetricEnvelopeCode request)) =
        some (symmetricOccurrenceTouchingCost request liveScale)) :
    runNPOracleProgram
        (CanonicalFourfoldRowTailProgram.sharedFourfoldAggregationProgram
          (selectedExactDecompositionAlgorithm contracts)
          (symmetricFourfoldAtomCountProgram
            (symmetricRowCountExponentProgram populationProgram costProgram
              accuracyExponent))
          rowEvaluator)
        maximumBits
        (CanonicalFourfoldRowTailProgram.symmetricSharedFourfoldAggregationFuel
          contracts liveScale accuracyExponent request
          (symmetricFourfoldAtomCountProgram
            (symmetricRowCountExponentProgram populationProgram costProgram
              accuracyExponent))
          rowEvaluator
          (fourfoldRangeAtomCountFuel request.q
            (symmetricRowCountFuel
              (symmetricRowCountExponentFuel populationProgram costProgram
                populationFuel costFuel liveScale accuracyExponent request)
              (symmetricRowCountExponent liveScale accuracyExponent request)))
          evaluatorFuel)
        (initialNPOracleState request.q (symmetricEnvelopeCode request)) =
      some
        (symmetricRatioComponentCode
          (publishedSymmetricRows contracts liveScale accuracyExponent)
          request) :=
  CanonicalFourfoldRowTailProgram.run_sharedFourfoldAggregationProgram_symmetric_bounded
    contracts liveScale accuracyExponent request
    (symmetricFourfoldAtomCountProgram
      (symmetricRowCountExponentProgram populationProgram costProgram
        accuracyExponent))
    rowEvaluator maximumBits calleeBits atomCountBits
    (fourfoldRangeAtomCountFuel request.q
      (symmetricRowCountFuel
        (symmetricRowCountExponentFuel populationProgram costProgram
          populationFuel costFuel liveScale accuracyExponent request)
        (symmetricRowCountExponent liveScale accuracyExponent request)))
    evaluatorFuel hpositive hlength hentryBits hcomponentBits hcalleePositive
    hcalleeLength hbottomBits hrepackBits hevaluator
    (run_symmetricFourfoldAtomCountProgram_of_pool contracts liveScale
      accuracyExponent request populationProgram costProgram populationBits
      populationFuel costBits costFuel exponentBits rowCountBits atomCountBits
      hrowCountLength hexponentBits hrowCountBits hatomCountBits hpopulation
      hcost)

end NearCubicWires.CanonicalRowCountExponentProgram
