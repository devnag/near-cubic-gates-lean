import Proof.MachineModel.CanonicalBitSerialMulProgram
import Proof.MachineModel.CanonicalSymmetricSupportMaskProgram

/-!
# The symmetric occurrence pool's touching cost, executed from the envelope

This module closes `CanonicalOccurrencePopulationProgram` §6.  Every ingredient
is already compiled:

* `CanonicalSymmetricSupportMaskProgram` turns the typed envelope into the
  pool's `coordinateMask` list;
* `CanonicalTouchingSweepRoundProgram.run_touchingSweepSelectProgram` runs the
  whole greedy conditional-expectation sweep on that list;
* `CanonicalTouchingSweepRoundProgram.run_roundBroadcast` builds one census
  request tree from a selection mask;
* `CanonicalConditionalTouchProgram.run_touchingCostProgram` scores it at step
  budget zero, which is the touching cost itself.

What is left is the sweep's *live count*.  It is
`min q (liveScale * Nat.clog 2 (q + 2))`, so the canonical ceiling logarithm and
the canonical bit-serial multiplication compute it from the preserved input
length alone; the saturating double subtraction `q - (q - x)` is the minimum.

The sweep's reachable carried states are bounded by one closed numeral: a
carried state is `pair context (pair mask stepCount)` with `mask < 2 ^ q` and
`stepCount ≤ liveCount`, so all four of the sweep controller's width premises
follow from a single envelope.  Only the round callee's own width premise stays
quantified, because it depends on the round's selection set through the census
trees.
-/

open Finset

namespace NearCubicWires.CanonicalSymmetricTouchingCostProgram

open NearCubicWires
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBitSerialMulProgram
open NearCubicWires.CanonicalConditionalTouchProgram
open NearCubicWires.CanonicalFourfoldRowCountFormula
open NearCubicWires.CanonicalFourfoldRowCountProgram
open NearCubicWires.CanonicalNatCeilLogProgram
open NearCubicWires.CanonicalOccurrencePopulationProgram
open NearCubicWires.CanonicalRoundCall
open NearCubicWires.CanonicalRowCountExponentProgram
open NearCubicWires.CanonicalSymmetricRowCountReduction
open NearCubicWires.CanonicalSymmetricSupportMaskProgram
open NearCubicWires.CanonicalTouchingSweepProgram
open NearCubicWires.CanonicalTouchingSweepRoundProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.SharedNormalizedEstimatorProgram
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierTouching
open NearCubicWires.VerifiedLinker

private theorem bits_of_le {value bound maximumBits : ℕ}
    (hvalue : value ≤ bound) (hbits : natBitLength bound ≤ maximumBits) :
    natBitLength value ≤ maximumBits :=
  (natBitLength_mono hvalue).trans hbits

private theorem le_foldr_max_of_mem
    {value base : ℕ} {values : List ℕ} (hvalue : value ∈ values) :
    value ≤ values.foldr max base := by
  induction values with
  | nil => simp at hvalue
  | cons head tail inductionHypothesis =>
      rcases List.mem_cons.mp hvalue with rfl | hvalue
      · exact Nat.le_max_left _ _
      · exact (inductionHypothesis hvalue).trans (Nat.le_max_right _ _)

private theorem pair_le_pair_left (right : ℕ) {left bound : ℕ}
    (hleft : left ≤ bound) : Nat.pair left right ≤ Nat.pair bound right := by
  rcases Nat.eq_or_lt_of_le hleft with hequal | hstrict
  · rw [hequal]
  · exact (Nat.pair_lt_pair_left right hstrict).le

private theorem pair_le_pair_right (left : ℕ) {right bound : ℕ}
    (hright : right ≤ bound) : Nat.pair left right ≤ Nat.pair left bound := by
  rcases Nat.eq_or_lt_of_le hright with hequal | hstrict
  · rw [hequal]
  · exact (Nat.pair_lt_pair_right left hstrict).le

private theorem pair_le_pair {left right leftBound rightBound : ℕ}
    (hleft : left ≤ leftBound) (hright : right ≤ rightBound) :
    Nat.pair left right ≤ Nat.pair leftBound rightBound :=
  (pair_le_pair_left right hleft).trans (pair_le_pair_right leftBound hright)

/-! ## §1 Three fixed arithmetic stages -/

/-- Copy the preserved input length and add the canonical logarithm offset. -/
def widthOffsetProgram : NPOracleProgram :=
  [ .copy 1 0 1
  , .increment 0 2
  , .increment 0 3
  , .halt 0
  ]

@[simp] theorem widthOffsetProgram_oracleFree :
    OracleFree widthOffsetProgram := by
  rfl

def widthOffsetBits (width : ℕ) : ℕ := natBitLength (width + 2)

theorem run_widthOffsetProgram (width code maximumBits : ℕ)
    (hbits : widthOffsetBits width ≤ maximumBits) :
    runNPOracleProgram widthOffsetProgram maximumBits 4
        (initialNPOracleState width code) =
      some (width + 2) := by
  have houtputBits : natBitLength (width + 2) ≤ maximumBits := hbits
  have hwidthBits : natBitLength width ≤ maximumBits :=
    bits_of_le (by omega) houtputBits
  have hsuccessorBits : natBitLength (width + 1) ≤ maximumBits :=
    bits_of_le (by omega) houtputBits
  rw [show (4 : ℕ) = 0 + 1 + 1 + 1 + 1 by omega]
  rw [run_copy_instruction (value := width) (by rfl) rfl
    (by simp [initialNPOracleState]) hwidthBits]
  rw [run_increment_instruction (value := width + 1) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hsuccessorBits]
  rw [run_increment_instruction (value := width + 2) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtputBits]
  exact run_halt_instruction (fuel := 0) (value := width + 2) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtputBits

/-- Attach a fixed left component to the register value. -/
def scalePairProgram (scale : ℕ) : NPOracleProgram :=
  [ .set 2 scale 1
  , .pair 2 0 0 2
  , .halt 0
  ]

theorem scalePairProgram_oracleFree (scale : ℕ) :
    OracleFree (scalePairProgram scale) := by
  rfl

def scalePairBits (scale value : ℕ) : ℕ := natBitLength (Nat.pair scale value)

theorem run_scalePairProgram (inputLength scale value maximumBits : ℕ)
    (hbits : scalePairBits scale value ≤ maximumBits) :
    runNPOracleProgram (scalePairProgram scale) maximumBits 3
        (initialNPOracleState inputLength value) =
      some (Nat.pair scale value) := by
  have houtputBits : natBitLength (Nat.pair scale value) ≤ maximumBits := hbits
  have hscaleBits : natBitLength scale ≤ maximumBits :=
    bits_of_le (Nat.left_le_pair scale value) houtputBits
  rw [show (3 : ℕ) = 0 + 1 + 1 + 1 by omega]
  rw [run_set_instruction (value := scale) (by rfl) rfl hscaleBits]
  rw [run_pair_instruction (value := Nat.pair scale value) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    houtputBits]
  exact run_halt_instruction (fuel := 0) (value := Nat.pair scale value)
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump])
    houtputBits

/-- The minimum of the preserved input length and the register value, as the
machine's only saturating double subtraction. -/
def minWidthProgram : NPOracleProgram :=
  [ .subtract 1 0 2 1
  , .subtract 1 2 0 2
  , .halt 0
  ]

@[simp] theorem minWidthProgram_oracleFree : OracleFree minWidthProgram := by
  rfl

def minWidthBits (width : ℕ) : ℕ := natBitLength width

theorem run_minWidthProgram (width value maximumBits : ℕ)
    (hbits : minWidthBits width ≤ maximumBits) :
    runNPOracleProgram minWidthProgram maximumBits 3
        (initialNPOracleState width value) =
      some (min width value) := by
  have hwidthBits : natBitLength width ≤ maximumBits := hbits
  have hresidualBits : natBitLength (width - value) ≤ maximumBits :=
    bits_of_le (Nat.sub_le width value) hwidthBits
  have hminimumBits : natBitLength (min width value) ≤ maximumBits :=
    bits_of_le (min_le_left width value) hwidthBits
  have hlengthRegister :
      (((initialNPOracleState width value).write 2 (width - value)).jump
        1).registers 1 = width := by
    simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump]
  have hresidualRegister :
      (((initialNPOracleState width value).write 2 (width - value)).jump
        1).registers 2 = width - value := by
    simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump]
  rw [show (3 : ℕ) = 0 + 1 + 1 + 1 by omega]
  rw [run_subtract_instruction (value := width - value) (by rfl) rfl
    (by simp [initialNPOracleState]) hresidualBits]
  rw [run_subtract_instruction (value := min width value) (by rfl) rfl
    (by rw [hlengthRegister, hresidualRegister]; omega) hminimumBits]
  exact run_halt_instruction (fuel := 0) (value := min width value) (by rfl)
    rfl (by simp [NPOracleState.write, NPOracleState.jump]) hminimumBits

/-! ## §2 The sweep's live count -/

private def liveCountTailFour : NPOracleProgram :=
  linkPrograms bitSerialMulProgram minWidthProgram

private def liveCountTailThree (liveScale : ℕ) : NPOracleProgram :=
  linkPrograms (scalePairProgram liveScale) liveCountTailFour

private def liveCountTailTwo (liveScale : ℕ) : NPOracleProgram :=
  linkPrograms binaryNatCeilLogProgram (liveCountTailThree liveScale)

/-- **The live-count program.**  The deterministic live budget
`normalizedLiveCount q liveScale` from the preserved input length alone. -/
def liveCountProgram (liveScale : ℕ) : NPOracleProgram :=
  linkPrograms widthOffsetProgram (liveCountTailTwo liveScale)

theorem liveCountProgram_oracleFree (liveScale : ℕ) :
    OracleFree (liveCountProgram liveScale) :=
  oracleFree_linkPrograms widthOffsetProgram_oracleFree
    (oracleFree_linkPrograms binaryNatCeilLogProgram_oracleFree
      (oracleFree_linkPrograms (scalePairProgram_oracleFree liveScale)
        (oracleFree_linkPrograms bitSerialMulProgram_oracleFree
          minWidthProgram_oracleFree)))

def liveCountFuel (liveScale width : ℕ) : ℕ :=
  linkFuel (liveCountTailTwo liveScale) 4
    (linkFuel (liveCountTailThree liveScale) (binaryNatCeilLogFuel (width + 2))
      (linkFuel liveCountTailFour 3
        (linkFuel minWidthProgram (bitSerialMulFuel (logScale width)) 3)))

def liveCountStageBits (liveScale width : ℕ) : List ℕ :=
  [ 1
  , natBitLength width
  , widthOffsetBits width
  , binaryNatCeilLogBits (width + 2)
  , scalePairBits liveScale (logScale width)
  , bitSerialMulBits width liveScale (logScale width)
  , minWidthBits width
  ]

def liveCountBits (liveScale width : ℕ) : ℕ :=
  (liveCountStageBits liveScale width).foldr max 1

/-- **The live count, executed.** -/
theorem run_liveCountProgram (liveScale width code maximumBits : ℕ)
    (hbits : liveCountBits liveScale width ≤ maximumBits) :
    runNPOracleProgram (liveCountProgram liveScale) maximumBits
        (liveCountFuel liveScale width)
        (initialNPOracleState width code) =
      some (normalizedLiveCount width liveScale) := by
  have bits_of_member {value : ℕ}
      (hvalue : value ∈ liveCountStageBits liveScale width) :
      value ≤ maximumBits :=
    le_trans (le_foldr_max_of_mem hvalue) hbits
  have hpositive : 1 ≤ maximumBits := by
    apply bits_of_member
    simp [liveCountStageBits]
  have hlength : natBitLength width ≤ maximumBits := by
    apply bits_of_member
    simp [liveCountStageBits]
  have hoffsetBits : widthOffsetBits width ≤ maximumBits := by
    apply bits_of_member
    simp [liveCountStageBits]
  have hlogBits : binaryNatCeilLogBits (width + 2) ≤ maximumBits := by
    apply bits_of_member
    simp [liveCountStageBits]
  have hscaleBits : scalePairBits liveScale (logScale width) ≤ maximumBits := by
    apply bits_of_member
    simp [liveCountStageBits]
  have hproductBits :
      bitSerialMulBits width liveScale (logScale width) ≤ maximumBits := by
    apply bits_of_member
    simp [liveCountStageBits]
  have hminimumBits : minWidthBits width ≤ maximumBits := by
    apply bits_of_member
    simp [liveCountStageBits]
  have hstageOne :
      runNPOracleProgram widthOffsetProgram maximumBits 4
          (initialNPOracleState width code) =
        some (width + 2) :=
    run_widthOffsetProgram width code maximumBits hoffsetBits
  have hstageTwo :
      runNPOracleProgram binaryNatCeilLogProgram maximumBits
          (binaryNatCeilLogFuel (width + 2))
          (initialNPOracleState width (width + 2)) =
        some (logScale width) :=
    run_binaryNatCeilLogProgram width (width + 2) maximumBits hlogBits
  have hstageThree :
      runNPOracleProgram (scalePairProgram liveScale) maximumBits 3
          (initialNPOracleState width (logScale width)) =
        some (Nat.pair liveScale (logScale width)) :=
    run_scalePairProgram width liveScale (logScale width) maximumBits hscaleBits
  have hstageFour :
      runNPOracleProgram bitSerialMulProgram maximumBits
          (bitSerialMulFuel (logScale width))
          (initialNPOracleState width
            (Nat.pair liveScale (logScale width))) =
        some (liveScale * logScale width) :=
    run_bits_mono
      (run_bitSerialMulProgram width liveScale (logScale width)) hproductBits
  have hstageFive :
      runNPOracleProgram minWidthProgram maximumBits 3
          (initialNPOracleState width (liveScale * logScale width)) =
        some (normalizedLiveCount width liveScale) :=
    run_minWidthProgram width (liveScale * logScale width) maximumBits
      hminimumBits
  exact run_linkPrograms hpositive hlength hstageOne
    (run_linkPrograms hpositive hlength hstageTwo
      (run_linkPrograms hpositive hlength hstageThree
        (run_linkPrograms hpositive hlength hstageFour hstageFive)))

/-! ## §3 The sweep's two framing stages -/

/-- Build the counted round call's public input from the live count beside the
pool's support-mask tree. -/
def roundInputProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .set 4 0 3
  , .pair 4 2 5 4
  , .pair 1 3 6 5
  , .pair 6 5 7 6
  , .pair 1 7 0 7
  , .halt 0
  ]

@[simp] theorem roundInputProgram_oracleFree :
    OracleFree roundInputProgram := by
  rfl

def roundInputOutput (width masksTree liveCount : ℕ) : ℕ :=
  roundCallInput width
    (sweepCode (Nat.pair width masksTree) 0 liveCount)

def roundInputBits (width masksTree liveCount : ℕ) : ℕ :=
  max (natBitLength (Nat.pair liveCount masksTree))
    (natBitLength (roundInputOutput width masksTree liveCount))

theorem run_roundInputProgram (width masksTree liveCount maximumBits : ℕ)
    (hbits : roundInputBits width masksTree liveCount ≤ maximumBits) :
    runNPOracleProgram roundInputProgram maximumBits 8
        (initialNPOracleState width (Nat.pair liveCount masksTree)) =
      some (roundInputOutput width masksTree liveCount) := by
  have hshape :
      roundInputOutput width masksTree liveCount =
        Nat.pair width
          (Nat.pair (Nat.pair width masksTree)
            (Nat.pair 0 liveCount)) := rfl
  have hinputBits :
      natBitLength (Nat.pair liveCount masksTree) ≤ maximumBits :=
    (Nat.le_max_left _ _).trans hbits
  have houtputBits :
      natBitLength
          (Nat.pair width
            (Nat.pair (Nat.pair width masksTree) (Nat.pair 0 liveCount))) ≤
        maximumBits := by
    rw [← hshape]
    exact (Nat.le_max_right _ _).trans hbits
  have hliveCountBits : natBitLength liveCount ≤ maximumBits :=
    bits_of_le (Nat.left_le_pair _ _) hinputBits
  have hmasksBits : natBitLength masksTree ≤ maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) hinputBits
  have hzeroBits : natBitLength 0 ≤ maximumBits :=
    bits_of_le (Nat.zero_le liveCount) hliveCountBits
  have hcarriedBits :
      natBitLength
          (Nat.pair (Nat.pair width masksTree) (Nat.pair 0 liveCount)) ≤
        maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) houtputBits
  have hcontextBits : natBitLength (Nat.pair width masksTree) ≤ maximumBits :=
    bits_of_le (Nat.left_le_pair _ _) hcarriedBits
  have hstateBits : natBitLength (Nat.pair 0 liveCount) ≤ maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) hcarriedBits
  rw [show (8 : ℕ) = 0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega]
  rw [run_unpairLeft_instruction (value := liveCount) (by rfl) rfl
    (by simp [initialNPOracleState]) hliveCountBits]
  rw [run_unpairRight_instruction (value := masksTree) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hmasksBits]
  rw [run_set_instruction (value := 0) (by rfl) rfl hzeroBits]
  rw [run_pair_instruction (value := Nat.pair 0 liveCount) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hstateBits]
  rw [run_pair_instruction (value := Nat.pair width masksTree) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hcontextBits]
  rw [run_pair_instruction
    (value := Nat.pair (Nat.pair width masksTree) (Nat.pair 0 liveCount))
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump])
    hcarriedBits]
  rw [run_pair_instruction
    (value := roundInputOutput width masksTree liveCount) (by rfl) rfl
    (by
      simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump,
        hshape])
    (by rw [hshape]; exact houtputBits)]
  exact run_halt_instruction (fuel := 0)
    (value := roundInputOutput width masksTree liveCount) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    (by rw [hshape]; exact houtputBits)

/-- The touching cost's census request: the selected mask with an empty
undecided set and an exhausted step budget, beside the pool's mask tree. -/
def costRequestOutput (width masksTree selectedMask : ℕ) : ℕ :=
  Nat.pair (censusShared selectedMask 0 width 0) masksTree

/-- Rebuild the touching cost's broadcast request from the sweep's final
carried state. -/
def costRequestProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 2 5 4
  , .set 6 0 5
  , .pair 4 6 7 6
  , .pair 1 6 8 7
  , .pair 7 8 9 8
  , .pair 9 5 0 9
  , .halt 0
  ]

@[simp] theorem costRequestProgram_oracleFree :
    OracleFree costRequestProgram := by
  rfl

def costRequestBits (width masksTree selectedMask stepCount : ℕ) : ℕ :=
  max
    (natBitLength
      (sweepCode (Nat.pair width masksTree) selectedMask stepCount))
    (natBitLength (costRequestOutput width masksTree selectedMask))

theorem run_costRequestProgram
    (width masksTree selectedMask stepCount maximumBits : ℕ)
    (hbits :
      costRequestBits width masksTree selectedMask stepCount ≤ maximumBits) :
    runNPOracleProgram costRequestProgram maximumBits 10
        (initialNPOracleState width
          (sweepCode (Nat.pair width masksTree) selectedMask stepCount)) =
      some (costRequestOutput width masksTree selectedMask) := by
  have hcarried :
      sweepCode (Nat.pair width masksTree) selectedMask stepCount =
        Nat.pair (Nat.pair width masksTree)
          (Nat.pair selectedMask stepCount) := rfl
  have hshape :
      costRequestOutput width masksTree selectedMask =
        Nat.pair
          (Nat.pair (Nat.pair selectedMask 0) (Nat.pair width 0))
          masksTree := rfl
  have hinputBits :
      natBitLength
          (Nat.pair (Nat.pair width masksTree)
            (Nat.pair selectedMask stepCount)) ≤
        maximumBits := by
    rw [← hcarried]
    exact (Nat.le_max_left _ _).trans hbits
  have houtputBits :
      natBitLength
          (Nat.pair (Nat.pair (Nat.pair selectedMask 0) (Nat.pair width 0))
            masksTree) ≤
        maximumBits := by
    rw [← hshape]
    exact (Nat.le_max_right _ _).trans hbits
  have hcontextBits : natBitLength (Nat.pair width masksTree) ≤ maximumBits :=
    bits_of_le (Nat.left_le_pair _ _) hinputBits
  have hstateBits :
      natBitLength (Nat.pair selectedMask stepCount) ≤ maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) hinputBits
  have hselectedBits : natBitLength selectedMask ≤ maximumBits :=
    bits_of_le (Nat.left_le_pair _ _) hstateBits
  have hmasksBits : natBitLength masksTree ≤ maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) hcontextBits
  have hzeroBits : natBitLength 0 ≤ maximumBits :=
    bits_of_le (Nat.zero_le selectedMask) hselectedBits
  have hsharedBits :
      natBitLength
          (Nat.pair (Nat.pair selectedMask 0) (Nat.pair width 0)) ≤
        maximumBits :=
    bits_of_le (Nat.left_le_pair _ _) houtputBits
  have hselectedPairBits :
      natBitLength (Nat.pair selectedMask 0) ≤ maximumBits :=
    bits_of_le (Nat.left_le_pair _ _) hsharedBits
  have hwidthPairBits : natBitLength (Nat.pair width 0) ≤ maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) hsharedBits
  rw [show (10 : ℕ) = 0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega]
  rw [run_unpairLeft_instruction (value := Nat.pair width masksTree) (by rfl)
    rfl (by simp [initialNPOracleState, sweepCode]) hcontextBits]
  rw [run_unpairRight_instruction (value := Nat.pair selectedMask stepCount)
    (by rfl) rfl
    (by
      simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump,
        sweepCode])
    hstateBits]
  rw [run_unpairLeft_instruction (value := selectedMask) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hselectedBits]
  rw [run_unpairRight_instruction (value := masksTree) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hmasksBits]
  rw [run_set_instruction (value := 0) (by rfl) rfl hzeroBits]
  rw [run_pair_instruction (value := Nat.pair selectedMask 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hselectedPairBits]
  rw [run_pair_instruction (value := Nat.pair width 0) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hwidthPairBits]
  rw [run_pair_instruction
    (value := Nat.pair (Nat.pair selectedMask 0) (Nat.pair width 0)) (by rfl)
    rfl (by simp [NPOracleState.write, NPOracleState.jump]) hsharedBits]
  rw [run_pair_instruction
    (value := costRequestOutput width masksTree selectedMask) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hshape])
    (by rw [hshape]; exact houtputBits)]
  exact run_halt_instruction (fuel := 0)
    (value := costRequestOutput width masksTree selectedMask) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    (by rw [hshape]; exact houtputBits)

/-! ## §4 The sweep's reachable states, in one closed envelope -/

/-- Every carried state the sweep can reach is below this numeral: the fixed
context beside a full coordinate mask and the initial step budget. -/
def sweepCarriedBound (context width liveCount : ℕ) : ℕ :=
  Nat.pair context (Nat.pair (2 ^ width) liveCount)

theorem sweepStateCode_le_sweepCarriedBound {q : ℕ} (context : ℕ)
    (selected : Finset (Fin q)) {stepCount liveCount : ℕ}
    (hstepCount : stepCount ≤ liveCount) :
    sweepStateCode context (selected, stepCount) ≤
      sweepCarriedBound context q liveCount := by
  have hmask : coordinateMask selected ≤ 2 ^ q :=
    le_of_lt (coordinateMask_lt selected)
  exact pair_le_pair (Nat.le_refl context)
    (pair_le_pair hmask hstepCount)

/-! ## §5 The touching-cost program -/

private def costTailFive : NPOracleProgram :=
  linkPrograms broadcastCallProgram conditionalTouchNumeratorProgram

private def costTailFour : NPOracleProgram :=
  linkPrograms costRequestProgram costTailFive

private def costTailThree : NPOracleProgram :=
  linkPrograms (roundCallProgram touchingSweepRoundProgram) costTailFour

private def costTailTwo : NPOracleProgram :=
  linkPrograms roundInputProgram costTailThree

private def costTailOne (liveScale : ℕ) : NPOracleProgram :=
  linkPrograms (preserveRightProgram (liveCountProgram liveScale)) costTailTwo

private def costTailZero (liveScale : ℕ) : NPOracleProgram :=
  linkPrograms (scalePairProgram 0) (costTailOne liveScale)

/-- **The symmetric occurrence pool's touching-cost program.**  Read the pool's
support masks from the typed envelope, compute the live budget, run the greedy
sweep, and score the selected set at step budget zero. -/
def symmetricOccurrenceTouchingCostProgram (liveScale : ℕ) : NPOracleProgram :=
  linkPrograms symmetricOccurrenceSupportMaskProgram (costTailZero liveScale)

theorem symmetricOccurrenceTouchingCostProgram_oracleFree (liveScale : ℕ) :
    OracleFree (symmetricOccurrenceTouchingCostProgram liveScale) :=
  oracleFree_linkPrograms symmetricOccurrenceSupportMaskProgram_oracleFree
    (oracleFree_linkPrograms (scalePairProgram_oracleFree 0)
      (oracleFree_linkPrograms
        (preserveRightProgram_oracleFree (liveCountProgram liveScale)
          (liveCountProgram_oracleFree liveScale))
        (oracleFree_linkPrograms roundInputProgram_oracleFree
          (oracleFree_linkPrograms
            (roundCallProgram_oracleFree
              touchingSweepRoundProgram_oracleFree)
            (oracleFree_linkPrograms costRequestProgram_oracleFree
              (oracleFree_linkPrograms broadcastCallProgram_oracleFree
                conditionalTouchNumeratorProgram_oracleFree))))))

/-- The pool's support-mask tree, as the sweep context carries it. -/
def symmetricPoolMasksTree
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) : ℕ :=
  encodeBalancedList
    (occurrenceSupportMasks (symmetricFourfoldOccurrences request))

def symmetricOccurrenceTouchingCostFuel (liveScale : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) : ℕ :=
  linkFuel (costTailZero liveScale)
    (symmetricOccurrenceSupportMaskFuel request)
    (linkFuel (costTailOne liveScale) 3
      (linkFuel costTailTwo
        (preserveRightFuel (liveCountFuel liveScale request.q))
        (linkFuel costTailThree 8
          (linkFuel costTailFour
            (roundCallFuel touchingSweepRoundProgram
              (touchingSweepCalleeFuel (symmetricFourfoldOccurrences request))
              (touchingSweepStep (symmetricFourfoldOccurrences request))
              (sweepStateCode
                (touchingSweepContext (symmetricFourfoldOccurrences request)
                  request.q)
                ((∅ : Finset (Fin request.q)),
                  normalizedLiveCount request.q liveScale))
              request.q)
            (linkFuel costTailFive 10
              (linkFuel conditionalTouchNumeratorProgram
                (roundBroadcastFuel (symmetricFourfoldOccurrences request)
                  (normalizedLiveSet (symmetricFourfoldOccurrences request)
                    liveScale)
                  (∅ : Finset (Fin request.q)) 0)
                (conditionalTouchNumeratorFuel
                  (symmetricFourfoldOccurrences request)
                  (normalizedLiveSet (symmetricFourfoldOccurrences request)
                    liveScale)
                  (∅ : Finset (Fin request.q)) 0)))))))

def symmetricOccurrenceTouchingCostStageBits (liveScale : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) :
    List ℕ :=
  [ 1
  , natBitLength request.q
  , symmetricOccurrenceSupportMaskBits request
  , scalePairBits 0 (symmetricPoolMasksTree request)
  , preserveRightBits (liveCountBits liveScale request.q) 0
      (symmetricPoolMasksTree request)
      (normalizedLiveCount request.q liveScale)
  , roundInputBits request.q (symmetricPoolMasksTree request)
      (normalizedLiveCount request.q liveScale)
  , natBitLength
      (Nat.pair
        (sweepCarriedBound
          (touchingSweepContext (symmetricFourfoldOccurrences request)
            request.q)
          request.q (normalizedLiveCount request.q liveScale))
        request.q)
  , natBitLength
      (Nat.pair
        (Nat.pair
          (sweepCarriedBound
            (touchingSweepContext (symmetricFourfoldOccurrences request)
              request.q)
            request.q (normalizedLiveCount request.q liveScale))
          request.q)
        (sweepCarriedBound
          (touchingSweepContext (symmetricFourfoldOccurrences request)
            request.q)
          request.q (normalizedLiveCount request.q liveScale)))
  , costRequestBits request.q (symmetricPoolMasksTree request)
      (coordinateMask
        (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale))
      (sweepFold
        (occurrenceSupport (symmetricFourfoldOccurrences request))
        (List.finRange request.q)
        ((∅ : Finset (Fin request.q)),
          normalizedLiveCount request.q liveScale)).2
  , roundBroadcastBits request.q (symmetricFourfoldOccurrences request)
      (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)
      (∅ : Finset (Fin request.q)) 0
  , conditionalTouchNumeratorBits request.q
      (symmetricFourfoldOccurrences request)
      (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)
      (∅ : Finset (Fin request.q)) 0
  ]

/-- The pre-finite-envelope stage ledger, retained as a compatibility formula. -/
def symmetricOccurrenceTouchingCostLegacyBits (liveScale : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) : ℕ :=
  (symmetricOccurrenceTouchingCostStageBits liveScale request).foldr max 1

/-- The exact finite controller domain quantified by the touching sweep. -/
structure SymmetricTouchingRoundIndex (liveScale : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) where
  selected : Finset (Fin request.q)
  stepCount : Fin (normalizedLiveCount request.q liveScale + 1)
  counter : Fin request.q
  deriving Fintype

def symmetricTouchingRoundBitsAt (liveScale : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (point : SymmetricTouchingRoundIndex liveScale request) : ℕ :=
  touchingSweepRoundBits (symmetricFourfoldOccurrences request)
    point.selected point.stepCount.val
    (request.q - (point.counter.val + 1)) point.counter.val

/-- Request-local supremum of every bounded touching-round width. -/
def symmetricTouchingRoundSupBits (liveScale : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) : ℕ :=
  Finset.univ.sup (symmetricTouchingRoundBitsAt liveScale request)

/-- The public resource width honestly includes both the legacy stage ledger
and every bounded invocation of its round callee. -/
def symmetricOccurrenceTouchingCostBits (liveScale : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) : ℕ :=
  max (symmetricOccurrenceTouchingCostLegacyBits liveScale request)
    (symmetricTouchingRoundSupBits liveScale request)

theorem symmetricOccurrenceTouchingCostLegacyBits_le_bits (liveScale : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) :
    symmetricOccurrenceTouchingCostLegacyBits liveScale request ≤
      symmetricOccurrenceTouchingCostBits liveScale request := by
  exact le_max_left _ _

theorem symmetricTouchingRoundBitsAt_le_supBits (liveScale : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (point : SymmetricTouchingRoundIndex liveScale request) :
    symmetricTouchingRoundBitsAt liveScale request point ≤
      symmetricTouchingRoundSupBits liveScale request := by
  exact Finset.le_sup (s := Finset.univ)
    (f := symmetricTouchingRoundBitsAt liveScale request)
    (Finset.mem_univ point)

theorem touchingSweepRoundBits_le_symmetricOccurrenceTouchingCostBits
    (liveScale : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (selected : Finset (Fin request.q)) (stepCount counter : ℕ)
    (hcounter : counter + 1 ≤ request.q)
    (hstep : stepCount ≤ normalizedLiveCount request.q liveScale) :
    touchingSweepRoundBits (symmetricFourfoldOccurrences request) selected
        stepCount (request.q - (counter + 1)) counter ≤
      symmetricOccurrenceTouchingCostBits liveScale request := by
  let point : SymmetricTouchingRoundIndex liveScale request :=
    { selected := selected
      stepCount := ⟨stepCount, Nat.lt_succ_iff.mpr hstep⟩
      counter := ⟨counter, Nat.lt_iff_add_one_le.mpr hcounter⟩ }
  exact (symmetricTouchingRoundBitsAt_le_supBits liveScale request point).trans
    (le_max_right _ _)

set_option maxHeartbeats 2000000 in
-- Seven linked stages at one shared register width; the sweep controller's
-- four width premises come from the single carried-state envelope of §4, and
-- only the round callee's own width premise stays quantified.
/-- **The symmetric occurrence pool's touching cost, executed from the typed
envelope.**  This is `CanonicalOccurrencePopulationProgram` §6's target. -/
theorem run_symmetricOccurrenceTouchingCostProgram (liveScale : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (maximumBits : ℕ)
    (hbits :
      symmetricOccurrenceTouchingCostBits liveScale request ≤ maximumBits)
    (hroundBits : ∀ (selected : Finset (Fin request.q)) (stepCount counter : ℕ),
      counter + 1 ≤ request.q →
      stepCount ≤ normalizedLiveCount request.q liveScale →
      touchingSweepRoundBits (symmetricFourfoldOccurrences request) selected
          stepCount (request.q - (counter + 1)) counter ≤
        maximumBits) :
    runNPOracleProgram (symmetricOccurrenceTouchingCostProgram liveScale)
        maximumBits (symmetricOccurrenceTouchingCostFuel liveScale request)
        (initialNPOracleState request.q (symmetricEnvelopeCode request)) =
      some (symmetricOccurrenceTouchingCost request liveScale) := by
  have bits_of_member {value : ℕ}
      (hvalue :
        value ∈ symmetricOccurrenceTouchingCostStageBits liveScale request) :
      value ≤ maximumBits :=
    le_trans (le_foldr_max_of_mem hvalue)
      ((symmetricOccurrenceTouchingCostLegacyBits_le_bits liveScale request).trans
        hbits)
  have hpositive : 1 ≤ maximumBits := by
    apply bits_of_member
    simp [symmetricOccurrenceTouchingCostStageBits]
  have hlength : natBitLength request.q ≤ maximumBits := by
    apply bits_of_member
    simp [symmetricOccurrenceTouchingCostStageBits]
  have hmaskBits : symmetricOccurrenceSupportMaskBits request ≤ maximumBits := by
    apply bits_of_member
    simp [symmetricOccurrenceTouchingCostStageBits]
  have hscaleBits :
      scalePairBits 0 (symmetricPoolMasksTree request) ≤ maximumBits := by
    apply bits_of_member
    simp [symmetricOccurrenceTouchingCostStageBits]
  have hpreserveBits :
      preserveRightBits (liveCountBits liveScale request.q) 0
          (symmetricPoolMasksTree request)
          (normalizedLiveCount request.q liveScale) ≤
        maximumBits := by
    apply bits_of_member
    simp [symmetricOccurrenceTouchingCostStageBits]
  have hroundInputBits :
      roundInputBits request.q (symmetricPoolMasksTree request)
          (normalizedLiveCount request.q liveScale) ≤
        maximumBits := by
    apply bits_of_member
    simp [symmetricOccurrenceTouchingCostStageBits]
  have hcarriedEnvelopeBits :
      natBitLength
          (Nat.pair
            (sweepCarriedBound
              (touchingSweepContext (symmetricFourfoldOccurrences request)
                request.q)
              request.q (normalizedLiveCount request.q liveScale))
            request.q) ≤
        maximumBits := by
    apply bits_of_member
    simp [symmetricOccurrenceTouchingCostStageBits]
  have hreturnEnvelopeBits :
      natBitLength
          (Nat.pair
            (Nat.pair
              (sweepCarriedBound
                (touchingSweepContext (symmetricFourfoldOccurrences request)
                  request.q)
                request.q (normalizedLiveCount request.q liveScale))
              request.q)
            (sweepCarriedBound
              (touchingSweepContext (symmetricFourfoldOccurrences request)
                request.q)
              request.q (normalizedLiveCount request.q liveScale))) ≤
        maximumBits := by
    apply bits_of_member
    simp [symmetricOccurrenceTouchingCostStageBits]
  have hcostRequestBits :
      costRequestBits request.q (symmetricPoolMasksTree request)
          (coordinateMask
            (normalizedLiveSet (symmetricFourfoldOccurrences request)
              liveScale))
          (sweepFold
            (occurrenceSupport (symmetricFourfoldOccurrences request))
            (List.finRange request.q)
            ((∅ : Finset (Fin request.q)),
              normalizedLiveCount request.q liveScale)).2 ≤
        maximumBits := by
    apply bits_of_member
    simp [symmetricOccurrenceTouchingCostStageBits]
  have hbroadcastBits :
      roundBroadcastBits request.q (symmetricFourfoldOccurrences request)
          (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)
          (∅ : Finset (Fin request.q)) 0 ≤
        maximumBits := by
    apply bits_of_member
    simp [symmetricOccurrenceTouchingCostStageBits]
  have hnumeratorBits :
      conditionalTouchNumeratorBits request.q
          (symmetricFourfoldOccurrences request)
          (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)
          (∅ : Finset (Fin request.q)) 0 ≤
        maximumBits := by
    apply bits_of_member
    simp [symmetricOccurrenceTouchingCostStageBits]
  have hcontext :
      touchingSweepContext (symmetricFourfoldOccurrences request) request.q =
        Nat.pair request.q (symmetricPoolMasksTree request) := rfl
  have hinitialState :
      sweepStateCode
          (touchingSweepContext (symmetricFourfoldOccurrences request)
            request.q)
          ((∅ : Finset (Fin request.q)),
            normalizedLiveCount request.q liveScale) =
        sweepCode (Nat.pair request.q (symmetricPoolMasksTree request)) 0
          (normalizedLiveCount request.q liveScale) := by
    unfold sweepStateCode
    rw [← hcontext, coordinateMask_empty]
  have hsweepInputBits :
      natBitLength
          (roundCallInput request.q
            (sweepStateCode
              (touchingSweepContext (symmetricFourfoldOccurrences request)
                request.q)
              ((∅ : Finset (Fin request.q)),
                normalizedLiveCount request.q liveScale))) ≤
        maximumBits := by
    rw [hinitialState]
    refine le_trans ?_ hroundInputBits
    exact Nat.le_max_right _ _
  have hsweepCarriedBits : ∀ carried counter,
      SweepReachable request.q
        (touchingSweepContext (symmetricFourfoldOccurrences request) request.q)
        (normalizedLiveCount request.q liveScale) carried counter →
      natBitLength (Nat.pair carried counter) ≤ maximumBits := by
    intro carried counter hreachable
    obtain ⟨hcounter, selected, stepCount, hstepCount, hcarried⟩ := hreachable
    rw [hcarried]
    refine bits_of_le ?_ hcarriedEnvelopeBits
    exact pair_le_pair
      (sweepStateCode_le_sweepCarriedBound
        (touchingSweepContext (symmetricFourfoldOccurrences request) request.q)
        selected hstepCount)
      hcounter
  have hsweepReturnBits : ∀ carried counter,
      SweepReachable request.q
        (touchingSweepContext (symmetricFourfoldOccurrences request) request.q)
        (normalizedLiveCount request.q liveScale) carried (counter + 1) →
      natBitLength
          (Nat.pair (Nat.pair carried (counter + 1))
            (touchingSweepStep (symmetricFourfoldOccurrences request) carried
              (counter + 1))) ≤
        maximumBits := by
    intro carried counter hreachable
    obtain ⟨hcounter, selected, stepCount, hstepCount, hcarried⟩ := hreachable
    rw [hcarried, touchingSweepStep_sweepStateCode
      (symmetricFourfoldOccurrences request) selected stepCount (counter + 1)]
    have hnextStep :
        (sweepRound (occurrenceSupport (symmetricFourfoldOccurrences request))
            ((List.finRange request.q).drop (request.q - (counter + 1)))
            (selected, stepCount)).2 ≤
          normalizedLiveCount request.q liveScale :=
      le_trans
        (sweepRound_snd_le
          (occurrenceSupport (symmetricFourfoldOccurrences request))
          ((List.finRange request.q).drop (request.q - (counter + 1)))
          (selected, stepCount))
        hstepCount
    refine bits_of_le ?_ hreturnEnvelopeBits
    refine pair_le_pair
      (pair_le_pair
        (sweepStateCode_le_sweepCarriedBound
          (touchingSweepContext (symmetricFourfoldOccurrences request)
            request.q)
          selected hstepCount)
        hcounter)
      ?_
    exact sweepStateCode_le_sweepCarriedBound
      (touchingSweepContext (symmetricFourfoldOccurrences request) request.q)
      (sweepRound (occurrenceSupport (symmetricFourfoldOccurrences request))
        ((List.finRange request.q).drop (request.q - (counter + 1)))
        (selected, stepCount)).1
      hnextStep
  have hstageOne :
      runNPOracleProgram symmetricOccurrenceSupportMaskProgram maximumBits
          (symmetricOccurrenceSupportMaskFuel request)
          (initialNPOracleState request.q (symmetricEnvelopeCode request)) =
        some (symmetricPoolMasksTree request) :=
    run_symmetricOccurrenceSupportMaskProgram request maximumBits hmaskBits
  have hstageTwo :
      runNPOracleProgram (scalePairProgram 0) maximumBits 3
          (initialNPOracleState request.q
            (symmetricPoolMasksTree request)) =
        some (Nat.pair 0 (symmetricPoolMasksTree request)) :=
    run_scalePairProgram request.q 0 (symmetricPoolMasksTree request)
      maximumBits hscaleBits
  have hstageThree :
      runNPOracleProgram (preserveRightProgram (liveCountProgram liveScale))
          maximumBits
          (preserveRightFuel (liveCountFuel liveScale request.q))
          (initialNPOracleState request.q
            (Nat.pair 0 (symmetricPoolMasksTree request))) =
        some
          (Nat.pair (normalizedLiveCount request.q liveScale)
            (symmetricPoolMasksTree request)) :=
    run_bits_mono
      (run_preserveRightProgram (liveCountProgram liveScale) request.q
        (liveCountBits liveScale request.q)
        (liveCountFuel liveScale request.q) 0
        (symmetricPoolMasksTree request)
        (normalizedLiveCount request.q liveScale)
        (run_liveCountProgram liveScale request.q 0
          (liveCountBits liveScale request.q) (le_refl _)))
      hpreserveBits
  have hstageFour :
      runNPOracleProgram roundInputProgram maximumBits 8
          (initialNPOracleState request.q
            (Nat.pair (normalizedLiveCount request.q liveScale)
              (symmetricPoolMasksTree request))) =
        some
          (roundCallInput request.q
            (sweepStateCode
              (touchingSweepContext (symmetricFourfoldOccurrences request)
                request.q)
              ((∅ : Finset (Fin request.q)),
                normalizedLiveCount request.q liveScale))) := by
    rw [hinitialState]
    exact run_roundInputProgram request.q (symmetricPoolMasksTree request)
      (normalizedLiveCount request.q liveScale) maximumBits hroundInputBits
  have hstageFive :
      runNPOracleProgram (roundCallProgram touchingSweepRoundProgram)
          maximumBits
          (roundCallFuel touchingSweepRoundProgram
            (touchingSweepCalleeFuel (symmetricFourfoldOccurrences request))
            (touchingSweepStep (symmetricFourfoldOccurrences request))
            (sweepStateCode
              (touchingSweepContext (symmetricFourfoldOccurrences request)
                request.q)
              ((∅ : Finset (Fin request.q)),
                normalizedLiveCount request.q liveScale))
            request.q)
          (initialNPOracleState request.q
            (roundCallInput request.q
              (sweepStateCode
                (touchingSweepContext (symmetricFourfoldOccurrences request)
                  request.q)
                ((∅ : Finset (Fin request.q)),
                  normalizedLiveCount request.q liveScale)))) =
        some
          (sweepCode
            (touchingSweepContext (symmetricFourfoldOccurrences request)
              request.q)
            (coordinateMask
              (normalizedLiveSet (symmetricFourfoldOccurrences request)
                liveScale))
            (sweepFold
              (occurrenceSupport (symmetricFourfoldOccurrences request))
              (List.finRange request.q)
              ((∅ : Finset (Fin request.q)),
                normalizedLiveCount request.q liveScale)).2) :=
    run_touchingSweepSelectProgram (symmetricFourfoldOccurrences request)
      request.q (normalizedLiveCount request.q liveScale) maximumBits
      hpositive hsweepInputBits hsweepCarriedBits hsweepReturnBits hroundBits
  have hstageSix :
      runNPOracleProgram costRequestProgram maximumBits 10
          (initialNPOracleState request.q
            (sweepCode
              (touchingSweepContext (symmetricFourfoldOccurrences request)
                request.q)
              (coordinateMask
                (normalizedLiveSet (symmetricFourfoldOccurrences request)
                  liveScale))
              (sweepFold
                (occurrenceSupport (symmetricFourfoldOccurrences request))
                (List.finRange request.q)
                ((∅ : Finset (Fin request.q)),
                  normalizedLiveCount request.q liveScale)).2)) =
        some
          (roundBroadcastRequest (symmetricFourfoldOccurrences request)
            (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)
            (∅ : Finset (Fin request.q)) 0) := by
    have hrequest :
        roundBroadcastRequest (symmetricFourfoldOccurrences request)
            (normalizedLiveSet (symmetricFourfoldOccurrences request)
              liveScale)
            (∅ : Finset (Fin request.q)) 0 =
          costRequestOutput request.q (symmetricPoolMasksTree request)
            (coordinateMask
              (normalizedLiveSet (symmetricFourfoldOccurrences request)
                liveScale)) := by
      unfold roundBroadcastRequest roundSharedContext costRequestOutput
        symmetricPoolMasksTree
      rw [coordinateMask_empty]
    rw [hrequest, hcontext]
    exact run_costRequestProgram request.q (symmetricPoolMasksTree request)
      (coordinateMask
        (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale))
      (sweepFold (occurrenceSupport (symmetricFourfoldOccurrences request))
        (List.finRange request.q)
        ((∅ : Finset (Fin request.q)),
          normalizedLiveCount request.q liveScale)).2
      maximumBits hcostRequestBits
  have hstageSeven :
      runNPOracleProgram broadcastCallProgram maximumBits
          (roundBroadcastFuel (symmetricFourfoldOccurrences request)
            (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)
            (∅ : Finset (Fin request.q)) 0)
          (initialNPOracleState request.q
            (roundBroadcastRequest (symmetricFourfoldOccurrences request)
              (normalizedLiveSet (symmetricFourfoldOccurrences request)
                liveScale)
              (∅ : Finset (Fin request.q)) 0)) =
        some
          (conditionalTouchNumeratorInput
            (symmetricFourfoldOccurrences request)
            (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)
            (∅ : Finset (Fin request.q)) 0) :=
    run_bits_mono
      (run_roundBroadcast request.q (symmetricFourfoldOccurrences request)
        (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)
        (∅ : Finset (Fin request.q)) 0)
      hbroadcastBits
  have hstageEight :
      runNPOracleProgram conditionalTouchNumeratorProgram maximumBits
          (conditionalTouchNumeratorFuel
            (symmetricFourfoldOccurrences request)
            (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)
            (∅ : Finset (Fin request.q)) 0)
          (initialNPOracleState request.q
            (conditionalTouchNumeratorInput
              (symmetricFourfoldOccurrences request)
              (normalizedLiveSet (symmetricFourfoldOccurrences request)
                liveScale)
              (∅ : Finset (Fin request.q)) 0)) =
        some (symmetricOccurrenceTouchingCost request liveScale) :=
    run_touchingCostProgram request.q (symmetricFourfoldOccurrences request)
      (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)
      (∅ : Finset (Fin request.q)) maximumBits hnumeratorBits
  exact run_linkPrograms hpositive hlength hstageOne
    (run_linkPrograms hpositive hlength hstageTwo
      (run_linkPrograms hpositive hlength hstageThree
        (run_linkPrograms hpositive hlength hstageFour
          (run_linkPrograms hpositive hlength hstageFive
            (run_linkPrograms hpositive hlength hstageSix
              (run_linkPrograms hpositive hlength hstageSeven
                hstageEight))))))

/-! ## §6 The symmetric counting side, closed

`CanonicalOccurrencePopulationProgram` §5 leaves the whole symmetric counting
path waiting on one program returning `symmetricOccurrenceTouchingCost`.  §5 of
this file supplies it, so both consumers become executable. -/

/-- **The symmetric row-count exponent program**, fully assembled. -/
def symmetricRowCountExponentProgramOfTouchingCost
    (liveScale accuracyExponent : ℕ) : NPOracleProgram :=
  symmetricRowCountExponentProgramOfCost
    (symmetricOccurrenceTouchingCostProgram liveScale) accuracyExponent

theorem symmetricRowCountExponentProgramOfTouchingCost_oracleFree
    (liveScale accuracyExponent : ℕ) :
    OracleFree
      (symmetricRowCountExponentProgramOfTouchingCost liveScale
        accuracyExponent) :=
  symmetricRowCountExponentProgramOfCost_oracleFree
    (symmetricOccurrenceTouchingCostProgram liveScale) accuracyExponent
    (symmetricOccurrenceTouchingCostProgram_oracleFree liveScale)

def symmetricRowCountExponentOfTouchingCostFuel
    (liveScale accuracyExponent : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) : ℕ :=
  symmetricRowCountExponentOfCostFuel
    (symmetricOccurrenceTouchingCostProgram liveScale)
    (symmetricOccurrenceTouchingCostFuel liveScale request) liveScale
    accuracyExponent request

/-- **The symmetric row-count exponent, executed from the typed envelope.**
No interpreter premise remains except the round callee's own register-width
envelope. -/
theorem run_symmetricRowCountExponentProgram_executable
    (liveScale accuracyExponent : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (costBits maximumBits : ℕ)
    (hbits :
      symmetricRowCountExponentOfCostBits costBits liveScale accuracyExponent
          request ≤
        maximumBits)
    (hcostBits :
      symmetricOccurrenceTouchingCostBits liveScale request ≤ costBits)
    (hroundBits : ∀ (selected : Finset (Fin request.q)) (stepCount counter : ℕ),
      counter + 1 ≤ request.q →
      stepCount ≤ normalizedLiveCount request.q liveScale →
      touchingSweepRoundBits (symmetricFourfoldOccurrences request) selected
          stepCount (request.q - (counter + 1)) counter ≤
        costBits) :
    runNPOracleProgram
        (symmetricRowCountExponentProgramOfTouchingCost liveScale
          accuracyExponent)
        maximumBits
        (symmetricRowCountExponentOfTouchingCostFuel liveScale accuracyExponent
          request)
        (initialNPOracleState request.q (symmetricEnvelopeCode request)) =
      some (symmetricRowCountExponent liveScale accuracyExponent request) :=
  run_symmetricRowCountExponentProgram_of_cost liveScale accuracyExponent
    request (symmetricOccurrenceTouchingCostProgram liveScale) costBits
    (symmetricOccurrenceTouchingCostFuel liveScale request) maximumBits hbits
    (run_symmetricOccurrenceTouchingCostProgram liveScale request costBits
      hcostBits hroundBits)

set_option maxHeartbeats 1200000 in
-- The premise list is the aggregation consumer's, minus its cost premise.
/-- **The artifact's symmetric execution field, counting side executed.**  Every
stage from the typed envelope to the published ratio component is a fixed
oracle-free program; the only remaining premises are register-width envelopes
and the abstract row evaluator. -/
theorem run_sharedFourfoldAggregationProgram_symmetric_executable
    (contracts : PublishedContracts) (liveScale accuracyExponent : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (rowEvaluator : NPOracleProgram)
    (maximumBits calleeBits atomCountBits rowCountBits exponentBits
      costBits : ℕ)
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
      symmetricRowCountExponentOfCostBits costBits liveScale accuracyExponent
          request ≤
        exponentBits)
    (hcostBits :
      symmetricOccurrenceTouchingCostBits liveScale request ≤ costBits)
    (hroundBits : ∀ (selected : Finset (Fin request.q)) (stepCount counter : ℕ),
      counter + 1 ≤ request.q →
      stepCount ≤ normalizedLiveCount request.q liveScale →
      touchingSweepRoundBits (symmetricFourfoldOccurrences request) selected
          stepCount (request.q - (counter + 1)) counter ≤
        costBits) :
    runNPOracleProgram
        (CanonicalFourfoldRowTailProgram.sharedFourfoldAggregationProgram
          (selectedExactDecompositionAlgorithm contracts)
          (symmetricFourfoldAtomCountProgram
            (symmetricRowCountExponentProgramOfTouchingCost liveScale
              accuracyExponent))
          rowEvaluator)
        maximumBits
        (CanonicalFourfoldRowTailProgram.symmetricSharedFourfoldAggregationFuel
          contracts liveScale accuracyExponent request
          (symmetricFourfoldAtomCountProgram
            (symmetricRowCountExponentProgramOfTouchingCost liveScale
              accuracyExponent))
          rowEvaluator
          (fourfoldRangeAtomCountFuel request.q
            (symmetricRowCountFuel
              (symmetricRowCountExponentOfTouchingCostFuel liveScale
                accuracyExponent request)
              (symmetricRowCountExponent liveScale accuracyExponent request)))
          evaluatorFuel)
        (initialNPOracleState request.q (symmetricEnvelopeCode request)) =
      some
        (symmetricRatioComponentCode
          (publishedSymmetricRows contracts liveScale accuracyExponent)
          request) :=
  run_sharedFourfoldAggregationProgram_symmetric_of_cost contracts liveScale
    accuracyExponent request (symmetricOccurrenceTouchingCostProgram liveScale)
    rowEvaluator maximumBits calleeBits atomCountBits rowCountBits exponentBits
    costBits (symmetricOccurrenceTouchingCostFuel liveScale request)
    evaluatorFuel hpositive hlength hentryBits hcomponentBits hcalleePositive
    hcalleeLength hbottomBits hrepackBits hevaluator hrowCountLength
    hrowCountBits hatomCountBits hexponentBits
    (run_symmetricOccurrenceTouchingCostProgram liveScale request costBits
      hcostBits hroundBits)

/-! ## §7 The single remaining counting obligation

Every theorem above is unconditional in the counting side's control flow: the
support masks, the live budget, the greedy sweep, the census broadcast, and the
final score are all fixed oracle-free programs, and the sweep controller's four
reachability-indexed width premises are discharged from the closed envelope of
§4.  What is left is a *register-width* premise only, namely the round callee's
own budget on the sweep's reachable rounds:

```text
∀ (selected : Finset (Fin request.q)) (stepCount counter : ℕ),
  counter + 1 ≤ request.q →
  stepCount ≤ normalizedLiveCount request.q liveScale →
  touchingSweepRoundBits (symmetricFourfoldOccurrences request) selected
      stepCount (request.q - (counter + 1)) counter ≤
    costBits
```

Discharging it needs a uniform bound on
`CanonicalTouchingSweepRoundProgram.touchingSweepRoundStageBits` over every
selection set, i.e. a monotone envelope for the two per-round census request
trees; no semantic obligation and no interpreter premise remains. -/

end NearCubicWires.CanonicalSymmetricTouchingCostProgram
