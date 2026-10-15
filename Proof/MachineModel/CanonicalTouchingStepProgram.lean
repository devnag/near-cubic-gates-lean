import Proof.MachineModel.CanonicalBinomialProgram
import Proof.MachineModel.CanonicalBitSerialMulProgram
import Proof.Circuits.CanonicalPairedCall
import Proof.Supplier.SupplierTouching

/-!
# The touching sweep's per-step comparison, executed

`SupplierTouching.touchingSelectAux` branches on exactly one inequality:

```text
included * Nat.choose rest.length stepCount ≤
  excluded * Nat.choose rest.length (stepCount - 1)
```

where `included` and `excluded` are the two conditional touch numerators of the
current coordinate.  This module turns that branch test into one fixed
oracle-free program with an exact width and clock.

The stage is assembled entirely from verified pieces: a straight-line fan-out
that duplicates the shared `(rest.length, stepCount)` context and takes the
saturating predecessor of the step count, one `CanonicalPairedCall` over a
score program that composes `binomialProgram` with `bitSerialMulProgram`, and a
three-instruction saturating comparison.  No arithmetic is repeated in the
proof: the two binomial coefficients come from `run_binomialProgram` and the
two products from `run_bitSerialMulProgram`.
-/

namespace NearCubicWires.CanonicalTouchingStepProgram

open NearCubicWires
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBinomialProgram
open NearCubicWires.CanonicalBitSerialMulProgram
open NearCubicWires.CanonicalPairedCall
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.VerifiedLinker

/-! ## §1 One weighted score

`touchingScoreProgram` maps `Nat.pair value (Nat.pair count position)` to
`Nat.choose count position * value`. -/

def touchingScoreProgram : NPOracleProgram :=
  linkPrograms
    (linkPrograms swapPairProgram (preserveRightProgram binomialProgram))
    bitSerialMulProgram

theorem touchingScoreProgram_oracleFree : OracleFree touchingScoreProgram := by
  apply oracleFree_linkPrograms
  · apply oracleFree_linkPrograms
    · exact swapPairProgram_oracleFree
    · exact preserveRightProgram_oracleFree binomialProgram
        binomialProgram_oracleFree
  · exact bitSerialMulProgram_oracleFree

def touchingScoreFuel (value count position : ℕ) : ℕ :=
  linkFuel bitSerialMulProgram
    (linkFuel (preserveRightProgram binomialProgram) 4
      (preserveRightFuel (binomialFuel count position)))
    (bitSerialMulFuel value)

def touchingScoreBits (inputLength value count position : ℕ) : ℕ :=
  max 1 <| max (natBitLength inputLength) <|
    max (swapPairBits value (Nat.pair count position)) <|
      max
        (preserveRightBits (binomialBits count position)
          (Nat.pair count position) value (Nat.choose count position))
        (bitSerialMulBits inputLength (Nat.choose count position) value)

theorem run_touchingScoreProgram
    (inputLength value count position maximumBits : ℕ)
    (hbits :
      touchingScoreBits inputLength value count position ≤ maximumBits) :
    runNPOracleProgram touchingScoreProgram maximumBits
        (touchingScoreFuel value count position)
        (initialNPOracleState inputLength
          (Nat.pair value (Nat.pair count position))) =
      some (Nat.choose count position * value) := by
  have hpositive : 1 ≤ maximumBits := by
    unfold touchingScoreBits at hbits
    omega
  have hlength : natBitLength inputLength ≤ maximumBits := by
    unfold touchingScoreBits at hbits
    omega
  have hswapBits :
      swapPairBits value (Nat.pair count position) ≤ maximumBits := by
    unfold touchingScoreBits at hbits
    omega
  have hpreserveBits :
      preserveRightBits (binomialBits count position)
          (Nat.pair count position) value (Nat.choose count position) ≤
        maximumBits := by
    unfold touchingScoreBits at hbits
    omega
  have hmulBits :
      bitSerialMulBits inputLength (Nat.choose count position) value ≤
        maximumBits := by
    unfold touchingScoreBits at hbits
    omega
  have hswap :
      runNPOracleProgram swapPairProgram maximumBits 4
          (initialNPOracleState inputLength
            (Nat.pair value (Nat.pair count position))) =
        some (Nat.pair (Nat.pair count position) value) :=
    run_bits_mono
      (run_swapPairProgram inputLength value (Nat.pair count position))
      hswapBits
  have hpreserve :
      runNPOracleProgram (preserveRightProgram binomialProgram) maximumBits
          (preserveRightFuel (binomialFuel count position))
          (initialNPOracleState inputLength
            (Nat.pair (Nat.pair count position) value)) =
        some (Nat.pair (Nat.choose count position) value) :=
    run_bits_mono
      (run_preserveRightProgram binomialProgram inputLength
        (binomialBits count position) (binomialFuel count position)
        (Nat.pair count position) value (Nat.choose count position)
        (run_binomialProgram_pair inputLength count position
          (binomialBits count position) (le_refl _)))
      hpreserveBits
  have hmul :
      runNPOracleProgram bitSerialMulProgram maximumBits
          (bitSerialMulFuel value)
          (initialNPOracleState inputLength
            (Nat.pair (Nat.choose count position) value)) =
        some (Nat.choose count position * value) :=
    run_bits_mono
      (run_bitSerialMulProgram inputLength (Nat.choose count position) value)
      hmulBits
  exact run_linkPrograms hpositive hlength
    (run_linkPrograms hpositive hlength hswap hpreserve) hmul

/-! ## §2 The straight-line fan-out -/

/-- `Nat.pair (Nat.pair included excluded) (Nat.pair restLength stepCount)`. -/
def touchingStepInput (included excluded restLength stepCount : ℕ) : ℕ :=
  Nat.pair (Nat.pair included excluded) (Nat.pair restLength stepCount)

/-- The two independent score requests, ready for one paired call. -/
def touchingStepHandoff (included excluded restLength stepCount : ℕ) : ℕ :=
  Nat.pair (Nat.pair included (Nat.pair restLength stepCount))
    (Nat.pair excluded (Nat.pair restLength (stepCount - 1)))

/-- Duplicate the shared context and take the saturating predecessor of the
step count. -/
def touchingStepFanoutProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 2 4 3
  , .unpairRight 2 5 4
  , .unpairLeft 3 6 5
  , .unpairRight 3 7 6
  , .decrement 7 7
  , .pair 6 7 8 8
  , .pair 5 8 8 9
  , .pair 4 3 9 10
  , .pair 9 8 0 11
  , .halt 0
  ]

@[simp] theorem touchingStepFanoutProgram_oracleFree :
    OracleFree touchingStepFanoutProgram := by
  rfl

def touchingStepFanoutBits (included excluded restLength stepCount : ℕ) : ℕ :=
  max (natBitLength (touchingStepInput included excluded restLength stepCount))
    (natBitLength
      (touchingStepHandoff included excluded restLength stepCount))

theorem run_touchingStepFanoutProgram
    (inputLength included excluded restLength stepCount maximumBits : ℕ)
    (hbits :
      touchingStepFanoutBits included excluded restLength stepCount ≤
        maximumBits) :
    runNPOracleProgram touchingStepFanoutProgram maximumBits 12
        (initialNPOracleState inputLength
          (touchingStepInput included excluded restLength stepCount)) =
      some (touchingStepHandoff included excluded restLength stepCount) := by
  have hinputBits :
      natBitLength
          (touchingStepInput included excluded restLength stepCount) ≤
        maximumBits := by
    unfold touchingStepFanoutBits at hbits
    omega
  have houtputBits :
      natBitLength
          (touchingStepHandoff included excluded restLength stepCount) ≤
        maximumBits := by
    unfold touchingStepFanoutBits at hbits
    omega
  have hleftBits :
      natBitLength (Nat.pair included excluded) ≤ maximumBits :=
    (natBitLength_mono (Nat.left_le_pair _ _)).trans hinputBits
  have hrightBits :
      natBitLength (Nat.pair restLength stepCount) ≤ maximumBits :=
    (natBitLength_mono (Nat.right_le_pair _ _)).trans hinputBits
  have hincludedBits : natBitLength included ≤ maximumBits :=
    (natBitLength_mono (Nat.left_le_pair _ _)).trans hleftBits
  have hexcludedBits : natBitLength excluded ≤ maximumBits :=
    (natBitLength_mono (Nat.right_le_pair _ _)).trans hleftBits
  have hrestBits : natBitLength restLength ≤ maximumBits :=
    (natBitLength_mono (Nat.left_le_pair _ _)).trans hrightBits
  have hstepBits : natBitLength stepCount ≤ maximumBits :=
    (natBitLength_mono (Nat.right_le_pair _ _)).trans hrightBits
  have hpredBits : natBitLength (stepCount - 1) ≤ maximumBits :=
    (natBitLength_mono (Nat.sub_le _ _)).trans hstepBits
  have hsecondBits :
      natBitLength (Nat.pair excluded (Nat.pair restLength (stepCount - 1))) ≤
        maximumBits :=
    (natBitLength_mono (Nat.right_le_pair _ _)).trans houtputBits
  have hpairPredBits :
      natBitLength (Nat.pair restLength (stepCount - 1)) ≤ maximumBits :=
    (natBitLength_mono (Nat.right_le_pair _ _)).trans hsecondBits
  have hfirstBits :
      natBitLength (Nat.pair included (Nat.pair restLength stepCount)) ≤
        maximumBits :=
    (natBitLength_mono (Nat.left_le_pair _ _)).trans houtputBits
  rw [show (12 : ℕ) =
    0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega]
  rw [run_unpairLeft_instruction (value := Nat.pair included excluded)
    (by rfl) rfl (by simp [initialNPOracleState, touchingStepInput])
    hleftBits]
  rw [run_unpairRight_instruction (value := Nat.pair restLength stepCount)
    (by rfl) rfl
    (by
      simp [initialNPOracleState, touchingStepInput, NPOracleState.write,
        NPOracleState.jump])
    hrightBits]
  rw [run_unpairLeft_instruction (value := included) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hincludedBits]
  rw [run_unpairRight_instruction (value := excluded) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hexcludedBits]
  rw [run_unpairLeft_instruction (value := restLength) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hrestBits]
  rw [run_unpairRight_instruction (value := stepCount) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hstepBits]
  rw [run_decrement_instruction (value := stepCount - 1) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hpredBits]
  rw [run_pair_instruction
    (value := Nat.pair restLength (stepCount - 1)) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hpairPredBits]
  rw [run_pair_instruction
    (value := Nat.pair excluded (Nat.pair restLength (stepCount - 1)))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hsecondBits]
  rw [run_pair_instruction
    (value := Nat.pair included (Nat.pair restLength stepCount)) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hfirstBits]
  rw [run_pair_instruction
    (value := touchingStepHandoff included excluded restLength stepCount)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, touchingStepHandoff])
    houtputBits]
  exact run_halt_instruction (fuel := 0)
    (value := touchingStepHandoff included excluded restLength stepCount)
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump])
    houtputBits

/-! ## §3 The saturating comparison -/

/-- `Nat.pair left right ↦ if left ≤ right then 1 else 0`. -/
def leCompareProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .subtract 2 3 4 3
  , .branchZero 4 4 5
  , .set 0 1 6
  , .set 0 0 6
  , .halt 0
  ]

@[simp] theorem leCompareProgram_oracleFree : OracleFree leCompareProgram := by
  rfl

def leCompareBits (left right : ℕ) : ℕ :=
  natBitLength (Nat.pair left right)

theorem run_leCompareProgram
    (inputLength left right maximumBits : ℕ)
    (hbits : leCompareBits left right ≤ maximumBits) :
    runNPOracleProgram leCompareProgram maximumBits 6
        (initialNPOracleState inputLength (Nat.pair left right)) =
      some (if left ≤ right then 1 else 0) := by
  have hpairBits : natBitLength (Nat.pair left right) ≤ maximumBits := hbits
  have hleftBits : natBitLength left ≤ maximumBits :=
    (natBitLength_mono (Nat.left_le_pair _ _)).trans hpairBits
  have hrightBits : natBitLength right ≤ maximumBits :=
    (natBitLength_mono (Nat.right_le_pair _ _)).trans hpairBits
  have hdifferenceBits : natBitLength (left - right) ≤ maximumBits :=
    (natBitLength_mono (Nat.sub_le _ _)).trans hleftBits
  have hzeroBits : natBitLength 0 ≤ maximumBits :=
    (natBitLength_mono (Nat.zero_le _)).trans hleftBits
  have honeBits : natBitLength 1 ≤ maximumBits := by
    have : natBitLength 1 = 1 := by simp [natBitLength]
    have hpositive : 1 ≤ natBitLength (Nat.pair left right) := by
      simp [natBitLength]
    omega
  rw [show (6 : ℕ) = 0 + 1 + 1 + 1 + 1 + 1 + 1 by omega]
  rw [run_unpairLeft_instruction (value := left) (by rfl) rfl
    (by simp [initialNPOracleState]) hleftBits]
  rw [run_unpairRight_instruction (value := right) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hrightBits]
  rw [run_subtract_instruction (value := left - right) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hdifferenceBits]
  rw [run_branchZero_instruction (by rfl) rfl]
  by_cases hle : left ≤ right
  · rw [show
      (((((initialNPOracleState inputLength (Nat.pair left right)).write 2
        left).jump 1).write 3 right).jump 2 |>.write 4 (left - right)
          |>.jump 3).registers 4 = 0 by
      simp [NPOracleState.write, NPOracleState.jump, Nat.sub_eq_zero_of_le hle]]
    rw [if_pos rfl]
    rw [run_set_instruction (value := 1) (by rfl) rfl honeBits]
    rw [if_pos hle]
    exact run_halt_instruction (fuel := 0) (value := 1) (by rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) honeBits
  · have hdifference : left - right ≠ 0 := by omega
    rw [show
      (((((initialNPOracleState inputLength (Nat.pair left right)).write 2
        left).jump 1).write 3 right).jump 2 |>.write 4 (left - right)
          |>.jump 3).registers 4 = left - right by
      simp [NPOracleState.write, NPOracleState.jump]]
    rw [if_neg hdifference]
    rw [run_set_instruction (value := 0) (by rfl) rfl hzeroBits]
    rw [if_neg hle]
    exact run_halt_instruction (fuel := 0) (value := 0) (by rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hzeroBits

/-! ## §4 The assembled step -/

/-- **The touching sweep's per-step comparison program.** -/
def touchingStepProgram : NPOracleProgram :=
  linkPrograms
    (linkPrograms touchingStepFanoutProgram
      (pairedCallProgram touchingScoreProgram))
    leCompareProgram

theorem touchingStepProgram_oracleFree : OracleFree touchingStepProgram := by
  apply oracleFree_linkPrograms
  · apply oracleFree_linkPrograms
    · exact touchingStepFanoutProgram_oracleFree
    · exact pairedCallProgram_oracleFree touchingScoreProgram
        touchingScoreProgram_oracleFree
  · exact leCompareProgram_oracleFree

def touchingStepFuel (included excluded restLength stepCount : ℕ) : ℕ :=
  linkFuel leCompareProgram
    (linkFuel (pairedCallProgram touchingScoreProgram) 12
      (pairedCallFuel touchingScoreProgram
        (touchingScoreFuel included restLength stepCount)
        (touchingScoreFuel excluded restLength (stepCount - 1))))
    6

def touchingStepBits
    (inputLength included excluded restLength stepCount : ℕ) : ℕ :=
  max 1 <| max (natBitLength inputLength) <|
    max (touchingStepFanoutBits included excluded restLength stepCount) <|
      max
        (pairedCallBits inputLength
          (touchingScoreBits inputLength included restLength stepCount)
          (touchingScoreBits inputLength excluded restLength (stepCount - 1))
          (Nat.pair included (Nat.pair restLength stepCount))
          (Nat.pair excluded (Nat.pair restLength (stepCount - 1)))
          (Nat.choose restLength stepCount * included)
          (Nat.choose restLength (stepCount - 1) * excluded))
        (leCompareBits (Nat.choose restLength stepCount * included)
          (Nat.choose restLength (stepCount - 1) * excluded))

set_option maxHeartbeats 800000 in
-- The three linked stages are widened to one shared register bound before
-- composition; only the closed `…Bits` names appear in the premises.
/-- **The exact branch test of `touchingSelectAux`, executed.**  One fixed
oracle-free program decides the greedy sweep's cross-multiplied comparison. -/
theorem run_touchingStepProgram
    (inputLength included excluded restLength stepCount maximumBits : ℕ)
    (hbits :
      touchingStepBits inputLength included excluded restLength stepCount ≤
        maximumBits) :
    runNPOracleProgram touchingStepProgram maximumBits
        (touchingStepFuel included excluded restLength stepCount)
        (initialNPOracleState inputLength
          (touchingStepInput included excluded restLength stepCount)) =
      some
        (if included * Nat.choose restLength stepCount ≤
            excluded * Nat.choose restLength (stepCount - 1) then 1 else 0) := by
  have hpositive : 1 ≤ maximumBits := by
    unfold touchingStepBits at hbits
    omega
  have hlength : natBitLength inputLength ≤ maximumBits := by
    unfold touchingStepBits at hbits
    omega
  have hfanoutBits :
      touchingStepFanoutBits included excluded restLength stepCount ≤
        maximumBits := by
    unfold touchingStepBits at hbits
    omega
  have hpairedBits :
      pairedCallBits inputLength
          (touchingScoreBits inputLength included restLength stepCount)
          (touchingScoreBits inputLength excluded restLength (stepCount - 1))
          (Nat.pair included (Nat.pair restLength stepCount))
          (Nat.pair excluded (Nat.pair restLength (stepCount - 1)))
          (Nat.choose restLength stepCount * included)
          (Nat.choose restLength (stepCount - 1) * excluded) ≤
        maximumBits := by
    unfold touchingStepBits at hbits
    omega
  have hcompareBits :
      leCompareBits (Nat.choose restLength stepCount * included)
          (Nat.choose restLength (stepCount - 1) * excluded) ≤
        maximumBits := by
    unfold touchingStepBits at hbits
    omega
  have hfanout :=
    run_touchingStepFanoutProgram inputLength included excluded restLength
      stepCount maximumBits hfanoutBits
  have hpaired :
      runNPOracleProgram (pairedCallProgram touchingScoreProgram) maximumBits
          (pairedCallFuel touchingScoreProgram
            (touchingScoreFuel included restLength stepCount)
            (touchingScoreFuel excluded restLength (stepCount - 1)))
          (initialNPOracleState inputLength
            (touchingStepHandoff included excluded restLength stepCount)) =
        some
          (Nat.pair (Nat.choose restLength stepCount * included)
            (Nat.choose restLength (stepCount - 1) * excluded)) :=
    run_bits_mono
      (run_pairedCallProgram touchingScoreProgram inputLength
        (touchingScoreBits inputLength included restLength stepCount)
        (touchingScoreBits inputLength excluded restLength (stepCount - 1))
        (touchingScoreFuel included restLength stepCount)
        (touchingScoreFuel excluded restLength (stepCount - 1))
        (Nat.pair included (Nat.pair restLength stepCount))
        (Nat.pair excluded (Nat.pair restLength (stepCount - 1)))
        (Nat.choose restLength stepCount * included)
        (Nat.choose restLength (stepCount - 1) * excluded)
        (run_touchingScoreProgram inputLength included restLength stepCount
          (touchingScoreBits inputLength included restLength stepCount)
          (le_refl _))
        (run_touchingScoreProgram inputLength excluded restLength
          (stepCount - 1)
          (touchingScoreBits inputLength excluded restLength (stepCount - 1))
          (le_refl _)))
      hpairedBits
  have hcompare :
      runNPOracleProgram leCompareProgram maximumBits 6
          (initialNPOracleState inputLength
            (Nat.pair (Nat.choose restLength stepCount * included)
              (Nat.choose restLength (stepCount - 1) * excluded))) =
        some
          (if included * Nat.choose restLength stepCount ≤
              excluded * Nat.choose restLength (stepCount - 1) then
            1
          else
            0) := by
    have hrun :=
      run_leCompareProgram inputLength
        (Nat.choose restLength stepCount * included)
        (Nat.choose restLength (stepCount - 1) * excluded) maximumBits
        hcompareBits
    rw [hrun]
    rw [Nat.mul_comm (Nat.choose restLength stepCount) included,
      Nat.mul_comm (Nat.choose restLength (stepCount - 1)) excluded]
  exact run_linkPrograms hpositive hlength
    (run_linkPrograms hpositive hlength hfanout hpaired) hcompare

/-! ## §5 One gate's conditional touch count

`SupplierTouching.conditionalGateTouchCount` is the only per-gate quantity the
sweep ever sums.  Given the gate's meeting indicator and the two fiber
cardinalities it is a difference of two binomial coefficients, so it is one
paired binomial call followed by a saturating selector. -/

/-- The pure per-gate value: `meets = 0` records a disjoint gate. -/
def gateTouchValue (meets undecidedCard residualCard stepCount : ℕ) : ℕ :=
  if meets = 0 then
    Nat.choose undecidedCard stepCount - Nat.choose residualCard stepCount
  else
    Nat.choose undecidedCard stepCount

/-- **The arithmetic core is exactly the ledger's per-gate score.** -/
theorem gateTouchValue_eq_conditionalGateTouchCount
    {Coordinate : Type} [DecidableEq Coordinate]
    (selected undecided support : Finset Coordinate) (stepCount : ℕ) :
    gateTouchValue (SupplierTouching.touchIndicator selected support)
        undecided.card (undecided \ support).card stepCount =
      SupplierTouching.conditionalGateTouchCount selected undecided support
        stepCount := by
  unfold gateTouchValue SupplierTouching.touchIndicator
    SupplierTouching.conditionalGateTouchCount
  by_cases hdisjoint : Disjoint selected support <;> simp [hdisjoint]

def gateTouchInput (meets undecidedCard residualCard stepCount : ℕ) : ℕ :=
  Nat.pair meets (Nat.pair (Nat.pair undecidedCard residualCard) stepCount)

def gateTouchHandoff (meets undecidedCard residualCard stepCount : ℕ) : ℕ :=
  Nat.pair
    (Nat.pair (Nat.pair undecidedCard stepCount)
      (Nat.pair residualCard stepCount))
    meets

/-- Duplicate the step count across both binomial requests and park the
meeting indicator on the preserved right. -/
def gateTouchFanoutProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .unpairLeft 4 6 5
  , .unpairRight 4 7 6
  , .pair 6 5 8 7
  , .pair 7 5 9 8
  , .pair 8 9 8 9
  , .pair 8 2 0 10
  , .halt 0
  ]

@[simp] theorem gateTouchFanoutProgram_oracleFree :
    OracleFree gateTouchFanoutProgram := by
  rfl

def gateTouchFanoutBits (meets undecidedCard residualCard stepCount : ℕ) : ℕ :=
  max (natBitLength (gateTouchInput meets undecidedCard residualCard stepCount))
    (natBitLength
      (gateTouchHandoff meets undecidedCard residualCard stepCount))

theorem run_gateTouchFanoutProgram
    (inputLength meets undecidedCard residualCard stepCount maximumBits : ℕ)
    (hbits :
      gateTouchFanoutBits meets undecidedCard residualCard stepCount ≤
        maximumBits) :
    runNPOracleProgram gateTouchFanoutProgram maximumBits 11
        (initialNPOracleState inputLength
          (gateTouchInput meets undecidedCard residualCard stepCount)) =
      some (gateTouchHandoff meets undecidedCard residualCard stepCount) := by
  have hinputBits :
      natBitLength
          (gateTouchInput meets undecidedCard residualCard stepCount) ≤
        maximumBits := by
    unfold gateTouchFanoutBits at hbits
    omega
  have houtputBits :
      natBitLength
          (gateTouchHandoff meets undecidedCard residualCard stepCount) ≤
        maximumBits := by
    unfold gateTouchFanoutBits at hbits
    omega
  have hmeetsBits : natBitLength meets ≤ maximumBits :=
    (natBitLength_mono (Nat.left_le_pair _ _)).trans hinputBits
  have htailBits :
      natBitLength
          (Nat.pair (Nat.pair undecidedCard residualCard) stepCount) ≤
        maximumBits :=
    (natBitLength_mono (Nat.right_le_pair _ _)).trans hinputBits
  have hcardsBits :
      natBitLength (Nat.pair undecidedCard residualCard) ≤ maximumBits :=
    (natBitLength_mono (Nat.left_le_pair _ _)).trans htailBits
  have hstepBits : natBitLength stepCount ≤ maximumBits :=
    (natBitLength_mono (Nat.right_le_pair _ _)).trans htailBits
  have hundecidedBits : natBitLength undecidedCard ≤ maximumBits :=
    (natBitLength_mono (Nat.left_le_pair _ _)).trans hcardsBits
  have hresidualBits : natBitLength residualCard ≤ maximumBits :=
    (natBitLength_mono (Nat.right_le_pair _ _)).trans hcardsBits
  have hbothBits :
      natBitLength
          (Nat.pair (Nat.pair undecidedCard stepCount)
            (Nat.pair residualCard stepCount)) ≤
        maximumBits :=
    (natBitLength_mono (Nat.left_le_pair _ _)).trans houtputBits
  have hfirstBits :
      natBitLength (Nat.pair undecidedCard stepCount) ≤ maximumBits :=
    (natBitLength_mono (Nat.left_le_pair _ _)).trans hbothBits
  have hsecondBits :
      natBitLength (Nat.pair residualCard stepCount) ≤ maximumBits :=
    (natBitLength_mono (Nat.right_le_pair _ _)).trans hbothBits
  rw [show (11 : ℕ) = 0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega]
  rw [run_unpairLeft_instruction (value := meets) (by rfl) rfl
    (by simp [initialNPOracleState, gateTouchInput]) hmeetsBits]
  rw [run_unpairRight_instruction
    (value := Nat.pair (Nat.pair undecidedCard residualCard) stepCount)
    (by rfl) rfl
    (by
      simp [initialNPOracleState, gateTouchInput, NPOracleState.write,
        NPOracleState.jump])
    htailBits]
  rw [run_unpairLeft_instruction
    (value := Nat.pair undecidedCard residualCard) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hcardsBits]
  rw [run_unpairRight_instruction (value := stepCount) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hstepBits]
  rw [run_unpairLeft_instruction (value := undecidedCard) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hundecidedBits]
  rw [run_unpairRight_instruction (value := residualCard) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hresidualBits]
  rw [run_pair_instruction (value := Nat.pair undecidedCard stepCount)
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump])
    hfirstBits]
  rw [run_pair_instruction (value := Nat.pair residualCard stepCount)
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump])
    hsecondBits]
  rw [run_pair_instruction
    (value :=
      Nat.pair (Nat.pair undecidedCard stepCount)
        (Nat.pair residualCard stepCount))
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump])
    hbothBits]
  rw [run_pair_instruction
    (value := gateTouchHandoff meets undecidedCard residualCard stepCount)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, gateTouchHandoff])
    houtputBits]
  exact run_halt_instruction (fuel := 0)
    (value := gateTouchHandoff meets undecidedCard residualCard stepCount)
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump])
    houtputBits

/-- `Nat.pair (Nat.pair left right) meets ↦ if meets = 0 then left - right
else left`. -/
def gateTouchSelectProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 2 4 3
  , .unpairRight 2 5 4
  , .branchZero 3 5 6
  , .subtract 4 5 0 7
  , .copy 4 0 7
  , .halt 0
  ]

@[simp] theorem gateTouchSelectProgram_oracleFree :
    OracleFree gateTouchSelectProgram := by
  rfl

def gateTouchSelectBits (left right meets : ℕ) : ℕ :=
  natBitLength (Nat.pair (Nat.pair left right) meets)

theorem run_gateTouchSelectProgram
    (inputLength left right meets maximumBits : ℕ)
    (hbits : gateTouchSelectBits left right meets ≤ maximumBits) :
    runNPOracleProgram gateTouchSelectProgram maximumBits 7
        (initialNPOracleState inputLength
          (Nat.pair (Nat.pair left right) meets)) =
      some (if meets = 0 then left - right else left) := by
  have hinputBits :
      natBitLength (Nat.pair (Nat.pair left right) meets) ≤ maximumBits :=
    hbits
  have hpairBits : natBitLength (Nat.pair left right) ≤ maximumBits :=
    (natBitLength_mono (Nat.left_le_pair _ _)).trans hinputBits
  have hmeetsBits : natBitLength meets ≤ maximumBits :=
    (natBitLength_mono (Nat.right_le_pair _ _)).trans hinputBits
  have hleftBits : natBitLength left ≤ maximumBits :=
    (natBitLength_mono (Nat.left_le_pair _ _)).trans hpairBits
  have hrightBits : natBitLength right ≤ maximumBits :=
    (natBitLength_mono (Nat.right_le_pair _ _)).trans hpairBits
  have hdifferenceBits : natBitLength (left - right) ≤ maximumBits :=
    (natBitLength_mono (Nat.sub_le _ _)).trans hleftBits
  rw [show (7 : ℕ) = 0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega]
  rw [run_unpairLeft_instruction (value := Nat.pair left right) (by rfl) rfl
    (by simp [initialNPOracleState]) hpairBits]
  rw [run_unpairRight_instruction (value := meets) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hmeetsBits]
  rw [run_unpairLeft_instruction (value := left) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hleftBits]
  rw [run_unpairRight_instruction (value := right) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hrightBits]
  rw [run_branchZero_instruction (by rfl) rfl]
  by_cases hmeets : meets = 0
  · rw [show
      (((((((initialNPOracleState inputLength
        (Nat.pair (Nat.pair left right) meets)).write 2
          (Nat.pair left right)).jump 1).write 3 meets).jump 2).write 4
            left).jump 3 |>.write 5 right |>.jump 4).registers 3 = 0 by
      simp [NPOracleState.write, NPOracleState.jump, hmeets]]
    rw [if_pos rfl]
    rw [run_subtract_instruction (value := left - right) (by rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hdifferenceBits]
    rw [if_pos hmeets]
    exact run_halt_instruction (fuel := 0) (value := left - right) (by rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hdifferenceBits
  · rw [show
      (((((((initialNPOracleState inputLength
        (Nat.pair (Nat.pair left right) meets)).write 2
          (Nat.pair left right)).jump 1).write 3 meets).jump 2).write 4
            left).jump 3 |>.write 5 right |>.jump 4).registers 3 = meets by
      simp [NPOracleState.write, NPOracleState.jump]]
    rw [if_neg hmeets]
    rw [run_copy_instruction (value := left) (by rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hleftBits]
    rw [if_neg hmeets]
    exact run_halt_instruction (fuel := 0) (value := left) (by rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hleftBits

/-- **The per-gate conditional touch count program.** -/
def gateTouchProgram : NPOracleProgram :=
  linkPrograms
    (linkPrograms gateTouchFanoutProgram
      (preserveRightProgram (pairedCallProgram binomialProgram)))
    gateTouchSelectProgram

theorem gateTouchProgram_oracleFree : OracleFree gateTouchProgram := by
  apply oracleFree_linkPrograms
  · apply oracleFree_linkPrograms
    · exact gateTouchFanoutProgram_oracleFree
    · exact preserveRightProgram_oracleFree (pairedCallProgram binomialProgram)
        (pairedCallProgram_oracleFree binomialProgram
          binomialProgram_oracleFree)
  · exact gateTouchSelectProgram_oracleFree

def gateTouchFuel (undecidedCard residualCard stepCount : ℕ) : ℕ :=
  linkFuel gateTouchSelectProgram
    (linkFuel (preserveRightProgram (pairedCallProgram binomialProgram)) 11
      (preserveRightFuel
        (pairedCallFuel binomialProgram (binomialFuel undecidedCard stepCount)
          (binomialFuel residualCard stepCount))))
    7

def gateTouchCalleeBits
    (inputLength undecidedCard residualCard stepCount : ℕ) : ℕ :=
  pairedCallBits inputLength (binomialBits undecidedCard stepCount)
    (binomialBits residualCard stepCount)
    (Nat.pair undecidedCard stepCount) (Nat.pair residualCard stepCount)
    (Nat.choose undecidedCard stepCount) (Nat.choose residualCard stepCount)

def gateTouchBits
    (inputLength meets undecidedCard residualCard stepCount : ℕ) : ℕ :=
  max 1 <| max (natBitLength inputLength) <|
    max (gateTouchFanoutBits meets undecidedCard residualCard stepCount) <|
      max
        (preserveRightBits
          (gateTouchCalleeBits inputLength undecidedCard residualCard
            stepCount)
          (Nat.pair (Nat.pair undecidedCard stepCount)
            (Nat.pair residualCard stepCount))
          meets
          (Nat.pair (Nat.choose undecidedCard stepCount)
            (Nat.choose residualCard stepCount)))
        (gateTouchSelectBits (Nat.choose undecidedCard stepCount)
          (Nat.choose residualCard stepCount) meets)

set_option maxHeartbeats 800000 in
-- One paired binomial call under a preserved indicator, then one saturating
-- selector; every stage is widened to the shared register bound first.
/-- **One gate's conditional touch count, executed.** -/
theorem run_gateTouchProgram
    (inputLength meets undecidedCard residualCard stepCount maximumBits : ℕ)
    (hbits :
      gateTouchBits inputLength meets undecidedCard residualCard stepCount ≤
        maximumBits) :
    runNPOracleProgram gateTouchProgram maximumBits
        (gateTouchFuel undecidedCard residualCard stepCount)
        (initialNPOracleState inputLength
          (gateTouchInput meets undecidedCard residualCard stepCount)) =
      some (gateTouchValue meets undecidedCard residualCard stepCount) := by
  have hpositive : 1 ≤ maximumBits := by
    unfold gateTouchBits at hbits
    omega
  have hlength : natBitLength inputLength ≤ maximumBits := by
    unfold gateTouchBits at hbits
    omega
  have hfanoutBits :
      gateTouchFanoutBits meets undecidedCard residualCard stepCount ≤
        maximumBits := by
    unfold gateTouchBits at hbits
    omega
  have hpreserveBits :
      preserveRightBits
          (gateTouchCalleeBits inputLength undecidedCard residualCard
            stepCount)
          (Nat.pair (Nat.pair undecidedCard stepCount)
            (Nat.pair residualCard stepCount))
          meets
          (Nat.pair (Nat.choose undecidedCard stepCount)
            (Nat.choose residualCard stepCount)) ≤
        maximumBits := by
    unfold gateTouchBits at hbits
    omega
  have hselectBits :
      gateTouchSelectBits (Nat.choose undecidedCard stepCount)
          (Nat.choose residualCard stepCount) meets ≤
        maximumBits := by
    unfold gateTouchBits at hbits
    omega
  have hfanout :=
    run_gateTouchFanoutProgram inputLength meets undecidedCard residualCard
      stepCount maximumBits hfanoutBits
  have hcallee :
      runNPOracleProgram (pairedCallProgram binomialProgram)
          (gateTouchCalleeBits inputLength undecidedCard residualCard
            stepCount)
          (pairedCallFuel binomialProgram
            (binomialFuel undecidedCard stepCount)
            (binomialFuel residualCard stepCount))
          (initialNPOracleState inputLength
            (Nat.pair (Nat.pair undecidedCard stepCount)
              (Nat.pair residualCard stepCount))) =
        some
          (Nat.pair (Nat.choose undecidedCard stepCount)
            (Nat.choose residualCard stepCount)) :=
    run_pairedCallProgram binomialProgram inputLength
      (binomialBits undecidedCard stepCount)
      (binomialBits residualCard stepCount)
      (binomialFuel undecidedCard stepCount)
      (binomialFuel residualCard stepCount)
      (Nat.pair undecidedCard stepCount) (Nat.pair residualCard stepCount)
      (Nat.choose undecidedCard stepCount)
      (Nat.choose residualCard stepCount)
      (run_binomialProgram_pair inputLength undecidedCard stepCount
        (binomialBits undecidedCard stepCount) (le_refl _))
      (run_binomialProgram_pair inputLength residualCard stepCount
        (binomialBits residualCard stepCount) (le_refl _))
  have hpreserve :
      runNPOracleProgram
          (preserveRightProgram (pairedCallProgram binomialProgram))
          maximumBits
          (preserveRightFuel
            (pairedCallFuel binomialProgram
              (binomialFuel undecidedCard stepCount)
              (binomialFuel residualCard stepCount)))
          (initialNPOracleState inputLength
            (gateTouchHandoff meets undecidedCard residualCard stepCount)) =
        some
          (Nat.pair
            (Nat.pair (Nat.choose undecidedCard stepCount)
              (Nat.choose residualCard stepCount))
            meets) :=
    run_bits_mono
      (run_preserveRightProgram (pairedCallProgram binomialProgram)
        inputLength
        (gateTouchCalleeBits inputLength undecidedCard residualCard stepCount)
        (pairedCallFuel binomialProgram
          (binomialFuel undecidedCard stepCount)
          (binomialFuel residualCard stepCount))
        (Nat.pair (Nat.pair undecidedCard stepCount)
          (Nat.pair residualCard stepCount))
        meets
        (Nat.pair (Nat.choose undecidedCard stepCount)
          (Nat.choose residualCard stepCount))
        hcallee)
      hpreserveBits
  have hselect :
      runNPOracleProgram gateTouchSelectProgram maximumBits 7
          (initialNPOracleState inputLength
            (Nat.pair
              (Nat.pair (Nat.choose undecidedCard stepCount)
                (Nat.choose residualCard stepCount))
              meets)) =
        some (gateTouchValue meets undecidedCard residualCard stepCount) :=
    run_gateTouchSelectProgram inputLength
      (Nat.choose undecidedCard stepCount)
      (Nat.choose residualCard stepCount) meets maximumBits hselectBits
  exact run_linkPrograms hpositive hlength
    (run_linkPrograms hpositive hlength hfanout hpreserve) hselect

end NearCubicWires.CanonicalTouchingStepProgram
