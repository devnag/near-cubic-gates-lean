import Proof.MachineModel.CanonicalNatCeilLogProgram
import Proof.MachineModel.LanguageScheduleDecoderProgram

/-!
# The run-time schedule numeral bank

`LanguageScheduleDecoderProgram` turns the two purely enumerative numerals —
the scheduled source index and the scheduled source length — into run-time
registers.  Every other numeral the two chains of `BranchTargetLanguageProgram`
still bake as an immediate is arithmetic in that length together with numerals
that do *not* vary with the request: the published outer shape coefficient and
proof exponent, the pairing-clock depth, the recovery block, and the scheduled
rate.  This module supplies the arithmetic.

Three groups of fixed programs are built.

* §2 collects the value-level primitives that the schedule arithmetic needs and
  that no earlier module exposes: iterated self-pairing (the pairing clock),
  the base-two *floor* logarithm (obtained from the published ceiling
  logarithm, not from a second loop), `Semantics.logScale`, immediate
  multiplication and addition, and the fixed-exponent power.
* §3 collects the straight-line framing adapters that move one numeral between
  the head of the frame and its retained context.
* §4 assembles the two composite numerals — the scheduled width
  `RecoveryScheduleEnvelope.scheduledWidth`, i.e. the base-two logarithm of the
  published width budget, and the scheduled copy count of
  `RecoveryScheduleEnvelope.inverseCopiesOf`/`fixedCopiesOf` — and §5 the bank
  itself.

## What the bank does and does not decide

The bank is oracle-free except for the single imported shape runner call, and
it is closed in `(publicLength, frozen numerals)`.  The scheduled query count is
*not* schedule arithmetic — it is an opaque field of the projection PCP — but it
is nevertheless run-time data: `ExecutableProjectionPCP.queryCount` is by
definition the right component of `pcp.shape.execute`, and `pcp.shape` is an
executable program.  §5 therefore reads it with one
`CanonicalNativeCallProgram.nativeContextCallProgram` call on that runner rather
than as an immediate, which removes it from the list of data that force the
instruction stream to depend on the request.

The one datum the bank does not produce is the Case-2 substituted circuit's
encoding, which is recovered from the accepting oracle rather than computed from
the request.
-/

namespace NearCubicWires.RuntimeScheduleNumeralBank

open NearCubicWires
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBitSerialMulProgram
open NearCubicWires.CanonicalNatCeilLogProgram
open NearCubicWires.CanonicalNativeCallProgram
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.LanguageScheduleDecoderProgram
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.VerifiedLinker

/-! ## 1. Width bookkeeping -/

private theorem bits_of_le_pair_left {value left right : ℕ}
    (hvalue : value ≤ left) :
    natBitLength value ≤ natBitLength (Nat.pair left right) :=
  natBitLength_mono (hvalue.trans (Nat.left_le_pair left right))

private theorem bits_of_le_pair_right {value left right : ℕ}
    (hvalue : value ≤ right) :
    natBitLength value ≤ natBitLength (Nat.pair left right) :=
  natBitLength_mono (hvalue.trans (Nat.right_le_pair left right))

/-! ## 2. Value-level primitives -/

/-! ### Iterated self-pairing -/

private def pairStepProgram : NPOracleProgram :=
  [ .pair 0 0 0 1
  , .halt 0
  ]

@[simp] private theorem pairStepProgram_oracleFree :
    OracleFree pairStepProgram := by
  rfl

private theorem run_pairStepProgram (inputLength value : ℕ) :
    runNPOracleProgram pairStepProgram
        (natBitLength (Nat.pair value value)) 2
        (initialNPOracleState inputLength value) =
      some (Nat.pair value value) := by
  have hbits :
      natBitLength (Nat.pair value value) ≤
        natBitLength (Nat.pair value value) := le_refl _
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair value value) (by rfl) rfl
    (by simp [initialNPOracleState]) hbits]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hbits

/-- The pairing clock as one fixed instruction stream: `depth` self-pairings of
the requested value. -/
def pairIterProgram : ℕ → NPOracleProgram
  | 0 => [ .halt 0 ]
  | depth + 1 => linkPrograms pairStepProgram (pairIterProgram depth)

theorem pairIterProgram_oracleFree : ∀ depth : ℕ,
    OracleFree (pairIterProgram depth)
  | 0 => by rfl
  | depth + 1 =>
      oracleFree_linkPrograms pairStepProgram_oracleFree
        (pairIterProgram_oracleFree depth)

def pairIterFuel : ℕ → ℕ
  | 0 => 1
  | depth + 1 => linkFuel (pairIterProgram depth) 2 (pairIterFuel depth)

def pairIterBits (inputLength : ℕ) : ℕ → ℕ → ℕ
  | 0, value => natBitLength value
  | depth + 1, value =>
      occurrenceStageBits inputLength (natBitLength (Nat.pair value value))
        (pairIterBits inputLength depth (Nat.pair value value))

/-- **The pairing clock, executed.**  `PolynomialClock.pairIter` is exactly the
output of the fixed stream at the requested depth. -/
theorem run_pairIterProgram (inputLength : ℕ) : ∀ (depth value : ℕ),
    runNPOracleProgram (pairIterProgram depth)
        (pairIterBits inputLength depth value) (pairIterFuel depth)
        (initialNPOracleState inputLength value) =
      some (pairIter depth value)
  | 0, value => by
      have hbits : natBitLength value ≤ pairIterBits inputLength 0 value :=
        le_refl _
      exact run_halt_instruction (fuel := 0) (by rfl) rfl
        (by simp [initialNPOracleState]) hbits
  | depth + 1, value =>
      run_occurrenceStage (run_pairStepProgram inputLength value)
        (run_pairIterProgram inputLength depth (Nat.pair value value))

/-- The pairing clock at the published depth. -/
theorem run_pairIterProgram_pairClock (inputLength depth value : ℕ) :
    runNPOracleProgram (pairIterProgram depth)
        (pairIterBits inputLength depth value) (pairIterFuel depth)
        (initialNPOracleState inputLength value) =
      some (pairClock depth value) :=
  run_pairIterProgram inputLength depth value

/-! ### The base-two floor logarithm -/

private def incrementProgram : NPOracleProgram :=
  [ .increment 0 1
  , .halt 0
  ]

@[simp] private theorem incrementProgram_oracleFree :
    OracleFree incrementProgram := by
  rfl

private theorem run_incrementProgram (inputLength value : ℕ) :
    runNPOracleProgram incrementProgram (natBitLength (value + 1)) 2
        (initialNPOracleState inputLength value) =
      some (value + 1) := by
  have hbits : natBitLength (value + 1) ≤ natBitLength (value + 1) := le_refl _
  rw [show 2 = 1 + 1 by omega]
  rw [run_increment_instruction (value := value + 1) (by rfl) rfl
    (by simp [initialNPOracleState]) hbits]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hbits

private def decrementProgram : NPOracleProgram :=
  [ .decrement 0 1
  , .halt 0
  ]

@[simp] private theorem decrementProgram_oracleFree :
    OracleFree decrementProgram := by
  rfl

private theorem run_decrementProgram (inputLength value : ℕ) :
    runNPOracleProgram decrementProgram (natBitLength value) 2
        (initialNPOracleState inputLength value) =
      some (value - 1) := by
  have hbits : natBitLength (value - 1) ≤ natBitLength value :=
    natBitLength_mono (Nat.sub_le value 1)
  rw [show 2 = 1 + 1 by omega]
  rw [run_decrement_instruction (value := value - 1) (by rfl) rfl
    (by simp [initialNPOracleState]) hbits]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hbits

/-- One ceiling logarithm decides the floor logarithm: no second search loop is
introduced for `Nat.log`. -/
theorem clog_succ_sub_one_eq_log (value : ℕ) (hvalue : 1 ≤ value) :
    Nat.clog 2 (value + 1) - 1 = Nat.log 2 value := by
  have hupper : Nat.clog 2 (value + 1) ≤ Nat.log 2 value + 1 := by
    rw [Nat.clog_le_iff_le_pow (b := 2) (by omega)]
    exact Nat.lt_pow_succ_log_self (b := 2) (by omega) value
  have hlower : Nat.log 2 value < Nat.clog 2 (value + 1) := by
    rw [Nat.lt_clog_iff_pow_lt (b := 2) (by omega)]
    exact Nat.lt_succ_of_le (Nat.pow_log_le_self 2 (by omega))
  omega

/-- The base-two floor logarithm as one fixed program. -/
def floorLogProgram : NPOracleProgram :=
  linkPrograms incrementProgram
    (linkPrograms binaryNatCeilLogProgram decrementProgram)

theorem floorLogProgram_oracleFree : OracleFree floorLogProgram :=
  oracleFree_linkPrograms incrementProgram_oracleFree
    (oracleFree_linkPrograms binaryNatCeilLogProgram_oracleFree
      decrementProgram_oracleFree)

def floorLogFuel (value : ℕ) : ℕ :=
  linkFuel (linkPrograms binaryNatCeilLogProgram decrementProgram) 2
    (linkFuel decrementProgram (binaryNatCeilLogFuel (value + 1)) 2)

def floorLogBits (inputLength value : ℕ) : ℕ :=
  occurrenceStageBits inputLength (natBitLength (value + 1)) <|
    occurrenceStageBits inputLength (binaryNatCeilLogBits (value + 1))
      (natBitLength (Nat.clog 2 (value + 1)))

private theorem run_floorLogProgram_raw (inputLength value : ℕ) :
    runNPOracleProgram floorLogProgram (floorLogBits inputLength value)
        (floorLogFuel value) (initialNPOracleState inputLength value) =
      some (Nat.clog 2 (value + 1) - 1) :=
  run_occurrenceStage (run_incrementProgram inputLength value)
    (run_occurrenceStage
      (run_binaryNatCeilLogProgram inputLength (value + 1)
        (binaryNatCeilLogBits (value + 1)) (le_refl _))
      (run_decrementProgram inputLength (Nat.clog 2 (value + 1))))

/-- **The base-two floor logarithm, executed.** -/
theorem run_floorLogProgram (inputLength value : ℕ) (hvalue : 1 ≤ value) :
    runNPOracleProgram floorLogProgram (floorLogBits inputLength value)
        (floorLogFuel value) (initialNPOracleState inputLength value) =
      some (Nat.log 2 value) := by
  rw [← clog_succ_sub_one_eq_log value hvalue]
  exact run_floorLogProgram_raw inputLength value

/-! ### The manuscript's logarithmic scale -/

private def twiceIncrementProgram : NPOracleProgram :=
  [ .increment 0 1
  , .increment 0 2
  , .halt 0
  ]

@[simp] private theorem twiceIncrementProgram_oracleFree :
    OracleFree twiceIncrementProgram := by
  rfl

private theorem run_twiceIncrementProgram (inputLength value : ℕ) :
    runNPOracleProgram twiceIncrementProgram (natBitLength (value + 2)) 3
        (initialNPOracleState inputLength value) =
      some (value + 2) := by
  have hbits : natBitLength (value + 2) ≤ natBitLength (value + 2) := le_refl _
  have hfirst : natBitLength (value + 1) ≤ natBitLength (value + 2) :=
    natBitLength_mono (by omega)
  rw [show 3 = 2 + 1 by omega]
  rw [run_increment_instruction (value := value + 1) (by rfl) rfl
    (by simp [initialNPOracleState]) hfirst]
  rw [show 2 = 1 + 1 by omega]
  rw [run_increment_instruction (value := value + 2) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hbits]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hbits

/-- `Semantics.logScale` as one fixed program. -/
def logScaleProgram : NPOracleProgram :=
  linkPrograms twiceIncrementProgram binaryNatCeilLogProgram

theorem logScaleProgram_oracleFree : OracleFree logScaleProgram :=
  oracleFree_linkPrograms twiceIncrementProgram_oracleFree
    binaryNatCeilLogProgram_oracleFree

def logScaleFuel (value : ℕ) : ℕ :=
  linkFuel binaryNatCeilLogProgram 3 (binaryNatCeilLogFuel (value + 2))

def logScaleBits (inputLength value : ℕ) : ℕ :=
  occurrenceStageBits inputLength (natBitLength (value + 2))
    (binaryNatCeilLogBits (value + 2))

/-- **The logarithmic scale, executed.** -/
theorem run_logScaleProgram (inputLength value : ℕ) :
    runNPOracleProgram logScaleProgram (logScaleBits inputLength value)
        (logScaleFuel value) (initialNPOracleState inputLength value) =
      some (logScale value) :=
  run_occurrenceStage (run_twiceIncrementProgram inputLength value)
    (run_binaryNatCeilLogProgram inputLength (value + 2)
      (binaryNatCeilLogBits (value + 2)) (le_refl _))

/-! ### Immediate multiplication and addition -/

private def immediateFactorProgram (factor : ℕ) : NPOracleProgram :=
  [ .set 2 factor 1
  , .pair 2 0 0 2
  , .halt 0
  ]

@[simp] private theorem immediateFactorProgram_oracleFree (factor : ℕ) :
    OracleFree (immediateFactorProgram factor) := by
  rfl

private theorem run_immediateFactorProgram
    (inputLength factor value : ℕ) :
    runNPOracleProgram (immediateFactorProgram factor)
        (natBitLength (Nat.pair factor value)) 3
        (initialNPOracleState inputLength value) =
      some (bitSerialMulInput factor value) := by
  have hbits :
      natBitLength (Nat.pair factor value) ≤
        natBitLength (Nat.pair factor value) := le_refl _
  have hfactor : natBitLength factor ≤ natBitLength (Nat.pair factor value) :=
    bits_of_le_pair_left (le_refl factor)
  rw [show 3 = 2 + 1 by omega]
  rw [run_set_instruction (value := factor) (by rfl) rfl hfactor]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair factor value) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hbits]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, bitSerialMulInput])
    hbits

/-- Multiplication by a numeral frozen in the instruction stream. -/
def immediateMulProgram (factor : ℕ) : NPOracleProgram :=
  linkPrograms (immediateFactorProgram factor) bitSerialMulProgram

theorem immediateMulProgram_oracleFree (factor : ℕ) :
    OracleFree (immediateMulProgram factor) :=
  oracleFree_linkPrograms (immediateFactorProgram_oracleFree factor)
    bitSerialMulProgram_oracleFree

def immediateMulFuel (value : ℕ) : ℕ :=
  linkFuel bitSerialMulProgram 3 (bitSerialMulFuel value)

def immediateMulBits (inputLength factor value : ℕ) : ℕ :=
  occurrenceStageBits inputLength (natBitLength (Nat.pair factor value))
    (bitSerialMulBits inputLength factor value)

/-- **Immediate multiplication, executed.** -/
theorem run_immediateMulProgram (inputLength factor value : ℕ) :
    runNPOracleProgram (immediateMulProgram factor)
        (immediateMulBits inputLength factor value) (immediateMulFuel value)
        (initialNPOracleState inputLength value) =
      some (factor * value) :=
  run_occurrenceStage (run_immediateFactorProgram inputLength factor value)
    (run_bitSerialMulProgram inputLength factor value)

/-- Addition of a numeral frozen in the instruction stream. -/
def immediateAddProgram (summand : ℕ) : NPOracleProgram :=
  [ .set 2 summand 1
  , .add 0 2 0 2
  , .halt 0
  ]

@[simp] theorem immediateAddProgram_oracleFree (summand : ℕ) :
    OracleFree (immediateAddProgram summand) := by
  rfl

def immediateAddBits (summand value : ℕ) : ℕ :=
  natBitLength (value + summand)

/-- **Immediate addition, executed.** -/
theorem run_immediateAddProgram (inputLength summand value : ℕ) :
    runNPOracleProgram (immediateAddProgram summand)
        (immediateAddBits summand value) 3
        (initialNPOracleState inputLength value) =
      some (value + summand) := by
  have hbits :
      natBitLength (value + summand) ≤ immediateAddBits summand value :=
    le_refl _
  have hsummand : natBitLength summand ≤ immediateAddBits summand value :=
    natBitLength_mono (by omega)
  rw [show 3 = 2 + 1 by omega]
  rw [run_set_instruction (value := summand) (by rfl) rfl hsummand]
  rw [show 2 = 1 + 1 by omega]
  rw [run_add_instruction (value := value + summand) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hbits]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hbits

/-! ### The fixed-exponent power -/

private def powDupProgram : NPOracleProgram :=
  [ .unpairRight 0 2 1
  , .pair 0 2 0 2
  , .halt 0
  ]

@[simp] private theorem powDupProgram_oracleFree :
    OracleFree powDupProgram := by
  rfl

def powDupBits (accumulator value : ℕ) : ℕ :=
  natBitLength (Nat.pair (Nat.pair accumulator value) value)

private theorem run_powDupProgram (inputLength accumulator value : ℕ) :
    runNPOracleProgram powDupProgram (powDupBits accumulator value) 3
        (initialNPOracleState inputLength (Nat.pair accumulator value)) =
      some (Nat.pair (Nat.pair accumulator value) value) := by
  have hbits :
      natBitLength (Nat.pair (Nat.pair accumulator value) value) ≤
        powDupBits accumulator value := le_refl _
  have hvalue : natBitLength value ≤ powDupBits accumulator value :=
    bits_of_le_pair_right (le_refl value)
  rw [show 3 = 2 + 1 by omega]
  rw [run_unpairRight_instruction (value := value) (by rfl) rfl
    (by simp [initialNPOracleState]) hvalue]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair (Nat.pair accumulator value) value) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hbits]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hbits

private def powStepProgram : NPOracleProgram :=
  linkPrograms powDupProgram (preserveRightProgram bitSerialMulProgram)

private theorem powStepProgram_oracleFree : OracleFree powStepProgram :=
  oracleFree_linkPrograms powDupProgram_oracleFree
    (preserveRightProgram_oracleFree bitSerialMulProgram
      bitSerialMulProgram_oracleFree)

def powStepFuel (value : ℕ) : ℕ :=
  linkFuel (preserveRightProgram bitSerialMulProgram) 3
    (preserveRightFuel (bitSerialMulFuel value))

def powStepBits (inputLength accumulator value : ℕ) : ℕ :=
  occurrenceStageBits inputLength (powDupBits accumulator value)
    (preserveRightBits (bitSerialMulBits inputLength accumulator value)
      (bitSerialMulInput accumulator value) value (accumulator * value))

private theorem run_powStepProgram (inputLength accumulator value : ℕ) :
    runNPOracleProgram powStepProgram
        (powStepBits inputLength accumulator value) (powStepFuel value)
        (initialNPOracleState inputLength (Nat.pair accumulator value)) =
      some (Nat.pair (accumulator * value) value) :=
  run_occurrenceStage (run_powDupProgram inputLength accumulator value)
    (run_preserveRightProgram bitSerialMulProgram inputLength
      (bitSerialMulBits inputLength accumulator value)
      (bitSerialMulFuel value) (bitSerialMulInput accumulator value) value
      (accumulator * value)
      (run_bitSerialMulProgram inputLength accumulator value))

private def powLoopProgram : ℕ → NPOracleProgram
  | 0 => [ .halt 0 ]
  | exponent + 1 => linkPrograms powStepProgram (powLoopProgram exponent)

private theorem powLoopProgram_oracleFree : ∀ exponent : ℕ,
    OracleFree (powLoopProgram exponent)
  | 0 => by rfl
  | exponent + 1 =>
      oracleFree_linkPrograms powStepProgram_oracleFree
        (powLoopProgram_oracleFree exponent)

def powLoopFuel : ℕ → ℕ → ℕ
  | 0, _ => 1
  | exponent + 1, value =>
      linkFuel (powLoopProgram exponent) (powStepFuel value)
        (powLoopFuel exponent value)

def powLoopBits (inputLength : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, accumulator, value => natBitLength (Nat.pair accumulator value)
  | exponent + 1, accumulator, value =>
      occurrenceStageBits inputLength
        (powStepBits inputLength accumulator value)
        (powLoopBits inputLength exponent (accumulator * value) value)

private theorem run_powLoopProgram (inputLength : ℕ) :
    ∀ exponent accumulator value : ℕ,
      runNPOracleProgram (powLoopProgram exponent)
          (powLoopBits inputLength exponent accumulator value)
          (powLoopFuel exponent value)
          (initialNPOracleState inputLength (Nat.pair accumulator value)) =
        some (Nat.pair (accumulator * value ^ exponent) value)
  | 0, accumulator, value => by
      have hbits :
          natBitLength (Nat.pair accumulator value) ≤
            powLoopBits inputLength 0 accumulator value := le_refl _
      rw [pow_zero, mul_one]
      exact run_halt_instruction (fuel := 0) (by rfl) rfl
        (by simp [initialNPOracleState]) hbits
  | exponent + 1, accumulator, value => by
      have hpower :
          accumulator * value ^ (exponent + 1) =
            accumulator * value * value ^ exponent := by
        ring
      rw [hpower]
      exact run_occurrenceStage
        (run_powStepProgram inputLength accumulator value)
        (run_powLoopProgram inputLength exponent (accumulator * value) value)

private def powFinishProgram : NPOracleProgram :=
  [ .unpairLeft 0 0 1
  , .halt 0
  ]

@[simp] private theorem powFinishProgram_oracleFree :
    OracleFree powFinishProgram := by
  rfl

private theorem run_powFinishProgram (inputLength left right : ℕ) :
    runNPOracleProgram powFinishProgram (natBitLength (Nat.pair left right)) 2
        (initialNPOracleState inputLength (Nat.pair left right)) =
      some left := by
  have hleft : natBitLength left ≤ natBitLength (Nat.pair left right) :=
    bits_of_le_pair_left (le_refl left)
  rw [show 2 = 1 + 1 by omega]
  rw [run_unpairLeft_instruction (value := left) (by rfl) rfl
    (by simp [initialNPOracleState]) hleft]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hleft

/-- The fixed-exponent power as one instruction stream. -/
def powProgram (exponent : ℕ) : NPOracleProgram :=
  linkPrograms (immediateFactorProgram 1)
    (linkPrograms (powLoopProgram exponent) powFinishProgram)

theorem powProgram_oracleFree (exponent : ℕ) :
    OracleFree (powProgram exponent) :=
  oracleFree_linkPrograms (immediateFactorProgram_oracleFree 1)
    (oracleFree_linkPrograms (powLoopProgram_oracleFree exponent)
      powFinishProgram_oracleFree)

def powFuel (exponent value : ℕ) : ℕ :=
  linkFuel (linkPrograms (powLoopProgram exponent) powFinishProgram) 3
    (linkFuel powFinishProgram (powLoopFuel exponent value) 2)

def powBits (inputLength exponent value : ℕ) : ℕ :=
  occurrenceStageBits inputLength (natBitLength (Nat.pair 1 value)) <|
    occurrenceStageBits inputLength (powLoopBits inputLength exponent 1 value)
      (natBitLength (Nat.pair (1 * value ^ exponent) value))

/-- **The fixed-exponent power, executed.** -/
theorem run_powProgram (inputLength exponent value : ℕ) :
    runNPOracleProgram (powProgram exponent)
        (powBits inputLength exponent value) (powFuel exponent value)
        (initialNPOracleState inputLength value) =
      some (value ^ exponent) := by
  have hrun :
      runNPOracleProgram (powProgram exponent)
          (powBits inputLength exponent value) (powFuel exponent value)
          (initialNPOracleState inputLength value) =
        some (1 * value ^ exponent) :=
    run_occurrenceStage (run_immediateFactorProgram inputLength 1 value)
      (run_occurrenceStage (run_powLoopProgram inputLength exponent 1 value)
        (run_powFinishProgram inputLength (1 * value ^ exponent) value))
  rw [one_mul] at hrun
  exact hrun

/-! ## 3. The two composite schedule numerals

The three numerals below are the exact values of
`ProjectionWidthEnvelope.widthBudget`, `RecoveryScheduleEnvelope.widthEnvelope`
and the copy counts of `RecoveryScheduleEnvelope.inverseCopiesOf`/`fixedCopiesOf`
once the published fields are read as numerals; §6 discharges the identifications.
-/

/-- The published width budget at one scheduled source length. -/
def widthBudgetValue (clockDepth coefficient exponent sourceLen : ℕ) : ℕ :=
  coefficient * pairClock clockDepth sourceLen *
    logScale (pairClock clockDepth sourceLen) ^ exponent

/-- The scheduled width at one scheduled source length. -/
def widthValue (clockDepth coefficient exponent sourceLen : ℕ) : ℕ :=
  Nat.log 2 (widthBudgetValue clockDepth coefficient exponent sourceLen)

/-- The scheduled copy count at one scheduled width. -/
def copyCountValue (factor summand width : ℕ) : ℕ :=
  factor * logScale width + summand

/-- The published width budget's logarithmic factor, raised to the published
proof exponent. -/
def logPowProgram (exponent : ℕ) : NPOracleProgram :=
  linkPrograms logScaleProgram (powProgram exponent)

theorem logPowProgram_oracleFree (exponent : ℕ) :
    OracleFree (logPowProgram exponent) :=
  oracleFree_linkPrograms logScaleProgram_oracleFree
    (powProgram_oracleFree exponent)

def logPowFuel (exponent value : ℕ) : ℕ :=
  linkFuel (powProgram exponent) (logScaleFuel value)
    (powFuel exponent (logScale value))

def logPowBits (inputLength exponent value : ℕ) : ℕ :=
  occurrenceStageBits inputLength (logScaleBits inputLength value)
    (powBits inputLength exponent (logScale value))

theorem run_logPowProgram (inputLength exponent value : ℕ) :
    runNPOracleProgram (logPowProgram exponent)
        (logPowBits inputLength exponent value) (logPowFuel exponent value)
        (initialNPOracleState inputLength value) =
      some (logScale value ^ exponent) :=
  run_occurrenceStage (run_logScaleProgram inputLength value)
    (run_powProgram inputLength exponent (logScale value))

/-- The published width budget from the scheduled clock value. -/
def widthBudgetCoreProgram (coefficient exponent : ℕ) : NPOracleProgram :=
  linkPrograms pairStepProgram <|
    linkPrograms (preserveRightProgram (logPowProgram exponent)) <|
      linkPrograms bitSerialMulProgram (immediateMulProgram coefficient)

theorem widthBudgetCoreProgram_oracleFree (coefficient exponent : ℕ) :
    OracleFree (widthBudgetCoreProgram coefficient exponent) :=
  oracleFree_linkPrograms pairStepProgram_oracleFree
    (oracleFree_linkPrograms
      (preserveRightProgram_oracleFree (logPowProgram exponent)
        (logPowProgram_oracleFree exponent))
      (oracleFree_linkPrograms bitSerialMulProgram_oracleFree
        (immediateMulProgram_oracleFree coefficient)))

def widthBudgetCoreFuel (coefficient exponent value : ℕ) : ℕ :=
  linkFuel
    (linkPrograms (preserveRightProgram (logPowProgram exponent))
      (linkPrograms bitSerialMulProgram (immediateMulProgram coefficient)))
    2 <|
    linkFuel (linkPrograms bitSerialMulProgram (immediateMulProgram coefficient))
      (preserveRightFuel (logPowFuel exponent value)) <|
      linkFuel (immediateMulProgram coefficient) (bitSerialMulFuel value)
        (immediateMulFuel (logScale value ^ exponent * value))

def widthBudgetCoreBits (inputLength coefficient exponent value : ℕ) : ℕ :=
  occurrenceStageBits inputLength (natBitLength (Nat.pair value value)) <|
    occurrenceStageBits inputLength
      (preserveRightBits (logPowBits inputLength exponent value) value value
        (logScale value ^ exponent)) <|
      occurrenceStageBits inputLength
        (bitSerialMulBits inputLength (logScale value ^ exponent) value)
        (immediateMulBits inputLength coefficient
          (logScale value ^ exponent * value))

/-- **The published width budget, executed.** -/
theorem run_widthBudgetCoreProgram
    (inputLength coefficient exponent value : ℕ) :
    runNPOracleProgram (widthBudgetCoreProgram coefficient exponent)
        (widthBudgetCoreBits inputLength coefficient exponent value)
        (widthBudgetCoreFuel coefficient exponent value)
        (initialNPOracleState inputLength value) =
      some (coefficient * value * logScale value ^ exponent) := by
  have hproduct :
      coefficient * value * logScale value ^ exponent =
        coefficient * (logScale value ^ exponent * value) := by
    ring
  rw [hproduct]
  exact run_occurrenceStage (run_pairStepProgram inputLength value)
    (run_occurrenceStage
      (run_preserveRightProgram (logPowProgram exponent) inputLength
        (logPowBits inputLength exponent value) (logPowFuel exponent value)
        value value (logScale value ^ exponent)
        (run_logPowProgram inputLength exponent value))
      (run_occurrenceStage
        (run_bitSerialMulProgram inputLength (logScale value ^ exponent) value)
        (run_immediateMulProgram inputLength coefficient
          (logScale value ^ exponent * value))))

/-- The scheduled width from the scheduled source length: the pairing clock,
the published width budget, and one base-two logarithm. -/
def widthEnvelopeProgram (clockDepth coefficient exponent : ℕ) :
    NPOracleProgram :=
  linkPrograms (pairIterProgram clockDepth)
    (linkPrograms (widthBudgetCoreProgram coefficient exponent) floorLogProgram)

theorem widthEnvelopeProgram_oracleFree (clockDepth coefficient exponent : ℕ) :
    OracleFree (widthEnvelopeProgram clockDepth coefficient exponent) :=
  oracleFree_linkPrograms (pairIterProgram_oracleFree clockDepth)
    (oracleFree_linkPrograms
      (widthBudgetCoreProgram_oracleFree coefficient exponent)
      floorLogProgram_oracleFree)

def widthEnvelopeFuel (clockDepth coefficient exponent sourceLen : ℕ) : ℕ :=
  linkFuel
    (linkPrograms (widthBudgetCoreProgram coefficient exponent)
      floorLogProgram)
    (pairIterFuel clockDepth) <|
    linkFuel floorLogProgram
      (widthBudgetCoreFuel coefficient exponent (pairClock clockDepth sourceLen))
      (floorLogFuel (widthBudgetValue clockDepth coefficient exponent sourceLen))

def widthEnvelopeBits (inputLength clockDepth coefficient exponent
    sourceLen : ℕ) : ℕ :=
  occurrenceStageBits inputLength
    (pairIterBits inputLength clockDepth sourceLen) <|
    occurrenceStageBits inputLength
      (widthBudgetCoreBits inputLength coefficient exponent
        (pairClock clockDepth sourceLen))
      (floorLogBits inputLength
        (widthBudgetValue clockDepth coefficient exponent sourceLen))

/-- **The scheduled width, executed.**  The published budget's positivity is
the only hypothesis: it is exactly `ProjectionWidthEnvelope.widthBudget_positive`
at the scheduled length. -/
theorem run_widthEnvelopeProgram
    (inputLength clockDepth coefficient exponent sourceLen : ℕ)
    (hbudget : 1 ≤ widthBudgetValue clockDepth coefficient exponent sourceLen) :
    runNPOracleProgram (widthEnvelopeProgram clockDepth coefficient exponent)
        (widthEnvelopeBits inputLength clockDepth coefficient exponent sourceLen)
        (widthEnvelopeFuel clockDepth coefficient exponent sourceLen)
        (initialNPOracleState inputLength sourceLen) =
      some (widthValue clockDepth coefficient exponent sourceLen) :=
  run_occurrenceStage
    (run_pairIterProgram_pairClock inputLength clockDepth sourceLen)
    (run_occurrenceStage
      (run_widthBudgetCoreProgram inputLength coefficient exponent
        (pairClock clockDepth sourceLen))
      (run_floorLogProgram inputLength
        (widthBudgetValue clockDepth coefficient exponent sourceLen) hbudget))

/-- The scheduled copy count: one logarithmic scale of the scheduled width,
one frozen factor, one frozen offset. -/
def copyCountProgram (factor summand : ℕ) : NPOracleProgram :=
  linkPrograms logScaleProgram
    (linkPrograms (immediateMulProgram factor) (immediateAddProgram summand))

theorem copyCountProgram_oracleFree (factor summand : ℕ) :
    OracleFree (copyCountProgram factor summand) :=
  oracleFree_linkPrograms logScaleProgram_oracleFree
    (oracleFree_linkPrograms (immediateMulProgram_oracleFree factor)
      (immediateAddProgram_oracleFree summand))

def copyCountFuel (factor summand width : ℕ) : ℕ :=
  linkFuel
    (linkPrograms (immediateMulProgram factor) (immediateAddProgram summand))
    (logScaleFuel width) <|
    linkFuel (immediateAddProgram summand) (immediateMulFuel (logScale width)) 3

def copyCountBits (inputLength factor summand width : ℕ) : ℕ :=
  occurrenceStageBits inputLength (logScaleBits inputLength width) <|
    occurrenceStageBits inputLength
      (immediateMulBits inputLength factor (logScale width))
      (immediateAddBits summand (factor * logScale width))

/-- **The scheduled copy count, executed.** -/
theorem run_copyCountProgram (inputLength factor summand width : ℕ) :
    runNPOracleProgram (copyCountProgram factor summand)
        (copyCountBits inputLength factor summand width)
        (copyCountFuel factor summand width)
        (initialNPOracleState inputLength width) =
      some (copyCountValue factor summand width) :=
  run_occurrenceStage (run_logScaleProgram inputLength width)
    (run_occurrenceStage
      (run_immediateMulProgram inputLength factor (logScale width))
      (run_immediateAddProgram inputLength summand (factor * logScale width)))

/-! ## 4. The framing adapters -/

private theorem le_pair_left {value left right : ℕ} (hvalue : value ≤ left) :
    value ≤ Nat.pair left right :=
  hvalue.trans (Nat.left_le_pair left right)

private theorem le_pair_right {value left right : ℕ} (hvalue : value ≤ right) :
    value ≤ Nat.pair left right :=
  hvalue.trans (Nat.right_le_pair left right)

/-- Discard the head of a frame. -/
private def dropLeftProgram : NPOracleProgram :=
  [ .unpairRight 0 0 1
  , .halt 0
  ]

@[simp] private theorem dropLeftProgram_oracleFree :
    OracleFree dropLeftProgram := by
  rfl

private def dropLeftBits (left right : ℕ) : ℕ :=
  natBitLength (Nat.pair left right)

private theorem run_dropLeftProgram (inputLength left right : ℕ) :
    runNPOracleProgram dropLeftProgram (dropLeftBits left right) 2
        (initialNPOracleState inputLength (Nat.pair left right)) =
      some right := by
  have hright : natBitLength right ≤ dropLeftBits left right :=
    natBitLength_mono (Nat.right_le_pair left right)
  rw [show 2 = 1 + 1 by omega]
  rw [run_unpairRight_instruction (value := right) (by rfl) rfl
    (by simp [initialNPOracleState]) hright]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hright

/-- Duplicate the head of a frame in front of the frame itself. -/
private def dupLeftProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .pair 2 0 0 2
  , .halt 0
  ]

@[simp] private theorem dupLeftProgram_oracleFree :
    OracleFree dupLeftProgram := by
  rfl

private def dupLeftBits (left right : ℕ) : ℕ :=
  natBitLength (Nat.pair left (Nat.pair left right))

private theorem run_dupLeftProgram (inputLength left right : ℕ) :
    runNPOracleProgram dupLeftProgram (dupLeftBits left right) 3
        (initialNPOracleState inputLength (Nat.pair left right)) =
      some (Nat.pair left (Nat.pair left right)) := by
  have houtput :
      natBitLength (Nat.pair left (Nat.pair left right)) ≤
        dupLeftBits left right := le_refl _
  have hleft : natBitLength left ≤ dupLeftBits left right :=
    natBitLength_mono (le_pair_left (le_refl left))
  rw [show 3 = 2 + 1 by omega]
  rw [run_unpairLeft_instruction (value := left) (by rfl) rfl
    (by simp [initialNPOracleState]) hleft]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair left (Nat.pair left right))
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

/-- Reframe the completed arithmetic as the shape runner's call request: the
scheduled source length is both the callee's public length and its request
code, and the numerals already decided ride along as retained context. -/
private def queryCallFrameProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .unpairLeft 5 6 5
  , .unpairRight 5 7 6
  , .pair 2 7 8 7
  , .pair 4 8 9 8
  , .pair 6 9 10 9
  , .pair 6 10 0 10
  , .halt 0
  ]

@[simp] private theorem queryCallFrameProgram_oracleFree :
    OracleFree queryCallFrameProgram := by
  rfl

/-- Public output of the bank's arithmetic front end: the scheduled copy count,
the scheduled width, the scheduled source length, and the retained request
code. -/
def bankFrontOutput (copies width sourceLen code : ℕ) : ℕ :=
  Nat.pair copies (Nat.pair width (Nat.pair sourceLen code))

private def queryCallFrameOutput (copies width sourceLen code : ℕ) : ℕ :=
  Nat.pair sourceLen
    (Nat.pair sourceLen (Nat.pair width (Nat.pair copies code)))

private def queryCallFrameBits (copies width sourceLen code : ℕ) : ℕ :=
  natBitLength
    (max (bankFrontOutput copies width sourceLen code)
      (queryCallFrameOutput copies width sourceLen code))

private theorem run_queryCallFrameProgram
    (inputLength copies width sourceLen code : ℕ) :
    runNPOracleProgram queryCallFrameProgram
        (queryCallFrameBits copies width sourceLen code) 11
        (initialNPOracleState inputLength
          (bankFrontOutput copies width sourceLen code)) =
      some (queryCallFrameOutput copies width sourceLen code) := by
  have hrequest : ∀ value : ℕ,
      value ≤ bankFrontOutput copies width sourceLen code →
      natBitLength value ≤ queryCallFrameBits copies width sourceLen code :=
    fun _ hvalue => natBitLength_mono (hvalue.trans (Nat.le_max_left _ _))
  have hresult : ∀ value : ℕ,
      value ≤ queryCallFrameOutput copies width sourceLen code →
      natBitLength value ≤ queryCallFrameBits copies width sourceLen code :=
    fun _ hvalue => natBitLength_mono (hvalue.trans (Nat.le_max_right _ _))
  have hcopies := hrequest copies (le_pair_left (le_refl copies))
  have htail :=
    hrequest (Nat.pair width (Nat.pair sourceLen code))
      (le_pair_right (le_refl _))
  have hwidth :=
    hrequest width (le_pair_right (le_pair_left (le_refl width)))
  have hinner :=
    hrequest (Nat.pair sourceLen code)
      (le_pair_right (le_pair_right (le_refl _)))
  have hsourceLen :=
    hrequest sourceLen
      (le_pair_right (le_pair_right (le_pair_left (le_refl sourceLen))))
  have hcode :=
    hrequest code
      (le_pair_right (le_pair_right (le_pair_right (le_refl code))))
  have hcopyCode :=
    hresult (Nat.pair copies code)
      (le_pair_right (le_pair_right (le_pair_right (le_refl _))))
  have hwidthFrame :=
    hresult (Nat.pair width (Nat.pair copies code))
      (le_pair_right (le_pair_right (le_refl _)))
  have hlengthFrame :=
    hresult (Nat.pair sourceLen (Nat.pair width (Nat.pair copies code)))
      (le_pair_right (le_refl _))
  have houtput := hresult _ (le_refl _)
  rw [show 11 = 10 + 1 by omega]
  rw [run_unpairLeft_instruction (value := copies) (by rfl) rfl
    (by simp [initialNPOracleState, bankFrontOutput]) hcopies]
  rw [show 10 = 9 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := Nat.pair width (Nat.pair sourceLen code)) (by rfl) rfl
    (by
      simp [initialNPOracleState, bankFrontOutput, NPOracleState.write,
        NPOracleState.jump])
    htail]
  rw [show 9 = 8 + 1 by omega]
  rw [run_unpairLeft_instruction (value := width) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hwidth]
  rw [show 8 = 7 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair sourceLen code)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hinner]
  rw [show 7 = 6 + 1 by omega]
  rw [run_unpairLeft_instruction (value := sourceLen) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hsourceLen]
  rw [show 6 = 5 + 1 by omega]
  rw [run_unpairRight_instruction (value := code) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hcode]
  rw [show 5 = 4 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair copies code) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hcopyCode]
  rw [show 4 = 3 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair width (Nat.pair copies code))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hwidthFrame]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair sourceLen (Nat.pair width (Nat.pair copies code)))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hlengthFrame]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction
    (value := queryCallFrameOutput copies width sourceLen code) (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, queryCallFrameOutput])
    houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

/-- Read the scheduled query count off the shape runner's output code and
restore the bank's public frame. -/
private def queryCountFrameProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 2 2 2
  , .unpairRight 0 3 3
  , .unpairLeft 3 4 4
  , .unpairRight 3 5 5
  , .unpairLeft 5 6 6
  , .unpairRight 5 7 7
  , .pair 2 7 8 8
  , .pair 6 8 9 9
  , .pair 4 9 0 10
  , .halt 0
  ]

@[simp] private theorem queryCountFrameProgram_oracleFree :
    OracleFree queryCountFrameProgram := by
  rfl

/-- Public output of the bank: the scheduled source length, the scheduled
width, the scheduled query count, the scheduled copy count, and the retained
request code. -/
def scheduleNumeralBankOutput
    (sourceLen width queryCount copies code : ℕ) : ℕ :=
  Nat.pair sourceLen
    (Nat.pair width (Nat.pair queryCount (Nat.pair copies code)))

private def queryCountFrameInput
    (shapeOutput sourceLen width copies code : ℕ) : ℕ :=
  Nat.pair shapeOutput
    (Nat.pair sourceLen (Nat.pair width (Nat.pair copies code)))

private def queryCountFrameBits
    (shapeOutput sourceLen width copies code : ℕ) : ℕ :=
  natBitLength
    (max (queryCountFrameInput shapeOutput sourceLen width copies code)
      (scheduleNumeralBankOutput sourceLen width
        (Nat.unpair shapeOutput).2 copies code))

private theorem run_queryCountFrameProgram
    (inputLength shapeOutput sourceLen width copies code : ℕ) :
    runNPOracleProgram queryCountFrameProgram
        (queryCountFrameBits shapeOutput sourceLen width copies code) 11
        (initialNPOracleState inputLength
          (queryCountFrameInput shapeOutput sourceLen width copies code)) =
      some
        (scheduleNumeralBankOutput sourceLen width
          (Nat.unpair shapeOutput).2 copies code) := by
  have hrequest : ∀ value : ℕ,
      value ≤ queryCountFrameInput shapeOutput sourceLen width copies code →
      natBitLength value ≤
        queryCountFrameBits shapeOutput sourceLen width copies code :=
    fun _ hvalue => natBitLength_mono (hvalue.trans (Nat.le_max_left _ _))
  have hresult : ∀ value : ℕ,
      value ≤
        scheduleNumeralBankOutput sourceLen width
          (Nat.unpair shapeOutput).2 copies code →
      natBitLength value ≤
        queryCountFrameBits shapeOutput sourceLen width copies code :=
    fun _ hvalue => natBitLength_mono (hvalue.trans (Nat.le_max_right _ _))
  have hshape := hrequest shapeOutput (le_pair_left (le_refl shapeOutput))
  have hcount :=
    hrequest (Nat.unpair shapeOutput).2
      (le_pair_left (Nat.unpair_right_le shapeOutput))
  have htail :=
    hrequest (Nat.pair sourceLen (Nat.pair width (Nat.pair copies code)))
      (le_pair_right (le_refl _))
  have hsourceLen :=
    hrequest sourceLen (le_pair_right (le_pair_left (le_refl sourceLen)))
  have hinner :=
    hrequest (Nat.pair width (Nat.pair copies code))
      (le_pair_right (le_pair_right (le_refl _)))
  have hwidth :=
    hrequest width
      (le_pair_right (le_pair_right (le_pair_left (le_refl width))))
  have hcopyFrame :=
    hrequest (Nat.pair copies code)
      (le_pair_right (le_pair_right (le_pair_right (le_refl _))))
  have hcountFrame :=
    hresult (Nat.pair (Nat.unpair shapeOutput).2 (Nat.pair copies code))
      (le_pair_right (le_pair_right (le_refl _)))
  have hwidthFrame :=
    hresult
      (Nat.pair width
        (Nat.pair (Nat.unpair shapeOutput).2 (Nat.pair copies code)))
      (le_pair_right (le_refl _))
  have houtput := hresult _ (le_refl _)
  rw [show 11 = 10 + 1 by omega]
  rw [run_unpairLeft_instruction (value := shapeOutput) (by rfl) rfl
    (by simp [initialNPOracleState, queryCountFrameInput]) hshape]
  rw [show 10 = 9 + 1 by omega]
  rw [run_unpairRight_instruction (value := (Nat.unpair shapeOutput).2)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hcount]
  rw [show 9 = 8 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := Nat.pair sourceLen (Nat.pair width (Nat.pair copies code)))
    (by rfl) rfl
    (by
      simp [initialNPOracleState, queryCountFrameInput, NPOracleState.write,
        NPOracleState.jump])
    htail]
  rw [show 8 = 7 + 1 by omega]
  rw [run_unpairLeft_instruction (value := sourceLen) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hsourceLen]
  rw [show 7 = 6 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := Nat.pair width (Nat.pair copies code)) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hinner]
  rw [show 6 = 5 + 1 by omega]
  rw [run_unpairLeft_instruction (value := width) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hwidth]
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair copies code) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hcopyFrame]
  rw [show 4 = 3 + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair (Nat.unpair shapeOutput).2 (Nat.pair copies code))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hcountFrame]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction
    (value :=
      Nat.pair width
        (Nat.pair (Nat.unpair shapeOutput).2 (Nat.pair copies code)))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hwidthFrame]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction
    (value :=
      scheduleNumeralBankOutput sourceLen width (Nat.unpair shapeOutput).2
        copies code)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump,
        scheduleNumeralBankOutput])
    houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

/-! ## 5. The arithmetic front end

The five stages below are linked one at a time: every intermediate frame is a
named program with its own width, clock, and exact-execution theorem, so no
composed instruction span is ever unfolded to justify the next link.
-/

/-- The scheduled source length the bank decodes from the public length. -/
def bankSourceLength (inputLength : ℕ) : ℕ :=
  sourceLength (sourceIndexOfLength inputLength)

/-- The scheduled width the bank computes from the public length. -/
def bankWidth (clockDepth coefficient exponent inputLength : ℕ) : ℕ :=
  widthValue clockDepth coefficient exponent (bankSourceLength inputLength)

/-- The scheduled copy count the bank computes from the public length. -/
def bankCopyCount
    (clockDepth coefficient exponent factor summand inputLength : ℕ) : ℕ :=
  copyCountValue factor summand
    (bankWidth clockDepth coefficient exponent inputLength)

/-! ### The decoded scheduled length -/

private def bankLengthProgram : NPOracleProgram :=
  linkPrograms scheduleDecoderProgram dropLeftProgram

private def bankLengthFuel (inputLength : ℕ) : ℕ :=
  linkFuel dropLeftProgram (scheduleDecoderFuel inputLength) 2

private def bankLengthBits (inputLength code : ℕ) : ℕ :=
  occurrenceStageBits inputLength (scheduleDecoderBits inputLength code)
    (dropLeftBits (sourceIndexOfLength inputLength)
      (Nat.pair (bankSourceLength inputLength) code))

private theorem run_bankLengthProgram (inputLength code : ℕ) :
    runNPOracleProgram bankLengthProgram (bankLengthBits inputLength code)
        (bankLengthFuel inputLength)
        (initialNPOracleState inputLength code) =
      some (Nat.pair (bankSourceLength inputLength) code) :=
  run_occurrenceStage (run_scheduleDecoderProgram inputLength code)
    (run_dropLeftProgram inputLength (sourceIndexOfLength inputLength)
      (Nat.pair (bankSourceLength inputLength) code))

private def bankLengthDupProgram : NPOracleProgram :=
  linkPrograms bankLengthProgram dupLeftProgram

private def bankLengthDupFuel (inputLength : ℕ) : ℕ :=
  linkFuel dupLeftProgram (bankLengthFuel inputLength) 3

private def bankLengthDupBits (inputLength code : ℕ) : ℕ :=
  occurrenceStageBits inputLength (bankLengthBits inputLength code)
    (dupLeftBits (bankSourceLength inputLength) code)

private theorem run_bankLengthDupProgram (inputLength code : ℕ) :
    runNPOracleProgram bankLengthDupProgram
        (bankLengthDupBits inputLength code) (bankLengthDupFuel inputLength)
        (initialNPOracleState inputLength code) =
      some
        (Nat.pair (bankSourceLength inputLength)
          (Nat.pair (bankSourceLength inputLength) code)) :=
  run_occurrenceStage (run_bankLengthProgram inputLength code)
    (run_dupLeftProgram inputLength (bankSourceLength inputLength) code)

/-! ### The scheduled width -/

private def bankWidthProgram
    (clockDepth coefficient exponent : ℕ) : NPOracleProgram :=
  linkPrograms bankLengthDupProgram
    (preserveRightProgram (widthEnvelopeProgram clockDepth coefficient exponent))

private def bankWidthFuel
    (clockDepth coefficient exponent inputLength : ℕ) : ℕ :=
  linkFuel
    (preserveRightProgram (widthEnvelopeProgram clockDepth coefficient exponent))
    (bankLengthDupFuel inputLength)
    (preserveRightFuel
      (widthEnvelopeFuel clockDepth coefficient exponent
        (bankSourceLength inputLength)))

private def bankWidthBits
    (clockDepth coefficient exponent inputLength code : ℕ) : ℕ :=
  occurrenceStageBits inputLength (bankLengthDupBits inputLength code)
    (preserveRightBits
      (widthEnvelopeBits inputLength clockDepth coefficient exponent
        (bankSourceLength inputLength))
      (bankSourceLength inputLength)
      (Nat.pair (bankSourceLength inputLength) code)
      (bankWidth clockDepth coefficient exponent inputLength))

private theorem run_bankWidthProgram
    (clockDepth coefficient exponent inputLength code : ℕ)
    (hbudget :
      1 ≤
        widthBudgetValue clockDepth coefficient exponent
          (bankSourceLength inputLength)) :
    runNPOracleProgram (bankWidthProgram clockDepth coefficient exponent)
        (bankWidthBits clockDepth coefficient exponent inputLength code)
        (bankWidthFuel clockDepth coefficient exponent inputLength)
        (initialNPOracleState inputLength code) =
      some
        (Nat.pair (bankWidth clockDepth coefficient exponent inputLength)
          (Nat.pair (bankSourceLength inputLength) code)) :=
  run_occurrenceStage (run_bankLengthDupProgram inputLength code)
    (run_preserveRightProgram
      (widthEnvelopeProgram clockDepth coefficient exponent) inputLength
      (widthEnvelopeBits inputLength clockDepth coefficient exponent
        (bankSourceLength inputLength))
      (widthEnvelopeFuel clockDepth coefficient exponent
        (bankSourceLength inputLength))
      (bankSourceLength inputLength)
      (Nat.pair (bankSourceLength inputLength) code)
      (bankWidth clockDepth coefficient exponent inputLength)
      (run_widthEnvelopeProgram inputLength clockDepth coefficient exponent
        (bankSourceLength inputLength) hbudget))

private def bankWidthDupProgram
    (clockDepth coefficient exponent : ℕ) : NPOracleProgram :=
  linkPrograms (bankWidthProgram clockDepth coefficient exponent) dupLeftProgram

private def bankWidthDupFuel
    (clockDepth coefficient exponent inputLength : ℕ) : ℕ :=
  linkFuel dupLeftProgram
    (bankWidthFuel clockDepth coefficient exponent inputLength) 3

private def bankWidthDupBits
    (clockDepth coefficient exponent inputLength code : ℕ) : ℕ :=
  occurrenceStageBits inputLength
    (bankWidthBits clockDepth coefficient exponent inputLength code)
    (dupLeftBits (bankWidth clockDepth coefficient exponent inputLength)
      (Nat.pair (bankSourceLength inputLength) code))

private theorem run_bankWidthDupProgram
    (clockDepth coefficient exponent inputLength code : ℕ)
    (hbudget :
      1 ≤
        widthBudgetValue clockDepth coefficient exponent
          (bankSourceLength inputLength)) :
    runNPOracleProgram (bankWidthDupProgram clockDepth coefficient exponent)
        (bankWidthDupBits clockDepth coefficient exponent inputLength code)
        (bankWidthDupFuel clockDepth coefficient exponent inputLength)
        (initialNPOracleState inputLength code) =
      some
        (Nat.pair (bankWidth clockDepth coefficient exponent inputLength)
          (Nat.pair (bankWidth clockDepth coefficient exponent inputLength)
            (Nat.pair (bankSourceLength inputLength) code))) :=
  run_occurrenceStage
    (run_bankWidthProgram clockDepth coefficient exponent inputLength code
      hbudget)
    (run_dupLeftProgram inputLength
      (bankWidth clockDepth coefficient exponent inputLength)
      (Nat.pair (bankSourceLength inputLength) code))

/-! ### The scheduled copy count -/

/-- The bank's arithmetic front end: the published schedule decoder, the
scheduled width, and the scheduled copy count. -/
def bankFrontProgram
    (clockDepth coefficient exponent factor summand : ℕ) : NPOracleProgram :=
  linkPrograms (bankWidthDupProgram clockDepth coefficient exponent)
    (preserveRightProgram (copyCountProgram factor summand))

def bankFrontFuel
    (clockDepth coefficient exponent factor summand inputLength : ℕ) : ℕ :=
  linkFuel (preserveRightProgram (copyCountProgram factor summand))
    (bankWidthDupFuel clockDepth coefficient exponent inputLength)
    (preserveRightFuel
      (copyCountFuel factor summand
        (bankWidth clockDepth coefficient exponent inputLength)))

def bankFrontBits
    (clockDepth coefficient exponent factor summand inputLength code : ℕ) : ℕ :=
  occurrenceStageBits inputLength
    (bankWidthDupBits clockDepth coefficient exponent inputLength code)
    (preserveRightBits
      (copyCountBits inputLength factor summand
        (bankWidth clockDepth coefficient exponent inputLength))
      (bankWidth clockDepth coefficient exponent inputLength)
      (Nat.pair (bankWidth clockDepth coefficient exponent inputLength)
        (Nat.pair (bankSourceLength inputLength) code))
      (bankCopyCount clockDepth coefficient exponent factor summand
        inputLength))

/-- **The arithmetic front end, executed.**  The published width budget's
positivity at the scheduled length is the only side condition. -/
theorem run_bankFrontProgram
    (clockDepth coefficient exponent factor summand inputLength code : ℕ)
    (hbudget :
      1 ≤
        widthBudgetValue clockDepth coefficient exponent
          (bankSourceLength inputLength)) :
    runNPOracleProgram
        (bankFrontProgram clockDepth coefficient exponent factor summand)
        (bankFrontBits clockDepth coefficient exponent factor summand
          inputLength code)
        (bankFrontFuel clockDepth coefficient exponent factor summand
          inputLength)
        (initialNPOracleState inputLength code) =
      some
        (bankFrontOutput
          (bankCopyCount clockDepth coefficient exponent factor summand
            inputLength)
          (bankWidth clockDepth coefficient exponent inputLength)
          (bankSourceLength inputLength) code) :=
  run_occurrenceStage
    (run_bankWidthDupProgram clockDepth coefficient exponent inputLength code
      hbudget)
    (run_preserveRightProgram (copyCountProgram factor summand) inputLength
      (copyCountBits inputLength factor summand
        (bankWidth clockDepth coefficient exponent inputLength))
      (copyCountFuel factor summand
        (bankWidth clockDepth coefficient exponent inputLength))
      (bankWidth clockDepth coefficient exponent inputLength)
      (Nat.pair (bankWidth clockDepth coefficient exponent inputLength)
        (Nat.pair (bankSourceLength inputLength) code))
      (bankCopyCount clockDepth coefficient exponent factor summand inputLength)
      (run_copyCountProgram inputLength factor summand
        (bankWidth clockDepth coefficient exponent inputLength)))

/-! ## 6. The scheduled query count and the bank -/

private def bankCallFrameProgram
    (clockDepth coefficient exponent factor summand : ℕ) : NPOracleProgram :=
  linkPrograms (bankFrontProgram clockDepth coefficient exponent factor summand)
    queryCallFrameProgram

private def bankCallFrameFuel
    (clockDepth coefficient exponent factor summand inputLength : ℕ) : ℕ :=
  linkFuel queryCallFrameProgram
    (bankFrontFuel clockDepth coefficient exponent factor summand inputLength)
    11

private def bankCallFrameBits
    (clockDepth coefficient exponent factor summand inputLength code : ℕ) : ℕ :=
  occurrenceStageBits inputLength
    (bankFrontBits clockDepth coefficient exponent factor summand inputLength
      code)
    (queryCallFrameBits
      (bankCopyCount clockDepth coefficient exponent factor summand inputLength)
      (bankWidth clockDepth coefficient exponent inputLength)
      (bankSourceLength inputLength) code)

private theorem run_bankCallFrameProgram
    (clockDepth coefficient exponent factor summand inputLength code : ℕ)
    (hbudget :
      1 ≤
        widthBudgetValue clockDepth coefficient exponent
          (bankSourceLength inputLength)) :
    runNPOracleProgram
        (bankCallFrameProgram clockDepth coefficient exponent factor summand)
        (bankCallFrameBits clockDepth coefficient exponent factor summand
          inputLength code)
        (bankCallFrameFuel clockDepth coefficient exponent factor summand
          inputLength)
        (initialNPOracleState inputLength code) =
      some
        (queryCallFrameOutput
          (bankCopyCount clockDepth coefficient exponent factor summand
            inputLength)
          (bankWidth clockDepth coefficient exponent inputLength)
          (bankSourceLength inputLength) code) :=
  run_occurrenceStage
    (run_bankFrontProgram clockDepth coefficient exponent factor summand
      inputLength code hbudget)
    (run_queryCallFrameProgram inputLength
      (bankCopyCount clockDepth coefficient exponent factor summand inputLength)
      (bankWidth clockDepth coefficient exponent inputLength)
      (bankSourceLength inputLength) code)

private def bankCallProgram (shapeProgram : NPOracleProgram)
    (clockDepth coefficient exponent factor summand : ℕ) : NPOracleProgram :=
  linkPrograms
    (bankCallFrameProgram clockDepth coefficient exponent factor summand)
    (nativeContextCallProgram shapeProgram)

private def bankCallFuel (shapeProgram : NPOracleProgram)
    (clockDepth coefficient exponent factor summand inputLength
      shapeFuel : ℕ) : ℕ :=
  linkFuel (nativeContextCallProgram shapeProgram)
    (bankCallFrameFuel clockDepth coefficient exponent factor summand
      inputLength)
    (nativeContextCallFuel shapeProgram shapeFuel
      (bankSourceLength inputLength) (bankSourceLength inputLength))

private def bankCallBits
    (clockDepth coefficient exponent factor summand inputLength code shapeBits
      shapeOutput : ℕ) : ℕ :=
  occurrenceStageBits inputLength
    (bankCallFrameBits clockDepth coefficient exponent factor summand
      inputLength code)
    (nativeContextCallBits inputLength (bankSourceLength inputLength)
      (bankSourceLength inputLength)
      (Nat.pair (bankWidth clockDepth coefficient exponent inputLength)
        (Nat.pair
          (bankCopyCount clockDepth coefficient exponent factor summand
            inputLength)
          code))
      shapeOutput shapeBits)

private theorem run_bankCallProgram (shapeProgram : NPOracleProgram)
    (clockDepth coefficient exponent factor summand inputLength code shapeBits
      shapeFuel shapeOutput : ℕ)
    (hbudget :
      1 ≤
        widthBudgetValue clockDepth coefficient exponent
          (bankSourceLength inputLength))
    (hshape :
      runNPOracleProgram shapeProgram shapeBits shapeFuel
          (initialNPOracleState (bankSourceLength inputLength)
            (bankSourceLength inputLength)) =
        some shapeOutput) :
    runNPOracleProgram
        (bankCallProgram shapeProgram clockDepth coefficient exponent factor
          summand)
        (bankCallBits clockDepth coefficient exponent factor summand inputLength
          code shapeBits shapeOutput)
        (bankCallFuel shapeProgram clockDepth coefficient exponent factor
          summand inputLength shapeFuel)
        (initialNPOracleState inputLength code) =
      some
        (queryCountFrameInput shapeOutput (bankSourceLength inputLength)
          (bankWidth clockDepth coefficient exponent inputLength)
          (bankCopyCount clockDepth coefficient exponent factor summand
            inputLength)
          code) :=
  run_occurrenceStage
    (run_bankCallFrameProgram clockDepth coefficient exponent factor summand
      inputLength code hbudget)
    (run_nativeContextCallProgram shapeProgram inputLength
      (bankSourceLength inputLength) (bankSourceLength inputLength)
      (Nat.pair (bankWidth clockDepth coefficient exponent inputLength)
        (Nat.pair
          (bankCopyCount clockDepth coefficient exponent factor summand
            inputLength)
          code))
      shapeOutput shapeBits shapeFuel hshape)

/-- **The run-time schedule numeral bank.**  One fixed instruction stream,
parameterized by the published shape runner and by numerals that do not vary
with the request, emitting the scheduled source length, the scheduled width,
the scheduled query count and the scheduled copy count of the requested public
length beside the retained request code. -/
def scheduleNumeralBankProgram (shapeProgram : NPOracleProgram)
    (clockDepth coefficient exponent factor summand : ℕ) : NPOracleProgram :=
  linkPrograms
    (bankCallProgram shapeProgram clockDepth coefficient exponent factor summand)
    queryCountFrameProgram

def scheduleNumeralBankFuel (shapeProgram : NPOracleProgram)
    (clockDepth coefficient exponent factor summand inputLength
      shapeFuel : ℕ) : ℕ :=
  linkFuel queryCountFrameProgram
    (bankCallFuel shapeProgram clockDepth coefficient exponent factor summand
      inputLength shapeFuel)
    11

def scheduleNumeralBankBits
    (clockDepth coefficient exponent factor summand inputLength code shapeBits
      shapeOutput : ℕ) : ℕ :=
  occurrenceStageBits inputLength
    (bankCallBits clockDepth coefficient exponent factor summand inputLength
      code shapeBits shapeOutput)
    (queryCountFrameBits shapeOutput (bankSourceLength inputLength)
      (bankWidth clockDepth coefficient exponent inputLength)
      (bankCopyCount clockDepth coefficient exponent factor summand inputLength)
      code)

/-- **The numeral bank, executed.**  From the public length alone — with the
published shape runner as the only imported execution and the published width
budget's positivity as the only side condition — the fixed stream emits every
target-derived numeral of the two chains except the Case-2 substituted
circuit's encoding. -/
theorem run_scheduleNumeralBankProgram (shapeProgram : NPOracleProgram)
    (clockDepth coefficient exponent factor summand inputLength code shapeBits
      shapeFuel shapeOutput : ℕ)
    (hbudget :
      1 ≤
        widthBudgetValue clockDepth coefficient exponent
          (bankSourceLength inputLength))
    (hshape :
      runNPOracleProgram shapeProgram shapeBits shapeFuel
          (initialNPOracleState (bankSourceLength inputLength)
            (bankSourceLength inputLength)) =
        some shapeOutput) :
    runNPOracleProgram
        (scheduleNumeralBankProgram shapeProgram clockDepth coefficient exponent
          factor summand)
        (scheduleNumeralBankBits clockDepth coefficient exponent factor summand
          inputLength code shapeBits shapeOutput)
        (scheduleNumeralBankFuel shapeProgram clockDepth coefficient exponent
          factor summand inputLength shapeFuel)
        (initialNPOracleState inputLength code) =
      some
        (scheduleNumeralBankOutput (bankSourceLength inputLength)
          (bankWidth clockDepth coefficient exponent inputLength)
          (Nat.unpair shapeOutput).2
          (bankCopyCount clockDepth coefficient exponent factor summand
            inputLength)
          code) :=
  run_occurrenceStage
    (run_bankCallProgram shapeProgram clockDepth coefficient exponent factor
      summand inputLength code shapeBits shapeFuel shapeOutput hbudget hshape)
    (run_queryCountFrameProgram inputLength shapeOutput
      (bankSourceLength inputLength)
      (bankWidth clockDepth coefficient exponent inputLength)
      (bankCopyCount clockDepth coefficient exponent factor summand inputLength)
      code)

/-! ## 7. The published numerals

Every numeral the bank computes is *definitionally* the published one at the
decoded index; the four identifications below are the whole bridge, and each is
`rfl`.  The published shape runner supplies the one imported execution, and the
published proof-size bound supplies the one side condition.
-/

/-- The bank's budget numeral is the published width budget. -/
theorem widthBudgetValue_eq_widthBudget
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) (sourceLen : ℕ) :
    widthBudgetValue clockDepth outer.pcp.shape.coefficient outer.proofExponent
        sourceLen =
      ProjectionWidthEnvelope.widthBudget outer sourceLen :=
  rfl

/-- The bank's width numeral is the scheduled width at the decoded index. -/
theorem bankWidth_eq_scheduledWidth
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) (inputLength : ℕ) :
    bankWidth clockDepth outer.pcp.shape.coefficient outer.proofExponent
        inputLength =
      scheduledWidth outer (sourceIndexOfLength inputLength) :=
  rfl

/-- The bank's copy-count numeral is the inverse schedule's copy count at the
decoded index. -/
theorem bankCopyCount_eq_inverseCopies
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource) (rate inputLength : ℕ) :
    bankCopyCount clockDepth outer.pcp.shape.coefficient outer.proofExponent
        (recoveryBlock pcppSource * rate) (recoveryBlock pcppSource + 1)
        inputLength =
      inverseCopies outer pcppSource rate (sourceIndexOfLength inputLength) := by
  rw [inverseCopies_eq outer pcppSource rate (sourceIndexOfLength inputLength)]
  rw [bankCopyCount, copyCountValue,
    bankWidth_eq_scheduledWidth outer inputLength]
  ring

/-- The right component of the published shape code is the scheduled query
count: the bank reads an opaque published field at run time rather than baking
it as an immediate. -/
theorem unpair_shapeExecute_eq_queryCount
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) (sourceLen : ℕ) :
    (Nat.unpair (outer.pcp.shape.execute sourceLen)).2 =
      outer.pcp.queryCount sourceLen :=
  rfl

/-- The published shape runner, executed at its own budget. -/
theorem run_publishedShapeProgram
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) (sourceLen : ℕ) :
    runNPOracleProgram outer.pcp.shape.program
        (outer.pcp.shape.budget sourceLen) (outer.pcp.shape.budget sourceLen)
        (initialNPOracleState sourceLen sourceLen) =
      some (outer.pcp.shape.execute sourceLen) :=
  outer.pcp.shape.run_eq_execute sourceLen

/-- The published width budget is positive, which is the bank's only side
condition. -/
theorem publishedWidthBudget_positive
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) (sourceLen : ℕ) :
    1 ≤
      widthBudgetValue clockDepth outer.pcp.shape.coefficient
        outer.proofExponent sourceLen :=
  ProjectionWidthEnvelope.widthBudget_positive outer sourceLen

/-- **The published numeral bank, executed.**  One fixed instruction stream,
parameterized only by `(outer.pcp.shape.program, clockDepth,
outer.pcp.shape.coefficient, outer.proofExponent, recoveryBlock, rate)` — none
of which varies with the request — emits the scheduled source length, the
scheduled width, the scheduled query count and the inverse schedule's copy
count of the requested public length, beside the retained request code.  No
hypothesis remains. -/
theorem run_publishedScheduleNumeralBankProgram
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource) (rate inputLength code : ℕ) :
    runNPOracleProgram
        (scheduleNumeralBankProgram outer.pcp.shape.program clockDepth
          outer.pcp.shape.coefficient outer.proofExponent
          (recoveryBlock pcppSource * rate) (recoveryBlock pcppSource + 1))
        (scheduleNumeralBankBits clockDepth outer.pcp.shape.coefficient
          outer.proofExponent (recoveryBlock pcppSource * rate)
          (recoveryBlock pcppSource + 1) inputLength code
          (outer.pcp.shape.budget (bankSourceLength inputLength))
          (outer.pcp.shape.execute (bankSourceLength inputLength)))
        (scheduleNumeralBankFuel outer.pcp.shape.program clockDepth
          outer.pcp.shape.coefficient outer.proofExponent
          (recoveryBlock pcppSource * rate) (recoveryBlock pcppSource + 1)
          inputLength (outer.pcp.shape.budget (bankSourceLength inputLength)))
        (initialNPOracleState inputLength code) =
      some
        (scheduleNumeralBankOutput (bankSourceLength inputLength)
          (scheduledWidth outer (sourceIndexOfLength inputLength))
          (outer.pcp.queryCount (bankSourceLength inputLength))
          (inverseCopies outer pcppSource rate (sourceIndexOfLength inputLength))
          code) := by
  have hwidth :
      scheduledWidth outer (sourceIndexOfLength inputLength) =
        bankWidth clockDepth outer.pcp.shape.coefficient outer.proofExponent
          inputLength :=
    (bankWidth_eq_scheduledWidth outer inputLength).symm
  have hcopies :
      inverseCopies outer pcppSource rate (sourceIndexOfLength inputLength) =
        bankCopyCount clockDepth outer.pcp.shape.coefficient
          outer.proofExponent (recoveryBlock pcppSource * rate)
          (recoveryBlock pcppSource + 1) inputLength :=
    (bankCopyCount_eq_inverseCopies outer pcppSource rate inputLength).symm
  have hcount :
      outer.pcp.queryCount (bankSourceLength inputLength) =
        (Nat.unpair (outer.pcp.shape.execute (bankSourceLength inputLength))).2 :=
    (unpair_shapeExecute_eq_queryCount outer (bankSourceLength inputLength)).symm
  rw [hwidth, hcopies, hcount]
  exact run_scheduleNumeralBankProgram outer.pcp.shape.program clockDepth
    outer.pcp.shape.coefficient outer.proofExponent
    (recoveryBlock pcppSource * rate) (recoveryBlock pcppSource + 1) inputLength
    code (outer.pcp.shape.budget (bankSourceLength inputLength))
    (outer.pcp.shape.budget (bankSourceLength inputLength))
    (outer.pcp.shape.execute (bankSourceLength inputLength))
    (publishedWidthBudget_positive outer (bankSourceLength inputLength))
    (run_publishedShapeProgram outer (bankSourceLength inputLength))

/-! ## 8. The bank on the scheduled diagonal

At a public length that is itself a scheduled source length the bank's decoded
index is that source's own, so every emitted numeral is the chain's numeral at
that source index.  These are the identities a register-driven chain body uses
to recognize the bank's frame.
-/

@[simp] theorem bankSourceLength_sourceLength (sourceIndex : ℕ) :
    bankSourceLength (sourceLength sourceIndex) = sourceLength sourceIndex := by
  rw [bankSourceLength, sourceIndexOfLength_sourceLength]

theorem bankWidth_at_sourceLength
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) (sourceIndex : ℕ) :
    bankWidth clockDepth outer.pcp.shape.coefficient outer.proofExponent
        (sourceLength sourceIndex) =
      scheduledWidth outer sourceIndex := by
  rw [bankWidth_eq_scheduledWidth outer (sourceLength sourceIndex),
    sourceIndexOfLength_sourceLength]

theorem bankCopyCount_at_sourceLength
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource) (rate sourceIndex : ℕ) :
    bankCopyCount clockDepth outer.pcp.shape.coefficient outer.proofExponent
        (recoveryBlock pcppSource * rate) (recoveryBlock pcppSource + 1)
        (sourceLength sourceIndex) =
      inverseCopies outer pcppSource rate sourceIndex := by
  rw [bankCopyCount_eq_inverseCopies outer pcppSource rate
    (sourceLength sourceIndex), sourceIndexOfLength_sourceLength]

end NearCubicWires.RuntimeScheduleNumeralBank
