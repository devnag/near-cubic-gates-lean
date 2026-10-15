import Proof.MachineModel.CanonicalNativeModProgram

/-!
# Bit-serial native-natural remainder

The earlier native remainder controller consumes one instruction group per
numeric unit of its numerator.  That exact implementation remains useful when
the numerator is already publicly bounded, but it is not an admissible decoder
for an arbitrary binary code.  This module supplies the one production
alternative: scan the numerator from its most significant bit and reduce after
each bit, so runtime depends on the numerator's binary width alone.

## Why the reduction is one saturating subtraction and not a counting loop

Every candidate entering the reduction is `2 * remainder + bit` with
`remainder < denominator`, hence strictly below `2 * denominator`; a single
conditional subtraction is therefore the whole reduction.  The earlier stage
executed that subtraction — and the doubling preceding it — as unary register
loops, so its charge contained `4 * remainder` and
`4 * min candidate denominator`.  Summed over the numerator's bits that is
`Θ(bits numerator · denominator)`, which is exponential in the width of the
public denominator.  That budget is affordable inside an exponential-time
caller, but the recovery-witness validator is charged against a *polynomial*
envelope and this stage sits on its critical path.

The production stage therefore uses the fixed-cost register operations the
machine already provides: `shiftLeft` for the doubling, `add` for the incoming
bit, and two `subtract` instructions for the reduction.  The saturating gap
`denominator - candidate` vanishes exactly when `denominator ≤ candidate`, so
the branch deciding whether to subtract is a plain zero test.  One numerator
bit now costs at most nine instructions, independently of every operand's
magnitude.

The public surface — `bitSerialModInput`, `bitSerialModProgram`,
`bitSerialModProgram_oracleFree`, `bitSerialModScan`, `bitSerialCountFuel`,
`bitSerialOuterFuel`, `bitSerialModFuel`, `bitSerialModRegisterBound`,
`bitSerialModBits`, `bitSerialModScan_eq_mod`, `run_bitSerialModProgram`,
`bitSerialModRegisterBound_le` and `bitSerialModBits_le` — is unchanged, as are
the program length, the register span and the public zero-divisor exit at
program indices `31` and `32`; only the internal reduction route and its charge
changed.  `bitSerialModFuel_le_natBitLength` records the resulting width-linear
budget.
-/

namespace NearCubicWires.CanonicalBitSerialModProgram

open NearCubicWires
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalNativeModProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock

def bitSerialModInput (numerator denominator : ℕ) : ℕ :=
  Nat.pair numerator denominator

/-!
Register ABI:

* `r0`: paired request, then the remainder;
* `r2`: remaining bit index;
* `r3`: current remainder, then the doubled candidate, then the reduction;
* `r4/r5`: immutable numerator and positive denominator;
* `r6`: bit-count cursor;
* `r8`: current input bit;
* `r9`: the saturating gap `denominator - candidate`, whose vanishing is the
  executable form of `denominator ≤ candidate`;
* `r10`: the constant zero used as a jump scratch.

Every candidate entering the reduction is below twice the denominator, so one
saturating subtraction is the whole reduction and no loop in this program is
charged by a numeric magnitude.

Indices `19` through `28` are unreachable padding.  They keep the program
length, the register span and the public zero-divisor exit at indices `31` and
`32` identical to the previous stage, so every caller naming those offsets
rebuilds unchanged.
-/
def bitSerialModProgram : NPOracleProgram :=
  [ .unpairLeft 0 4 1
  , .unpairRight 0 5 2
  , .branchZero 5 31 3
  , .set 2 0 4
  , .copy 4 6 5
  , .branchZero 6 9 6
  , .shiftRight 6 1 6 7
  , .increment 2 8
  , .decrement 10 5
  , .set 3 0 10
  , .branchZero 2 29 11
  , .decrement 2 12
  , .shiftLeft 3 1 3 13
  , .testBit 4 2 8 14
  , .add 3 8 3 15
  , .subtract 5 3 9 16
  , .branchZero 9 17 18
  , .subtract 3 5 3 18
  , .decrement 10 10
  , .halt 0
  , .halt 0
  , .halt 0
  , .halt 0
  , .halt 0
  , .halt 0
  , .halt 0
  , .halt 0
  , .halt 0
  , .halt 0
  , .copy 3 0 30
  , .halt 0
  , .set 0 0 32
  , .halt 0
  ]

@[simp] theorem bitSerialModProgram_oracleFree :
    OracleFree bitSerialModProgram := by
  rfl

/-- Fold the `count` low positions in descending index order.  At each step
the accumulator is reduced immediately, matching the register controller. -/
def bitSerialModScan (numerator denominator : ℕ) :
    ℕ → ℕ → ℕ
  | 0, remainder => remainder
  | count + 1, remainder =>
      let candidate :=
        2 * remainder + (numerator.testBit count).toNat
      bitSerialModScan numerator denominator count
        (candidate % denominator)

/-- Exact cost of the bit-count phase, including its final zero branch. -/
def bitSerialCountFuel (numerator : ℕ) : ℕ :=
  4 * numerator.bits.length + 1

/-- One scanned bit costs eight fixed instructions, plus one more exactly when
the candidate needs its single saturating subtraction. -/
def bitSerialStepFuel
    (numerator denominator count remainder : ℕ) : ℕ :=
  8 +
    if denominator ≤ 2 * remainder + (numerator.testBit count).toNat then
      1
    else
      0

def bitSerialOuterFuel (numerator denominator : ℕ) :
    ℕ → ℕ → ℕ
  | 0, _remainder => 3
  | count + 1, remainder =>
      let candidate :=
        2 * remainder + (numerator.testBit count).toNat
      bitSerialStepFuel numerator denominator count remainder +
        bitSerialOuterFuel numerator denominator count
          (candidate % denominator)

def bitSerialModFuel (numerator denominator : ℕ) : ℕ :=
  if denominator = 0 then
    5
  else
    6 + bitSerialCountFuel numerator +
      bitSerialOuterFuel numerator denominator numerator.bits.length 0

def bitSerialModRegisterBound (numerator denominator : ℕ) : ℕ :=
  max (bitSerialModInput numerator denominator)
    (max numerator.bits.length (2 * denominator + 1))

def bitSerialModBits (numerator denominator : ℕ) : ℕ :=
  natBitLength (bitSerialModRegisterBound numerator denominator)

private theorem shiftLeft_one (value : ℕ) :
    Nat.shiftLeft value 1 = 2 * value := by
  simp [Nat.shiftLeft_eq, Nat.mul_comm]

private theorem bits_of_nonzero {value : ℕ} (hvalue : value ≠ 0) :
    value.bits =
      value.testBit 0 :: (value >>> 1).bits := by
  calc
    value.bits =
        (Nat.bit (value.testBit 0) (value >>> 1)).bits := by
      rw [Nat.bit_testBit_zero_shiftRight_one]
    _ = value.testBit 0 :: (value >>> 1).bits := by
      apply Nat.bits_append_bit
      intro hshift
      have hbit :
          Nat.bit (value.testBit 0) (value >>> 1) ≠ 0 := by
        simpa only [Nat.bit_testBit_zero_shiftRight_one] using hvalue
      exact (Nat.bit_ne_zero_iff.mp hbit) hshift

private theorem shiftRight_one_lt
    {value : ℕ} (hpositive : 0 < value) :
    value >>> 1 < value := by
  rw [Nat.shiftRight_eq_div_pow]
  exact Nat.div_lt_self hpositive (by norm_num)

private theorem testBit_shiftRight_zero
    (value index : ℕ) :
    (value >>> index).testBit 0 = value.testBit index := by
  simp [Nat.testBit, Nat.shiftRight_eq_div_pow]

private theorem shiftRight_shiftRight_one
    (value index : ℕ) :
    (value >>> index) >>> 1 = value >>> (index + 1) := by
  rw [← Nat.shiftRight_add]

private theorem shiftRight_decompose
    (value index : ℕ) :
    value >>> index =
      2 * (value >>> (index + 1)) +
        (value.testBit index).toNat := by
  calc
    value >>> index =
        Nat.bit ((value >>> index).testBit 0)
          ((value >>> index) >>> 1) := by
      exact (Nat.bit_testBit_zero_shiftRight_one _).symm
    _ =
        Nat.bit (value.testBit index)
          (value >>> (index + 1)) := by
      rw [testBit_shiftRight_zero, shiftRight_shiftRight_one]
    _ =
        2 * (value >>> (index + 1)) +
          (value.testBit index).toNat := by
      cases value.testBit index <;> simp [Nat.bit]

private theorem bitSerialModScan_shift
    (numerator denominator count remainder : ℕ)
    (_hpositive : 0 < denominator)
    (hremainder :
      remainder = (numerator >>> count) % denominator) :
    bitSerialModScan numerator denominator count remainder =
      numerator % denominator := by
  induction count generalizing remainder with
  | zero =>
      simpa [bitSerialModScan] using hremainder
  | succ count inductionHypothesis =>
      rw [bitSerialModScan]
      apply inductionHypothesis
      rw [hremainder, shiftRight_decompose numerator count]
      conv_rhs => rw [Nat.add_mod, Nat.mul_mod]
      conv_lhs => rw [Nat.add_mod, Nat.mul_mod]
      conv_lhs => rw [Nat.mod_mod]

theorem bitSerialModScan_eq_mod
    (numerator denominator : ℕ) (hpositive : 0 < denominator) :
    bitSerialModScan numerator denominator numerator.bits.length 0 =
      numerator % denominator := by
  apply bitSerialModScan_shift numerator denominator numerator.bits.length 0
    hpositive
  have hshift :
      numerator >>> numerator.bits.length = 0 := by
    apply Nat.shiftRight_eq_zero
    simpa [Nat.size_eq_bits_len] using Nat.lt_size_self numerator
  simp [hshift]

private theorem registerValue_bits
    (numerator denominator value : ℕ)
    (hvalue : value ≤ bitSerialModRegisterBound numerator denominator) :
    natBitLength value ≤ bitSerialModBits numerator denominator := by
  exact natBitLength_mono hvalue

private theorem numerator_le_registerBound
    (numerator denominator : ℕ) :
    numerator ≤ bitSerialModRegisterBound numerator denominator := by
  unfold bitSerialModRegisterBound bitSerialModInput
  exact (Nat.left_le_pair numerator denominator).trans (le_max_left _ _)

private theorem denominator_le_registerBound
    (numerator denominator : ℕ) :
    denominator ≤ bitSerialModRegisterBound numerator denominator := by
  unfold bitSerialModRegisterBound bitSerialModInput
  exact (Nat.right_le_pair numerator denominator).trans (le_max_left _ _)

private theorem count_le_registerBound
    (numerator denominator : ℕ) :
    numerator.bits.length ≤
      bitSerialModRegisterBound numerator denominator := by
  unfold bitSerialModRegisterBound
  exact (le_max_left _ _).trans (le_max_right _ _)

private theorem candidate_le_registerBound
    (numerator denominator candidate : ℕ)
    (hcandidate : candidate < 2 * denominator) :
    candidate ≤ bitSerialModRegisterBound numerator denominator := by
  unfold bitSerialModRegisterBound
  exact (Nat.le_of_lt hcandidate).trans (by
    apply (show 2 * denominator ≤ 2 * denominator + 1 by omega).trans
    exact (le_max_right _ _).trans (le_max_right _ _))

private theorem small_le_registerBound
    (numerator denominator value : ℕ)
    (hvalue : value ≤ 1) :
    value ≤ bitSerialModRegisterBound numerator denominator := by
  unfold bitSerialModRegisterBound
  exact hvalue.trans (by
    apply (show 1 ≤ 2 * denominator + 1 by omega).trans
    exact (le_max_right _ _).trans (le_max_right _ _))

private theorem one_le_bitSerialModBits
    (numerator denominator : ℕ) :
    1 ≤ bitSerialModBits numerator denominator := by
  simp [bitSerialModBits, natBitLength]

/-! ## Exact interpreter loops -/

private theorem run_bitSerialOuterLoop
    (numerator denominator count remainder maximumBits : ℕ)
    (state : NPOracleState)
    (hpositive : 0 < denominator)
    (hpc : state.pc = 10)
    (hcount : state.registers 2 = count)
    (hremainder : state.registers 3 = remainder)
    (hnumerator : state.registers 4 = numerator)
    (hdenominator : state.registers 5 = denominator)
    (hscratch : state.registers 10 = 0)
    (hremainderLt : remainder < denominator)
    (hcountBits : natBitLength count ≤ maximumBits)
    (hremainderBits : natBitLength remainder ≤ maximumBits)
    (_hnumeratorBits : natBitLength numerator ≤ maximumBits)
    (hdenominatorBits : natBitLength denominator ≤ maximumBits)
    (hsmallBits : natBitLength 1 ≤ maximumBits)
    (hregisterBoundBits :
      bitSerialModBits numerator denominator ≤ maximumBits) :
    runNPOracleProgram bitSerialModProgram maximumBits
        (bitSerialOuterFuel numerator denominator count remainder) state =
      some (bitSerialModScan numerator denominator count remainder) := by
  induction count generalizing remainder state with
  | zero =>
      rw [bitSerialOuterFuel, bitSerialModScan]
      rw [show 3 = (1 + 1) + 1 by omega]
      rw [run_branchZero_instruction (by rfl) hpc]
      rw [hcount, if_pos rfl]
      rw [run_copy_instruction (value := remainder)
        (by rfl) rfl
        (by simp [NPOracleState.jump, hremainder])
        hremainderBits]
      rw [run_halt_instruction (by rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump])
        hremainderBits]
  | succ count inductionHypothesis =>
      let candidate := 2 * remainder + (numerator.testBit count).toNat
      let reduced := candidate % denominator
      have hbit : (numerator.testBit count).toNat ≤ 1 := by
        cases numerator.testBit count <;> simp
      have hcountPredBits :
          natBitLength count ≤ maximumBits :=
        (decrement_bits_le (count + 1)).trans hcountBits
      have hcandidateLt : candidate < 2 * denominator := by
        change 2 * remainder + (numerator.testBit count).toNat < 2 * denominator
        omega
      have hcandidateBits :
          natBitLength candidate ≤ maximumBits :=
        (registerValue_bits numerator denominator candidate
          (candidate_le_registerBound numerator denominator candidate
            hcandidateLt)).trans hregisterBoundBits
      have hdoubleBits :
          natBitLength (2 * remainder) ≤ maximumBits := by
        refine (natBitLength_mono ?_).trans hcandidateBits
        change 2 * remainder ≤ 2 * remainder + (numerator.testBit count).toNat
        omega
      have hbitBits :
          natBitLength (numerator.testBit count).toNat ≤ maximumBits :=
        (registerValue_bits numerator denominator
          (numerator.testBit count).toNat
          (small_le_registerBound numerator denominator
            (numerator.testBit count).toNat hbit)).trans hregisterBoundBits
      have hzeroBits : natBitLength 0 ≤ maximumBits :=
        (natBitLength_mono (Nat.zero_le 1)).trans hsmallBits
      have hgapBits :
          natBitLength (denominator - candidate) ≤ maximumBits :=
        (natBitLength_mono (Nat.sub_le denominator candidate)).trans
          hdenominatorBits
      have hreducedLt : reduced < denominator :=
        Nat.mod_lt candidate hpositive
      have hreducedBits :
          natBitLength reduced ≤ maximumBits :=
        (natBitLength_mono hreducedLt.le).trans hdenominatorBits
      let stepState := (state.write 2 count).jump 12
      let doubledState := (stepState.write 3 (2 * remainder)).jump 13
      let bitState :=
        (doubledState.write 8 (numerator.testBit count).toNat).jump 14
      let candidateState := (bitState.write 3 candidate).jump 15
      let gapState :=
        (candidateState.write 9 (denominator - candidate)).jump 16
      have hgapCount : gapState.registers 2 = count := by
        simp [gapState, candidateState, bitState, doubledState, stepState,
          NPOracleState.write, NPOracleState.jump]
      have hgapCandidate : gapState.registers 3 = candidate := by
        simp [gapState, candidateState, NPOracleState.write,
          NPOracleState.jump]
      have hgapNumerator : gapState.registers 4 = numerator := by
        simp [gapState, candidateState, bitState, doubledState, stepState,
          NPOracleState.write, NPOracleState.jump, hnumerator]
      have hgapDenominator : gapState.registers 5 = denominator := by
        simp [gapState, candidateState, bitState, doubledState, stepState,
          NPOracleState.write, NPOracleState.jump, hdenominator]
      have hgapValue :
          gapState.registers 9 = denominator - candidate := by
        simp [gapState, NPOracleState.write, NPOracleState.jump]
      have hgapScratch : gapState.registers 10 = 0 := by
        simp [gapState, candidateState, bitState, doubledState, stepState,
          NPOracleState.write, NPOracleState.jump, hscratch]
      have hcommon :
          ∀ tailFuel : ℕ,
            runNPOracleProgram bitSerialModProgram maximumBits
                (tailFuel + 6) state =
              runNPOracleProgram bitSerialModProgram maximumBits
                tailFuel gapState := by
        intro tailFuel
        have hstepRemainder : stepState.registers 3 = remainder := by
          simp [stepState, NPOracleState.write, NPOracleState.jump,
            hremainder]
        have hdoubledNumerator : doubledState.registers 4 = numerator := by
          simp [doubledState, stepState, NPOracleState.write,
            NPOracleState.jump, hnumerator]
        have hdoubledIndex : doubledState.registers 2 = count := by
          simp [doubledState, stepState, NPOracleState.write,
            NPOracleState.jump]
        have hbitDouble : bitState.registers 3 = 2 * remainder := by
          simp [bitState, doubledState, NPOracleState.write,
            NPOracleState.jump]
        have hbitObserved :
            bitState.registers 8 = (numerator.testBit count).toNat := by
          simp [bitState, NPOracleState.write, NPOracleState.jump]
        have hcandidateValue : candidateState.registers 3 = candidate := by
          simp [candidateState, NPOracleState.write, NPOracleState.jump]
        have hcandidateDenominator :
            candidateState.registers 5 = denominator := by
          simp [candidateState, bitState, doubledState, stepState,
            NPOracleState.write, NPOracleState.jump, hdenominator]
        rw [show tailFuel + 6 = (((((tailFuel + 1) + 1) + 1) + 1) + 1) + 1 by
          omega]
        rw [run_branchZero_instruction (by rfl) hpc]
        rw [hcount, if_neg (by omega)]
        rw [run_decrement_instruction (value := count)
          (by rfl) rfl
          (by simp [NPOracleState.jump, hcount])
          hcountPredBits]
        change
          runNPOracleProgram bitSerialModProgram maximumBits
              ((((tailFuel + 1) + 1) + 1) + 1) stepState =
            runNPOracleProgram bitSerialModProgram maximumBits
              tailFuel gapState
        rw [run_shiftLeft_instruction (value := 2 * remainder)
          (by rfl) rfl
          (by
            rw [hstepRemainder]
            exact shiftLeft_one remainder)
          hdoubleBits]
        change
          runNPOracleProgram bitSerialModProgram maximumBits
              (((tailFuel + 1) + 1) + 1) doubledState =
            runNPOracleProgram bitSerialModProgram maximumBits
              tailFuel gapState
        rw [run_testBit_instruction
          (value := (numerator.testBit count).toNat)
          (by rfl) rfl
          (by rw [hdoubledNumerator, hdoubledIndex])
          hbitBits]
        change
          runNPOracleProgram bitSerialModProgram maximumBits
              ((tailFuel + 1) + 1) bitState =
            runNPOracleProgram bitSerialModProgram maximumBits
              tailFuel gapState
        rw [run_add_instruction (value := candidate)
          (by rfl) rfl
          (by rw [hbitDouble, hbitObserved])
          hcandidateBits]
        change
          runNPOracleProgram bitSerialModProgram maximumBits
              (tailFuel + 1) candidateState =
            runNPOracleProgram bitSerialModProgram maximumBits
              tailFuel gapState
        rw [run_subtract_instruction (value := denominator - candidate)
          (by rfl) rfl
          (by rw [hcandidateDenominator, hcandidateValue])
          hgapBits]
      rw [bitSerialModScan, bitSerialOuterFuel]
      by_cases hreduce : denominator ≤ candidate
      · have hcondition :
            denominator ≤ 2 * remainder + (numerator.testBit count).toNat :=
          hreduce
        have hstep :
            bitSerialStepFuel numerator denominator count remainder = 9 := by
          simp only [bitSerialStepFuel]
          rw [if_pos hcondition]
        have hreducedEq : reduced = candidate - denominator := by
          change candidate % denominator = candidate - denominator
          rw [Nat.mod_eq_sub_mod hreduce,
            Nat.mod_eq_of_lt
              (by omega : candidate - denominator < denominator)]
        rw [hstep]
        rw [show
          9 + bitSerialOuterFuel numerator denominator count reduced =
            (bitSerialOuterFuel numerator denominator count reduced +
              1 + 1 + 1) + 6 by omega]
        rw [hcommon
          (bitSerialOuterFuel numerator denominator count reduced + 1 + 1 + 1)]
        rw [run_branchZero_instruction (by rfl) rfl]
        rw [hgapValue,
          if_pos (by omega : denominator - candidate = 0)]
        rw [run_subtract_instruction (value := reduced)
          (by rfl) rfl
          (by
            simp only [NPOracleState.jump]
            rw [hgapCandidate, hgapDenominator, hreducedEq])
          hreducedBits]
        rw [run_decrement_instruction (value := 0)
          (by rfl) rfl
          (by
            simp [NPOracleState.write, NPOracleState.jump, hgapScratch])
          hzeroBits]
        apply inductionHypothesis reduced
          ((((((gapState.jump 17).write 3 reduced).jump 18).write 10 0).jump
            10))
        · rfl
        · simpa [NPOracleState.write, NPOracleState.jump] using hgapCount
        · simp [NPOracleState.write, NPOracleState.jump]
        · simpa [NPOracleState.write, NPOracleState.jump] using hgapNumerator
        · simpa [NPOracleState.write, NPOracleState.jump] using
            hgapDenominator
        · simp [NPOracleState.write, NPOracleState.jump]
        · exact hreducedLt
        · exact hcountPredBits
        · exact hreducedBits
      · have hcondition :
            ¬ denominator ≤
              2 * remainder + (numerator.testBit count).toNat :=
          hreduce
        have hstep :
            bitSerialStepFuel numerator denominator count remainder = 8 := by
          simp only [bitSerialStepFuel]
          rw [if_neg hcondition]
        have hreducedEq : reduced = candidate := by
          change candidate % denominator = candidate
          exact Nat.mod_eq_of_lt (by omega)
        rw [hstep]
        rw [show
          8 + bitSerialOuterFuel numerator denominator count reduced =
            (bitSerialOuterFuel numerator denominator count reduced +
              1 + 1) + 6 by omega]
        rw [hcommon
          (bitSerialOuterFuel numerator denominator count reduced + 1 + 1)]
        rw [run_branchZero_instruction (by rfl) rfl]
        rw [hgapValue,
          if_neg (by omega : ¬ denominator - candidate = 0)]
        rw [run_decrement_instruction (value := 0)
          (by rfl) rfl
          (by simp [NPOracleState.jump, hgapScratch])
          hzeroBits]
        apply inductionHypothesis reduced
          (((gapState.jump 18).write 10 0).jump 10)
        · rfl
        · simpa [NPOracleState.write, NPOracleState.jump] using hgapCount
        · have hthree :
              (((gapState.jump 18).write 10 0).jump 10).registers 3 =
                candidate := by
            simpa [NPOracleState.write, NPOracleState.jump] using
              hgapCandidate
          rw [hthree, hreducedEq]
        · simpa [NPOracleState.write, NPOracleState.jump] using hgapNumerator
        · simpa [NPOracleState.write, NPOracleState.jump] using
            hgapDenominator
        · simp [NPOracleState.write, NPOracleState.jump]
        · exact hreducedLt
        · exact hcountPredBits
        · exact hreducedBits

private theorem run_bitSerialCountLoop
    (cursor count numerator denominator maximumBits extra : ℕ)
    (state : NPOracleState) (result : Option ℕ)
    (hpc : state.pc = 5)
    (hcursor : state.registers 6 = cursor)
    (hcount : state.registers 2 = count)
    (hnumerator : state.registers 4 = numerator)
    (hdenominator : state.registers 5 = denominator)
    (hscratch : state.registers 10 = 0)
    (hcursorBits : natBitLength cursor ≤ maximumBits)
    (hfinalCountBits :
      natBitLength (count + cursor.bits.length) ≤ maximumBits)
    (hfinish :
      ∀ finalState : NPOracleState,
        finalState.pc = 9 →
        finalState.registers 6 = 0 →
        finalState.registers 2 = count + cursor.bits.length →
        finalState.registers 4 = numerator →
        finalState.registers 5 = denominator →
        finalState.registers 10 = 0 →
        runNPOracleProgram bitSerialModProgram maximumBits extra finalState =
          result) :
    runNPOracleProgram bitSerialModProgram maximumBits
        (bitSerialCountFuel cursor + extra) state =
      result := by
  induction cursor using Nat.strong_induction_on generalizing count state with
  | h cursor inductionHypothesis =>
      by_cases hzero : cursor = 0
      · have hstateCursorZero : state.registers 6 = 0 :=
          hcursor.trans hzero
        rw [hzero] at hcursorBits hfinalCountBits hfinish ⊢
        rw [bitSerialCountFuel]
        simp only [Nat.zero_bits, List.length_nil, mul_zero, zero_add]
        rw [show 1 + extra = extra + 1 by omega]
        rw [run_branchZero_instruction (by rfl) hpc]
        rw [hstateCursorZero, if_pos rfl]
        apply hfinish (state.jump 9)
        · rfl
        · simpa [NPOracleState.jump] using hstateCursorZero
        · simpa [NPOracleState.jump] using hcount
        · simpa [NPOracleState.jump] using hnumerator
        · simpa [NPOracleState.jump] using hdenominator
        · simpa [NPOracleState.jump] using hscratch
      · have hpositive : 0 < cursor := Nat.pos_of_ne_zero hzero
        have hshiftLt : cursor >>> 1 < cursor :=
          shiftRight_one_lt hpositive
        have hbits :
            cursor.bits.length =
              (cursor >>> 1).bits.length + 1 := by
          rw [bits_of_nonzero hzero]
          simp
        have hshiftBits :
            natBitLength (cursor >>> 1) ≤ maximumBits :=
          (shiftRight_bits_le cursor 1).trans hcursorBits
        have hnextCountBits :
            natBitLength (count + 1) ≤ maximumBits := by
          apply (natBitLength_mono ?_).trans hfinalCountBits
          rw [hbits]
          omega
        let shiftedState :=
          (state.write 6 (cursor >>> 1)).jump 7
        let countedState :=
          (shiftedState.write 2 (count + 1)).jump 8
        let nextState := (countedState.write 10 0).jump 5
        rw [bitSerialCountFuel]
        rw [hbits]
        rw [show
          4 * ((cursor >>> 1).bits.length + 1) + 1 + extra =
            (((bitSerialCountFuel (cursor >>> 1) + extra + 1) + 1) + 1) + 1 by
          unfold bitSerialCountFuel
          omega]
        rw [run_branchZero_instruction (by rfl) hpc]
        rw [hcursor, if_neg hzero]
        rw [run_shiftRight_instruction
          (pc := 6) (source := 6) (amount := 1) (destination := 6)
          (next := 7) (value := cursor >>> 1)
          (by rfl) (by rfl)
          (by simp [NPOracleState.jump, hcursor])
          hshiftBits]
        change
          runNPOracleProgram bitSerialModProgram maximumBits
              ((bitSerialCountFuel (cursor >>> 1) + extra + 1) + 1)
              shiftedState =
            result
        rw [run_increment_instruction (value := count + 1)
          (by rfl) rfl
          (by simp [shiftedState, hcount])
          hnextCountBits]
        change
          runNPOracleProgram bitSerialModProgram maximumBits
              (bitSerialCountFuel (cursor >>> 1) + extra + 1)
              countedState =
            result
        rw [run_decrement_instruction (value := 0)
          (by rfl) rfl
          (by simp [countedState, shiftedState, hscratch])
          (by
            exact (natBitLength_mono (Nat.zero_le (count + 1))).trans
              hnextCountBits)]
        change
          runNPOracleProgram bitSerialModProgram maximumBits
              (bitSerialCountFuel (cursor >>> 1) + extra)
              nextState =
            result
        apply inductionHypothesis (cursor >>> 1) hshiftLt
          (count + 1) nextState
        · rfl
        · simp [nextState, countedState, shiftedState]
        · simp [nextState, countedState]
        · simp [nextState, countedState, shiftedState, hnumerator]
        · simp [nextState, countedState, shiftedState, hdenominator]
        · simp [nextState]
        · exact hshiftBits
        · simpa [hbits, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
            hfinalCountBits
        · intro finalState hfinalPc hfinalCursor hfinalCount
            hfinalNumerator hfinalDenominator hfinalScratch
          apply hfinish finalState hfinalPc hfinalCursor
          · simpa [hbits, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
              hfinalCount
          · exact hfinalNumerator
          · exact hfinalDenominator
          · exact hfinalScratch

/-- Exact execution theorem for a positive divisor.  Unlike
`run_nativeModProgram`, its charged fuel is independent of the numerator's
numeric magnitude. -/
theorem run_bitSerialModProgram
    (inputLength numerator denominator : ℕ)
    (hpositive : 0 < denominator) :
    runNPOracleProgram bitSerialModProgram
        (bitSerialModBits numerator denominator)
        (bitSerialModFuel numerator denominator)
        (initialNPOracleState inputLength
          (bitSerialModInput numerator denominator)) =
      some (numerator % denominator) := by
  let maximumBits := bitSerialModBits numerator denominator
  let initial :=
    initialNPOracleState inputLength (bitSerialModInput numerator denominator)
  let numeratorState := (initial.write 4 numerator).jump 1
  let denominatorState := (numeratorState.write 5 denominator).jump 2
  let countZeroState := (denominatorState.write 2 0).jump 4
  let countState := (countZeroState.write 6 numerator).jump 5
  have hregisterBoundBits :
      bitSerialModBits numerator denominator ≤ maximumBits := by
    rfl
  have hnumeratorBits :
      natBitLength numerator ≤ maximumBits :=
    (registerValue_bits numerator denominator numerator
      (numerator_le_registerBound numerator denominator)).trans
        hregisterBoundBits
  have hdenominatorBits :
      natBitLength denominator ≤ maximumBits :=
    (registerValue_bits numerator denominator denominator
      (denominator_le_registerBound numerator denominator)).trans
        hregisterBoundBits
  have hcountBits :
      natBitLength numerator.bits.length ≤ maximumBits :=
    (registerValue_bits numerator denominator numerator.bits.length
      (count_le_registerBound numerator denominator)).trans
        hregisterBoundBits
  have hsmallBits : natBitLength 1 ≤ maximumBits := by
    simpa [maximumBits, natBitLength] using
      one_le_bitSerialModBits numerator denominator
  have hzeroBits : natBitLength 0 ≤ maximumBits :=
    (natBitLength_mono (Nat.zero_le 1)).trans hsmallBits
  rw [bitSerialModFuel, if_neg hpositive.ne']
  rw [show
    6 + bitSerialCountFuel numerator +
        bitSerialOuterFuel numerator denominator numerator.bits.length 0 =
      ((bitSerialCountFuel numerator +
        (1 + bitSerialOuterFuel numerator denominator
          numerator.bits.length 0) + 1) + 1) + 3 by omega]
  rw [show
    (bitSerialCountFuel numerator +
        (1 + bitSerialOuterFuel numerator denominator
          numerator.bits.length 0) + 1) + 1 + 3 =
      (((bitSerialCountFuel numerator +
        (1 + bitSerialOuterFuel numerator denominator
          numerator.bits.length 0) + 1) + 1) + 1) + 1 + 1 by omega]
  rw [run_unpairLeft_instruction (value := numerator)
    (by rfl) rfl
    (by simp [initialNPOracleState, bitSerialModInput])
    hnumeratorBits]
  change
    runNPOracleProgram bitSerialModProgram maximumBits
        (((bitSerialCountFuel numerator +
          (1 + bitSerialOuterFuel numerator denominator
            numerator.bits.length 0) + 1) + 1) + 1 + 1)
        numeratorState =
      some (numerator % denominator)
  rw [run_unpairRight_instruction (value := denominator)
    (by rfl) rfl
    (by simp [numeratorState, initial, initialNPOracleState,
      bitSerialModInput])
    hdenominatorBits]
  change
    runNPOracleProgram bitSerialModProgram maximumBits
        ((bitSerialCountFuel numerator +
          (1 + bitSerialOuterFuel numerator denominator
            numerator.bits.length 0) + 1) + 1 + 1)
        denominatorState =
      some (numerator % denominator)
  rw [run_branchZero_instruction (by rfl) rfl]
  rw [show denominatorState.registers 5 = denominator by
    simp [denominatorState], if_neg hpositive.ne']
  change
    runNPOracleProgram bitSerialModProgram maximumBits
        ((bitSerialCountFuel numerator +
          (1 + bitSerialOuterFuel numerator denominator
            numerator.bits.length 0) + 1) + 1)
        (denominatorState.jump 3) =
      some (numerator % denominator)
  rw [run_set_instruction (value := 0)
    (by rfl) rfl hzeroBits]
  change
    runNPOracleProgram bitSerialModProgram maximumBits
        (bitSerialCountFuel numerator +
          (1 + bitSerialOuterFuel numerator denominator
            numerator.bits.length 0) + 1)
        countZeroState =
      some (numerator % denominator)
  rw [run_copy_instruction (value := numerator)
    (by rfl) rfl
    (by simp [countZeroState, denominatorState, numeratorState])
    hnumeratorBits]
  change
    runNPOracleProgram bitSerialModProgram maximumBits
        (bitSerialCountFuel numerator +
          (1 + bitSerialOuterFuel numerator denominator
            numerator.bits.length 0))
        countState =
      some (numerator % denominator)
  apply run_bitSerialCountLoop numerator 0 numerator denominator maximumBits
    (1 + bitSerialOuterFuel numerator denominator numerator.bits.length 0)
    countState (some (numerator % denominator))
  · rfl
  · simp [countState]
  · simp [countState, countZeroState]
  · simp [countState, countZeroState, denominatorState, numeratorState]
  · simp [countState, countZeroState, denominatorState]
  · simp [countState, countZeroState, denominatorState, numeratorState,
      initial, initialNPOracleState]
  · exact hnumeratorBits
  · simpa using hcountBits
  · intro finalState hfinalPc hfinalCursor hfinalCount hfinalNumerator
      hfinalDenominator hfinalScratch
    rw [show
      1 + bitSerialOuterFuel numerator denominator numerator.bits.length 0 =
        bitSerialOuterFuel numerator denominator numerator.bits.length 0 + 1 by
      omega]
    rw [run_set_instruction (value := 0)
      (by rfl) hfinalPc hzeroBits]
    have hrun :=
      run_bitSerialOuterLoop numerator denominator numerator.bits.length 0
        maximumBits ((finalState.write 3 0).jump 10)
        hpositive rfl
        (by simp [NPOracleState.write, NPOracleState.jump, hfinalCount])
        (by simp [NPOracleState.write, NPOracleState.jump])
        (by simp [NPOracleState.write, NPOracleState.jump, hfinalNumerator])
        (by simp [NPOracleState.write, NPOracleState.jump, hfinalDenominator])
        (by simp [NPOracleState.write, NPOracleState.jump, hfinalScratch])
        hpositive
        hcountBits hzeroBits hnumeratorBits hdenominatorBits hsmallBits
        hregisterBoundBits
    rw [hrun, bitSerialModScan_eq_mod numerator denominator hpositive]

/-! ## The polynomial charge

Every loop of the production stage is charged by a bit index, never by a
register's numeric value. -/

/-- The scan charges at most nine instructions per numerator bit. -/
theorem bitSerialOuterFuel_le_linear
    (numerator denominator count remainder : ℕ) :
    bitSerialOuterFuel numerator denominator count remainder ≤
      9 * count + 3 := by
  induction count generalizing remainder with
  | zero =>
      simp [bitSerialOuterFuel]
  | succ count inductionHypothesis =>
      have hstep :
          bitSerialStepFuel numerator denominator count remainder ≤ 9 := by
        simp only [bitSerialStepFuel]
        split <;> omega
      have htail :=
        inductionHypothesis
          ((2 * remainder + (numerator.testBit count).toNat) % denominator)
      rw [bitSerialOuterFuel]
      omega

theorem bitSerialOuterFuel_le
    (numerator denominator count remainder : ℕ)
    (_hpositive : 0 < denominator)
    (_hremainder : remainder < denominator) :
    bitSerialOuterFuel numerator denominator count remainder ≤
      count * (8 * denominator + 12) + 3 := by
  have hlinear :=
    bitSerialOuterFuel_le_linear numerator denominator count remainder
  have hstep : 9 * count ≤ count * (8 * denominator + 12) := by
    calc
      9 * count = count * 9 := Nat.mul_comm 9 count
      _ ≤ count * (8 * denominator + 12) :=
        Nat.mul_le_mul_left count (by omega)
  omega

/-- The production clock is linear in numerator bit width and in the public
divisor.  In particular it never contains the native numerator as a factor. -/
theorem bitSerialModFuel_le
    (numerator denominator : ℕ) (hpositive : 0 < denominator) :
    bitSerialModFuel numerator denominator ≤
      10 + 4 * numerator.bits.length +
        numerator.bits.length * (8 * denominator + 12) := by
  rw [bitSerialModFuel, if_neg hpositive.ne']
  unfold bitSerialCountFuel
  have houter :=
    bitSerialOuterFuel_le numerator denominator numerator.bits.length 0
      hpositive hpositive
  omega

/-- **The remainder charge is linear in the numerator's bit width.**  No term
of `bitSerialModFuel` grows with the numerator's or the denominator's numeric
magnitude; this is the fact the rational validator's polynomial envelope
consumes. -/
theorem bitSerialModFuel_le_bits (numerator denominator : ℕ) :
    bitSerialModFuel numerator denominator ≤
      13 * numerator.bits.length + 10 := by
  by_cases hzero : denominator = 0
  · rw [bitSerialModFuel, if_pos hzero]
    omega
  · rw [bitSerialModFuel, if_neg hzero]
    unfold bitSerialCountFuel
    have houter :=
      bitSerialOuterFuel_le_linear numerator denominator
        numerator.bits.length 0
    omega

private theorem bits_length_le_natBitLength (value : ℕ) :
    value.bits.length ≤ natBitLength value := by
  rw [Nat.size_eq_bits_len]
  apply (Nat.size_le).2
  simpa [natBitLength, Nat.succ_eq_add_one] using
    (Nat.lt_pow_succ_log_self (b := 2) (by omega) value)

/-- The same charge stated against the canonical binary width. -/
theorem bitSerialModFuel_le_natBitLength (numerator denominator : ℕ) :
    bitSerialModFuel numerator denominator ≤
      13 * natBitLength numerator + 10 := by
  have hbound := bitSerialModFuel_le_bits numerator denominator
  have hlength := bits_length_le_natBitLength numerator
  omega

private theorem bits_length_le_succ (value : ℕ) :
    value.bits.length ≤ value + 1 := by
  rw [Nat.size_eq_bits_len]
  apply (Nat.size_le).2
  exact value.lt_two_pow_self.trans_le <|
    Nat.pow_le_pow_right (by omega) (Nat.le_succ value)

theorem bitSerialModRegisterBound_le
    (numerator denominator : ℕ) :
    bitSerialModRegisterBound numerator denominator ≤
      2 * (bitSerialModInput numerator denominator + 1) := by
  have hnumerator :
      numerator ≤ bitSerialModInput numerator denominator :=
    Nat.left_le_pair numerator denominator
  have hdenominator :
      denominator ≤ bitSerialModInput numerator denominator :=
    Nat.right_le_pair numerator denominator
  have hlength := bits_length_le_succ numerator
  unfold bitSerialModRegisterBound
  omega

theorem bitSerialModBits_le
    (numerator denominator : ℕ) :
    bitSerialModBits numerator denominator ≤
      natBitLength
        (2 * (bitSerialModInput numerator denominator + 1)) := by
  exact natBitLength_mono
    (bitSerialModRegisterBound_le numerator denominator)

end NearCubicWires.CanonicalBitSerialModProgram
