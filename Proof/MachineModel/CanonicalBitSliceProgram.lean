import Proof.Foundations.CanonicalBinaryProgram
import Proof.Foundations.ExecutableInterfaces
import Proof.Foundations.VerifiedLinker

/-!
# Canonical run-time bit slice

`BitInputPrefixProgram` reads the low `width` digits of a code.  The Case-2
occurrence coordinates additionally need an interior window: the clause
address of one occurrence input occupies digits `offset, …, offset + width - 1`
of the public code, and both `offset` and `width` are run-time data recovered
from the scheduled envelope, so the immediate `shiftRight` amount of the
instruction set cannot be used.

This module supplies the single fixed program for that window.  It scans the
selected digits from high to low with the register-indexed `testBit`
instruction and doubles the accumulator with one `add`; no second window
convention, no host-side shift, and no per-width program family is introduced.
-/

namespace NearCubicWires.CanonicalBitSliceProgram

open NearCubicWires
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.VerifiedLinker

/-! ## 1. The scanned value -/

/-- The interior digit window of a natural code. -/
def bitSlice (offset width value : ℕ) : ℕ :=
  Nat.shiftRight value offset % 2 ^ width

/-- High-to-low accumulation of the selected digits, exactly as the loop
below computes it. -/
def bitSliceScan (offset value : ℕ) : ℕ → ℕ → ℕ
  | accumulator, 0 => accumulator
  | accumulator, remaining + 1 =>
      bitSliceScan offset value
        (2 * accumulator + (value.testBit (offset + remaining)).toNat)
        remaining

private theorem mod_two_pow_succ (value index : ℕ) :
    value % 2 ^ (index + 1) =
      (value.testBit index).toNat * 2 ^ index + value % 2 ^ index := by
  have hpow : (2 : ℕ) ^ (index + 1) = 2 ^ index * 2 := pow_succ 2 index
  have hdiv :
      value % 2 ^ (index + 1) / 2 ^ index = value / 2 ^ index % 2 := by
    rw [hpow]
    exact Nat.mod_mul_right_div_self value (2 ^ index) 2
  have hmod :
      value % 2 ^ (index + 1) % 2 ^ index = value % 2 ^ index :=
    Nat.mod_mod_of_dvd value (pow_dvd_pow 2 (Nat.le_succ index))
  have hsplit :=
    Nat.div_add_mod (value % 2 ^ (index + 1)) (2 ^ index)
  rw [hdiv, hmod] at hsplit
  rw [Nat.toNat_testBit, Nat.mul_comm]
  exact hsplit.symm

theorem bitSliceScan_eq (offset value accumulator remaining : ℕ) :
    bitSliceScan offset value accumulator remaining =
      accumulator * 2 ^ remaining +
        Nat.shiftRight value offset % 2 ^ remaining := by
  induction remaining generalizing accumulator with
  | zero => simp [bitSliceScan, Nat.mod_one]
  | succ remaining inductionHypothesis =>
      rw [bitSliceScan, inductionHypothesis]
      have hshift :
          (Nat.shiftRight value offset).testBit remaining =
            value.testBit (offset + remaining) :=
        Nat.testBit_shiftRight value
      rw [mod_two_pow_succ (Nat.shiftRight value offset) remaining, hshift]
      rw [pow_succ]
      ring

/-- The scan started at zero is the window itself. -/
@[simp] theorem bitSliceScan_zero (offset width value : ℕ) :
    bitSliceScan offset value 0 width = bitSlice offset width value := by
  rw [bitSliceScan_eq, bitSlice]
  omega

/-! ## 2. The fixed program -/

/-- Public callable ABI: `pair(offset, pair(width, value))`. -/
def bitSliceInput (offset width value : ℕ) : ℕ :=
  Nat.pair offset (Nat.pair width value)

/-!
Register ABI:

* `r0`: request, then output;
* `r2`: window offset;
* `r3`: request tail, then the current absolute digit index;
* `r4`: remaining digit count;
* `r5`: scanned value;
* `r6`: accumulator;
* `r7`: current digit.

Instruction `11` is the canonical unconditional jump: both branch targets of
`branchZero` are the loop head.
-/
def bitSliceProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .set 6 0 5
  , .branchZero 4 12 6
  , .decrement 4 7
  , .add 2 4 3 8
  , .testBit 5 3 7 9
  , .add 6 6 6 10
  , .add 6 7 6 11
  , .branchZero 6 5 5
  , .copy 6 0 13
  , .halt 0
  ]

@[simp] theorem bitSliceProgram_oracleFree :
    OracleFree bitSliceProgram := by
  rfl

def bitSliceLoopFuel : ℕ → ℕ
  | 0 => 3
  | remaining + 1 => 7 + bitSliceLoopFuel remaining

def bitSliceFuel (width : ℕ) : ℕ :=
  5 + bitSliceLoopFuel width

/-- Exact register width of the scan: the request, the largest absolute digit
index, and the window's own capacity. -/
def bitSliceBits (inputLength offset width value : ℕ) : ℕ :=
  natBitLength
    (max inputLength
      (max (bitSliceInput offset width value)
        (max (offset + width) (2 ^ width))))

/-! ## 3. Exact execution -/

private theorem run_bitSliceLoop
    (offset value width maximumBits : ℕ)
    (accumulator remaining : ℕ) (state : NPOracleState)
    (hpc : state.pc = 5)
    (hoffset : state.registers 2 = offset)
    (hremaining : state.registers 4 = remaining)
    (hvalue : state.registers 5 = value)
    (haccumulator : state.registers 6 = accumulator)
    (hbound : (accumulator + 1) * 2 ^ remaining ≤ 2 ^ width)
    (hboundBits : natBitLength (2 ^ width) ≤ maximumBits)
    (hindexBits : natBitLength (offset + remaining) ≤ maximumBits) :
    runNPOracleProgram bitSliceProgram maximumBits
        (bitSliceLoopFuel remaining) state =
      some (bitSliceScan offset value accumulator remaining) := by
  induction remaining generalizing accumulator state with
  | zero =>
      have haccumulatorBits :
          natBitLength accumulator ≤ maximumBits := by
        apply (natBitLength_mono ?_).trans hboundBits
        have hle : accumulator + 1 ≤ 2 ^ 0 * (accumulator + 1) := by
          simp
        omega
      rw [bitSliceLoopFuel, bitSliceScan]
      rw [show 3 = 2 + 1 by omega]
      rw [run_branchZero_instruction (by rfl) hpc]
      rw [hremaining, if_pos rfl]
      rw [show 2 = 1 + 1 by omega]
      rw [run_copy_instruction (value := accumulator)
        (by rfl) rfl
        (by simp [NPOracleState.jump, haccumulator])
        haccumulatorBits]
      exact run_halt_instruction (fuel := 0)
        (by rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump])
        haccumulatorBits
  | succ remaining inductionHypothesis =>
      have hpow : (2 : ℕ) ^ (remaining + 1) = 2 * 2 ^ remaining := by
        rw [pow_succ]
        ring
      let digit := (value.testBit (offset + remaining)).toNat
      have hdigit : digit ≤ 1 := by
        unfold digit
        cases value.testBit (offset + remaining) <;> simp
      have hnextBound :
          (2 * accumulator + digit + 1) * 2 ^ remaining ≤ 2 ^ width := by
        apply le_trans ?_ hbound
        rw [hpow]
        have hfactor :
            2 * accumulator + digit + 1 ≤ 2 * (accumulator + 1) := by
          omega
        calc
          (2 * accumulator + digit + 1) * 2 ^ remaining ≤
              2 * (accumulator + 1) * 2 ^ remaining :=
            Nat.mul_le_mul_right _ hfactor
          _ = (accumulator + 1) * (2 * 2 ^ remaining) := by ring
      have hdoubleBound :
          2 * accumulator + digit ≤ 2 ^ width := by
        apply le_trans ?_ hnextBound
        have hpositive : 1 ≤ 2 ^ remaining := Nat.one_le_two_pow
        nlinarith
      have hdoubleBits :
          natBitLength (2 * accumulator) ≤ maximumBits := by
        apply (natBitLength_mono ?_).trans hboundBits
        omega
      have hsumBits :
          natBitLength (2 * accumulator + digit) ≤ maximumBits := by
        exact (natBitLength_mono hdoubleBound).trans hboundBits
      have hdigitBits : natBitLength digit ≤ maximumBits := by
        apply (natBitLength_mono ?_).trans hboundBits
        have hpositive : 1 ≤ 2 ^ width := Nat.one_le_two_pow
        omega
      have hnextIndexBits :
          natBitLength (offset + remaining) ≤ maximumBits := by
        exact (natBitLength_mono (by omega)).trans hindexBits
      have hremainingBits :
          natBitLength remaining ≤ maximumBits := by
        exact (natBitLength_mono (by omega)).trans hindexBits
      rw [bitSliceLoopFuel, bitSliceScan]
      rw [show
        7 + bitSliceLoopFuel remaining =
          (6 + bitSliceLoopFuel remaining) + 1 by omega]
      rw [run_branchZero_instruction (by rfl) hpc]
      rw [show (if state.registers 4 = 0 then 12 else 6) = 6 by
        rw [hremaining]
        exact if_neg (by omega)]
      rw [show
        6 + bitSliceLoopFuel remaining =
          (5 + bitSliceLoopFuel remaining) + 1 by omega]
      rw [run_decrement_instruction (value := remaining)
        (by rfl) rfl
        (by simp [NPOracleState.jump, hremaining])
        hremainingBits]
      rw [show
        5 + bitSliceLoopFuel remaining =
          (4 + bitSliceLoopFuel remaining) + 1 by omega]
      rw [run_add_instruction (value := offset + remaining)
        (by rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump, hoffset])
        hnextIndexBits]
      rw [show
        4 + bitSliceLoopFuel remaining =
          (3 + bitSliceLoopFuel remaining) + 1 by omega]
      rw [run_testBit_instruction (value := digit)
        (by rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump, hvalue, digit])
        hdigitBits]
      rw [show
        3 + bitSliceLoopFuel remaining =
          (2 + bitSliceLoopFuel remaining) + 1 by omega]
      rw [run_add_instruction (value := 2 * accumulator)
        (by rfl) rfl
        (by
          simp [NPOracleState.write, NPOracleState.jump, haccumulator]
          omega)
        hdoubleBits]
      rw [show
        2 + bitSliceLoopFuel remaining =
          (1 + bitSliceLoopFuel remaining) + 1 by omega]
      rw [run_add_instruction (value := 2 * accumulator + digit)
        (by rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump])
        hsumBits]
      rw [show
        1 + bitSliceLoopFuel remaining =
          bitSliceLoopFuel remaining + 1 by omega]
      rw [run_branchZero_instruction (by rfl) rfl]
      rw [ite_self]
      apply inductionHypothesis (2 * accumulator + digit)
      · rfl
      · simp [NPOracleState.write, NPOracleState.jump, hoffset]
      · simp [NPOracleState.write, NPOracleState.jump]
      · simp [NPOracleState.write, NPOracleState.jump, hvalue]
      · simp [NPOracleState.write, NPOracleState.jump]
      · exact hnextBound
      · exact hnextIndexBits

theorem run_bitSliceProgram (inputLength offset width value : ℕ) :
    runNPOracleProgram bitSliceProgram
        (bitSliceBits inputLength offset width value)
        (bitSliceFuel width)
        (initialNPOracleState inputLength
          (bitSliceInput offset width value)) =
      some (bitSlice offset width value) := by
  let request := bitSliceInput offset width value
  let tail := Nat.pair width value
  let maximumBits := bitSliceBits inputLength offset width value
  have hrequestBits : natBitLength request ≤ maximumBits := by
    apply natBitLength_mono
    exact (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hboundBits : natBitLength (2 ^ width) ≤ maximumBits := by
    apply natBitLength_mono
    exact
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hindexBits : natBitLength (offset + width) ≤ maximumBits := by
    apply natBitLength_mono
    exact
      (Nat.le_max_left _ _).trans <|
        (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hoffsetBits : natBitLength offset ≤ maximumBits := by
    apply (natBitLength_mono ?_).trans hrequestBits
    simpa only [request, bitSliceInput] using Nat.left_le_pair offset tail
  have htailBits : natBitLength tail ≤ maximumBits := by
    apply (natBitLength_mono ?_).trans hrequestBits
    simpa only [request, bitSliceInput] using Nat.right_le_pair offset tail
  have hwidthBits : natBitLength width ≤ maximumBits := by
    exact (natBitLength_mono (Nat.left_le_pair width value)).trans htailBits
  have hvalueBits : natBitLength value ≤ maximumBits := by
    exact (natBitLength_mono (Nat.right_le_pair width value)).trans htailBits
  have hzeroBits : natBitLength 0 ≤ maximumBits := by
    exact (natBitLength_mono (Nat.zero_le _)).trans hboundBits
  rw [← bitSliceScan_zero offset width value]
  rw [show bitSliceFuel width = (4 + bitSliceLoopFuel width) + 1 by
    unfold bitSliceFuel
    omega]
  rw [run_unpairLeft_instruction (value := offset)
    (by rfl) rfl
    (by simp [initialNPOracleState, bitSliceInput])
    hoffsetBits]
  rw [show
    4 + bitSliceLoopFuel width = (3 + bitSliceLoopFuel width) + 1 by omega]
  rw [run_unpairRight_instruction (value := tail)
    (by rfl) rfl
    (by
      simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump,
        bitSliceInput, tail])
    htailBits]
  rw [show
    3 + bitSliceLoopFuel width = (2 + bitSliceLoopFuel width) + 1 by omega]
  rw [run_unpairLeft_instruction (value := width)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, tail])
    hwidthBits]
  rw [show
    2 + bitSliceLoopFuel width = (1 + bitSliceLoopFuel width) + 1 by omega]
  rw [run_unpairRight_instruction (value := value)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, tail])
    hvalueBits]
  rw [show
    1 + bitSliceLoopFuel width = bitSliceLoopFuel width + 1 by omega]
  rw [run_set_instruction (value := 0) (by rfl) rfl hzeroBits]
  apply run_bitSliceLoop offset value width maximumBits 0 width
  · rfl
  · simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · simp
  · exact hboundBits
  · exact hindexBits

end NearCubicWires.CanonicalBitSliceProgram
