import Proof.Foundations.CanonicalBinaryProgram

/-!
# The base-two ceiling logarithm as a fixed program

`Nat.clog 2` selects every canonical walk length and graded rank in the
normalized supplier: `canonicalWalkLength denominator` is
`2 * Nat.clog 2 (denominator + 1) + 1`, and `canonicalGradedRank` is a maximum
of two base-two ceiling logarithms.  Consequently no executable row counter
can exist until the machine can evaluate `Nat.clog 2`.

This module supplies that primitive.  The loop compares by saturating
subtraction rather than by an inlined comparator, so the whole program is a
single fixed instruction list with no callee and no oracle query, and its
charged fuel is linear in the answer rather than in the input value.
-/

namespace NearCubicWires.CanonicalNatCeilLogProgram

open NearCubicWires
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock

/-!
Register ABI:

* `r0`: the input value, then the output logarithm;
* `r2`: the current power `2 ^ offset`;
* `r3`: the current exponent `offset`;
* `r4`: the saturating difference `value - 2 ^ offset`, which is zero exactly
  when the loop has reached the ceiling logarithm.
-/
def binaryNatCeilLogProgram : NPOracleProgram :=
  [ .set 2 1 1
  , .set 3 0 2
  , .subtract 0 2 4 3
  , .branchZero 4 6 4
  , .add 2 2 2 5
  , .increment 3 2
  , .copy 3 0 7
  , .halt 0
  ]

@[simp] theorem binaryNatCeilLogProgram_oracleFree :
    OracleFree binaryNatCeilLogProgram := by
  rfl

/-- Every register value stays below the smallest power of two dominating the
input, so one closed bound covers the whole run. -/
def binaryNatCeilLogRegisterBound (value : ℕ) : ℕ :=
  2 ^ Nat.clog 2 value

def binaryNatCeilLogBits (value : ℕ) : ℕ :=
  natBitLength (binaryNatCeilLogRegisterBound value)

/-- The charge is linear in the answer, not in the input value. -/
def binaryNatCeilLogFuel (value : ℕ) : ℕ :=
  4 * Nat.clog 2 value + 6

private theorem boundedBits
    {value candidate maximumBits : ℕ}
    (hcandidate : candidate ≤ binaryNatCeilLogRegisterBound value)
    (hbits : binaryNatCeilLogBits value ≤ maximumBits) :
    natBitLength candidate ≤ maximumBits :=
  (natBitLength_mono hcandidate).trans hbits

private theorem value_le_bound (value : ℕ) :
    value ≤ binaryNatCeilLogRegisterBound value :=
  Nat.le_pow_clog (by norm_num) value

private theorem one_le_bound (value : ℕ) :
    1 ≤ binaryNatCeilLogRegisterBound value :=
  Nat.one_le_two_pow

private theorem power_le_bound {value offset : ℕ}
    (hoffset : offset ≤ Nat.clog 2 value) :
    2 ^ offset ≤ binaryNatCeilLogRegisterBound value :=
  Nat.pow_le_pow_right (by norm_num) hoffset

private theorem exponent_le_bound {value offset : ℕ}
    (hoffset : offset ≤ Nat.clog 2 value) :
    offset ≤ binaryNatCeilLogRegisterBound value :=
  hoffset.trans (Nat.lt_two_pow_self).le

private theorem run_binaryNatCeilLogLoop (maximumBits value : ℕ)
    (hbits : binaryNatCeilLogBits value ≤ maximumBits) :
    ∀ (steps offset : ℕ), Nat.clog 2 value - offset = steps →
      offset ≤ Nat.clog 2 value →
      ∀ state : NPOracleState, state.pc = 2 →
        state.registers 0 = value →
        state.registers 2 = 2 ^ offset →
        state.registers 3 = offset →
        runNPOracleProgram binaryNatCeilLogProgram maximumBits
            (4 * steps + 4) state =
          some (Nat.clog 2 value) := by
  intro steps
  induction steps with
  | zero =>
      intro offset hsteps hoffset state hpc hvalue hpower hexponent
      have hoffsetEq : offset = Nat.clog 2 value := by omega
      have hle : value ≤ 2 ^ offset := by
        rw [hoffsetEq]
        exact Nat.le_pow_clog (by norm_num) value
      have hzero : value - 2 ^ offset = 0 := Nat.sub_eq_zero_iff_le.mpr hle
      have hdifferenceBits :
          natBitLength (value - 2 ^ offset) ≤ maximumBits :=
        boundedBits ((Nat.sub_le value (2 ^ offset)).trans
          (value_le_bound value)) hbits
      have hexponentBits : natBitLength offset ≤ maximumBits :=
        boundedBits (exponent_le_bound hoffset) hbits
      rw [← hoffsetEq]
      rw [show 4 * 0 + 4 = 3 + 1 by omega]
      rw [run_subtract_instruction (value := value - 2 ^ offset)
        (by rfl) hpc
        (by rw [hvalue, hpower]) hdifferenceBits]
      rw [show 3 = 2 + 1 by omega]
      rw [run_branchZero_instruction
        (program := binaryNatCeilLogProgram) (register := 4)
        (zeroTarget := 6) (nonzeroTarget := 4) (by rfl) rfl]
      rw [show 2 = 1 + 1 by omega]
      rw [run_copy_instruction (value := offset) (pc := 6) (by rfl)
        (by simp [NPOracleState.write, NPOracleState.jump, hzero])
        (by simp [NPOracleState.write, NPOracleState.jump, hexponent])
        hexponentBits]
      exact run_halt_instruction (fuel := 0) (value := offset) (by rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump])
        hexponentBits
  | succ predecessor inductionHypothesis =>
      intro offset hsteps hoffset state hpc hvalue hpower hexponent
      have hlt : offset < Nat.clog 2 value := by omega
      have hpowerLt : 2 ^ offset < value :=
        (Nat.lt_clog_iff_pow_lt (by norm_num)).mp hlt
      have hnonzero : value - 2 ^ offset ≠ 0 := by omega
      have hsuccessor : offset + 1 ≤ Nat.clog 2 value := hlt
      have hdifferenceBits :
          natBitLength (value - 2 ^ offset) ≤ maximumBits :=
        boundedBits ((Nat.sub_le value (2 ^ offset)).trans
          (value_le_bound value)) hbits
      have hdoubleBits :
          natBitLength (2 ^ offset + 2 ^ offset) ≤ maximumBits := by
        have hdouble : 2 ^ offset + 2 ^ offset = 2 ^ (offset + 1) := by
          ring
        rw [hdouble]
        exact boundedBits (power_le_bound hsuccessor) hbits
      have hexponentBits : natBitLength (offset + 1) ≤ maximumBits :=
        boundedBits (exponent_le_bound hsuccessor) hbits
      rw [show 4 * (predecessor + 1) + 4 = 4 * predecessor + 4 + 1 + 1 + 1 + 1 by
        omega]
      rw [run_subtract_instruction (value := value - 2 ^ offset)
        (by rfl) hpc
        (by rw [hvalue, hpower]) hdifferenceBits]
      rw [run_branchZero_instruction
        (program := binaryNatCeilLogProgram) (register := 4)
        (zeroTarget := 6) (nonzeroTarget := 4) (by rfl) rfl]
      rw [run_add_instruction (value := 2 ^ offset + 2 ^ offset) (pc := 4)
        (by rfl)
        (by simp [NPOracleState.write, NPOracleState.jump, hnonzero])
        (by simp [NPOracleState.write, NPOracleState.jump, hpower])
        hdoubleBits]
      rw [run_increment_instruction (value := offset + 1) (by rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump, hexponent])
        hexponentBits]
      refine inductionHypothesis (offset + 1) (by omega) hsuccessor _ rfl ?_
        ?_ ?_
      · simp [NPOracleState.write, NPOracleState.jump, hvalue]
      · have hdouble : 2 ^ offset + 2 ^ offset = 2 ^ (offset + 1) := by
          ring
        simp [NPOracleState.write, NPOracleState.jump, hdouble]
      · simp [NPOracleState.write, NPOracleState.jump]

/-- **The base-two ceiling logarithm, executed.**  The fixed program returns
`Nat.clog 2 value` exactly, for every natural input including zero and one. -/
theorem run_binaryNatCeilLogProgram
    (inputLength value maximumBits : ℕ)
    (hbits : binaryNatCeilLogBits value ≤ maximumBits) :
    runNPOracleProgram binaryNatCeilLogProgram maximumBits
        (binaryNatCeilLogFuel value)
        (initialNPOracleState inputLength value) =
      some (Nat.clog 2 value) := by
  have honeBits : natBitLength 1 ≤ maximumBits :=
    boundedBits (one_le_bound value) hbits
  have hzeroBits : natBitLength 0 ≤ maximumBits :=
    boundedBits (Nat.zero_le _) hbits
  unfold binaryNatCeilLogFuel
  rw [show 4 * Nat.clog 2 value + 6 = 4 * Nat.clog 2 value + 4 + 1 + 1 by omega]
  rw [run_set_instruction (value := 1) (by rfl) rfl honeBits]
  rw [run_set_instruction (value := 0) (by rfl) rfl hzeroBits]
  refine run_binaryNatCeilLogLoop maximumBits value hbits (Nat.clog 2 value) 0
    (by omega) (Nat.zero_le _) _ rfl ?_ ?_ ?_
  · simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump]
  · simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump]
  · simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump]

end NearCubicWires.CanonicalNatCeilLogProgram
