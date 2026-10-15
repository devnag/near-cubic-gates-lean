import Proof.Foundations.CanonicalBinaryProgram

/-!
# The dyadic exponential as a fixed program

`CanonicalFourfoldRowCountFormula` collapses both published row counts to a
single power of two with a *run-time* exponent, so the counting side needs one
more primitive: `2 ^ e` for an `e` that arrives in register zero rather than
as an immediate.  The instruction set's `shiftLeft` takes a compile-time
amount only, so this module supplies the doubling loop instead.

Its charge is linear in the exponent and its register width is exactly the
answer's width; no oracle query and no callee appear.
-/

namespace NearCubicWires.CanonicalTwoPowProgram

open NearCubicWires
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock

/-!
Register ABI:

* `r0`: the exponent, then the output power;
* `r2`: the remaining exponent;
* `r3`: the accumulated power.
-/
def binaryTwoPowProgram : NPOracleProgram :=
  [ .copy 0 2 1
  , .set 3 1 2
  , .branchZero 2 5 3
  , .decrement 2 4
  , .add 3 3 3 2
  , .copy 3 0 6
  , .halt 0
  ]

@[simp] theorem binaryTwoPowProgram_oracleFree :
    OracleFree binaryTwoPowProgram := by
  rfl

def binaryTwoPowBits (exponent : ℕ) : ℕ :=
  natBitLength (2 ^ exponent)

def binaryTwoPowFuel (exponent : ℕ) : ℕ :=
  3 * exponent + 5

private theorem run_binaryTwoPowLoop (maximumBits : ℕ) :
    ∀ (remaining accumulator : ℕ) (state : NPOracleState),
      state.pc = 2 →
      state.registers 2 = remaining →
      state.registers 3 = accumulator →
      natBitLength remaining ≤ maximumBits →
      (∀ step, step ≤ remaining →
        natBitLength (accumulator * 2 ^ step) ≤ maximumBits) →
      runNPOracleProgram binaryTwoPowProgram maximumBits (3 * remaining + 3)
          state =
        some (accumulator * 2 ^ remaining) := by
  intro remaining
  induction remaining with
  | zero =>
      intro accumulator state hpc hremaining haccumulator _hremainingBits
        hstepBits
      have haccumulatorBits : natBitLength accumulator ≤ maximumBits := by
        have hstep := hstepBits 0 (Nat.le_refl _)
        rwa [pow_zero, mul_one] at hstep
      rw [pow_zero, mul_one]
      have hjump :
          (state.jump (if state.registers 2 = 0 then 5 else 3)).pc = 5 := by
        simp [NPOracleState.jump, hremaining]
      rw [show 3 * 0 + 3 = 2 + 1 by omega]
      rw [run_branchZero_instruction
        (program := binaryTwoPowProgram) (register := 2)
        (zeroTarget := 5) (nonzeroTarget := 3) (by rfl) hpc]
      rw [show 2 = 1 + 1 by omega]
      rw [run_copy_instruction (value := accumulator) (pc := 5) (by rfl) hjump
        (by simp [NPOracleState.jump, haccumulator]) haccumulatorBits]
      exact run_halt_instruction (fuel := 0) (value := accumulator)
        (by rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump])
        haccumulatorBits
  | succ predecessor inductionHypothesis =>
      intro accumulator state hpc hremaining haccumulator hremainingBits
        hstepBits
      have hdouble : ∀ step : ℕ,
          (accumulator + accumulator) * 2 ^ step =
            accumulator * 2 ^ (step + 1) := by
        intro step
        ring
      have hjump :
          (state.jump (if state.registers 2 = 0 then 5 else 3)).pc = 3 := by
        simp [NPOracleState.jump, hremaining]
      have hpredecessorBits : natBitLength predecessor ≤ maximumBits :=
        (natBitLength_mono (Nat.le_succ predecessor)).trans hremainingBits
      have hdoubleBits :
          natBitLength (accumulator + accumulator) ≤ maximumBits := by
        have hstep := hstepBits 1 (by omega)
        rwa [pow_one, Nat.mul_two] at hstep
      rw [show 3 * (predecessor + 1) + 3 = 3 * predecessor + 3 + 1 + 1 + 1 by
        omega]
      rw [run_branchZero_instruction
        (program := binaryTwoPowProgram) (register := 2)
        (zeroTarget := 5) (nonzeroTarget := 3) (by rfl) hpc]
      rw [run_decrement_instruction (value := predecessor) (by rfl) hjump
        (by simp [NPOracleState.jump, hremaining]) hpredecessorBits]
      rw [run_add_instruction (value := accumulator + accumulator)
        (by rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump, haccumulator])
        hdoubleBits]
      rw [show accumulator * 2 ^ (predecessor + 1) =
        (accumulator + accumulator) * 2 ^ predecessor from
          (hdouble predecessor).symm]
      refine inductionHypothesis (accumulator + accumulator) _ rfl ?_ ?_
        hpredecessorBits ?_
      · simp [NPOracleState.write, NPOracleState.jump]
      · simp [NPOracleState.write, NPOracleState.jump]
      · intro step hstep
        rw [hdouble step]
        exact hstepBits (step + 1) (by omega)

/-- **The dyadic exponential, executed.**  The fixed doubling loop returns
`2 ^ exponent` for the exponent supplied in register zero. -/
theorem run_binaryTwoPowProgram
    (inputLength exponent maximumBits : ℕ)
    (hbits : binaryTwoPowBits exponent ≤ maximumBits) :
    runNPOracleProgram binaryTwoPowProgram maximumBits
        (binaryTwoPowFuel exponent)
        (initialNPOracleState inputLength exponent) =
      some (2 ^ exponent) := by
  have hpowerBits : natBitLength (2 ^ exponent) ≤ maximumBits := hbits
  have hexponentBits : natBitLength exponent ≤ maximumBits :=
    (natBitLength_mono (Nat.lt_two_pow_self).le).trans hpowerBits
  have honeBits : natBitLength 1 ≤ maximumBits :=
    (natBitLength_mono Nat.one_le_two_pow).trans hpowerBits
  have hstepBits : ∀ step, step ≤ exponent →
      natBitLength (1 * 2 ^ step) ≤ maximumBits := by
    intro step hstep
    rw [one_mul]
    exact (natBitLength_mono (Nat.pow_le_pow_right (by omega) hstep)).trans
      hpowerBits
  unfold binaryTwoPowFuel
  rw [show 3 * exponent + 5 = 3 * exponent + 3 + 1 + 1 by omega]
  rw [run_copy_instruction (value := exponent) (by rfl) rfl
    (by simp [initialNPOracleState]) hexponentBits]
  rw [run_set_instruction (value := 1) (by rfl) rfl honeBits]
  rw [show (2 : ℕ) ^ exponent = 1 * 2 ^ exponent from (one_mul _).symm]
  refine run_binaryTwoPowLoop maximumBits exponent 1 _ rfl ?_ ?_ hexponentBits
    hstepBits
  · simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]

end NearCubicWires.CanonicalTwoPowProgram
