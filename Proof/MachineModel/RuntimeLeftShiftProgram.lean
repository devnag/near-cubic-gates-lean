import Proof.MachineModel.CanonicalBitSerialMulProgram
import Proof.MachineModel.CanonicalTwoPowProgram
import Proof.MachineModel.CaseTwoOccurrenceProgram

/-!
# The run-time left shift

The instruction set's `shiftLeft` takes a compile-time amount only, so a stage
that has to scale a value by `2 ^ e` for an exponent computed at run time needs
one more primitive.  `CanonicalTwoPowProgram` already supplies the doubling
loop `e ↦ 2 ^ e`, and `CanonicalBitSerialMulProgram` already supplies the
bit-serial product; this module is nothing but their composition through the
count-preserving adapter of `PreserveRightProgram`.

The public ABI is `pair exponent value`, and the certified output is exactly
`2 ^ exponent * value`.  No oracle query, no callee, and no new loop is
introduced: both stages and the linker are already verified.
-/

namespace NearCubicWires.RuntimeLeftShiftProgram

open NearCubicWires
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBitSerialMulProgram
open NearCubicWires.CanonicalTwoPowProgram
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.VerifiedLinker

/-! ## 1. The program -/

/-- Public request of the run-time left shift. -/
def runtimeLeftShiftInput (exponent value : ℕ) : ℕ :=
  Nat.pair exponent value

/-- One fixed program computing `2 ^ exponent * value` for an exponent that
arrives in the request rather than in the instruction stream. -/
def runtimeLeftShiftProgram : NPOracleProgram :=
  linkPrograms (preserveRightProgram binaryTwoPowProgram) bitSerialMulProgram

theorem runtimeLeftShiftProgram_oracleFree :
    OracleFree runtimeLeftShiftProgram := by
  apply oracleFree_linkPrograms
  · exact preserveRightProgram_oracleFree binaryTwoPowProgram
      binaryTwoPowProgram_oracleFree
  · exact bitSerialMulProgram_oracleFree

/-! ## 2. Closed budgets -/

def runtimeLeftShiftFuel (exponent value : ℕ) : ℕ :=
  linkFuel bitSerialMulProgram
    (preserveRightFuel (binaryTwoPowFuel exponent))
    (bitSerialMulFuel value)

def runtimeLeftShiftBits (inputLength exponent value : ℕ) : ℕ :=
  occurrenceStageBits inputLength
    (preserveRightBits (binaryTwoPowBits exponent) exponent value
      (2 ^ exponent))
    (bitSerialMulBits inputLength (2 ^ exponent) value)

/-! ## 3. Exact execution -/

/-- The exponential stage, framed so that its output lands in the left
component of the multiplier's own request ABI. -/
private theorem run_runtimeLeftShiftExponential
    (inputLength exponent value : ℕ) :
    runNPOracleProgram (preserveRightProgram binaryTwoPowProgram)
        (preserveRightBits (binaryTwoPowBits exponent) exponent value
          (2 ^ exponent))
        (preserveRightFuel (binaryTwoPowFuel exponent))
        (initialNPOracleState inputLength
          (runtimeLeftShiftInput exponent value)) =
      some (bitSerialMulInput (2 ^ exponent) value) :=
  run_preserveRightProgram binaryTwoPowProgram inputLength
    (binaryTwoPowBits exponent) (binaryTwoPowFuel exponent) exponent value
    (2 ^ exponent)
    (run_binaryTwoPowProgram inputLength exponent (binaryTwoPowBits exponent)
      (le_refl (binaryTwoPowBits exponent)))

/-- **The run-time left shift, executed.**  One fixed oracle-free program
returns `2 ^ exponent * value` from the public request alone. -/
theorem run_runtimeLeftShiftProgram (inputLength exponent value : ℕ) :
    runNPOracleProgram runtimeLeftShiftProgram
        (runtimeLeftShiftBits inputLength exponent value)
        (runtimeLeftShiftFuel exponent value)
        (initialNPOracleState inputLength
          (runtimeLeftShiftInput exponent value)) =
      some (2 ^ exponent * value) :=
  run_occurrenceStage
    (run_runtimeLeftShiftExponential inputLength exponent value)
    (run_bitSerialMulProgram inputLength (2 ^ exponent) value)

end NearCubicWires.RuntimeLeftShiftProgram
