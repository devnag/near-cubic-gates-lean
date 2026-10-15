import Proof.MachineModel.CanonicalBalancedLengthProgram
import Proof.MachineModel.CanonicalBooleanNodeBatchProgram
import Proof.Circuits.CanonicalForkCall

/-!
# Canonical Boolean-circuit preparation

One in-machine fork derives the exact balanced-list length and the validated
node-descriptor tree from the same canonical node word.  The topology pass
therefore receives a machine-derived count paired with the sole structural
descriptor stream; neither value can be supplied independently by a caller.
-/

namespace NearCubicWires.CanonicalBooleanCircuitPreparationProgram

open NearCubicWires
open NearCubicWires.CanonicalBalancedLengthProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBooleanNodeBatchProgram
open NearCubicWires.CanonicalForkCall
open NearCubicWires.ExecutableInterfaces

def booleanCircuitPreparationOutput (rawNodes : List ℕ) : ℕ :=
  Nat.pair rawNodes.length
    (encodeBalancedList (booleanNodeOutputs rawNodes))

def booleanCircuitPreparationProgram : NPOracleProgram :=
  forkCallProgram balancedLengthProgram booleanNodeBatchProgram

@[simp] theorem booleanCircuitPreparationProgram_oracleFree :
    OracleFree booleanCircuitPreparationProgram := by
  exact forkCallProgram_oracleFree
    balancedLengthProgram booleanNodeBatchProgram
    balancedLengthProgram_oracleFree
    booleanNodeBatchProgram_oracleFree

def booleanCircuitPreparationBits
    (inputLength : ℕ) (rawNodes : List ℕ) : ℕ :=
  forkCallBits inputLength (encodeBalancedList rawNodes)
    (balancedLengthBits inputLength rawNodes)
    (booleanNodeBatchBits inputLength rawNodes)
    rawNodes.length
    (encodeBalancedList (booleanNodeOutputs rawNodes))

def booleanCircuitPreparationFuel
    (inputLength : ℕ) (rawNodes : List ℕ) : ℕ :=
  forkCallFuel balancedLengthProgram booleanNodeBatchProgram
    (balancedLengthFuel rawNodes)
    (booleanNodeBatchFuel inputLength rawNodes)

theorem run_booleanCircuitPreparationProgram
    (inputLength : ℕ) (rawNodes : List ℕ) :
    runNPOracleProgram booleanCircuitPreparationProgram
        (booleanCircuitPreparationBits inputLength rawNodes)
        (booleanCircuitPreparationFuel inputLength rawNodes)
        (initialNPOracleState inputLength
          (encodeBalancedList rawNodes)) =
      some (booleanCircuitPreparationOutput rawNodes) := by
  exact run_forkCallProgram
    balancedLengthProgram booleanNodeBatchProgram
    inputLength (encodeBalancedList rawNodes)
    (balancedLengthBits inputLength rawNodes)
    (booleanNodeBatchBits inputLength rawNodes)
    (balancedLengthFuel rawNodes)
    (booleanNodeBatchFuel inputLength rawNodes)
    rawNodes.length
    (encodeBalancedList (booleanNodeOutputs rawNodes))
    (run_balancedLengthProgram inputLength rawNodes)
    (run_booleanNodeBatchProgram inputLength rawNodes)

end NearCubicWires.CanonicalBooleanCircuitPreparationProgram
