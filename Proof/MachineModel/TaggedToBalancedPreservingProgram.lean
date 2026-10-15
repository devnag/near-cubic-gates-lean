import Proof.Circuits.CanonicalBalancedBuilder
import Proof.MachineModel.PreserveRightProgram

namespace NearCubicWires.TaggedToBalancedPreservingProgram

open NearCubicWires
open NearCubicWires.CanonicalBalancedBuilder
open NearCubicWires.CanonicalBinary
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PreserveRightProgram

def taggedToBalancedPreservingProgram : NPOracleProgram :=
  preserveRightProgram taggedToBalancedProgram

def taggedToBalancedPreservingInput
    (values : List ℕ) (context : ℕ) : ℕ :=
  Nat.pair (encodeTaggedList values) context

def taggedToBalancedPreservingOutput
    (values : List ℕ) (context : ℕ) : ℕ :=
  Nat.pair (encodeBalancedList values) context

def taggedToBalancedPreservingFuel (values : List ℕ) : ℕ :=
  preserveRightFuel (taggedToBalancedFuel values)

def taggedToBalancedPreservingMaximumBits
    (inputLength : ℕ) (values : List ℕ) (context : ℕ) : ℕ :=
  preserveRightBits
    (taggedToBalancedRegisterBitsFor inputLength values)
    (encodeTaggedList values) context
    (encodeBalancedList values)

theorem taggedToBalancedPreservingProgram_oracleFree :
    OracleFree taggedToBalancedPreservingProgram := by
  exact preserveRightProgram_oracleFree taggedToBalancedProgram
    taggedToBalancedProgram_oracleFree

theorem run_taggedToBalancedPreservingProgram
    (inputLength : ℕ) (values : List ℕ) (context : ℕ) :
    runNPOracleProgram taggedToBalancedPreservingProgram
        (taggedToBalancedPreservingMaximumBits
          inputLength values context)
        (taggedToBalancedPreservingFuel values)
        (initialNPOracleState inputLength
          (taggedToBalancedPreservingInput values context)) =
      some (taggedToBalancedPreservingOutput values context) := by
  exact run_preserveRightProgram taggedToBalancedProgram inputLength
    (taggedToBalancedRegisterBitsFor inputLength values)
    (taggedToBalancedFuel values)
    (encodeTaggedList values) context
    (encodeBalancedList values)
    (run_taggedToBalancedProgram_from inputLength values)

end NearCubicWires.TaggedToBalancedPreservingProgram
