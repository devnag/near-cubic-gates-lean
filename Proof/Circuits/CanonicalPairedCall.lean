import Proof.MachineModel.PreserveRightProgram

namespace NearCubicWires.CanonicalPairedCall

open NearCubicWires
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.VerifiedLinker

/-! ## Fixed pair swap -/

def swapPairProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .pair 3 2 0 3
  , .halt 0
  ]

def swapPairBits (left right : ℕ) : ℕ :=
  max (natBitLength (Nat.pair left right))
    (natBitLength (Nat.pair right left))

@[simp] theorem swapPairProgram_oracleFree :
    OracleFree swapPairProgram := by
  rfl

theorem run_swapPairProgram
    (inputLength left right : ℕ) :
    runNPOracleProgram swapPairProgram (swapPairBits left right) 4
        (initialNPOracleState inputLength (Nat.pair left right)) =
      some (Nat.pair right left) := by
  have hinput :
      natBitLength (Nat.pair left right) ≤ swapPairBits left right :=
    Nat.le_max_left _ _
  have houtput :
      natBitLength (Nat.pair right left) ≤ swapPairBits left right :=
    Nat.le_max_right _ _
  have hleft : natBitLength left ≤ swapPairBits left right := by
    exact
      (natBitLength_mono (Nat.left_le_pair left right)).trans hinput
  have hright : natBitLength right ≤ swapPairBits left right := by
    exact
      (natBitLength_mono (Nat.right_le_pair left right)).trans hinput
  rw [show 4 = 3 + 1 by omega]
  rw [run_unpairLeft_instruction (by rfl) rfl
    (by simp [initialNPOracleState]) hleft]
  rw [show 3 = 2 + 1 by omega]
  rw [run_unpairRight_instruction (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump]) hright]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump]) houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

/-! ## One callee, two adjacent requests -/

def pairedCallProgram (source : NPOracleProgram) : NPOracleProgram :=
  linkPrograms
    (linkPrograms
      (linkPrograms
        (preserveRightProgram source)
        swapPairProgram)
      (preserveRightProgram source))
    swapPairProgram

def pairedCallFuel
    (source : NPOracleProgram) (leftFuel rightFuel : ℕ) : ℕ :=
  linkFuel swapPairProgram
    (linkFuel (preserveRightProgram source)
      (linkFuel swapPairProgram
        (preserveRightFuel leftFuel) 4)
      (preserveRightFuel rightFuel))
    4

/-- One closed width for every request, output, and linker handoff. -/
def pairedCallBits
    (inputLength leftBits rightBits left right leftOutput rightOutput : ℕ) :
    ℕ :=
  max 1 <| max (natBitLength inputLength) <|
    max (preserveRightBits leftBits left right leftOutput) <|
      max (swapPairBits leftOutput right) <|
        max (preserveRightBits rightBits right leftOutput rightOutput)
          (swapPairBits rightOutput leftOutput)

theorem pairedCallProgram_oracleFree
    (source : NPOracleProgram) (hsource : OracleFree source) :
    OracleFree (pairedCallProgram source) := by
  apply oracleFree_linkPrograms
  · apply oracleFree_linkPrograms
    · apply oracleFree_linkPrograms
      · exact preserveRightProgram_oracleFree source hsource
      · exact swapPairProgram_oracleFree
    · exact preserveRightProgram_oracleFree source hsource
  · exact swapPairProgram_oracleFree

theorem run_pairedCallProgram
    (source : NPOracleProgram)
    (inputLength leftBits rightBits leftFuel rightFuel
      left right leftOutput rightOutput : ℕ)
    (hleft :
      runNPOracleProgram source leftBits leftFuel
          (initialNPOracleState inputLength left) =
        some leftOutput)
    (hright :
      runNPOracleProgram source rightBits rightFuel
          (initialNPOracleState inputLength right) =
        some rightOutput) :
    runNPOracleProgram (pairedCallProgram source)
        (pairedCallBits inputLength leftBits rightBits
          left right leftOutput rightOutput)
        (pairedCallFuel source leftFuel rightFuel)
        (initialNPOracleState inputLength (Nat.pair left right)) =
      some (Nat.pair leftOutput rightOutput) := by
  let maximumBits :=
    pairedCallBits inputLength leftBits rightBits
      left right leftOutput rightOutput
  have hpositive : 1 ≤ maximumBits := by
    simp [maximumBits, pairedCallBits]
  have hlength : natBitLength inputLength ≤ maximumBits := by
    simp [maximumBits, pairedCallBits]
  have hfirstBits :
      preserveRightBits leftBits left right leftOutput ≤ maximumBits := by
    simp [maximumBits, pairedCallBits]
  have hfirstSwapBits :
      swapPairBits leftOutput right ≤ maximumBits := by
    simp [maximumBits, pairedCallBits]
  have hsecondBits :
      preserveRightBits rightBits right leftOutput rightOutput ≤
        maximumBits := by
    simp [maximumBits, pairedCallBits]
  have hsecondSwapBits :
      swapPairBits rightOutput leftOutput ≤ maximumBits := by
    simp [maximumBits, pairedCallBits]
  have hfirst :
      runNPOracleProgram (preserveRightProgram source)
          maximumBits (preserveRightFuel leftFuel)
          (initialNPOracleState inputLength (Nat.pair left right)) =
        some (Nat.pair leftOutput right) := by
    exact run_bits_mono
      (run_preserveRightProgram source inputLength leftBits leftFuel
        left right leftOutput hleft)
      hfirstBits
  have hfirstSwap :
      runNPOracleProgram swapPairProgram maximumBits 4
          (initialNPOracleState inputLength
            (Nat.pair leftOutput right)) =
        some (Nat.pair right leftOutput) := by
    exact run_bits_mono
      (run_swapPairProgram inputLength leftOutput right)
      hfirstSwapBits
  have hsecond :
      runNPOracleProgram (preserveRightProgram source)
          maximumBits (preserveRightFuel rightFuel)
          (initialNPOracleState inputLength
            (Nat.pair right leftOutput)) =
        some (Nat.pair rightOutput leftOutput) := by
    exact run_bits_mono
      (run_preserveRightProgram source inputLength rightBits rightFuel
        right leftOutput rightOutput hright)
      hsecondBits
  have hsecondSwap :
      runNPOracleProgram swapPairProgram maximumBits 4
          (initialNPOracleState inputLength
            (Nat.pair rightOutput leftOutput)) =
        some (Nat.pair leftOutput rightOutput) := by
    exact run_bits_mono
      (run_swapPairProgram inputLength rightOutput leftOutput)
      hsecondSwapBits
  have hfirstLinked :
      runNPOracleProgram
          (linkPrograms (preserveRightProgram source) swapPairProgram)
          maximumBits
          (linkFuel swapPairProgram
            (preserveRightFuel leftFuel) 4)
          (initialNPOracleState inputLength (Nat.pair left right)) =
        some (Nat.pair right leftOutput) := by
    exact run_linkPrograms hpositive hlength hfirst hfirstSwap
  have hsecondLinked :
      runNPOracleProgram
          (linkPrograms
            (linkPrograms (preserveRightProgram source) swapPairProgram)
            (preserveRightProgram source))
          maximumBits
          (linkFuel (preserveRightProgram source)
            (linkFuel swapPairProgram
              (preserveRightFuel leftFuel) 4)
            (preserveRightFuel rightFuel))
          (initialNPOracleState inputLength (Nat.pair left right)) =
        some (Nat.pair rightOutput leftOutput) := by
    exact run_linkPrograms hpositive hlength hfirstLinked hsecond
  exact run_linkPrograms hpositive hlength hsecondLinked hsecondSwap

end NearCubicWires.CanonicalPairedCall
