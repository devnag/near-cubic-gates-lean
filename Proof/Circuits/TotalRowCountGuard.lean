import Proof.MachineModel.TaggedProgramChoice

/-!
# A reusable zero-count call guard

This is the small ABI adapter used by the total PCP row emitter.  It preserves
the original `pair table (pair count payload)` request, exposes `count` as a
choice tag, and runs a canonical-zero branch before the nonzero callee can
decode the payload.
-/

namespace NearCubicWires.TotalRowCountGuard

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.TaggedProgramChoice
open NearCubicWires.VerifiedLinker

def countGuardFrameOutput (tableCode count payload : ℕ) : ℕ :=
  Nat.pair count (Nat.pair tableCode (Nat.pair count payload))

def countGuardFrameProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .pair 2 3 5 4
  , .pair 4 5 0 5
  , .halt 0
  ]

@[simp] theorem countGuardFrameProgram_oracleFree :
    OracleFree countGuardFrameProgram := by
  rfl

def countGuardFrameBits
    (inputLength tableCode count payload : ℕ) : ℕ :=
  max 1 <| max (natBitLength inputLength) <|
    max (natBitLength (Nat.pair tableCode (Nat.pair count payload)))
      (natBitLength (countGuardFrameOutput tableCode count payload))

theorem run_countGuardFrameProgram
    (inputLength tableCode count payload : ℕ) :
    runNPOracleProgram countGuardFrameProgram
        (countGuardFrameBits inputLength tableCode count payload) 6
        (initialNPOracleState inputLength
          (Nat.pair tableCode (Nat.pair count payload))) =
      some (countGuardFrameOutput tableCode count payload) := by
  let maximumBits := countGuardFrameBits inputLength tableCode count payload
  have hinputBits :
      natBitLength (Nat.pair tableCode (Nat.pair count payload)) ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have houtputBits :
      natBitLength (countGuardFrameOutput tableCode count payload) ≤
        maximumBits :=
    (Nat.le_max_right _ _).trans <|
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have htableBits : natBitLength tableCode ≤ maximumBits :=
    (natBitLength_mono
      (Nat.left_le_pair tableCode (Nat.pair count payload))).trans hinputBits
  have htailBits : natBitLength (Nat.pair count payload) ≤ maximumBits :=
    (natBitLength_mono
      (Nat.right_le_pair tableCode (Nat.pair count payload))).trans hinputBits
  have hcountBits : natBitLength count ≤ maximumBits :=
    (natBitLength_mono (Nat.left_le_pair count payload)).trans htailBits
  rw [show (6 : ℕ) = 5 + 1 by omega]
  rw [run_unpairLeft_instruction (value := tableCode)
    (by rfl) rfl (by simp [initialNPOracleState]) htableBits]
  rw [show (5 : ℕ) = 4 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair count payload)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    htailBits]
  rw [show (4 : ℕ) = 3 + 1 by omega]
  rw [run_unpairLeft_instruction (value := count)
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump])
    hcountBits]
  rw [show (3 : ℕ) = 2 + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair tableCode (Nat.pair count payload))
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump])
    hinputBits]
  rw [show (2 : ℕ) = 1 + 1 by omega]
  rw [run_pair_instruction
    (value := countGuardFrameOutput tableCode count payload)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, countGuardFrameOutput])
    houtputBits]
  exact run_halt_instruction (fuel := 0)
    (value := countGuardFrameOutput tableCode count payload)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtputBits

def emptyGuardProgram : NPOracleProgram :=
  [ .set 0 0 1
  , .halt 0
  ]

@[simp] theorem emptyGuardProgram_oracleFree : OracleFree emptyGuardProgram := by
  rfl

theorem run_emptyGuardProgram
    (inputLength value maximumBits : ℕ) (hpositive : 1 ≤ maximumBits) :
    runNPOracleProgram emptyGuardProgram maximumBits 2
        (initialNPOracleState inputLength value) = some 0 := by
  have hzero : natBitLength 0 ≤ maximumBits := by
    simpa [natBitLength] using hpositive
  rw [show (2 : ℕ) = 1 + 1 by omega]
  rw [run_set_instruction (value := 0) (by rfl) rfl hzero]
  exact run_halt_instruction (fuel := 0) (value := 0)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hzero

def countGuardProgram (nonzeroProgram : NPOracleProgram) : NPOracleProgram :=
  linkPrograms countGuardFrameProgram
    (taggedProgramChoice emptyGuardProgram nonzeroProgram)

theorem countGuardProgram_oracleFree
    (nonzeroProgram : NPOracleProgram) (hfree : OracleFree nonzeroProgram) :
    OracleFree (countGuardProgram nonzeroProgram) :=
  oracleFree_linkPrograms countGuardFrameProgram_oracleFree <|
    taggedProgramChoice_oracleFree emptyGuardProgram nonzeroProgram
      emptyGuardProgram_oracleFree hfree

theorem run_countGuardProgram_zero
    (nonzeroProgram : NPOracleProgram)
    (inputLength tableCode payload maximumBits : ℕ)
    (hpositive : 1 ≤ maximumBits)
    (hlength : natBitLength inputLength ≤ maximumBits)
    (hframe :
      countGuardFrameBits inputLength tableCode 0 payload ≤ maximumBits)
    (htagged :
      natBitLength
          (Nat.pair inputLength (countGuardFrameOutput tableCode 0 payload)) ≤
        maximumBits) :
    runNPOracleProgram (countGuardProgram nonzeroProgram) maximumBits
        (linkFuel (taggedProgramChoice emptyGuardProgram nonzeroProgram) 6
          (taggedProgramChoiceFuel 2))
        (initialNPOracleState inputLength
          (Nat.pair tableCode (Nat.pair 0 payload))) =
      some 0 := by
  have hframeRun := run_bits_mono
    (run_countGuardFrameProgram inputLength tableCode 0 payload) hframe
  have hchoice := run_taggedProgramChoice_zero emptyGuardProgram nonzeroProgram
    inputLength (Nat.pair tableCode (Nat.pair 0 payload)) maximumBits 2 0
    htagged
    (run_emptyGuardProgram inputLength
      (Nat.pair tableCode (Nat.pair 0 payload)) maximumBits hpositive)
    (by simpa [natBitLength] using hpositive)
  exact run_linkPrograms hpositive hlength hframeRun hchoice

theorem run_countGuardProgram_nonzero
    (nonzeroProgram : NPOracleProgram)
    (inputLength tableCode count payload maximumBits sourceFuel output : ℕ)
    (hcount : count ≠ 0) (hpositive : 1 ≤ maximumBits)
    (hlength : natBitLength inputLength ≤ maximumBits)
    (hframe :
      countGuardFrameBits inputLength tableCode count payload ≤ maximumBits)
    (htagged :
      natBitLength
          (Nat.pair inputLength
            (countGuardFrameOutput tableCode count payload)) ≤
        maximumBits)
    (hsource :
      runNPOracleProgram nonzeroProgram maximumBits sourceFuel
          (initialNPOracleState inputLength
            (Nat.pair tableCode (Nat.pair count payload))) =
        some output)
    (houtput : natBitLength output ≤ maximumBits) :
    runNPOracleProgram (countGuardProgram nonzeroProgram) maximumBits
        (linkFuel (taggedProgramChoice emptyGuardProgram nonzeroProgram) 6
          (taggedProgramChoiceFuel sourceFuel))
        (initialNPOracleState inputLength
          (Nat.pair tableCode (Nat.pair count payload))) =
      some output := by
  have hframeRun := run_bits_mono
    (run_countGuardFrameProgram inputLength tableCode count payload) hframe
  have hchoice := run_taggedProgramChoice_nonzero emptyGuardProgram
    nonzeroProgram inputLength count
    (Nat.pair tableCode (Nat.pair count payload)) maximumBits sourceFuel output
    hcount htagged hsource houtput
  exact run_linkPrograms hpositive hlength hframeRun hchoice

end NearCubicWires.TotalRowCountGuard
