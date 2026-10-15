import Proof.MachineModel.BitInputPrefixProgram
import Proof.MachineModel.CanonicalNativeCallProgram

/-!
# The refuter-word frame

Every scheduled recovery stage below the branch dispatcher consumes the frame
`pair (encodeBitInput word) (pair sourceLength pointCode)`, where `word` is the
published refuter's own output at the scheduled source length.  This module is
the single fixed program that builds that frame from the requested point code
alone.

Three fixed stages, one imported call:

* a six-instruction prelude that emits the canonical `RefuterRequest` code
  beside the retained `(sourceLength, pointCode)` context;
* the shared context-preserving native caller applied once to the published
  refuter's own runner program;
* a six-instruction reframing adapter followed by the shared low-bit
  normalizer, which truncates the refuter's opaque output code to exactly the
  `sourceLength` bits read by `ExecutableSATOracleRefuter.output`.

The machine enters only through the numeral
`ExecutableWeakNondeterministicMachine.description`, which is the sole
machine-dependent register of the refuter request; this is exactly the
dependence isolated by
`CanonicalTargetLanguageProgram.inverseRefuterInput_eq_of_description`.
-/

namespace NearCubicWires.RefuterWordFrameProgram

open NearCubicWires
open NearCubicWires.BitInputPrefixProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalNativeCallProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.VerifiedLinker

/-! ## 1. The request prelude

Input `pointCode`, output
`pair (pair description sourceLength) (pair sourceLength pointCode)`.  The two
numerals are immediates of the instruction stream: the description is the only
machine-dependent one. -/

private def refuterRequestFrameProgram
    (description sourceLength : ℕ) : NPOracleProgram :=
  [ .set 2 description 1
  , .set 3 sourceLength 2
  , .pair 2 3 4 3
  , .pair 3 0 5 4
  , .pair 4 5 0 5
  , .halt 0
  ]

@[simp] private theorem refuterRequestFrameProgram_oracleFree
    (description sourceLength : ℕ) :
    OracleFree (refuterRequestFrameProgram description sourceLength) := by
  rfl

/-- Exact output of the prelude. -/
def refuterRequestFrameOutput
    (description sourceLength pointCode : ℕ) : ℕ :=
  Nat.pair (Nat.pair description sourceLength)
    (Nat.pair sourceLength pointCode)

def refuterRequestFrameBits
    (description sourceLength pointCode : ℕ) : ℕ :=
  natBitLength (refuterRequestFrameOutput description sourceLength pointCode)

private theorem run_refuterRequestFrameProgram
    (inputLength description sourceLength pointCode : ℕ) :
    runNPOracleProgram (refuterRequestFrameProgram description sourceLength)
        (refuterRequestFrameBits description sourceLength pointCode) 6
        (initialNPOracleState inputLength pointCode) =
      some (refuterRequestFrameOutput description sourceLength pointCode) := by
  have houtputBits :
      natBitLength (refuterRequestFrameOutput description sourceLength pointCode)
        ≤ refuterRequestFrameBits description sourceLength pointCode :=
    Nat.le_refl _
  have hrequestBits :
      natBitLength (Nat.pair description sourceLength) ≤
        refuterRequestFrameBits description sourceLength pointCode :=
    natBitLength_mono
      (Nat.left_le_pair (Nat.pair description sourceLength)
        (Nat.pair sourceLength pointCode))
  have hretainedBits :
      natBitLength (Nat.pair sourceLength pointCode) ≤
        refuterRequestFrameBits description sourceLength pointCode :=
    natBitLength_mono
      (Nat.right_le_pair (Nat.pair description sourceLength)
        (Nat.pair sourceLength pointCode))
  have hdescriptionBits :
      natBitLength description ≤
        refuterRequestFrameBits description sourceLength pointCode :=
    (natBitLength_mono (Nat.left_le_pair description sourceLength)).trans
      hrequestBits
  have hsourceLengthBits :
      natBitLength sourceLength ≤
        refuterRequestFrameBits description sourceLength pointCode :=
    (natBitLength_mono (Nat.right_le_pair description sourceLength)).trans
      hrequestBits
  rw [show 6 = 5 + 1 by omega]
  rw [run_set_instruction (value := description) (by rfl) rfl hdescriptionBits]
  rw [show 5 = 4 + 1 by omega]
  rw [run_set_instruction (value := sourceLength) (by rfl) rfl
    hsourceLengthBits]
  rw [show 4 = 3 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair description sourceLength)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hrequestBits]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair sourceLength pointCode)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hretainedBits]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction
    (value := refuterRequestFrameOutput description sourceLength pointCode)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump,
        refuterRequestFrameOutput])
    houtputBits]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    houtputBits

/-! ## 2. The truncation adapter

Input `pair outputCode (pair sourceLength pointCode)`, output
`pair (pair sourceLength outputCode) (pair sourceLength pointCode)`.  The left
component is precisely `bitInputPrefixInput sourceLength outputCode`. -/

private def refuterPrefixFrameProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .pair 4 2 5 4
  , .pair 5 3 0 5
  , .halt 0
  ]

@[simp] private theorem refuterPrefixFrameProgram_oracleFree :
    OracleFree refuterPrefixFrameProgram := by
  rfl

def refuterPrefixFrameInput
    (sourceLength pointCode outputCode : ℕ) : ℕ :=
  Nat.pair outputCode (Nat.pair sourceLength pointCode)

def refuterPrefixFrameOutput
    (sourceLength pointCode outputCode : ℕ) : ℕ :=
  Nat.pair (bitInputPrefixInput sourceLength outputCode)
    (Nat.pair sourceLength pointCode)

def refuterPrefixFrameBits
    (sourceLength pointCode outputCode : ℕ) : ℕ :=
  natBitLength
    (max (refuterPrefixFrameInput sourceLength pointCode outputCode)
      (refuterPrefixFrameOutput sourceLength pointCode outputCode))

private theorem run_refuterPrefixFrameProgram
    (inputLength sourceLength pointCode outputCode : ℕ) :
    runNPOracleProgram refuterPrefixFrameProgram
        (refuterPrefixFrameBits sourceLength pointCode outputCode) 6
        (initialNPOracleState inputLength
          (refuterPrefixFrameInput sourceLength pointCode outputCode)) =
      some (refuterPrefixFrameOutput sourceLength pointCode outputCode) := by
  have hinputBits :
      natBitLength (refuterPrefixFrameInput sourceLength pointCode outputCode) ≤
        refuterPrefixFrameBits sourceLength pointCode outputCode :=
    natBitLength_mono (Nat.le_max_left _ _)
  have houtputBits :
      natBitLength (refuterPrefixFrameOutput sourceLength pointCode outputCode) ≤
        refuterPrefixFrameBits sourceLength pointCode outputCode :=
    natBitLength_mono (Nat.le_max_right _ _)
  have hcodeBits :
      natBitLength outputCode ≤
        refuterPrefixFrameBits sourceLength pointCode outputCode :=
    (natBitLength_mono
      (Nat.left_le_pair outputCode (Nat.pair sourceLength pointCode))).trans
      hinputBits
  have hretainedBits :
      natBitLength (Nat.pair sourceLength pointCode) ≤
        refuterPrefixFrameBits sourceLength pointCode outputCode :=
    (natBitLength_mono
      (Nat.right_le_pair outputCode (Nat.pair sourceLength pointCode))).trans
      hinputBits
  have hsourceLengthBits :
      natBitLength sourceLength ≤
        refuterPrefixFrameBits sourceLength pointCode outputCode :=
    (natBitLength_mono (Nat.left_le_pair sourceLength pointCode)).trans
      hretainedBits
  have hprefixBits :
      natBitLength (bitInputPrefixInput sourceLength outputCode) ≤
        refuterPrefixFrameBits sourceLength pointCode outputCode :=
    (natBitLength_mono
      (Nat.left_le_pair (bitInputPrefixInput sourceLength outputCode)
        (Nat.pair sourceLength pointCode))).trans houtputBits
  rw [show 6 = 5 + 1 by omega]
  rw [run_unpairLeft_instruction (value := outputCode)
    (by rfl) rfl
    (by simp [initialNPOracleState, refuterPrefixFrameInput])
    hcodeBits]
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair sourceLength pointCode)
    (by rfl) rfl
    (by
      simp [initialNPOracleState, refuterPrefixFrameInput,
        NPOracleState.write, NPOracleState.jump])
    hretainedBits]
  rw [show 4 = 3 + 1 by omega]
  rw [run_unpairLeft_instruction (value := sourceLength)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hsourceLengthBits]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction
    (value := bitInputPrefixInput sourceLength outputCode)
    (by
      rfl)
    rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, bitInputPrefixInput])
    hprefixBits]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction
    (value := refuterPrefixFrameOutput sourceLength pointCode outputCode)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump,
        refuterPrefixFrameOutput])
    houtputBits]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    houtputBits

/-! ## 3. The composed frame builder -/

/-- The published refuter's word, truncated to its own arity, is exactly the
canonical prefix of its opaque output code. -/
theorem encodeBitInput_refuterOutput
    {hierarchy : Language} {bound : ℕ → ℕ}
    (refuter : ExecutableSATOracleRefuter hierarchy bound)
    (machine : ExecutableWeakNondeterministicMachine) (arity : ℕ) :
    encodeBitInput (refuter.output machine arity) =
      bitInputPrefix arity (refuter.outputCode machine arity) := by
  rw [bitInputPrefix_eq_encodeView]
  rfl

/-- One fixed program: from the requested point code alone it emits the exact
frame consumed by every scheduled recovery stage. -/
def refuterWordFrameProgram
    (refuterProgram : NPOracleProgram) (description sourceLength : ℕ) :
    NPOracleProgram :=
  linkPrograms (refuterRequestFrameProgram description sourceLength)
    (linkPrograms (nativeContextCallProgram refuterProgram)
      (linkPrograms refuterPrefixFrameProgram
        (preserveRightProgram bitInputPrefixProgram)))

theorem refuterWordFrameProgram_oracleFree
    {refuterProgram : NPOracleProgram} (hrefuter : OracleFree refuterProgram)
    (description sourceLength : ℕ) :
    OracleFree
      (refuterWordFrameProgram refuterProgram description sourceLength) := by
  apply oracleFree_linkPrograms
  · exact refuterRequestFrameProgram_oracleFree description sourceLength
  · apply oracleFree_linkPrograms
    · exact nativeContextCallProgram_oracleFree hrefuter
    · apply oracleFree_linkPrograms
      · exact refuterPrefixFrameProgram_oracleFree
      · exact preserveRightProgram_oracleFree bitInputPrefixProgram
          bitInputPrefixProgram_oracleFree

def refuterWordFrameFuel
    {hierarchy : Language} {bound : ℕ → ℕ}
    (refuter : ExecutableSATOracleRefuter hierarchy bound)
    (machine : ExecutableWeakNondeterministicMachine)
    (sourceLength : ℕ) : ℕ :=
  linkFuel
    (linkPrograms (nativeContextCallProgram refuter.runner.program)
      (linkPrograms refuterPrefixFrameProgram
        (preserveRightProgram bitInputPrefixProgram)))
    6
    (linkFuel
      (linkPrograms refuterPrefixFrameProgram
        (preserveRightProgram bitInputPrefixProgram))
      (nativeContextCallFuel refuter.runner.program
        (refuter.runner.budget (refuter.request machine sourceLength))
        sourceLength (Nat.pair machine.description sourceLength))
      (linkFuel (preserveRightProgram bitInputPrefixProgram) 6
        (preserveRightFuel
          (bitInputPrefixFuel sourceLength
            (refuter.outputCode machine sourceLength)))))

def refuterWordFrameBits
    {hierarchy : Language} {bound : ℕ → ℕ}
    (refuter : ExecutableSATOracleRefuter hierarchy bound)
    (machine : ExecutableWeakNondeterministicMachine)
    (target sourceLength pointCode : ℕ) : ℕ :=
  max 1 <|
    max (natBitLength target) <|
      max
        (refuterRequestFrameBits machine.description sourceLength pointCode) <|
        max
          (nativeContextCallBits target sourceLength
            (Nat.pair machine.description sourceLength) pointCode
            (refuter.outputCode machine sourceLength)
            (refuter.runner.budget (refuter.request machine sourceLength))) <|
          max
            (refuterPrefixFrameBits sourceLength pointCode
              (refuter.outputCode machine sourceLength))
            (preserveRightBits
              (bitInputPrefixBits sourceLength
                (refuter.outputCode machine sourceLength))
              (bitInputPrefixInput sourceLength
                (refuter.outputCode machine sourceLength))
              (Nat.pair sourceLength pointCode)
              (bitInputPrefix sourceLength
                (refuter.outputCode machine sourceLength)))

/-- Exact refuter-word framing.  One fixed instruction stream, parameterized by
the machine description numeral and the scheduled source length, turns the
requested point code into the frame
`pair (encodeBitInput word) (pair sourceLength pointCode)` of the published
refuter's word at that length.  The only imported execution is the single
published refuter call. -/
theorem run_refuterWordFrameProgram
    {hierarchy : Language} {bound : ℕ → ℕ}
    (refuter : ExecutableSATOracleRefuter hierarchy bound)
    (machine : ExecutableWeakNondeterministicMachine)
    (target sourceLength pointCode : ℕ) :
    runNPOracleProgram
        (refuterWordFrameProgram refuter.runner.program machine.description
          sourceLength)
        (refuterWordFrameBits refuter machine target sourceLength pointCode)
        (refuterWordFrameFuel refuter machine sourceLength)
        (initialNPOracleState target pointCode) =
      some
        (Nat.pair (encodeBitInput (refuter.output machine sourceLength))
          (Nat.pair sourceLength pointCode)) := by
  have hpositive :
      1 ≤ refuterWordFrameBits refuter machine target sourceLength pointCode :=
    Nat.le_max_left _ _
  have htargetBits :
      natBitLength target ≤
        refuterWordFrameBits refuter machine target sourceLength pointCode :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hpreludeBits :
      refuterRequestFrameBits machine.description sourceLength pointCode ≤
        refuterWordFrameBits refuter machine target sourceLength pointCode :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hcallBits :
      nativeContextCallBits target sourceLength
          (Nat.pair machine.description sourceLength) pointCode
          (refuter.outputCode machine sourceLength)
          (refuter.runner.budget (refuter.request machine sourceLength)) ≤
        refuterWordFrameBits refuter machine target sourceLength pointCode :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hadapterBits :
      refuterPrefixFrameBits sourceLength pointCode
          (refuter.outputCode machine sourceLength) ≤
        refuterWordFrameBits refuter machine target sourceLength pointCode :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans <|
          (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hprefixBits :
      preserveRightBits
          (bitInputPrefixBits sourceLength
            (refuter.outputCode machine sourceLength))
          (bitInputPrefixInput sourceLength
            (refuter.outputCode machine sourceLength))
          (Nat.pair sourceLength pointCode)
          (bitInputPrefix sourceLength
            (refuter.outputCode machine sourceLength)) ≤
        refuterWordFrameBits refuter machine target sourceLength pointCode :=
    (Nat.le_max_right _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans <|
          (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hprelude :=
    run_bits_mono
      (run_refuterRequestFrameProgram target machine.description sourceLength
        pointCode)
      hpreludeBits
  have hrefuter :
      runNPOracleProgram refuter.runner.program
          (refuter.runner.budget (refuter.request machine sourceLength))
          (refuter.runner.budget (refuter.request machine sourceLength))
          (initialNPOracleState sourceLength
            (Nat.pair machine.description sourceLength)) =
        some (refuter.outputCode machine sourceLength) :=
    refuter.runner.run_eq_execute (refuter.request machine sourceLength)
  have hcall :=
    run_bits_mono
      (run_nativeContextCallProgram refuter.runner.program target sourceLength
        (Nat.pair machine.description sourceLength) pointCode
        (refuter.outputCode machine sourceLength)
        (refuter.runner.budget (refuter.request machine sourceLength))
        (refuter.runner.budget (refuter.request machine sourceLength))
        hrefuter)
      hcallBits
  have hadapter :=
    run_bits_mono
      (run_refuterPrefixFrameProgram target sourceLength pointCode
        (refuter.outputCode machine sourceLength))
      hadapterBits
  have hprefix :=
    run_bits_mono
      (run_preserveRightProgram bitInputPrefixProgram target
        (bitInputPrefixBits sourceLength
          (refuter.outputCode machine sourceLength))
        (bitInputPrefixFuel sourceLength
          (refuter.outputCode machine sourceLength))
        (bitInputPrefixInput sourceLength
          (refuter.outputCode machine sourceLength))
        (Nat.pair sourceLength pointCode)
        (bitInputPrefix sourceLength
          (refuter.outputCode machine sourceLength))
        (run_bitInputPrefixProgram target sourceLength
          (refuter.outputCode machine sourceLength)
          (bitInputPrefixBits sourceLength
            (refuter.outputCode machine sourceLength))
          0 (Nat.le_refl _)))
      hprefixBits
  have hthird := run_linkPrograms hpositive htargetBits hadapter hprefix
  have hsecond := run_linkPrograms hpositive htargetBits hcall hthird
  have hrun := run_linkPrograms hpositive htargetBits hprelude hsecond
  rw [encodeBitInput_refuterOutput refuter machine sourceLength]
  simpa only [refuterWordFrameProgram, refuterWordFrameFuel,
    refuterRequestFrameOutput, refuterPrefixFrameInput,
    refuterPrefixFrameOutput] using hrun

end NearCubicWires.RefuterWordFrameProgram
