import Proof.MachineModel.BranchTargetLanguageProgram

/-!
# The per-block Case-2 occurrence callee

`CaseTwoSeedBlockListProgram` closes the Case-2 branch of the canonical target
modulo exactly one parameter: a program receiving `pair block pointCode` at the
public target length and returning the honest occurrence bit of the published
factory at that block's occurrence code.  This module builds that program.

Nothing new is computed.  The occurrence itself is already executed by
`CaseTwoOccurrenceProgram.run_caseTwoOccurrenceProgram`; what has to be added
in front of it is the occurrence-code assembly of
`CaseTwoOccurrenceCoordinates.nativeOccurrenceCode`, which is

* one product `block * arity`, the block's digit offset in the requested point
  code — `CanonicalBitSerialMulProgram`;
* three interior digit windows — `CanonicalBitSliceProgram`: the block window
  itself, then its low input window and its interior clause window;
* one occurrence position digit — the register-indexed `testBit` opcode;
* two scalings by a run-time power of two — `RuntimeLeftShiftProgram`;
* two additions.

Seven straight-line framing adapters move those already computed naturals
between the published call ABIs, and the whole chain is assembled with the
verified linker and the count-preserving wrapper.  No oracle query, no
callback, and no second occurrence convention is introduced: the only oracle
opcode anywhere below the target dispatcher is the branch selector's, which
lives elsewhere.

The circuit data — arity, size, and encoding — are immediates of the stream,
exactly as the XOR copy count is an immediate of the block-list stage.  They
are supplied by the caller rather than recomputed inside the callee.
-/

namespace NearCubicWires.CaseTwoBlockOccurrenceProgram

open NearCubicWires
open NearCubicWires.BranchTargetLanguageProgram
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBitSerialMulProgram
open NearCubicWires.CanonicalBitSliceProgram
open NearCubicWires.CanonicalTargetBitProgram
open NearCubicWires.CanonicalTargetLanguageProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceCoordinates
open NearCubicWires.CaseTwoOccurrenceEvaluation
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.CaseTwoOccurrenceSpecification
open NearCubicWires.CaseTwoRecoveryAssembly
open NearCubicWires.CaseTwoSeedBlockListProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PCPPClausePadding
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.ProjectionWidthEnvelope
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RuntimeLeftShiftProgram
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.VerifiedLinker

/-! ## 1. Width bookkeeping shared by every framing adapter -/

private theorem le_pair_of_le_left {value left right : ℕ}
    (hvalue : value ≤ left) : value ≤ Nat.pair left right :=
  hvalue.trans (Nat.left_le_pair left right)

private theorem le_pair_of_le_right {value left right : ℕ}
    (hvalue : value ≤ right) : value ≤ Nat.pair left right :=
  hvalue.trans (Nat.right_le_pair left right)

/-! ## 2. The block window of the requested point code

Register ABI of both adapters: `r2` the leading field of the request, `r3` its
trailing field, `r4` the block arity immediate, `r5` the assembled callee
request. -/

/-- Frame the requested `pair block pointCode` as the bit-serial product
request for the block's digit offset, retaining the point code. -/
def blockOffsetPrepProgram (arity : ℕ) : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .set 4 arity 3
  , .pair 2 4 5 4
  , .pair 5 3 0 5
  , .halt 0
  ]

@[simp] theorem blockOffsetPrepProgram_oracleFree (arity : ℕ) :
    OracleFree (blockOffsetPrepProgram arity) := by
  rfl

def blockOffsetPrepOutput (arity block pointCode : ℕ) : ℕ :=
  Nat.pair (bitSerialMulInput block arity) pointCode

def blockOffsetPrepBits (arity block pointCode : ℕ) : ℕ :=
  natBitLength
    (max (Nat.pair block pointCode) (blockOffsetPrepOutput arity block pointCode))

theorem run_blockOffsetPrepProgram (inputLength arity block pointCode : ℕ) :
    runNPOracleProgram (blockOffsetPrepProgram arity)
        (blockOffsetPrepBits arity block pointCode) 6
        (initialNPOracleState inputLength (Nat.pair block pointCode)) =
      some (blockOffsetPrepOutput arity block pointCode) := by
  have hrequest : ∀ value : ℕ, value ≤ Nat.pair block pointCode →
      natBitLength value ≤ blockOffsetPrepBits arity block pointCode :=
    fun _ hvalue => natBitLength_mono (hvalue.trans (Nat.le_max_left _ _))
  have hresult : ∀ value : ℕ,
      value ≤ blockOffsetPrepOutput arity block pointCode →
      natBitLength value ≤ blockOffsetPrepBits arity block pointCode :=
    fun _ hvalue => natBitLength_mono (hvalue.trans (Nat.le_max_right _ _))
  have hblock := hrequest block (Nat.left_le_pair block pointCode)
  have hpoint := hrequest pointCode (Nat.right_le_pair block pointCode)
  have harity :=
    hresult arity (le_pair_of_le_left (Nat.right_le_pair block arity))
  have hproduct :=
    hresult (bitSerialMulInput block arity)
      (le_pair_of_le_left (le_refl _))
  have houtput := hresult _ (le_refl _)
  rw [show 6 = 5 + 1 by omega]
  rw [run_unpairLeft_instruction (value := block) (by rfl) rfl
    (by simp [initialNPOracleState]) hblock]
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairRight_instruction (value := pointCode) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hpoint]
  rw [show 4 = 3 + 1 by omega]
  rw [run_set_instruction (value := arity) (by rfl) rfl harity]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction (value := bitSerialMulInput block arity) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, bitSerialMulInput])
    hproduct]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction
    (value := blockOffsetPrepOutput arity block pointCode) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, blockOffsetPrepOutput])
    houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

/-- Frame the computed digit offset and the retained point code as the digit
window request of the block. -/
def blockWindowPrepProgram (arity : ℕ) : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .set 4 arity 3
  , .pair 4 3 5 4
  , .pair 2 5 0 5
  , .halt 0
  ]

@[simp] theorem blockWindowPrepProgram_oracleFree (arity : ℕ) :
    OracleFree (blockWindowPrepProgram arity) := by
  rfl

def blockWindowPrepBits (arity offset pointCode : ℕ) : ℕ :=
  natBitLength
    (max (Nat.pair offset pointCode) (bitSliceInput offset arity pointCode))

theorem run_blockWindowPrepProgram (inputLength arity offset pointCode : ℕ) :
    runNPOracleProgram (blockWindowPrepProgram arity)
        (blockWindowPrepBits arity offset pointCode) 6
        (initialNPOracleState inputLength (Nat.pair offset pointCode)) =
      some (bitSliceInput offset arity pointCode) := by
  have hrequest : ∀ value : ℕ, value ≤ Nat.pair offset pointCode →
      natBitLength value ≤ blockWindowPrepBits arity offset pointCode :=
    fun _ hvalue => natBitLength_mono (hvalue.trans (Nat.le_max_left _ _))
  have hresult : ∀ value : ℕ,
      value ≤ bitSliceInput offset arity pointCode →
      natBitLength value ≤ blockWindowPrepBits arity offset pointCode :=
    fun _ hvalue => natBitLength_mono (hvalue.trans (Nat.le_max_right _ _))
  have hoffset := hrequest offset (Nat.left_le_pair offset pointCode)
  have hpoint := hrequest pointCode (Nat.right_le_pair offset pointCode)
  have harity :=
    hresult arity
      (le_pair_of_le_right (Nat.left_le_pair arity pointCode))
  have htail :=
    hresult (Nat.pair arity pointCode) (le_pair_of_le_right (le_refl _))
  have houtput := hresult _ (le_refl _)
  rw [show 6 = 5 + 1 by omega]
  rw [run_unpairLeft_instruction (value := offset) (by rfl) rfl
    (by simp [initialNPOracleState]) hoffset]
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairRight_instruction (value := pointCode) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hpoint]
  rw [show 4 = 3 + 1 by omega]
  rw [run_set_instruction (value := arity) (by rfl) rfl harity]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair arity pointCode) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) htail]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (value := bitSliceInput offset arity pointCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, bitSliceInput])
    houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

/-! ### The window chain -/

private def blockWindowTailTwo (arity : ℕ) : NPOracleProgram :=
  linkPrograms (blockWindowPrepProgram arity) bitSliceProgram

private def blockWindowTailOne (arity : ℕ) : NPOracleProgram :=
  linkPrograms (preserveRightProgram bitSerialMulProgram)
    (blockWindowTailTwo arity)

/-- **The block window stage.**  One fixed oracle-free program turning the
requested `pair block pointCode` into the arity-wide digit window of the point
code at that block's offset. -/
def blockWindowProgram (arity : ℕ) : NPOracleProgram :=
  linkPrograms (blockOffsetPrepProgram arity) (blockWindowTailOne arity)

theorem blockWindowProgram_oracleFree (arity : ℕ) :
    OracleFree (blockWindowProgram arity) := by
  apply oracleFree_linkPrograms (blockOffsetPrepProgram_oracleFree arity)
  apply oracleFree_linkPrograms
  · exact preserveRightProgram_oracleFree bitSerialMulProgram
      bitSerialMulProgram_oracleFree
  exact oracleFree_linkPrograms (blockWindowPrepProgram_oracleFree arity)
    bitSliceProgram_oracleFree

def blockWindowFuel (arity : ℕ) : ℕ :=
  linkFuel (blockWindowTailOne arity) 6 <|
    linkFuel (blockWindowTailTwo arity)
      (preserveRightFuel (bitSerialMulFuel arity)) <|
      linkFuel bitSliceProgram 6 (bitSliceFuel arity)

def blockWindowBits (inputLength arity block pointCode : ℕ) : ℕ :=
  occurrenceStageBits inputLength (blockOffsetPrepBits arity block pointCode) <|
    occurrenceStageBits inputLength
      (preserveRightBits (bitSerialMulBits inputLength block arity)
        (bitSerialMulInput block arity) pointCode (block * arity)) <|
      occurrenceStageBits inputLength
        (blockWindowPrepBits arity (block * arity) pointCode)
        (bitSliceBits inputLength (block * arity) arity pointCode)

theorem run_blockWindowProgram (inputLength arity block pointCode : ℕ) :
    runNPOracleProgram (blockWindowProgram arity)
        (blockWindowBits inputLength arity block pointCode)
        (blockWindowFuel arity)
        (initialNPOracleState inputLength (Nat.pair block pointCode)) =
      some (bitSlice (block * arity) arity pointCode) := by
  have hproduct :
      runNPOracleProgram (preserveRightProgram bitSerialMulProgram)
          (preserveRightBits (bitSerialMulBits inputLength block arity)
            (bitSerialMulInput block arity) pointCode (block * arity))
          (preserveRightFuel (bitSerialMulFuel arity))
          (initialNPOracleState inputLength
            (blockOffsetPrepOutput arity block pointCode)) =
        some (Nat.pair (block * arity) pointCode) :=
    run_preserveRightProgram bitSerialMulProgram inputLength
      (bitSerialMulBits inputLength block arity) (bitSerialMulFuel arity)
      (bitSerialMulInput block arity) pointCode (block * arity)
      (run_bitSerialMulProgram inputLength block arity)
  exact run_occurrenceStage
    (run_blockOffsetPrepProgram inputLength arity block pointCode)
    (run_occurrenceStage hproduct
      (run_occurrenceStage
        (run_blockWindowPrepProgram inputLength arity (block * arity) pointCode)
        (run_bitSliceProgram inputLength (block * arity) arity pointCode)))

/-! ## 3. The native occurrence code of one block window

Three windows of the block window are repacked into the occurrence ABI of
`CaseTwoOccurrenceProgram`.  The occurrence position digit is read first, by a
single register-indexed `testBit`, so that the block window itself may be
consumed by the two remaining slices. -/

/-! ### 3.1 The low input window and the position digit

Register ABI: `r2` the position index, `r3` the position digit, `r4` the
retained context, `r5`/`r6` the slice immediates, `r7`/`r8` the slice
request. -/

def blockDigitPrepProgram
    (inputArity paddedInputBits paddedClauseBits : ℕ) : NPOracleProgram :=
  [ .set 2 (paddedInputBits + paddedClauseBits) 1
  , .testBit 0 2 3 2
  , .pair 3 0 4 3
  , .set 5 0 4
  , .set 6 inputArity 5
  , .pair 6 0 7 6
  , .pair 5 7 8 7
  , .pair 8 4 0 8
  , .halt 0
  ]

@[simp] theorem blockDigitPrepProgram_oracleFree
    (inputArity paddedInputBits paddedClauseBits : ℕ) :
    OracleFree
      (blockDigitPrepProgram inputArity paddedInputBits paddedClauseBits) := by
  rfl

def blockDigitPrepOutput
    (inputArity paddedInputBits paddedClauseBits window : ℕ) : ℕ :=
  Nat.pair (bitSliceInput 0 inputArity window)
    (Nat.pair (window.testBit (paddedInputBits + paddedClauseBits)).toNat
      window)

def blockDigitPrepBits
    (inputArity paddedInputBits paddedClauseBits window : ℕ) : ℕ :=
  natBitLength
    (max (paddedInputBits + paddedClauseBits)
      (max window
        (blockDigitPrepOutput inputArity paddedInputBits paddedClauseBits
          window)))

theorem run_blockDigitPrepProgram
    (inputLength inputArity paddedInputBits paddedClauseBits window : ℕ) :
    runNPOracleProgram
        (blockDigitPrepProgram inputArity paddedInputBits paddedClauseBits)
        (blockDigitPrepBits inputArity paddedInputBits paddedClauseBits window)
        9 (initialNPOracleState inputLength window) =
      some
        (blockDigitPrepOutput inputArity paddedInputBits paddedClauseBits
          window) := by
  have hindex :
      natBitLength (paddedInputBits + paddedClauseBits) ≤
        blockDigitPrepBits inputArity paddedInputBits paddedClauseBits window :=
    natBitLength_mono (Nat.le_max_left _ _)
  have hwindow :
      natBitLength window ≤
        blockDigitPrepBits inputArity paddedInputBits paddedClauseBits window :=
    natBitLength_mono ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _))
  have hresult : ∀ value : ℕ,
      value ≤
        blockDigitPrepOutput inputArity paddedInputBits paddedClauseBits
          window →
      natBitLength value ≤
        blockDigitPrepBits inputArity paddedInputBits paddedClauseBits
          window :=
    fun _ hvalue =>
      natBitLength_mono
        (hvalue.trans ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _)))
  have hdigit :=
    hresult (window.testBit (paddedInputBits + paddedClauseBits)).toNat
      (le_pair_of_le_right (Nat.left_le_pair _ _))
  have hcontext :=
    hresult
      (Nat.pair (window.testBit (paddedInputBits + paddedClauseBits)).toNat
        window)
      (le_pair_of_le_right (le_refl _))
  have hzero := hresult 0 (Nat.zero_le _)
  have harity :=
    hresult inputArity
      (le_pair_of_le_left
        (le_pair_of_le_right (Nat.left_le_pair inputArity window)))
  have htail :=
    hresult (Nat.pair inputArity window)
      (le_pair_of_le_left (Nat.right_le_pair 0 (Nat.pair inputArity window)))
  have hslice :=
    hresult (bitSliceInput 0 inputArity window)
      (le_pair_of_le_left (le_refl _))
  have houtput := hresult _ (le_refl _)
  rw [show 9 = 8 + 1 by omega]
  rw [run_set_instruction (value := paddedInputBits + paddedClauseBits)
    (by rfl) rfl hindex]
  rw [show 8 = 7 + 1 by omega]
  rw [run_testBit_instruction
    (value := (window.testBit (paddedInputBits + paddedClauseBits)).toNat)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hdigit]
  rw [show 7 = 6 + 1 by omega]
  rw [run_pair_instruction
    (value :=
      Nat.pair (window.testBit (paddedInputBits + paddedClauseBits)).toNat
        window)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hcontext]
  rw [show 6 = 5 + 1 by omega]
  rw [run_set_instruction (value := 0) (by rfl) rfl hzero]
  rw [show 5 = 4 + 1 by omega]
  rw [run_set_instruction (value := inputArity) (by rfl) rfl harity]
  rw [show 4 = 3 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair inputArity window) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    htail]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction (value := bitSliceInput 0 inputArity window)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, bitSliceInput])
    hslice]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction
    (value :=
      blockDigitPrepOutput inputArity paddedInputBits paddedClauseBits window)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, blockDigitPrepOutput])
    houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

/-- The low input window and the position digit, computed. -/
def blockLowStageProgram
    (inputArity paddedInputBits paddedClauseBits : ℕ) : NPOracleProgram :=
  linkPrograms
    (blockDigitPrepProgram inputArity paddedInputBits paddedClauseBits)
    (preserveRightProgram bitSliceProgram)

theorem blockLowStageProgram_oracleFree
    (inputArity paddedInputBits paddedClauseBits : ℕ) :
    OracleFree
      (blockLowStageProgram inputArity paddedInputBits paddedClauseBits) :=
  oracleFree_linkPrograms
    (blockDigitPrepProgram_oracleFree inputArity paddedInputBits
      paddedClauseBits)
    (preserveRightProgram_oracleFree bitSliceProgram bitSliceProgram_oracleFree)

def blockLowStageFuel (inputArity : ℕ) : ℕ :=
  linkFuel (preserveRightProgram bitSliceProgram) 9
    (preserveRightFuel (bitSliceFuel inputArity))

def blockLowStageBits
    (inputLength inputArity paddedInputBits paddedClauseBits window : ℕ) : ℕ :=
  occurrenceStageBits inputLength
    (blockDigitPrepBits inputArity paddedInputBits paddedClauseBits window)
    (preserveRightBits (bitSliceBits inputLength 0 inputArity window)
      (bitSliceInput 0 inputArity window)
      (Nat.pair (window.testBit (paddedInputBits + paddedClauseBits)).toNat
        window)
      (bitSlice 0 inputArity window))

theorem run_blockLowStageProgram
    (inputLength inputArity paddedInputBits paddedClauseBits window : ℕ) :
    runNPOracleProgram
        (blockLowStageProgram inputArity paddedInputBits paddedClauseBits)
        (blockLowStageBits inputLength inputArity paddedInputBits
          paddedClauseBits window)
        (blockLowStageFuel inputArity)
        (initialNPOracleState inputLength window) =
      some
        (Nat.pair (bitSlice 0 inputArity window)
          (Nat.pair
            (window.testBit (paddedInputBits + paddedClauseBits)).toNat
            window)) :=
  run_occurrenceStage
    (run_blockDigitPrepProgram inputLength inputArity paddedInputBits
      paddedClauseBits window)
    (run_preserveRightProgram bitSliceProgram inputLength
      (bitSliceBits inputLength 0 inputArity window)
      (bitSliceFuel inputArity) (bitSliceInput 0 inputArity window)
      (Nat.pair (window.testBit (paddedInputBits + paddedClauseBits)).toNat
        window)
      (bitSlice 0 inputArity window)
      (run_bitSliceProgram inputLength 0 inputArity window))

/-! ### 3.2 The interior clause window

Register ABI: `r2` the low window, `r3` the retained context, `r4` the position
digit, `r5` the block window, `r6` the new context, `r7`/`r9` the slice
immediates, `r8`/`r10` the slice request. -/

def blockClausePrepProgram
    (paddedInputBits nativeClauseBits : ℕ) : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .pair 2 4 6 5
  , .set 7 nativeClauseBits 6
  , .pair 7 5 8 7
  , .set 9 paddedInputBits 8
  , .pair 9 8 10 9
  , .pair 10 6 0 10
  , .halt 0
  ]

@[simp] theorem blockClausePrepProgram_oracleFree
    (paddedInputBits nativeClauseBits : ℕ) :
    OracleFree (blockClausePrepProgram paddedInputBits nativeClauseBits) := by
  rfl

def blockClausePrepOutput
    (paddedInputBits nativeClauseBits low digit window : ℕ) : ℕ :=
  Nat.pair (bitSliceInput paddedInputBits nativeClauseBits window)
    (Nat.pair low digit)

def blockClausePrepBits
    (paddedInputBits nativeClauseBits low digit window : ℕ) : ℕ :=
  natBitLength
    (max (Nat.pair low (Nat.pair digit window))
      (blockClausePrepOutput paddedInputBits nativeClauseBits low digit
        window))

theorem run_blockClausePrepProgram
    (inputLength paddedInputBits nativeClauseBits low digit window : ℕ) :
    runNPOracleProgram
        (blockClausePrepProgram paddedInputBits nativeClauseBits)
        (blockClausePrepBits paddedInputBits nativeClauseBits low digit window)
        11
        (initialNPOracleState inputLength
          (Nat.pair low (Nat.pair digit window))) =
      some
        (blockClausePrepOutput paddedInputBits nativeClauseBits low digit
          window) := by
  have hrequest : ∀ value : ℕ, value ≤ Nat.pair low (Nat.pair digit window) →
      natBitLength value ≤
        blockClausePrepBits paddedInputBits nativeClauseBits low digit window :=
    fun _ hvalue => natBitLength_mono (hvalue.trans (Nat.le_max_left _ _))
  have hresult : ∀ value : ℕ,
      value ≤
        blockClausePrepOutput paddedInputBits nativeClauseBits low digit
          window →
      natBitLength value ≤
        blockClausePrepBits paddedInputBits nativeClauseBits low digit window :=
    fun _ hvalue => natBitLength_mono (hvalue.trans (Nat.le_max_right _ _))
  have hlow := hrequest low (Nat.left_le_pair _ _)
  have hcontext :=
    hrequest (Nat.pair digit window) (Nat.right_le_pair _ _)
  have hdigit :=
    hrequest digit (le_pair_of_le_right (Nat.left_le_pair digit window))
  have hwindow :=
    hrequest window (le_pair_of_le_right (Nat.right_le_pair digit window))
  have hpair :=
    hresult (Nat.pair low digit) (Nat.right_le_pair _ _)
  have hclause :=
    hresult nativeClauseBits
      (le_pair_of_le_left
        (le_pair_of_le_right (Nat.left_le_pair nativeClauseBits window)))
  have htail :=
    hresult (Nat.pair nativeClauseBits window)
      (le_pair_of_le_left (Nat.right_le_pair _ _))
  have hpadded :=
    hresult paddedInputBits (le_pair_of_le_left (Nat.left_le_pair _ _))
  have hslice :=
    hresult (bitSliceInput paddedInputBits nativeClauseBits window)
      (Nat.left_le_pair _ _)
  have houtput := hresult _ (le_refl _)
  rw [show 11 = 10 + 1 by omega]
  rw [run_unpairLeft_instruction (value := low) (by rfl) rfl
    (by simp [initialNPOracleState]) hlow]
  rw [show 10 = 9 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair digit window) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hcontext]
  rw [show 9 = 8 + 1 by omega]
  rw [run_unpairLeft_instruction (value := digit) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hdigit]
  rw [show 8 = 7 + 1 by omega]
  rw [run_unpairRight_instruction (value := window) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hwindow]
  rw [show 7 = 6 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair low digit) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hpair]
  rw [show 6 = 5 + 1 by omega]
  rw [run_set_instruction (value := nativeClauseBits) (by rfl) rfl hclause]
  rw [show 5 = 4 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair nativeClauseBits window)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) htail]
  rw [show 4 = 3 + 1 by omega]
  rw [run_set_instruction (value := paddedInputBits) (by rfl) rfl hpadded]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction
    (value := bitSliceInput paddedInputBits nativeClauseBits window)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, bitSliceInput])
    hslice]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction
    (value :=
      blockClausePrepOutput paddedInputBits nativeClauseBits low digit window)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, blockClausePrepOutput])
    houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

/-- The interior clause window, computed. -/
def blockClauseStageProgram
    (paddedInputBits nativeClauseBits : ℕ) : NPOracleProgram :=
  linkPrograms (blockClausePrepProgram paddedInputBits nativeClauseBits)
    (preserveRightProgram bitSliceProgram)

theorem blockClauseStageProgram_oracleFree
    (paddedInputBits nativeClauseBits : ℕ) :
    OracleFree (blockClauseStageProgram paddedInputBits nativeClauseBits) :=
  oracleFree_linkPrograms
    (blockClausePrepProgram_oracleFree paddedInputBits nativeClauseBits)
    (preserveRightProgram_oracleFree bitSliceProgram bitSliceProgram_oracleFree)

def blockClauseStageFuel (nativeClauseBits : ℕ) : ℕ :=
  linkFuel (preserveRightProgram bitSliceProgram) 11
    (preserveRightFuel (bitSliceFuel nativeClauseBits))

def blockClauseStageBits
    (inputLength paddedInputBits nativeClauseBits low digit window : ℕ) : ℕ :=
  occurrenceStageBits inputLength
    (blockClausePrepBits paddedInputBits nativeClauseBits low digit window)
    (preserveRightBits
      (bitSliceBits inputLength paddedInputBits nativeClauseBits window)
      (bitSliceInput paddedInputBits nativeClauseBits window)
      (Nat.pair low digit)
      (bitSlice paddedInputBits nativeClauseBits window))

theorem run_blockClauseStageProgram
    (inputLength paddedInputBits nativeClauseBits low digit window : ℕ) :
    runNPOracleProgram
        (blockClauseStageProgram paddedInputBits nativeClauseBits)
        (blockClauseStageBits inputLength paddedInputBits nativeClauseBits low
          digit window)
        (blockClauseStageFuel nativeClauseBits)
        (initialNPOracleState inputLength
          (Nat.pair low (Nat.pair digit window))) =
      some
        (Nat.pair (bitSlice paddedInputBits nativeClauseBits window)
          (Nat.pair low digit)) :=
  run_occurrenceStage
    (run_blockClausePrepProgram inputLength paddedInputBits nativeClauseBits
      low digit window)
    (run_preserveRightProgram bitSliceProgram inputLength
      (bitSliceBits inputLength paddedInputBits nativeClauseBits window)
      (bitSliceFuel nativeClauseBits)
      (bitSliceInput paddedInputBits nativeClauseBits window)
      (Nat.pair low digit)
      (bitSlice paddedInputBits nativeClauseBits window)
      (run_bitSliceProgram inputLength paddedInputBits nativeClauseBits window))

/-! ### 3.3 The two scalings and the digit sum

The instruction set's `shiftLeft` takes a compile-time amount only, so both
scalings go through `RuntimeLeftShiftProgram`.  Register ABI of the two
adapters: `r2` the value to scale, `r3` the retained context, `r4`/`r5` its
fields, `r6` the running sum, `r7` the exponent, `r8` the shift request. -/

def blockClauseShiftPrepProgram (inputArity : ℕ) : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .set 4 inputArity 3
  , .pair 4 2 5 4
  , .pair 5 3 0 5
  , .halt 0
  ]

@[simp] theorem blockClauseShiftPrepProgram_oracleFree (inputArity : ℕ) :
    OracleFree (blockClauseShiftPrepProgram inputArity) := by
  rfl

def blockClauseShiftPrepOutput
    (inputArity clause low digit : ℕ) : ℕ :=
  Nat.pair (runtimeLeftShiftInput inputArity clause) (Nat.pair low digit)

def blockClauseShiftPrepBits (inputArity clause low digit : ℕ) : ℕ :=
  natBitLength
    (max (Nat.pair clause (Nat.pair low digit))
      (blockClauseShiftPrepOutput inputArity clause low digit))

theorem run_blockClauseShiftPrepProgram
    (inputLength inputArity clause low digit : ℕ) :
    runNPOracleProgram (blockClauseShiftPrepProgram inputArity)
        (blockClauseShiftPrepBits inputArity clause low digit) 6
        (initialNPOracleState inputLength
          (Nat.pair clause (Nat.pair low digit))) =
      some (blockClauseShiftPrepOutput inputArity clause low digit) := by
  have hrequest : ∀ value : ℕ, value ≤ Nat.pair clause (Nat.pair low digit) →
      natBitLength value ≤
        blockClauseShiftPrepBits inputArity clause low digit :=
    fun _ hvalue => natBitLength_mono (hvalue.trans (Nat.le_max_left _ _))
  have hresult : ∀ value : ℕ,
      value ≤ blockClauseShiftPrepOutput inputArity clause low digit →
      natBitLength value ≤
        blockClauseShiftPrepBits inputArity clause low digit :=
    fun _ hvalue => natBitLength_mono (hvalue.trans (Nat.le_max_right _ _))
  have hclause := hrequest clause (Nat.left_le_pair _ _)
  have hcontext := hrequest (Nat.pair low digit) (Nat.right_le_pair _ _)
  have harity :=
    hresult inputArity
      (le_pair_of_le_left (Nat.left_le_pair inputArity clause))
  have hshift :=
    hresult (runtimeLeftShiftInput inputArity clause)
      (Nat.left_le_pair _ _)
  have houtput := hresult _ (le_refl _)
  rw [show 6 = 5 + 1 by omega]
  rw [run_unpairLeft_instruction (value := clause) (by rfl) rfl
    (by simp [initialNPOracleState]) hclause]
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair low digit) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hcontext]
  rw [show 4 = 3 + 1 by omega]
  rw [run_set_instruction (value := inputArity) (by rfl) rfl harity]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction (value := runtimeLeftShiftInput inputArity clause)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, runtimeLeftShiftInput])
    hshift]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction
    (value := blockClauseShiftPrepOutput inputArity clause low digit)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      blockClauseShiftPrepOutput])
    houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

/-- The clause window scaled to its place in the occurrence code. -/
def blockClauseShiftStageProgram (inputArity : ℕ) : NPOracleProgram :=
  linkPrograms (blockClauseShiftPrepProgram inputArity)
    (preserveRightProgram runtimeLeftShiftProgram)

theorem blockClauseShiftStageProgram_oracleFree (inputArity : ℕ) :
    OracleFree (blockClauseShiftStageProgram inputArity) :=
  oracleFree_linkPrograms (blockClauseShiftPrepProgram_oracleFree inputArity)
    (preserveRightProgram_oracleFree runtimeLeftShiftProgram
      runtimeLeftShiftProgram_oracleFree)

def blockClauseShiftStageFuel (inputArity clause : ℕ) : ℕ :=
  linkFuel (preserveRightProgram runtimeLeftShiftProgram) 6
    (preserveRightFuel (runtimeLeftShiftFuel inputArity clause))

def blockClauseShiftStageBits
    (inputLength inputArity clause low digit : ℕ) : ℕ :=
  occurrenceStageBits inputLength
    (blockClauseShiftPrepBits inputArity clause low digit)
    (preserveRightBits (runtimeLeftShiftBits inputLength inputArity clause)
      (runtimeLeftShiftInput inputArity clause) (Nat.pair low digit)
      (2 ^ inputArity * clause))

theorem run_blockClauseShiftStageProgram
    (inputLength inputArity clause low digit : ℕ) :
    runNPOracleProgram (blockClauseShiftStageProgram inputArity)
        (blockClauseShiftStageBits inputLength inputArity clause low digit)
        (blockClauseShiftStageFuel inputArity clause)
        (initialNPOracleState inputLength
          (Nat.pair clause (Nat.pair low digit))) =
      some (Nat.pair (2 ^ inputArity * clause) (Nat.pair low digit)) :=
  run_occurrenceStage
    (run_blockClauseShiftPrepProgram inputLength inputArity clause low digit)
    (run_preserveRightProgram runtimeLeftShiftProgram inputLength
      (runtimeLeftShiftBits inputLength inputArity clause)
      (runtimeLeftShiftFuel inputArity clause)
      (runtimeLeftShiftInput inputArity clause) (Nat.pair low digit)
      (2 ^ inputArity * clause)
      (run_runtimeLeftShiftProgram inputLength inputArity clause))

def blockDigitShiftPrepProgram
    (inputArity nativeClauseBits : ℕ) : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .add 4 2 6 5
  , .set 7 (inputArity + nativeClauseBits) 6
  , .pair 7 5 8 7
  , .pair 8 6 0 8
  , .halt 0
  ]

@[simp] theorem blockDigitShiftPrepProgram_oracleFree
    (inputArity nativeClauseBits : ℕ) :
    OracleFree (blockDigitShiftPrepProgram inputArity nativeClauseBits) := by
  rfl

def blockDigitShiftPrepOutput
    (inputArity nativeClauseBits scaledClause low digit : ℕ) : ℕ :=
  Nat.pair (runtimeLeftShiftInput (inputArity + nativeClauseBits) digit)
    (low + scaledClause)

def blockDigitShiftPrepBits
    (inputArity nativeClauseBits scaledClause low digit : ℕ) : ℕ :=
  natBitLength
    (max (Nat.pair scaledClause (Nat.pair low digit))
      (blockDigitShiftPrepOutput inputArity nativeClauseBits scaledClause low
        digit))

theorem run_blockDigitShiftPrepProgram
    (inputLength inputArity nativeClauseBits scaledClause low digit : ℕ) :
    runNPOracleProgram (blockDigitShiftPrepProgram inputArity nativeClauseBits)
        (blockDigitShiftPrepBits inputArity nativeClauseBits scaledClause low
          digit)
        9
        (initialNPOracleState inputLength
          (Nat.pair scaledClause (Nat.pair low digit))) =
      some
        (blockDigitShiftPrepOutput inputArity nativeClauseBits scaledClause low
          digit) := by
  have hrequest : ∀ value : ℕ,
      value ≤ Nat.pair scaledClause (Nat.pair low digit) →
      natBitLength value ≤
        blockDigitShiftPrepBits inputArity nativeClauseBits scaledClause low
          digit :=
    fun _ hvalue => natBitLength_mono (hvalue.trans (Nat.le_max_left _ _))
  have hresult : ∀ value : ℕ,
      value ≤
        blockDigitShiftPrepOutput inputArity nativeClauseBits scaledClause low
          digit →
      natBitLength value ≤
        blockDigitShiftPrepBits inputArity nativeClauseBits scaledClause low
          digit :=
    fun _ hvalue => natBitLength_mono (hvalue.trans (Nat.le_max_right _ _))
  have hscaled := hrequest scaledClause (Nat.left_le_pair _ _)
  have hcontext := hrequest (Nat.pair low digit) (Nat.right_le_pair _ _)
  have hlow :=
    hrequest low (le_pair_of_le_right (Nat.left_le_pair low digit))
  have hdigit :=
    hrequest digit (le_pair_of_le_right (Nat.right_le_pair low digit))
  have hsum := hresult (low + scaledClause) (Nat.right_le_pair _ _)
  have hexponent :=
    hresult (inputArity + nativeClauseBits)
      (le_pair_of_le_left
        (Nat.left_le_pair (inputArity + nativeClauseBits) digit))
  have hshift :=
    hresult (runtimeLeftShiftInput (inputArity + nativeClauseBits) digit)
      (Nat.left_le_pair _ _)
  have houtput := hresult _ (le_refl _)
  rw [show 9 = 8 + 1 by omega]
  rw [run_unpairLeft_instruction (value := scaledClause) (by rfl) rfl
    (by simp [initialNPOracleState]) hscaled]
  rw [show 8 = 7 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair low digit) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hcontext]
  rw [show 7 = 6 + 1 by omega]
  rw [run_unpairLeft_instruction (value := low) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hlow]
  rw [show 6 = 5 + 1 by omega]
  rw [run_unpairRight_instruction (value := digit) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hdigit]
  rw [show 5 = 4 + 1 by omega]
  rw [run_add_instruction (value := low + scaledClause) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hsum]
  rw [show 4 = 3 + 1 by omega]
  rw [run_set_instruction (value := inputArity + nativeClauseBits)
    (by rfl) rfl hexponent]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction
    (value := runtimeLeftShiftInput (inputArity + nativeClauseBits) digit)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, runtimeLeftShiftInput])
    hshift]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction
    (value :=
      blockDigitShiftPrepOutput inputArity nativeClauseBits scaledClause low
        digit)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      blockDigitShiftPrepOutput])
    houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

/-- The position digit scaled to its place, with the low two summands already
added. -/
def blockDigitShiftStageProgram
    (inputArity nativeClauseBits : ℕ) : NPOracleProgram :=
  linkPrograms (blockDigitShiftPrepProgram inputArity nativeClauseBits)
    (preserveRightProgram runtimeLeftShiftProgram)

theorem blockDigitShiftStageProgram_oracleFree
    (inputArity nativeClauseBits : ℕ) :
    OracleFree (blockDigitShiftStageProgram inputArity nativeClauseBits) :=
  oracleFree_linkPrograms
    (blockDigitShiftPrepProgram_oracleFree inputArity nativeClauseBits)
    (preserveRightProgram_oracleFree runtimeLeftShiftProgram
      runtimeLeftShiftProgram_oracleFree)

def blockDigitShiftStageFuel
    (inputArity nativeClauseBits digit : ℕ) : ℕ :=
  linkFuel (preserveRightProgram runtimeLeftShiftProgram) 9
    (preserveRightFuel
      (runtimeLeftShiftFuel (inputArity + nativeClauseBits) digit))

def blockDigitShiftStageBits
    (inputLength inputArity nativeClauseBits scaledClause low digit : ℕ) : ℕ :=
  occurrenceStageBits inputLength
    (blockDigitShiftPrepBits inputArity nativeClauseBits scaledClause low
      digit)
    (preserveRightBits
      (runtimeLeftShiftBits inputLength (inputArity + nativeClauseBits) digit)
      (runtimeLeftShiftInput (inputArity + nativeClauseBits) digit)
      (low + scaledClause)
      (2 ^ (inputArity + nativeClauseBits) * digit))

theorem run_blockDigitShiftStageProgram
    (inputLength inputArity nativeClauseBits scaledClause low digit : ℕ) :
    runNPOracleProgram
        (blockDigitShiftStageProgram inputArity nativeClauseBits)
        (blockDigitShiftStageBits inputLength inputArity nativeClauseBits
          scaledClause low digit)
        (blockDigitShiftStageFuel inputArity nativeClauseBits digit)
        (initialNPOracleState inputLength
          (Nat.pair scaledClause (Nat.pair low digit))) =
      some
        (Nat.pair (2 ^ (inputArity + nativeClauseBits) * digit)
          (low + scaledClause)) :=
  run_occurrenceStage
    (run_blockDigitShiftPrepProgram inputLength inputArity nativeClauseBits
      scaledClause low digit)
    (run_preserveRightProgram runtimeLeftShiftProgram inputLength
      (runtimeLeftShiftBits inputLength (inputArity + nativeClauseBits) digit)
      (runtimeLeftShiftFuel (inputArity + nativeClauseBits) digit)
      (runtimeLeftShiftInput (inputArity + nativeClauseBits) digit)
      (low + scaledClause)
      (2 ^ (inputArity + nativeClauseBits) * digit)
      (run_runtimeLeftShiftProgram inputLength (inputArity + nativeClauseBits)
        digit))

/-- The final addition of the occurrence code. -/
def blockCodeSumProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .add 3 2 0 3
  , .halt 0
  ]

@[simp] theorem blockCodeSumProgram_oracleFree :
    OracleFree blockCodeSumProgram := by
  rfl

def blockCodeSumBits (left right : ℕ) : ℕ :=
  natBitLength (max (Nat.pair left right) (right + left))

theorem run_blockCodeSumProgram (inputLength left right : ℕ) :
    runNPOracleProgram blockCodeSumProgram (blockCodeSumBits left right) 4
        (initialNPOracleState inputLength (Nat.pair left right)) =
      some (right + left) := by
  have hrequest : ∀ value : ℕ, value ≤ Nat.pair left right →
      natBitLength value ≤ blockCodeSumBits left right :=
    fun _ hvalue => natBitLength_mono (hvalue.trans (Nat.le_max_left _ _))
  have hleft := hrequest left (Nat.left_le_pair _ _)
  have hright := hrequest right (Nat.right_le_pair _ _)
  have hsum : natBitLength (right + left) ≤ blockCodeSumBits left right :=
    natBitLength_mono (Nat.le_max_right _ _)
  rw [show 4 = 3 + 1 by omega]
  rw [run_unpairLeft_instruction (value := left) (by rfl) rfl
    (by simp [initialNPOracleState]) hleft]
  rw [show 3 = 2 + 1 by omega]
  rw [run_unpairRight_instruction (value := right) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hright]
  rw [show 2 = 1 + 1 by omega]
  rw [run_add_instruction (value := right + left) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hsum]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hsum

/-! ### 3.4 The native occurrence code chain -/

private def blockNativeCodeTailThree
    (inputArity nativeClauseBits : ℕ) : NPOracleProgram :=
  linkPrograms (blockDigitShiftStageProgram inputArity nativeClauseBits)
    blockCodeSumProgram

private def blockNativeCodeTailTwo
    (inputArity nativeClauseBits : ℕ) : NPOracleProgram :=
  linkPrograms (blockClauseShiftStageProgram inputArity)
    (blockNativeCodeTailThree inputArity nativeClauseBits)

private def blockNativeCodeTailOne
    (inputArity paddedInputBits nativeClauseBits : ℕ) : NPOracleProgram :=
  linkPrograms (blockClauseStageProgram paddedInputBits nativeClauseBits)
    (blockNativeCodeTailTwo inputArity nativeClauseBits)

/-- **The native occurrence code, computed.**  One fixed oracle-free program
turning one block window into the occurrence request payload of
`CaseTwoOccurrenceProgram`. -/
def blockNativeCodeProgram
    (inputArity paddedInputBits nativeClauseBits paddedClauseBits : ℕ) :
    NPOracleProgram :=
  linkPrograms
    (blockLowStageProgram inputArity paddedInputBits paddedClauseBits)
    (blockNativeCodeTailOne inputArity paddedInputBits nativeClauseBits)

theorem blockNativeCodeProgram_oracleFree
    (inputArity paddedInputBits nativeClauseBits paddedClauseBits : ℕ) :
    OracleFree
      (blockNativeCodeProgram inputArity paddedInputBits nativeClauseBits
        paddedClauseBits) := by
  apply oracleFree_linkPrograms
    (blockLowStageProgram_oracleFree inputArity paddedInputBits
      paddedClauseBits)
  apply oracleFree_linkPrograms
    (blockClauseStageProgram_oracleFree paddedInputBits nativeClauseBits)
  apply oracleFree_linkPrograms
    (blockClauseShiftStageProgram_oracleFree inputArity)
  exact oracleFree_linkPrograms
    (blockDigitShiftStageProgram_oracleFree inputArity nativeClauseBits)
    blockCodeSumProgram_oracleFree

def blockNativeCodeFuel
    (inputArity paddedInputBits nativeClauseBits paddedClauseBits
      window : ℕ) : ℕ :=
  linkFuel (blockNativeCodeTailOne inputArity paddedInputBits nativeClauseBits)
    (blockLowStageFuel inputArity) <|
    linkFuel (blockNativeCodeTailTwo inputArity nativeClauseBits)
      (blockClauseStageFuel nativeClauseBits) <|
      linkFuel (blockNativeCodeTailThree inputArity nativeClauseBits)
        (blockClauseShiftStageFuel inputArity
          (bitSlice paddedInputBits nativeClauseBits window)) <|
        linkFuel blockCodeSumProgram
          (blockDigitShiftStageFuel inputArity nativeClauseBits
            (window.testBit (paddedInputBits + paddedClauseBits)).toNat)
          4

def blockNativeCodeBits
    (inputLength inputArity paddedInputBits nativeClauseBits paddedClauseBits
      window : ℕ) : ℕ :=
  occurrenceStageBits inputLength
    (blockLowStageBits inputLength inputArity paddedInputBits paddedClauseBits
      window) <|
    occurrenceStageBits inputLength
      (blockClauseStageBits inputLength paddedInputBits nativeClauseBits
        (bitSlice 0 inputArity window)
        (window.testBit (paddedInputBits + paddedClauseBits)).toNat window) <|
      occurrenceStageBits inputLength
        (blockClauseShiftStageBits inputLength inputArity
          (bitSlice paddedInputBits nativeClauseBits window)
          (bitSlice 0 inputArity window)
          (window.testBit (paddedInputBits + paddedClauseBits)).toNat) <|
        occurrenceStageBits inputLength
          (blockDigitShiftStageBits inputLength inputArity nativeClauseBits
            (2 ^ inputArity * bitSlice paddedInputBits nativeClauseBits window)
            (bitSlice 0 inputArity window)
            (window.testBit (paddedInputBits + paddedClauseBits)).toNat)
          (blockCodeSumBits
            (2 ^ (inputArity + nativeClauseBits) *
              (window.testBit (paddedInputBits + paddedClauseBits)).toNat)
            (bitSlice 0 inputArity window +
              2 ^ inputArity *
                bitSlice paddedInputBits nativeClauseBits window))

theorem run_blockNativeCodeProgram
    (inputLength inputArity paddedInputBits nativeClauseBits paddedClauseBits
      window : ℕ) :
    runNPOracleProgram
        (blockNativeCodeProgram inputArity paddedInputBits nativeClauseBits
          paddedClauseBits)
        (blockNativeCodeBits inputLength inputArity paddedInputBits
          nativeClauseBits paddedClauseBits window)
        (blockNativeCodeFuel inputArity paddedInputBits nativeClauseBits
          paddedClauseBits window)
        (initialNPOracleState inputLength window) =
      some
        (nativeOccurrenceCode inputArity paddedInputBits nativeClauseBits
          paddedClauseBits window) := by
  rw [nativeOccurrenceCode]
  exact run_occurrenceStage
    (run_blockLowStageProgram inputLength inputArity paddedInputBits
      paddedClauseBits window)
    (run_occurrenceStage
      (run_blockClauseStageProgram inputLength paddedInputBits nativeClauseBits
        (bitSlice 0 inputArity window)
        (window.testBit (paddedInputBits + paddedClauseBits)).toNat window)
      (run_occurrenceStage
        (run_blockClauseShiftStageProgram inputLength inputArity
          (bitSlice paddedInputBits nativeClauseBits window)
          (bitSlice 0 inputArity window)
          (window.testBit (paddedInputBits + paddedClauseBits)).toNat)
        (run_occurrenceStage
          (run_blockDigitShiftStageProgram inputLength inputArity
            nativeClauseBits
            (2 ^ inputArity * bitSlice paddedInputBits nativeClauseBits window)
            (bitSlice 0 inputArity window)
            (window.testBit (paddedInputBits + paddedClauseBits)).toNat)
          (run_blockCodeSumProgram inputLength
            (2 ^ (inputArity + nativeClauseBits) *
              (window.testBit (paddedInputBits + paddedClauseBits)).toNat)
            (bitSlice 0 inputArity window +
              2 ^ inputArity *
                bitSlice paddedInputBits nativeClauseBits window)))))

/-! ## 4. The assembled per-block occurrence callee

Register ABI of the last adapter: `r2` the encoded circuit, `r3` the encoded
request tail, `r4` the circuit size, `r5` the sized tail, `r6` the circuit
arity. -/

def blockOccurrenceFramePrepProgram
    (inputArity circuitSize encoded : ℕ) : NPOracleProgram :=
  [ .set 2 encoded 1
  , .pair 2 0 3 2
  , .set 4 circuitSize 3
  , .pair 4 3 5 4
  , .set 6 inputArity 5
  , .pair 6 5 0 6
  , .halt 0
  ]

@[simp] theorem blockOccurrenceFramePrepProgram_oracleFree
    (inputArity circuitSize encoded : ℕ) :
    OracleFree
      (blockOccurrenceFramePrepProgram inputArity circuitSize encoded) := by
  rfl

def blockOccurrenceFramePrepBits
    (inputArity circuitSize encoded code : ℕ) : ℕ :=
  natBitLength (caseTwoOccurrenceInput inputArity circuitSize encoded code)

theorem run_blockOccurrenceFramePrepProgram
    (inputLength inputArity circuitSize encoded code : ℕ) :
    runNPOracleProgram
        (blockOccurrenceFramePrepProgram inputArity circuitSize encoded)
        (blockOccurrenceFramePrepBits inputArity circuitSize encoded code) 7
        (initialNPOracleState inputLength code) =
      some (caseTwoOccurrenceInput inputArity circuitSize encoded code) := by
  have hresult : ∀ value : ℕ,
      value ≤ caseTwoOccurrenceInput inputArity circuitSize encoded code →
      natBitLength value ≤
        blockOccurrenceFramePrepBits inputArity circuitSize encoded code :=
    fun _ hvalue => natBitLength_mono hvalue
  have hencoded :=
    hresult encoded
      (le_pair_of_le_right
        (le_pair_of_le_right (Nat.left_le_pair encoded code)))
  have hcode :=
    hresult (Nat.pair encoded code)
      (le_pair_of_le_right (le_pair_of_le_right (le_refl _)))
  have hsize :=
    hresult circuitSize
      (le_pair_of_le_right (Nat.left_le_pair circuitSize _))
  have htail :=
    hresult (Nat.pair circuitSize (Nat.pair encoded code))
      (Nat.right_le_pair _ _)
  have harity := hresult inputArity (Nat.left_le_pair _ _)
  have houtput := hresult _ (le_refl _)
  rw [show 7 = 6 + 1 by omega]
  rw [run_set_instruction (value := encoded) (by rfl) rfl hencoded]
  rw [show 6 = 5 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair encoded code) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hcode]
  rw [show 5 = 4 + 1 by omega]
  rw [run_set_instruction (value := circuitSize) (by rfl) rfl hsize]
  rw [show 4 = 3 + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair circuitSize (Nat.pair encoded code)) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) htail]
  rw [show 3 = 2 + 1 by omega]
  rw [run_set_instruction (value := inputArity) (by rfl) rfl harity]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction
    (value := caseTwoOccurrenceInput inputArity circuitSize encoded code)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, caseTwoOccurrenceInput])
    houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

private def blockOccurrenceTailTwo (factory : ExecutablePointwisePCPPFactory)
    (inputArity circuitSize encoded : ℕ) : NPOracleProgram :=
  linkPrograms (blockOccurrenceFramePrepProgram inputArity circuitSize encoded)
    (caseTwoOccurrenceProgram factory)

private def blockOccurrenceTailOne (factory : ExecutablePointwisePCPPFactory)
    (inputArity circuitSize encoded paddedInputBits nativeClauseBits
      paddedClauseBits : ℕ) : NPOracleProgram :=
  linkPrograms
    (blockNativeCodeProgram inputArity paddedInputBits nativeClauseBits
      paddedClauseBits)
    (blockOccurrenceTailTwo factory inputArity circuitSize encoded)

/-- **The per-block Case-2 occurrence callee.**  One fixed oracle-free program
receiving `pair block pointCode` and returning the honest occurrence bit of the
published factory at that block's occurrence code. -/
def caseTwoBlockOccurrenceProgram (factory : ExecutablePointwisePCPPFactory)
    (inputArity circuitSize encoded paddedInputBits nativeClauseBits
      paddedClauseBits arity : ℕ) : NPOracleProgram :=
  linkPrograms (blockWindowProgram arity)
    (blockOccurrenceTailOne factory inputArity circuitSize encoded
      paddedInputBits nativeClauseBits paddedClauseBits)

theorem caseTwoBlockOccurrenceProgram_oracleFree
    (factory : ExecutablePointwisePCPPFactory)
    (inputArity circuitSize encoded paddedInputBits nativeClauseBits
      paddedClauseBits arity : ℕ) :
    OracleFree
      (caseTwoBlockOccurrenceProgram factory inputArity circuitSize encoded
        paddedInputBits nativeClauseBits paddedClauseBits arity) := by
  apply oracleFree_linkPrograms (blockWindowProgram_oracleFree arity)
  apply oracleFree_linkPrograms
    (blockNativeCodeProgram_oracleFree inputArity paddedInputBits
      nativeClauseBits paddedClauseBits)
  exact oracleFree_linkPrograms
    (blockOccurrenceFramePrepProgram_oracleFree inputArity circuitSize encoded)
    (caseTwoOccurrenceProgram_oracleFree factory)

def caseTwoBlockOccurrenceFuel (factory : ExecutablePointwisePCPPFactory)
    (inputLength : ℕ) {n : ℕ} (circuit : BooleanCircuit n)
    (paddedInputBits nativeClauseBits paddedClauseBits arity block
      pointCode : ℕ) : ℕ :=
  linkFuel
    (blockOccurrenceTailOne factory n circuit.size
      (encodeBooleanCircuit circuit) paddedInputBits nativeClauseBits
      paddedClauseBits)
    (blockWindowFuel arity) <|
    linkFuel
      (blockOccurrenceTailTwo factory n circuit.size
        (encodeBooleanCircuit circuit))
      (blockNativeCodeFuel n paddedInputBits nativeClauseBits paddedClauseBits
        (bitSlice (block * arity) arity pointCode)) <|
      linkFuel (caseTwoOccurrenceProgram factory) 7
        (caseTwoOccurrenceFuel factory inputLength circuit
          (caseTwoBlockOccurrenceCode n paddedInputBits nativeClauseBits
            paddedClauseBits arity pointCode block))

noncomputable def caseTwoBlockOccurrenceBits
    (factory : ExecutablePointwisePCPPFactory)
    (inputLength : ℕ) {n : ℕ} (circuit : BooleanCircuit n)
    (paddedInputBits nativeClauseBits paddedClauseBits arity block
      pointCode : ℕ) : ℕ :=
  occurrenceStageBits inputLength
    (blockWindowBits inputLength arity block pointCode) <|
    occurrenceStageBits inputLength
      (blockNativeCodeBits inputLength n paddedInputBits nativeClauseBits
        paddedClauseBits (bitSlice (block * arity) arity pointCode)) <|
      occurrenceStageBits inputLength
        (blockOccurrenceFramePrepBits n circuit.size
          (encodeBooleanCircuit circuit)
          (caseTwoBlockOccurrenceCode n paddedInputBits nativeClauseBits
            paddedClauseBits arity pointCode block))
        (caseTwoOccurrenceBits factory inputLength circuit
          (caseTwoBlockOccurrenceCode n paddedInputBits nativeClauseBits
            paddedClauseBits arity pointCode block))

/-- **Exact execution of the per-block occurrence callee.**  From
`pair block pointCode` alone the fixed program returns the honest occurrence
bit of the published factory at the occurrence code of that block's window of
the requested point. -/
theorem run_caseTwoBlockOccurrenceProgram
    (factory : ExecutablePointwisePCPPFactory)
    (inputLength : ℕ) {n : ℕ} (circuit : BooleanCircuit n)
    (paddedInputBits nativeClauseBits paddedClauseBits arity block
      pointCode : ℕ) :
    runNPOracleProgram
        (caseTwoBlockOccurrenceProgram factory n circuit.size
          (encodeBooleanCircuit circuit) paddedInputBits nativeClauseBits
          paddedClauseBits arity)
        (caseTwoBlockOccurrenceBits factory inputLength circuit
          paddedInputBits nativeClauseBits paddedClauseBits arity block
          pointCode)
        (caseTwoBlockOccurrenceFuel factory inputLength circuit
          paddedInputBits nativeClauseBits paddedClauseBits arity block
          pointCode)
        (initialNPOracleState inputLength (Nat.pair block pointCode)) =
      some
        (caseTwoBlockValue factory circuit n paddedInputBits nativeClauseBits
          paddedClauseBits arity pointCode block).toNat :=
  run_occurrenceStage
    (run_blockWindowProgram inputLength arity block pointCode)
    (run_occurrenceStage
      (run_blockNativeCodeProgram inputLength n paddedInputBits
        nativeClauseBits paddedClauseBits
        (bitSlice (block * arity) arity pointCode))
      (run_occurrenceStage
        (run_blockOccurrenceFramePrepProgram inputLength n circuit.size
          (encodeBooleanCircuit circuit)
          (caseTwoBlockOccurrenceCode n paddedInputBits nativeClauseBits
            paddedClauseBits arity pointCode block))
        (run_caseTwoOccurrenceProgram factory inputLength circuit
          (caseTwoBlockOccurrenceCode n paddedInputBits nativeClauseBits
            paddedClauseBits arity pointCode block))))

/-! ## 5. The callee at the scheduled Case-2 coordinates

Instantiating §4 at the substituted circuit of the recovered oracle gives
exactly the value `CaseTwoSeedBlockListProgram` asks its per-block parameter
for.  The circuit's arity, size, and encoding, the two padded widths, the
native clause width, and the block arity are the stream's immediates. -/

/-- The per-block occurrence callee of the scheduled Case-2 branch. -/
noncomputable def caseTwoScheduledOccurrenceProgram
    (pcppSource : UniformPointwisePCPPSource)
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    {outer : HierarchyOuterPCP source}
    {requiredDegree sourceIndex : ℕ}
    {input : BitInput (sourceLength sourceIndex)}
    (caseTwo :
      CanonicalAcceptingOracle
        (sizeBound := oracleSizeBound requiredDegree)
        (paddedOuterPCP outer) input) : NPOracleProgram :=
  caseTwoBlockOccurrenceProgram pcppSource.factory
    (outer.pcp.nativeWidth (sourceLength sourceIndex))
    (caseTwoSubstitutedCircuit caseTwo).size
    (encodeBooleanCircuit (caseTwoSubstitutedCircuit caseTwo))
    (widthEnvelope outer (sourceLength sourceIndex))
    (caseTwoFactoryPCPP pcppSource caseTwo).clauseBits
    (clauseBitsEnvelope outer pcppSource (oracleSizeBound requiredDegree)
      (sourceLength sourceIndex))
    (seedArity outer pcppSource requiredDegree sourceIndex)

theorem caseTwoScheduledOccurrenceProgram_oracleFree
    (pcppSource : UniformPointwisePCPPSource)
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    {outer : HierarchyOuterPCP source}
    {requiredDegree sourceIndex : ℕ}
    {input : BitInput (sourceLength sourceIndex)}
    (caseTwo :
      CanonicalAcceptingOracle
        (sizeBound := oracleSizeBound requiredDegree)
        (paddedOuterPCP outer) input) :
    OracleFree (caseTwoScheduledOccurrenceProgram pcppSource caseTwo) :=
  caseTwoBlockOccurrenceProgram_oracleFree pcppSource.factory _ _ _ _ _ _ _

/-- Closed fuel envelope of the scheduled callee, eta-reduced in the block
index so that the block-list stage receives a named function. -/
noncomputable def caseTwoScheduledOccurrenceFuel
    (pcppSource : UniformPointwisePCPPSource)
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    {outer : HierarchyOuterPCP source}
    {requiredDegree sourceIndex : ℕ}
    {input : BitInput (sourceLength sourceIndex)}
    (caseTwo :
      CanonicalAcceptingOracle
        (sizeBound := oracleSizeBound requiredDegree)
        (paddedOuterPCP outer) input)
    (inputLength pointCode block : ℕ) : ℕ :=
  caseTwoBlockOccurrenceFuel pcppSource.factory inputLength
    (caseTwoSubstitutedCircuit caseTwo)
    (widthEnvelope outer (sourceLength sourceIndex))
    (caseTwoFactoryPCPP pcppSource caseTwo).clauseBits
    (clauseBitsEnvelope outer pcppSource (oracleSizeBound requiredDegree)
      (sourceLength sourceIndex))
    (seedArity outer pcppSource requiredDegree sourceIndex) block pointCode

/-- Closed register-width envelope of the scheduled callee, eta-reduced in the
block index. -/
noncomputable def caseTwoScheduledOccurrenceBits
    (pcppSource : UniformPointwisePCPPSource)
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    {outer : HierarchyOuterPCP source}
    {requiredDegree sourceIndex : ℕ}
    {input : BitInput (sourceLength sourceIndex)}
    (caseTwo :
      CanonicalAcceptingOracle
        (sizeBound := oracleSizeBound requiredDegree)
        (paddedOuterPCP outer) input)
    (inputLength pointCode block : ℕ) : ℕ :=
  caseTwoBlockOccurrenceBits pcppSource.factory inputLength
    (caseTwoSubstitutedCircuit caseTwo)
    (widthEnvelope outer (sourceLength sourceIndex))
    (caseTwoFactoryPCPP pcppSource caseTwo).clauseBits
    (clauseBitsEnvelope outer pcppSource (oracleSizeBound requiredDegree)
      (sourceLength sourceIndex))
    (seedArity outer pcppSource requiredDegree sourceIndex) block pointCode

/-- **The scheduled per-block occurrence value, executed.**  This is exactly
the hypothesis `CaseTwoSeedBlockListProgram` carries for its per-block
parameter, now a theorem. -/
theorem run_caseTwoScheduledOccurrenceProgram
    (pcppSource : UniformPointwisePCPPSource)
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    {outer : HierarchyOuterPCP source}
    {requiredDegree sourceIndex : ℕ}
    {input : BitInput (sourceLength sourceIndex)}
    (caseTwo :
      CanonicalAcceptingOracle
        (sizeBound := oracleSizeBound requiredDegree)
        (paddedOuterPCP outer) input)
    (inputLength pointCode block : ℕ) :
    runNPOracleProgram (caseTwoScheduledOccurrenceProgram pcppSource caseTwo)
        (caseTwoScheduledOccurrenceBits pcppSource caseTwo inputLength
          pointCode block)
        (caseTwoScheduledOccurrenceFuel pcppSource caseTwo inputLength
          pointCode block)
        (initialNPOracleState inputLength (Nat.pair block pointCode)) =
      some
        (caseTwoScheduledBlockValue pcppSource caseTwo pointCode block).toNat :=
  run_caseTwoBlockOccurrenceProgram pcppSource.factory inputLength
    (caseTwoSubstitutedCircuit caseTwo)
    (widthEnvelope outer (sourceLength sourceIndex))
    (caseTwoFactoryPCPP pcppSource caseTwo).clauseBits
    (clauseBitsEnvelope outer pcppSource (oracleSizeBound requiredDegree)
      (sourceLength sourceIndex))
    (seedArity outer pcppSource requiredDegree sourceIndex) block pointCode

/-! ## 6. The Case-2 chains with the occurrence parameter discharged

Both published schedules now carry no per-block hypothesis at all: the whole
Case-2 branch is one fixed instruction stream over the scheduled immediates. -/

/-- **The inverse schedule's Case-2 target bit, closed.**  The per-block
occurrence hypothesis of
`CaseTwoSeedBlockListProgram.run_caseTwoTargetBitFromPointRangeProgram_inverse`
is discharged by §5. -/
theorem run_caseTwoTargetBitFromPointRangeProgram_inverse_closed
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ) (target : ℕ)
    (hlarge :
      inverseCaseOneTargetOnset contracts outer advantageExponent ≤ target)
    (hyes : source.hierarchyMachine.accepts
      (sourceLength (inverseSourceIndex
        (inverseSelectedSource contracts outer
          (inverseCoreAdvantagePower advantageExponent) target)))
      (inverseRefuterInput contracts outer machine advantageExponent target))
    (hrejects : ¬machine.toSemantic.accepts
      (inverseRefuterInput contracts outer machine advantageExponent target))
    (haccepts : ∀ caseTwo : CanonicalAcceptingOracle
        (sizeBound := oracleSizeBound
          (inverseRequiredDegree contracts
            (inverseCoreAdvantagePower advantageExponent)))
        (paddedOuterPCP outer)
        (inverseRefuterInput contracts outer machine advantageExponent target),
      InverseCaseTwoAcceptance contracts outer
        (inverseCoreAdvantagePower advantageExponent)
        (inverseSelectedSource contracts outer
          (inverseCoreAdvantagePower advantageExponent) target)
        caseTwo machine)
    (caseTwo : CanonicalAcceptingOracle
      (sizeBound := oracleSizeBound
        (inverseRequiredDegree contracts
          (inverseCoreAdvantagePower advantageExponent)))
      (paddedOuterPCP outer)
      (inverseRefuterInput contracts outer machine advantageExponent target))
    (hbranch :
      inverseTargetBranch contracts outer machine advantageExponent target
          hyes = .caseTwo caseTwo)
    (point : BitInput target) :
    runNPOracleProgram
        (caseTwoTargetBitFromPointRangeProgram
          (publishedAmplifier contracts).algorithm
          (caseTwoScheduledOccurrenceProgram (publishedPointwisePCPP contracts)
            caseTwo)
          (inverseCopies outer (publishedPointwisePCPP contracts)
            (inverseRate contracts
              (inverseCoreAdvantagePower advantageExponent))
            (inverseSourceIndex
              (inverseSelectedSource contracts outer
                (inverseCoreAdvantagePower advantageExponent) target))))
        (caseTwoTargetBitFromPointRangeBits target
          (inverseCopies outer (publishedPointwisePCPP contracts)
            (inverseRate contracts
              (inverseCoreAdvantagePower advantageExponent))
            (inverseSourceIndex
              (inverseSelectedSource contracts outer
                (inverseCoreAdvantagePower advantageExponent) target)))
          (encodeBitInput point)
          (caseTwoScheduledOccurrenceBits (publishedPointwisePCPP contracts)
            caseTwo target (encodeBitInput point))
          (caseTwoScheduledBlockValue (publishedPointwisePCPP contracts)
            caseTwo (encodeBitInput point))
          ((List.range
            (inverseCopies outer (publishedPointwisePCPP contracts)
              (inverseRate contracts
                (inverseCoreAdvantagePower advantageExponent))
              (inverseSourceIndex
                (inverseSelectedSource contracts outer
                  (inverseCoreAdvantagePower advantageExponent) target)))).map
            (caseTwoScheduledBlockValue (publishedPointwisePCPP contracts)
              caseTwo (encodeBitInput point))))
        (caseTwoTargetBitFromPointRangeFuel
          (publishedAmplifier contracts).algorithm
          (caseTwoScheduledOccurrenceProgram (publishedPointwisePCPP contracts)
            caseTwo)
          target
          (inverseCopies outer (publishedPointwisePCPP contracts)
            (inverseRate contracts
              (inverseCoreAdvantagePower advantageExponent))
            (inverseSourceIndex
              (inverseSelectedSource contracts outer
                (inverseCoreAdvantagePower advantageExponent) target)))
          (encodeBitInput point)
          (caseTwoScheduledOccurrenceFuel (publishedPointwisePCPP contracts)
            caseTwo target (encodeBitInput point))
          ((List.range
            (inverseCopies outer (publishedPointwisePCPP contracts)
              (inverseRate contracts
                (inverseCoreAdvantagePower advantageExponent))
              (inverseSourceIndex
                (inverseSelectedSource contracts outer
                  (inverseCoreAdvantagePower advantageExponent) target)))).map
            (caseTwoScheduledBlockValue (publishedPointwisePCPP contracts)
              caseTwo (encodeBitInput point))))
        (initialNPOracleState target (encodeBitInput point)) =
      some
        (inverseCanonicalTargetFunction contracts outer machine
          advantageExponent target hlarge hyes hrejects haccepts point).toNat :=
  run_caseTwoTargetBitFromPointRangeProgram_inverse
    (caseTwoScheduledOccurrenceProgram (publishedPointwisePCPP contracts)
      caseTwo)
    contracts outer machine advantageExponent target hlarge hyes hrejects
    haccepts caseTwo hbranch point
    (caseTwoScheduledOccurrenceBits (publishedPointwisePCPP contracts) caseTwo
      target (encodeBitInput point))
    (caseTwoScheduledOccurrenceFuel (publishedPointwisePCPP contracts) caseTwo
      target (encodeBitInput point))
    (fun block _ =>
      run_caseTwoScheduledOccurrenceProgram (publishedPointwisePCPP contracts)
        caseTwo target (encodeBitInput point) block)

/-- **The fixed schedule's Case-2 target bit, closed.** -/
theorem run_caseTwoTargetBitFromPointRangeProgram_fixed_closed
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (machine : ExecutableWeakNondeterministicMachine)
    (requestedRate target : ℕ)
    (hlarge : fixedCaseOneTargetOnset contracts outer requestedRate ≤ target)
    (hyes : source.hierarchyMachine.accepts
      (sourceLength
        (fixedSelectedSource contracts outer requestedRate target))
      (fixedRefuterInput contracts outer machine requestedRate target))
    (hrejects : ¬machine.toSemantic.accepts
      (fixedRefuterInput contracts outer machine requestedRate target))
    (haccepts : ∀ caseTwo : CanonicalAcceptingOracle
        (sizeBound := oracleSizeBound
          (fixedRequiredDegree contracts requestedRate))
        (paddedOuterPCP outer)
        (fixedRefuterInput contracts outer machine requestedRate target),
      FixedCaseTwoAcceptance contracts outer requestedRate
        (fixedSelectedSource contracts outer requestedRate target)
        caseTwo machine)
    (caseTwo : CanonicalAcceptingOracle
      (sizeBound := oracleSizeBound
        (fixedRequiredDegree contracts requestedRate))
      (paddedOuterPCP outer)
      (fixedRefuterInput contracts outer machine requestedRate target))
    (hbranch :
      fixedTargetBranch contracts outer machine requestedRate target hyes =
        .caseTwo caseTwo)
    (point : BitInput target) :
    runNPOracleProgram
        (caseTwoTargetBitFromPointRangeProgram
          (publishedAmplifier contracts).algorithm
          (caseTwoScheduledOccurrenceProgram (publishedPointwisePCPP contracts)
            caseTwo)
          (fixedCopies (publishedPointwisePCPP contracts)
            (fixedRate contracts requestedRate)))
        (caseTwoTargetBitFromPointRangeBits target
          (fixedCopies (publishedPointwisePCPP contracts)
            (fixedRate contracts requestedRate))
          (encodeBitInput point)
          (caseTwoScheduledOccurrenceBits (publishedPointwisePCPP contracts)
            caseTwo target (encodeBitInput point))
          (caseTwoScheduledBlockValue (publishedPointwisePCPP contracts)
            caseTwo (encodeBitInput point))
          ((List.range
            (fixedCopies (publishedPointwisePCPP contracts)
              (fixedRate contracts requestedRate))).map
            (caseTwoScheduledBlockValue (publishedPointwisePCPP contracts)
              caseTwo (encodeBitInput point))))
        (caseTwoTargetBitFromPointRangeFuel
          (publishedAmplifier contracts).algorithm
          (caseTwoScheduledOccurrenceProgram (publishedPointwisePCPP contracts)
            caseTwo)
          target
          (fixedCopies (publishedPointwisePCPP contracts)
            (fixedRate contracts requestedRate))
          (encodeBitInput point)
          (caseTwoScheduledOccurrenceFuel (publishedPointwisePCPP contracts)
            caseTwo target (encodeBitInput point))
          ((List.range
            (fixedCopies (publishedPointwisePCPP contracts)
              (fixedRate contracts requestedRate))).map
            (caseTwoScheduledBlockValue (publishedPointwisePCPP contracts)
              caseTwo (encodeBitInput point))))
        (initialNPOracleState target (encodeBitInput point)) =
      some
        (fixedCanonicalTargetFunction contracts outer machine requestedRate
          target hlarge hyes hrejects haccepts point).toNat :=
  run_caseTwoTargetBitFromPointRangeProgram_fixed
    (caseTwoScheduledOccurrenceProgram (publishedPointwisePCPP contracts)
      caseTwo)
    contracts outer machine requestedRate target hlarge hyes hrejects
    haccepts caseTwo hbranch point
    (caseTwoScheduledOccurrenceBits (publishedPointwisePCPP contracts) caseTwo
      target (encodeBitInput point))
    (caseTwoScheduledOccurrenceFuel (publishedPointwisePCPP contracts) caseTwo
      target (encodeBitInput point))
    (fun block _ =>
      run_caseTwoScheduledOccurrenceProgram (publishedPointwisePCPP contracts)
        caseTwo target (encodeBitInput point) block)

end NearCubicWires.CaseTwoBlockOccurrenceProgram
